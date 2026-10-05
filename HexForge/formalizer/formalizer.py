"""Step-by-step translation of a deduction proof into Lean 4, plus compilation.

Unlike v0.0 (which handed every hypothesis to a single ``omega``), each deducer
step becomes one Lean ``have`` whose justification cites exactly the dependencies
of that step:

    inventory entry   -> call the Inventory / HexLemmas lemma, close locally
    linear combination-> linarith [the dependency `have`s]
    integer rounding  -> omega      (acting on the single dependency `have`)
    case split        -> by_cases, each branch expanded step by step
    conditional thm   -> apply JucovicTheorem / Barnette_P6Bound with its
                         hypothesis discharged from the trigger dependency

The ``json`` proof steps, the ``md`` proof, and this Lean proof therefore
correspond one-to-one.  A proof that fails to compile is dropped (never patched
back to a monolithic ``omega``).

Statement conventions (spec §4): p_k -> ``maps.p_i k``; the tail/face sums are
the exact Finset sums below; everything with subtraction or a negative
coefficient is stated in ℤ.
"""

from __future__ import annotations

import subprocess
import time
from fractions import Fraction
from math import gcd
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent / "lean"

# v0.6.4 §III: the shared import header.  Every record / batch theorem uses the
# identical preamble so Mathlib is elaborated once per batch file.
LEAN_HEADER = ("import Mathlib\n"
               "import Inventory\n"
               "import HexLemmas\n\n"
               "open Finset\n\n")


# ── v0.6.4 §I: automatic HexLemmas rebuild ───────────────────────────────────
def ensure_hexlemmas_fresh():
    """If ``HexLemmas.lean`` is newer than its compiled ``.olean``, rebuild it with
    ``lake build HexLemmas`` so records never import a stale module.  Raises on a
    build failure (the whole run must stop — every proof imports HexLemmas)."""
    src = LEAN_DIR / "HexLemmas.lean"
    olean = LEAN_DIR / ".lake" / "build" / "lib" / "lean" / "HexLemmas.olean"
    fresh = olean.exists() and olean.stat().st_mtime >= src.stat().st_mtime
    if fresh:
        return "up-to-date"
    print("  HexLemmas.lean changed — running `lake build HexLemmas` ...")
    res = subprocess.run(["lake", "build", "HexLemmas"], cwd=str(LEAN_DIR),
                         capture_output=True, text=True)
    out = (res.stdout + res.stderr).strip()
    if res.returncode != 0 or "error:" in out:
        raise RuntimeError("lake build HexLemmas failed:\n" + out[:4000])
    return "rebuilt"

# ── atom → Lean ℤ expression (M_MAX-aware) ──────────────────────────────────
from ..anvil.inventory import M_MAX, TAIL_VAR, TAIL_COUNT_VARS

_TAIL_START = M_MAX + 1                       # 7 for M_MAX=6, 11 for M_MAX=10
_HAS_LARGE = M_MAX >= 7                       # are p_7..p_{M_MAX} individual?
_SUM_TAIL = f"∑ k ∈ Finset.Ico {_TAIL_START} (maps.m + 1), (maps.p_i k : ℤ)"
_SUM_BIG = "∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)"   # Σ_{k≥7}
_INT = {
    "p_3": "(maps.p_i 3 : ℤ)", "p_4": "(maps.p_i 4 : ℤ)",
    "p_5": "(maps.p_i 5 : ℤ)", "p_6": "(maps.p_i 6 : ℤ)",
    TAIL_VAR: _SUM_TAIL,
    "sum_pk_after_p6": _SUM_BIG,
    "f_2": "∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)",
    "W_tail": f"∑ k ∈ Finset.Ico {_TAIL_START} (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ)",
    "J_tail": f"∑ k ∈ Finset.Ico {_TAIL_START} (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ)",
}
_NAT = {
    "p_3": "maps.p_i 3", "p_4": "maps.p_i 4", "p_5": "maps.p_i 5",
    "p_6": "maps.p_i 6",
    TAIL_VAR: f"∑ k ∈ Finset.Ico {_TAIL_START} (maps.m + 1), maps.p_i k",
    "f_2": "∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k",
}
for _k in range(7, M_MAX + 1):                # individual large faces (none at M_MAX=6)
    _INT[f"p_{_k}"] = f"(maps.p_i {_k} : ℤ)"
    _NAT[f"p_{_k}"] = f"maps.p_i {_k}"

_ORDER = (["p_3", "p_4", "p_5", "p_6"] + [f"p_{k}" for k in range(7, M_MAX + 1)]
          + [TAIL_VAR, "sum_pk_after_p6", "f_2", "W_tail", "J_tail"])
# keep _ORDER free of duplicates (TAIL_VAR == sum_pk_after_p6 at M_MAX=6)
_seen = set()
_ORDER = [v for v in _ORDER if not (v in _seen or _seen.add(v))]

# v0.7.1: at M_MAX=10 the tail sums are over Ico 11, so the tail lemmas are the
# ``_10`` variants (W_tail/J_tail/tail over k≥11); at M_MAX=6 they are over Ico 7.
_TAIL_SUFFIX = "_10" if _HAS_LARGE else ""
_TAIL_LEMMA = {
    name: f"SimplyCon3ConnectedMap.{name}{_TAIL_SUFFIX} maps"
    for name in ("tail_excess", "tail_juc_lower", "tail_juc_upper", "tail_juc_half")
}

_REL = {">=": "≥", "<=": "≤", "==": "=", "=": "="}

_TAILCOUNT_VARS = list(TAIL_COUNT_VARS)


def _nk(coeffs: dict):
    """Normalised key of a linear form (coprime, canonical sign) — matches an
    assumption's LHS to the enclosing by_cases expression regardless of branch."""
    ic = {v: int(c) for v, c in coeffs.items() if int(c) != 0}
    if not ic:
        return ()
    g = 0
    for c in ic.values():
        g = gcd(g, abs(c))
    ic = {v: c // g for v, c in ic.items()}
    for v in _ORDER:
        if ic.get(v, 0) != 0:
            if ic[v] < 0:
                ic = {k: -x for k, x in ic.items()}
            break
    return tuple(sorted(ic.items()))


# ── rendering helpers ───────────────────────────────────────────────────────
def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b) if a and b else max(a, b)


def _clear(coeffs: dict, const: Fraction):
    """Scale by the lcm of all denominators so coefficients/const are integers."""
    vals = list(coeffs.values()) + [const]
    L = 1
    for v in vals:
        L = _lcm(L, Fraction(v).denominator)
    ic = {k: int(Fraction(c) * L) for k, c in coeffs.items() if Fraction(c) != 0}
    k = int(Fraction(const) * L)
    return ic, k


def _render_expr(ic: dict, atoms: dict) -> str:
    terms = []
    for v in _ORDER:
        c = ic.get(v, 0)
        if c == 0:
            continue
        atom = atoms[v]
        piece = atom if abs(c) == 1 else f"{abs(c)} * {atom}"
        terms.append(("-" if c < 0 else "+", piece))
    if not terms:
        return "0"
    sign, first = terms[0]
    out = ("-" + first) if sign == "-" else first
    for sign, piece in terms[1:]:
        out += f" {sign} {piece}"
    return out


def _stmt(coeffs: dict, const: Fraction, rel: str) -> str:
    """Render ``Σ coeffs·atom + const  rel  0`` as an integer ℤ statement
    ``EXPR rel RHS`` (const moved to the right)."""
    ic, k = _clear(coeffs, const)
    expr = _render_expr(ic, _INT)
    return f"{expr} {_REL[rel]} {-k}"


def _two_sided(coeffs: dict, rhs: int, atoms: dict):
    left, right = [], []
    for v in _ORDER:
        c = coeffs.get(v, 0)
        c = int(c) if Fraction(c).denominator == 1 else c
        if c == 0:
            continue
        atom = atoms[v]
        piece = atom if abs(c) == 1 else f"{abs(c)} * {atom}"
        (left if c > 0 else right).append(piece)
    if rhs > 0:
        right.append(str(rhs))
    elif rhs < 0:
        left.append(str(-rhs))
    ls = " + ".join(left) if left else "0"
    rs = " + ".join(right) if right else "0"
    return ls, rs


def _render_affine(ic: dict, const: int) -> str:
    expr = _render_expr(ic, _INT)
    if const == 0:
        return expr
    if expr == "0":
        return str(const)
    return expr + (f" + {const}" if const > 0 else f" - {-const}")


def _display_goal(coeffs: dict, rel: str, rhs: int) -> str:
    """Render ``a·p_6 (≥|≤) RHS`` with p_6 isolated on the left (a > 0)."""
    a = int(coeffs["p_6"])
    left = _INT["p_6"] if a == 1 else f"{a} * {_INT['p_6']}"
    rest = {v: -int(c) for v, c in coeffs.items() if v != "p_6" and int(c) != 0}
    return f"{left} {_REL[rel]} {_render_affine(rest, int(rhs))}"


# ── theorem signature ───────────────────────────────────────────────────────
def _premise_hyp(pr: dict, name: str) -> str:
    coeffs = {v: Fraction(c) for v, c in pr["coeffs"].items() if Fraction(c) != 0}
    ls, rs = _two_sided(coeffs, int(pr["rhs"]), _NAT)
    return f"({name} : {ls} {_REL[pr['rel']]} {rs})"


# ── per-step emission ───────────────────────────────────────────────────────
def _coeffs_frac(step) -> dict:
    return {v: Fraction(c) for v, c in step["coeffs"].items()}


def _emit_step(step, lines, indent, text2hyp, case_hyps):
    """Append the ``have h{fid} : … := by …`` lines for one proof step."""
    fid = step["fid"]
    coeffs = _coeffs_frac(step)
    const = Fraction(step["const"])
    rel = step["rel"]
    stmt = _stmt(coeffs, const, rel)
    hid = f"s{fid}"
    rule = step["rule"]

    if rule == "inventory":
        inv = step["inventory"]
        if inv == "Juc_EulerFormula":
            lines.append(f"{indent}have {hid} : {stmt} := by")
            lines.append(f"{indent}  have he := Juc_EulerFormula maps hM")
            if _HAS_LARGE:
                # expand Σ_{k≥7}(k-6)p via split_W, then combine with Euler
                lines.append(f"{indent}  have hw := SimplyCon3ConnectedMap.split_W maps hM")
                lines.append(f"{indent}  linear_combination he + hw")
            else:
                # W_tail IS Σ_{k≥7}(k-6)p — exactly the Euler sum, no split needed
                lines.append(f"{indent}  linear_combination he")
            return
        elif inv == "face_split":
            fs = ("face_split" if _HAS_LARGE else "face_split_agg")
            lines.append(f"{indent}have {hid} : {stmt} := by")
            lines.append(f"{indent}  have h := SimplyCon3ConnectedMap.{fs} maps hM")
            lines.append(f"{indent}  have h2 := congrArg (Nat.cast : ℕ → ℤ) h")
            lines.append(f"{indent}  push_cast at h2")
            lines.append(f"{indent}  omega")
            return
        elif inv in _TAIL_LEMMA:
            tac = f"by have h := {_TAIL_LEMMA[inv]}; linarith [h]"
        elif inv == f"nonneg_{TAIL_VAR}":
            tac = "by exact Finset.sum_nonneg (fun k _ => by positivity)"
        elif inv and inv.startswith("nonneg_"):
            tac = "by positivity"
        else:
            tac = "by positivity"
        lines.append(f"{indent}have {hid} : {stmt} := {tac}")
        return

    if rule == "premise":
        hyp = text2hyp.get(step.get("note", ""))
        ls, rs = _two_sided(coeffs, int(-const), _INT)
        lines.append(f"{indent}have {hid} : {ls} {_REL[rel]} {rs} := by "
                     f"exact_mod_cast {hyp}")
        return

    if rule == "assumption":
        # derived from the enclosing by_cases hypothesis on a linear expression
        Cd = {v: int(c) for v, c in coeffs.items() if int(c) != 0}
        hit = case_hyps.get(_nk(Cd))
        if hit is None:
            lines.append(f"{indent}have {hid} : {stmt} := by omega")
        else:
            hc, E = hit
            if Cd == E:                   # positive branch: expr >= threshold
                lines.append(f"{indent}have {hid} : {stmt} := by linarith [{hc}]")
            else:                         # negative branch: expr <= threshold-1
                lines.append(f"{indent}have {hid} : {stmt} := by "
                             f"have hcc := {hc}; omega")
        return

    if rule == "conditional":
        trig = f"s{step['deps'][0]}"
        inv = step["inventory"]
        lines.append(f"{indent}have {hid} : {stmt} := by")
        if inv == "JucovicTheorem":
            lines.append(f"{indent}  have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), "
                         f"maps.p_i k := by zify; linarith [{trig}]")
            lines.append(f"{indent}  have hj := (JucovicTheorem maps hM hf7).1")
            if _HAS_LARGE:
                lines.append(f"{indent}  have hJs := SimplyCon3ConnectedMap.split_J maps hM")
                lines.append(f"{indent}  linarith [hj, hJs]")
            else:
                # J_tail IS Σ_{k≥7}(⌊(k+1)/2⌋-6)p — the Jučovič sum, no split needed
                lines.append(f"{indent}  linarith [hj]")
        elif inv == "Barnette_P6Bound":
            if _HAS_LARGE:
                tc = " + ".join(_INT[v] for v in _TAILCOUNT_VARS)
                lines.append(f"{indent}  have hcnt := SimplyCon3ConnectedMap.split_count maps hM")
                lines.append(f"{indent}  have hS3 : (3 : ℤ) ≤ {tc} := by linarith [{trig}]")
                lines.append(f"{indent}  have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), "
                             f"(maps.p_i k : ℤ) := by linarith [hS3, hcnt]")
                lines.append(f"{indent}  have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7")
                lines.append(f"{indent}  have hb := Barnette_P6Bound maps hM hm6 hsum7")
                lines.append(f"{indent}  linarith [hb, hcnt]")
            else:
                # the trigger fact is Σ_{k≥7} p_k ≥ 3 directly (= sum_pk_after_p6)
                lines.append(f"{indent}  have hsum7 : (3 : ℤ) ≤ {_SUM_BIG} := by linarith [{trig}]")
                lines.append(f"{indent}  have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7")
                lines.append(f"{indent}  have hb := Barnette_P6Bound maps hM hm6 hsum7")
                lines.append(f"{indent}  linarith [hb]")
        return

    if rule == "lemma":
        # v0.7 §5: apply the inlined lemma HF_lemma_C{k}; discharge each of its
        # premises from the cited entailing fact (deps align with premise order).
        k = step["lemma_cnum"]
        args = " ".join(f"(by zify; linarith [s{d}])" for d in step["deps"])
        lines.append(f"{indent}have {hid} : {stmt} := by")
        lines.append(f"{indent}  have hlem := HF_lemma_C{k} maps hM {args}".rstrip())
        lines.append(f"{indent}  linarith [hlem]")
        return

    if rule == "combination":
        deps = ", ".join(f"s{d}" for d in step["deps"])
        if rel == "==":
            lines.append(f"{indent}have {hid} : {stmt} := by omega")
        else:
            lines.append(f"{indent}have {hid} : {stmt} := by linarith [{deps}]")
        return

    if rule == "rounding":
        dep = f"s{step['deps'][0]}"
        lines.append(f"{indent}have {hid} : {stmt} := by have hr := {dep}; omega")
        return

    if rule == "case_split":
        c = step["split_threshold"]
        ecoeffs = {v: int(Fraction(x)) for v, x in step.get("split_coeffs", {}).items()}
        expr = _render_expr(ecoeffs, _INT)
        cond = f"({c} : ℤ) ≤ {expr}"
        lines.append(f"{indent}have {hid} : {stmt} := by")
        hpos = f"hc{fid}"
        lines.append(f"{indent}  by_cases {hpos} : {cond}")
        for cse in step["cases"]:
            branch_hyps = dict(case_hyps)
            branch_hyps[_nk(ecoeffs)] = (hpos, ecoeffs)
            lines.append(f"{indent}  · -- {cse['assume']}")
            sub = cse["steps"]
            for s in sub:
                _emit_step(s, lines, indent + "    ", text2hyp, branch_hyps)
            concl_fid = sub[-1]["fid"] if sub else None
            if concl_fid is not None:
                lines.append(f"{indent}    linarith [s{concl_fid}]")
            else:
                lines.append(f"{indent}    omega")
        return

    # fallback
    lines.append(f"{indent}have {hid} : {stmt} := by omega")


def build_theorem(name: str, premises: list, conclusion: dict, proof_steps: list,
                  used_inventory: set = None, display: bool = False) -> str:
    """The single ``theorem … := by …`` block with NO import header (so many can
    share one import header inside a batch file)."""
    prem_names = [f"h{i + 1}" for i in range(len(premises))]
    text2hyp = {pr.get("text", ""): nm for pr, nm in zip(premises, prem_names)}
    sig_prem = " ".join(_premise_hyp(pr, nm) for pr, nm in zip(premises, prem_names))
    if sig_prem:
        sig_prem = " " + sig_prem

    need_big = False
    if display:
        # §1.2 (v0.6.2): when the individual large faces p_7..p_{M_MAX} and the tail
        # share one coefficient, merge them to ∑_{k>=7} p_k, bridged via split_count.
        # At M_MAX=6 there are no individual large faces (the tail IS Σ_{k≥7}), so no
        # bridge is needed and the conclusion already uses sum_pk_after_p6.
        vals = set(int(conclusion["coeffs"].get(v, 0)) for v in _TAILCOUNT_VARS)
        if _HAS_LARGE and len(vals) == 1 and next(iter(vals)) != 0:
            b = next(iter(vals))
            gcoeffs = {k: int(c) for k, c in conclusion["coeffs"].items()
                       if k not in _TAILCOUNT_VARS}
            gcoeffs["sum_pk_after_p6"] = b
            need_big = True
        else:
            gcoeffs = {k: int(c) for k, c in conclusion["coeffs"].items()}
        goal = _display_goal(gcoeffs, conclusion["rel"], int(conclusion["rhs"]))
    else:
        concl_coeffs = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
        goal = _stmt(concl_coeffs, Fraction(-int(conclusion["rhs"])), conclusion["rel"])

    lines = []
    for s in proof_steps:
        _emit_step(s, lines, "  ", text2hyp, {})
    target_fid = proof_steps[-1]["fid"]
    # face_split bridge so the final linarith can reconcile the display form
    # (p_6 vs the rest, possibly using f_2) with the proven fact
    _rhs = " + ".join(_INT[v] for v in
                      (["p_3", "p_4", "p_5", "p_6"]
                       + [f"p_{k}" for k in range(7, M_MAX + 1)] + [TAIL_VAR]))
    _fs = ("face_split" if _HAS_LARGE else "face_split_agg")
    lines.append(f"  have hFaceZ : {_INT['f_2']} = {_rhs} := by")
    lines.append(f"    have h := SimplyCon3ConnectedMap.{_fs} maps hM")
    lines.append("    have h2 := congrArg (Nat.cast : ℕ → ℤ) h")
    lines.append("    push_cast at h2")
    lines.append("    omega")
    extra = ""
    if need_big:
        _big_rhs = (f"{_INT['p_7']} + {_INT['p_8']} + {_INT['p_9']} + "
                    f"{_INT['p_10']} + {_SUM_TAIL}")
        lines.append(f"  have hBig : {_SUM_BIG} = {_big_rhs} := "
                     f"SimplyCon3ConnectedMap.split_count maps hM")
        extra = ", hBig"
    lines.append(f"  linarith [s{target_fid}, hFaceZ{extra}]")

    theorem = (
        f"theorem {name} (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps)"
        f"{sig_prem} :\n    {goal} := by\n"
        + "\n".join(lines) + "\n"
    )
    return theorem


def build_lean(name: str, premises: list, conclusion: dict, proof_steps: list,
               used_inventory: set = None, display: bool = False) -> str:
    """Full, standalone-compilable source (import header + single theorem)."""
    return LEAN_HEADER + build_theorem(name, premises, conclusion, proof_steps,
                                       used_inventory, display)


# ── v0.7 §5: inline lemmas so each record compiles on its own ─────────────────
def _lemma_cnums_in(steps) -> set:
    """C-numbers of every lemma step in a proof (recursing into case branches)."""
    out = set()
    for s in steps:
        if s.get("rule") == "lemma":
            out.add(s["lemma_cnum"])
        for c in s.get("cases", []):
            out |= _lemma_cnums_in(c.get("steps", []))
    return out


def _lemma_topo_order(root_cnums, lemma_data) -> list:
    """Transitive closure of used lemmas, topologically ordered (a lemma appears
    after every lemma it itself uses).  ``lemma_data``: cnum -> record json."""
    order, seen = [], set()

    def visit(k):
        if k in seen:
            return
        seen.add(k)
        for j in _lemma_cnums_in(lemma_data[k]["proof"]["steps"]):
            visit(j)
        order.append(k)

    for k in sorted(root_cnums):
        visit(k)
    return order


def lemma_defs_block(cnums, lemma_data) -> str:
    """Render ``HF_lemma_C{k}`` theorems (header-less) for the transitive closure of
    ``cnums``, topologically ordered, as one block."""
    defs = []
    for k in _lemma_topo_order(set(cnums), lemma_data):
        d = lemma_data[k]
        defs.append(build_theorem(f"HF_lemma_C{k}", d["conjecture"]["premises"],
                                  d["conjecture"]["conclusion"], d["proof"]["steps"],
                                  display=True))
    return "\n\n".join(defs)


def build_record_lean(name, premises, conclusion, proof_steps, lemma_data,
                      display=True) -> str:
    """Standalone source for one record: header + inlined lemma defs + the theorem."""
    block = lemma_defs_block(_lemma_cnums_in(proof_steps), lemma_data)
    body = build_theorem(name, premises, conclusion, proof_steps, display=display)
    return LEAN_HEADER + (block + "\n\n" if block else "") + body


# ── compilation ─────────────────────────────────────────────────────────────
import re as _re


def _check_source(returncode, out, source):
    """Shared success criteria (§2 v0.5, §III.4 v0.6.4): return code 0, no
    ``error:``, no ``declaration uses 'sorry'`` warning, and no banned token in
    the source itself.  Returns ``(ok, reason_str)``."""
    banned = [w for w in ("sorry", "admit", "axiom", "native_decide")
              if _re.search(r"\b" + w + r"\b", source)]
    reasons = []
    if returncode != 0:
        reasons.append(f"return code {returncode}")
    if "error:" in out:
        reasons.append("error: in output")
    if "declaration uses 'sorry'" in out:
        reasons.append("declaration uses 'sorry'")
    if banned:
        reasons.append("banned tokens in source: " + ",".join(banned))
    return (not reasons), "; ".join(reasons)


def _run_lean(stem: str, source: str, timeout: int):
    """Write ``{stem}.lean`` in the Lean project, run ``lake env lean`` on it,
    and delete it.  Returns ``(ok, message)``."""
    target = LEAN_DIR / f"{stem}.lean"
    target.write_text(source)
    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(target)],
            cwd=str(LEAN_DIR), capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        target.unlink(missing_ok=True)
        return False, "compile timeout"
    out = (res.stdout + res.stderr).strip()
    ok, reason = _check_source(res.returncode, out, source)
    target.unlink(missing_ok=True)
    if ok:
        return True, "ok"
    return False, (reason + " || " + out)[:2000]


def compile_lean(name: str, source: str, timeout: int = 300) -> tuple:
    """Compile a single full (header + theorem) source.  Used for standalone
    record verification (checkpoint §9.5) and single-conjecture fallbacks."""
    return _run_lean(name, source, timeout)


def compile_batch(entries: list, timeout: int = 300, preamble: str = ""):
    """v0.6.4 §III: compile many theorems in ONE file (Mathlib loaded once).

    ``entries`` is a list of ``(name, theorem_src)`` with header-less theorem
    bodies and unique names.  ``preamble`` (v0.7 §5) is a shared block of inlined
    ``HF_lemma_C{k}`` definitions placed once after the header, so lemma-using
    theorems in the batch can reference them.  On a whole-batch failure the batch is
    bisected to locate the offender(s); only the failing theorems are reported failed.

    Returns ``(results, meta)`` where ``results`` maps name -> bool (compiled)
    and ``meta`` is ``{"bisections": k}`` (number of extra sub-compiles beyond
    the initial whole-batch attempt)."""
    results = {}
    meta = {"bisections": 0}
    pre = (preamble + "\n\n") if preamble else ""

    def src_of(subset):
        return LEAN_HEADER + pre + "\n\n".join(t for _n, t in subset) + "\n"

    def stem_of(subset):
        return "_HexBatch_" + "_".join(n for n, _t in subset[:1]) + f"_{len(subset)}"

    def recurse(subset, is_top):
        if not subset:
            return
        ok, _msg = _run_lean(stem_of(subset), src_of(subset), timeout)
        if not is_top:
            meta["bisections"] += 1
        if ok:
            for n, _t in subset:
                results[n] = True
            return
        if len(subset) == 1:
            results[subset[0][0]] = False
            return
        mid = len(subset) // 2
        recurse(subset[:mid], False)
        recurse(subset[mid:], False)

    recurse(list(entries), True)
    return results, meta
