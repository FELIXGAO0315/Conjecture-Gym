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
from fractions import Fraction
from math import gcd
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent / "lean"

# ── atom → Lean ℤ expression (v0.6.1) ───────────────────────────────────────
_SUM_TAIL = "∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ)"
_SUM_BIG = "∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)"
_INT = {
    "p_3": "(maps.p_i 3 : ℤ)", "p_4": "(maps.p_i 4 : ℤ)",
    "p_5": "(maps.p_i 5 : ℤ)", "p_6": "(maps.p_i 6 : ℤ)",
    "p_7": "(maps.p_i 7 : ℤ)", "p_8": "(maps.p_i 8 : ℤ)",
    "p_9": "(maps.p_i 9 : ℤ)", "p_10": "(maps.p_i 10 : ℤ)",
    "sum_pk_after_p10": _SUM_TAIL,
    "sum_pk_after_p6": _SUM_BIG,
    "f_2": "∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)",
    "W_tail": "∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ)",
    "J_tail": "∑ k ∈ Finset.Ico 11 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ)",
}
_NAT = {
    "p_3": "maps.p_i 3", "p_4": "maps.p_i 4", "p_5": "maps.p_i 5",
    "p_6": "maps.p_i 6", "p_7": "maps.p_i 7", "p_8": "maps.p_i 8",
    "p_9": "maps.p_i 9", "p_10": "maps.p_i 10",
    "sum_pk_after_p10": "∑ k ∈ Finset.Ico 11 (maps.m + 1), maps.p_i k",
    "f_2": "∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k",
}
_ORDER = ["p_3", "p_4", "p_5", "p_6", "p_7", "p_8", "p_9", "p_10",
          "sum_pk_after_p10", "sum_pk_after_p6", "f_2", "W_tail", "J_tail"]

_TAIL_LEMMA = {
    "tail_excess": "SimplyCon3ConnectedMap.tail_excess maps",
    "tail_juc_nonneg": "SimplyCon3ConnectedMap.tail_juc_nonneg maps",
    "tail_juc_upper": "SimplyCon3ConnectedMap.tail_juc_upper maps",
    "tail_juc_half": "SimplyCon3ConnectedMap.tail_juc_half maps",
}

_REL = {">=": "≥", "<=": "≤", "==": "=", "=": "="}

_TAILCOUNT_VARS = ["p_7", "p_8", "p_9", "p_10", "sum_pk_after_p10"]


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
            # expand Σ_{k≥7}(k-6)p via split_W, then combine with Euler
            lines.append(f"{indent}have {hid} : {stmt} := by")
            lines.append(f"{indent}  have he := Juc_EulerFormula maps hM")
            lines.append(f"{indent}  have hw := SimplyCon3ConnectedMap.split_W maps hM")
            lines.append(f"{indent}  linear_combination he + hw")
            return
        elif inv == "face_split":
            lines.append(f"{indent}have {hid} : {stmt} := by")
            lines.append(f"{indent}  have h := SimplyCon3ConnectedMap.face_split maps hM")
            lines.append(f"{indent}  have h2 := congrArg (Nat.cast : ℕ → ℤ) h")
            lines.append(f"{indent}  push_cast at h2")
            lines.append(f"{indent}  omega")
            return
        elif inv in _TAIL_LEMMA:
            tac = f"by have h := {_TAIL_LEMMA[inv]}; linarith [h]"
        elif inv == "nonneg_sum_pk_after_p10":
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
            lines.append(f"{indent}  have hJs := SimplyCon3ConnectedMap.split_J maps hM")
            lines.append(f"{indent}  linarith [hj, hJs]")
        elif inv == "Barnette_P6Bound":
            tc = " + ".join(_INT[v] for v in _TAILCOUNT_VARS)
            lines.append(f"{indent}  have hcnt := SimplyCon3ConnectedMap.split_count maps hM")
            lines.append(f"{indent}  have hS3 : (3 : ℤ) ≤ {tc} := by linarith [{trig}]")
            lines.append(f"{indent}  have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), "
                         f"(maps.p_i k : ℤ) := by linarith [hS3, hcnt]")
            lines.append(f"{indent}  have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7")
            lines.append(f"{indent}  have hb := Barnette_P6Bound maps hM hm6 hsum7")
            lines.append(f"{indent}  linarith [hb, hcnt]")
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


def build_lean(name: str, premises: list, conclusion: dict, proof_steps: list,
               used_inventory: set = None, display: bool = False) -> str:
    prem_names = [f"h{i + 1}" for i in range(len(premises))]
    text2hyp = {pr.get("text", ""): nm for pr, nm in zip(premises, prem_names)}
    sig_prem = " ".join(_premise_hyp(pr, nm) for pr, nm in zip(premises, prem_names))
    if sig_prem:
        sig_prem = " " + sig_prem

    need_big = False
    if display:
        # §1.2 (v0.6.2): merge p_7..p_10 + sum_pk_after_p10 into ∑_{k>=7} p_k when
        # they share one coefficient, bridged below via split_count.
        vals = set(int(conclusion["coeffs"].get(v, 0)) for v in _TAILCOUNT_VARS)
        if len(vals) == 1 and next(iter(vals)) != 0:
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
                      ["p_3", "p_4", "p_5", "p_6", "p_7", "p_8", "p_9", "p_10",
                       "sum_pk_after_p10"])
    lines.append(f"  have hFaceZ : {_INT['f_2']} = {_rhs} := by")
    lines.append("    have h := SimplyCon3ConnectedMap.face_split maps hM")
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

    header = (
        "import Mathlib\n"
        "import Inventory\n"
        "import HexLemmas\n\n"
        "open Finset\n\n"
        f"theorem {name} (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps)"
        f"{sig_prem} :\n    {goal} := by\n"
    )
    return header + "\n".join(lines) + "\n"


# ── compilation ─────────────────────────────────────────────────────────────
def compile_lean(name: str, source: str, timeout: int = 300) -> tuple:
    target = LEAN_DIR / f"{name}.lean"
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
    # §2 (v0.5): a compile counts as success only if ALL hold —
    #   (1) return code 0 and no "error:" in output,
    #   (2) no "declaration uses 'sorry'" warning (Inventory's own sorries live in
    #       the pre-compiled module and never surface here),
    #   (3) the source itself contains no sorry / admit / axiom / native_decide.
    import re
    banned = [w for w in ("sorry", "admit", "axiom", "native_decide")
              if re.search(r"\b" + w + r"\b", source)]
    reasons = []
    if res.returncode != 0:
        reasons.append(f"return code {res.returncode}")
    if "error:" in out:
        reasons.append("error: in output")
    if "declaration uses 'sorry'" in out:
        reasons.append("declaration uses 'sorry'")
    if banned:
        reasons.append("banned tokens in source: " + ",".join(banned))
    ok = not reasons
    if not ok:
        target.unlink(missing_ok=True)
        return False, (("; ".join(reasons)) + " || " + out)[:2000]
    return True, "ok"
