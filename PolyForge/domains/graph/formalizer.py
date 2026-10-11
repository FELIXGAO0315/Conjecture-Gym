"""Graph-domain Lean 4 translation: deduction proof → Lean theorem (PolyForge v1.1).

Follows the v1.1 §I style (everything in ℤ; each inventory fact introduced via a
GraphLemmas ℤ wrapper lemma; linarith/omega/by_cases) and the shape proven by the
two hand-written samples.  Compilation itself is deferred to the domain-agnostic
``formalizer.formalizer`` machinery.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd
from pathlib import Path

from ...formalizer import formalizer as _CF
from . import deduction as DED

LEAN_DIR = Path(__file__).resolve().parent / "lean"
LEAN_HEADER = ("import Mathlib\n"
               "import GraphLemmas\n\n"
               "open SimpleGraph\n"
               "open PolyForge.Graph\n\n")
_BATCH_STEM = "_GraphBatch_"

VARS = list(DED.VARS)

# ── invariant → ℤ Lean expression ────────────────────────────────────────────
_Z = {
    "n": "(Fintype.card V : ℤ)",
    "m": "(G.edgeFinset.card : ℤ)",
    "max_deg": "(G.maxDegree : ℤ)",
    "min_deg": "(G.minDegree : ℤ)",
    "chi": "(G.chromaticNumber.toNat : ℤ)",
    "omega": "(G.cliqueNum : ℤ)",
    "alpha": "(G.indepNum : ℤ)",
    "tau": "(G.vertexCoverNum.toNat : ℤ)",
    "diam": "(G.diam : ℤ)",
    "radius": "(G.radius.toNat : ℤ)",
    "girth": "(G.girth : ℤ)",
}
# v1.2 §III.1: product (auxiliary) variables render as the literal product of
# their factor atoms, in the SAME factor order the GraphLemmas ℤ wrappers use
# (n → Fintype.card V first).  These appear only inside intermediate `have`
# statements (product inventory facts / the product step), never in goals.
for _p, (_x, _y) in DED.PRODUCT_VARS.items():
    _Z[_p] = f"{_Z[_x]} * {_Z[_y]}"
_RENDER_VARS = list(VARS) + list(DED.PRODUCT_VARS)
_REL = {">=": "≥", "<=": "≤", "==": "=", "=": "="}

# inventory entry name → (ℤ wrapper lemma, required properties, positivity need)
WRAPPER = {
    "omega_le_chi": ("omega_le_chi_int", [], None),
    "chi_le_n": ("chi_le_n_int", [], None),
    "min_le_max": ("min_le_max_int", [], None),
    "max_lt_card": ("max_lt_card_int'", [], None),         # v1.1.2: nonempty-unconditional
    "max_le_edges": ("max_le_edges_int", [], None),
    "tau_le_card_sub_one": ("tau_le_card_sub_one_int'", [], None),
    "gallai": ("gallai_int", [], None),
    "chi_ge_one": ("chi_ge_one_int'", [], None),
    "omega_ge_one": ("omega_ge_one_int'", [], None),
    "alpha_ge_one": ("alpha_ge_one_int'", [], None),
    "radius_le_diam": ("radius_le_diam_int", ["is_connected"], None),
    "diam_le_two_radius": ("diam_le_two_radius_int", ["is_connected"], None),
    "tree_edges": ("tree_edges_int", ["is_tree"], None),
    "tree_min_deg": ("tree_min_deg_int", ["is_tree"], "n2"),
    "acyclic_chi": ("acyclic_chi_int", ["is_acyclic"], None),
    "girth_le_diam": ("girth_le_diam_int", ["is_connected", "has_cycle"], None),
    "girth_ge_three": ("girth_ge_three_int", ["has_cycle"], None),
    "connected_min_deg": ("connected_min_deg_int", ["is_connected"], "n2"),
    "regular_max": ("regular_max_int'", ["is_regular"], None),
    "regular_min": ("regular_min_int'", ["is_regular"], None),
    "edge_conn_min_deg": ("edge_conn_min_deg_int", ["is_k_edge_connected"], "n2"),
    "bipartite_chi": ("bipartite_chi_int", ["is_bipartite"], None),
    "not_bipartite_chi": ("not_bipartite_chi_int", ["not_bipartite"], None),
    # v1.1.1 elementary facts
    "diam_ge_one": ("diam_ge_one_int", ["is_connected"], "n2"),
    "radius_ge_one": ("radius_ge_one_int", ["is_connected"], "n2"),
    "connected_edges": ("connected_edges_int", ["is_connected"], None),
    # v1.1.2 elementary facts
    "n_ge_one": ("card_ge_one_int", [], None),
    "alpha_le_n": ("alpha_le_card_int", [], None),
    "omega_le_n": ("omega_le_card_int", [], None),
    "tau_le_m": ("tau_le_edges_int", [], None),
    "conn_cycle_edges": ("conn_cycle_edges_ge_card_int", ["is_connected", "has_cycle"], None),
    # v1.2 §II/§III product (handshake / edge-count) facts
    "handshake_min": ("handshake_min_int", [], None),
    "handshake_max": ("handshake_max_int", [], None),
    "edge_card_bound": ("two_mul_edges_le_card_sq_sub_card_int", [], None),
    "bipartite_edges": ("bipartite_four_mul_edges_int", ["is_bipartite"], None),
    "regular_edges": ("regular_edges_int", ["is_regular"], None),
    # v1.2.1 §VI second batch
    "card_le_alpha_chi": ("card_le_alpha_chi_int", [], None),
    "omega_le_maxdeg": ("omega_le_maxdeg_add_one_int", [], None),
}

# v1.2.1 §VI.2: Turán conditional theorems — the numeric hypothesis omega ≤ r is
# discharged from the trigger fact (the conditional step's dep), not from G/props.
TURAN_WRAPPER = {f"turan_r{r}": f"turan_r{r}_int" for r in (2, 3, 4, 5, 6)}


# ── rendering ─────────────────────────────────────────────────────────────────
def _lcm(a, b):
    return a * b // gcd(a, b) if a and b else max(a, b)


def _clear(coeffs, const):
    vals = list(coeffs.values()) + [const]
    L = 1
    for v in vals:
        L = _lcm(L, Fraction(v).denominator)
    ic = {k: int(Fraction(c) * L) for k, c in coeffs.items() if Fraction(c) != 0}
    k = int(Fraction(const) * L)
    return ic, k


def _render_expr(ic):
    terms = []
    for v in _RENDER_VARS:
        c = ic.get(v, 0)
        if c == 0:
            continue
        atom = _Z[v]
        piece = atom if abs(c) == 1 else f"{abs(c)} * {atom}"
        terms.append(("-" if c < 0 else "+", piece))
    if not terms:
        return "0"
    sign, first = terms[0]
    out = ("-" + first) if sign == "-" else first
    for sign, piece in terms[1:]:
        out += f" {sign} {piece}"
    return out


def _stmt(coeffs, const, rel):
    """Render ``Σ coeffs·atom + const  rel  0`` as ``EXPR rel (-const)`` in ℤ."""
    ic, k = _clear(coeffs, const)
    return f"{_render_expr(ic)} {_REL[rel]} {-k}"


def _ineq(coeffs, rel, rhs):
    """Render ``Σ coeffs·atom rel rhs`` in ℤ."""
    ic = {v: int(c) for v, c in coeffs.items() if int(c) != 0}
    return f"{_render_expr(ic)} {_REL[rel]} {int(rhs)}"


# ── property hypotheses ───────────────────────────────────────────────────────
def _prop_sig(p):
    name = p["name"]
    return {
        "is_connected": "G.Connected", "is_tree": "G.IsTree", "is_acyclic": "G.IsAcyclic",
        "has_cycle": "¬ G.IsAcyclic", "is_bipartite": "G.IsBipartite",
        "not_bipartite": "¬ G.IsBipartite", "nontrivial": "2 ≤ Fintype.card V",
    }.get(name) or (f"G.IsRegularOfDegree {p['param']}" if name == "is_regular"
                    else f"G.IsEdgeConnected {p['param']}")


def _prop_term(req, prop_hyps):
    if req in prop_hyps:
        return prop_hyps[req]
    if req == "is_connected" and "is_tree" in prop_hyps:
        return f"(isTree_connected G {prop_hyps['is_tree']})"
    if req == "is_acyclic" and "is_tree" in prop_hyps:
        return f"(isTree_acyclic G {prop_hyps['is_tree']})"
    if req == "is_bipartite":
        if "is_acyclic" in prop_hyps:
            return f"(isAcyclic_bipartite G {prop_hyps['is_acyclic']})"
        if "is_tree" in prop_hyps:
            return f"(isAcyclic_bipartite G (isTree_acyclic G {prop_hyps['is_tree']}))"
    if req == "nontrivial" and "has_cycle" in prop_hyps:        # §II.2: has_cycle ⟹ 2 ≤ card
        return f"(hasCycle_two_le_card G {prop_hyps['has_cycle']})"
    raise KeyError(f"cannot discharge property {req} from {list(prop_hyps)}")


def _wrapper_call(inv_name, prop_hyps):
    wname, req, pos = WRAPPER[inv_name]
    if wname == "card_ge_one_int":            # n ≥ 1 does not mention G
        return "card_ge_one_int (V := V)"
    args = ["G"] + [_prop_term(p, prop_hyps) for p in req]
    if pos == "n2":
        args.append(_prop_term("nontrivial", prop_hyps))
    elif pos == "n1":
        args.append("(by omega)")      # 1 ≤ Fintype.card V from the trigger fact in context
    return wname + " " + " ".join(args)


# ── per-step emission ─────────────────────────────────────────────────────────
def _nk(coeffs):
    ic = {v: int(c) for v, c in coeffs.items() if int(c) != 0}
    if not ic:
        return ()
    g = 0
    for c in ic.values():
        g = gcd(g, abs(c))
    ic = {v: c // g for v, c in ic.items()}
    for v in VARS:
        if ic.get(v, 0) != 0:
            if ic[v] < 0:
                ic = {k: -x for k, x in ic.items()}
            break
    return tuple(sorted(ic.items()))


def _emit_step(step, lines, indent, text2hyp, prop_hyps, case_hyps):
    fid = step["fid"]
    coeffs = {v: Fraction(c) for v, c in step["coeffs"].items()}
    const = Fraction(step["const"])
    rel = step["rel"]
    stmt = _stmt(coeffs, const, rel)
    hid = f"s{fid}"
    rule = step["rule"]

    if rule == "inventory" or rule == "conditional":
        inv = step["inventory"]
        if inv and inv.startswith("nonneg_"):
            lines.append(f"{indent}have {hid} : {stmt} := by positivity")
            return
        if rule == "conditional" and inv in TURAN_WRAPPER:
            # discharge the omega ≤ r hypothesis from the trigger fact (deps[0])
            dep = f"s{step['deps'][0]}" if step.get("deps") else None
            disch = f"(by linarith [{dep}])" if dep else "(by omega)"
            lines.append(f"{indent}have {hid} : {stmt} := by")
            lines.append(f"{indent}  have hw := {TURAN_WRAPPER[inv]} G {disch}")
            lines.append(f"{indent}  try push_cast at hw")
            lines.append(f"{indent}  linarith [hw]")
            return
        call = _wrapper_call(inv, prop_hyps)
        lines.append(f"{indent}have {hid} : {stmt} := by")
        lines.append(f"{indent}  have hw := {call}")
        # normalise a parametric Nat-literal cast (↑k / ↑d from edge_conn / regular)
        # so linarith equates e.g. (↑2 : ℤ) with the literal 2; a no-op (and so
        # harmless) for the non-parametric facts, and it leaves product atoms intact.
        lines.append(f"{indent}  try push_cast at hw")
        lines.append(f"{indent}  linarith [hw]")
        return

    if rule == "premise":
        hyp = text2hyp.get(step.get("note", ""))
        if hyp is None:
            lines.append(f"{indent}have {hid} : {stmt} := by omega")
        else:
            lines.append(f"{indent}have {hid} : {stmt} := by linarith [{hyp}]")
        return

    if rule == "assumption":
        Cd = {v: int(c) for v, c in coeffs.items() if int(c) != 0}
        hit = case_hyps.get(_nk(Cd))
        if hit is None:
            lines.append(f"{indent}have {hid} : {stmt} := by omega")
        else:
            hc, _E = hit
            lines.append(f"{indent}have {hid} : {stmt} := by have hcc := {hc}; omega")
        return

    if rule == "combination":
        deps = ", ".join(f"s{d}" for d in step["deps"])
        if rel in ("==", "="):
            lines.append(f"{indent}have {hid} : {stmt} := by omega")
        else:
            lines.append(f"{indent}have {hid} : {stmt} := by linarith [{deps}]")
        return

    if rule == "rounding":
        dep = f"s{step['deps'][0]}"
        lines.append(f"{indent}have {hid} : {stmt} := by have hr := {dep}; omega")
        return

    if rule == "product":
        # v1.2 §III.3: McCormick envelope from a nonnegative product of two factors.
        # factor for (var,"lower",b): (Z[var] − b) ≥ 0 ;  for "upper": (b − Z[var]) ≥ 0.
        def _factor(fac):
            var, kind, bnd, dfid = fac
            z = _Z[var]
            return (f"({z} - {int(bnd)})" if kind == "lower" else f"({int(bnd)} - {z})"), dfid
        f1, d1 = _factor(step["prod_factors"][0])
        f2, d2 = _factor(step["prod_factors"][1])
        lines.append(f"{indent}have {hid} : {stmt} := by")
        lines.append(f"{indent}  have hmul : (0 : ℤ) ≤ {f1} * {f2} :=")
        lines.append(f"{indent}    mul_nonneg (by linarith [s{d1}]) (by linarith [s{d2}])")
        lines.append(f"{indent}  ring_nf at hmul ⊢")
        lines.append(f"{indent}  linarith [hmul]")
        return

    if rule == "case_split":
        c = step["split_threshold"]
        ecoeffs = {v: int(Fraction(x)) for v, x in step.get("split_coeffs", {}).items()}
        expr = _render_expr(ecoeffs)
        lines.append(f"{indent}have {hid} : {stmt} := by")
        hpos = f"hc{fid}"
        lines.append(f"{indent}  by_cases {hpos} : ({c} : ℤ) ≤ {expr}")
        for cse in step["cases"]:
            branch = dict(case_hyps)
            branch[_nk(ecoeffs)] = (hpos, ecoeffs)
            lines.append(f"{indent}  · -- {cse['assume']}")
            sub = cse["steps"]
            for s in sub:
                _emit_step(s, lines, indent + "    ", text2hyp, prop_hyps, branch)
            concl_fid = sub[-1]["fid"] if sub else None
            if concl_fid is not None:
                lines.append(f"{indent}    linarith [s{concl_fid}]")
            else:
                lines.append(f"{indent}    omega")
        return

    lines.append(f"{indent}have {hid} : {stmt} := by omega")


# ── theorem assembly ──────────────────────────────────────────────────────────
def _render_affine(ic, const):
    """Render ``Σ ic[v]·Z[v] + const`` in ℤ (just ``const`` if all zero)."""
    terms = []
    for v in VARS:
        c = int(ic.get(v, 0))
        if c == 0:
            continue
        atom = _Z[v]
        terms.append(("-" if c < 0 else "+", atom if abs(c) == 1 else f"{abs(c)} * {atom}"))
    if not terms:
        return str(const)
    sign, first = terms[0]
    out = ("-" + first) if sign == "-" else first
    for sign, piece in terms[1:]:
        out += f" {sign} {piece}"
    if const > 0:
        out += f" + {const}"
    elif const < 0:
        out += f" - {-const}"
    return out


def _display_goal(conclusion, primary):
    """§VII: ℤ goal with ``primary`` alone on the left (positive coefficient)."""
    L = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    c = int(conclusion["rhs"])            # internal ">=" form
    if primary is None or L.get(primary, 0) == 0:
        primary = next((v for v in VARS if L.get(v, 0) == 1), None)
        if primary is None:
            primary = max(L, key=lambda v: (abs(L[v]), -VARS.index(v)))
    if L[primary] >= 0:
        coeffs, rel, rhs = L, "≥", c
    else:
        coeffs, rel, rhs = {v: -x for v, x in L.items()}, "≤", -c
    a = coeffs[primary]
    left = _Z[primary] if a == 1 else f"{a} * {_Z[primary]}"
    rest = {v: -coeffs[v] for v in coeffs if v != primary}
    return f"{left} {rel} {_render_affine(rest, rhs)}"


def _prem_hyp(pr):
    """§IV.2: render a numeric premise with its (coefficient-1) subject variable
    alone on the left with a positive coefficient, in ℤ."""
    coeffs = {v: int(c) for v, c in pr["coeffs"].items() if int(c) != 0}
    rel, rhs = pr["rel"], int(pr["rhs"])
    subj = next((v for v in VARS if coeffs.get(v, 0) == 1), None)
    if subj is None:
        subj = next((v for v in VARS if coeffs.get(v, 0) > 0), None)
    if subj is None:
        return _ineq(coeffs, rel, rhs)
    a = coeffs[subj]
    left = _Z[subj] if a == 1 else f"{a} * {_Z[subj]}"
    rest = {v: -coeffs[v] for v in coeffs if v != subj}
    return f"{left} {_REL[rel]} {_render_affine(rest, rhs)}"


def build_theorem(name, premises, conclusion, proof_steps, used_inventory=None, display=False):
    props = premises["props"]
    numeric = premises["numeric"]
    primary = premises.get("primary")
    hyp_decls = []
    prop_hyps = {}
    for i, p in enumerate(props, 1):
        hn = f"hp{i}"
        hyp_decls.append(f"({hn} : {_prop_sig(p)})")
        prop_hyps[p["name"]] = hn
    text2hyp = {}
    for j, pr in enumerate(numeric, 1):
        hn = f"hn{j}"
        hyp_decls.append(f"({hn} : {_prem_hyp(pr)})")
        text2hyp[pr.get("text", "")] = hn
    sig = (" " + " ".join(hyp_decls)) if hyp_decls else ""
    goal = _display_goal(conclusion, primary)

    lines = []
    for s in proof_steps:
        _emit_step(s, lines, "  ", text2hyp, prop_hyps, {})
    target = proof_steps[-1]["fid"] if proof_steps else None
    closing = f"  linarith [s{target}]" if target is not None else "  omega"
    body = "\n".join(lines + [closing])
    return (f"theorem {name} {{V : Type}} [Fintype V] [DecidableEq V] [Nonempty V] "
            f"(G : SimpleGraph V) [DecidableRel G.Adj]{sig} :\n"
            f"    {goal} := by\n{body}\n")


def build_lean(name, premises, conclusion, proof_steps, used_inventory=None, display=False):
    return LEAN_HEADER + build_theorem(name, premises, conclusion, proof_steps, used_inventory, display)


# ── lemma inlining (graph library; empty in stage 1 but mechanism present) ────
def _lemma_cnums_in(steps) -> set:
    out = set()
    for s in steps:
        if s.get("rule") == "lemma":
            out.add(s["lemma_cnum"])
        for c in s.get("cases", []):
            out |= _lemma_cnums_in(c.get("steps", []))
    return out


def _lemma_topo_order(root, lemma_data):
    order, seen = [], set()

    def visit(k):
        if k in seen:
            return
        seen.add(k)
        for j in _lemma_cnums_in(lemma_data[k]["proof"]["steps"]):
            visit(j)
        order.append(k)
    for k in sorted(root):
        visit(k)
    return order


def lemma_defs_block(cnums, lemma_data):
    defs = []
    for k in _lemma_topo_order(set(cnums), lemma_data):
        d = lemma_data[k]
        cj = d["conjecture"]
        prem = {"props": [{"name": p["name"], **({"param": p["param"]} if "param" in p else {})}
                          for p in cj.get("properties_premises", [])],
                "numeric": cj.get("numeric_premises", [])}
        defs.append(build_theorem(f"GF_lemma_C{k}", prem, cj["conclusion"], d["proof"]["steps"]))
    return "\n\n".join(defs)


def build_record_lean(name, premises, conclusion, proof_steps, lemma_data, display=True):
    block = lemma_defs_block(_lemma_cnums_in(proof_steps), lemma_data)
    body = build_theorem(name, premises, conclusion, proof_steps, display=display)
    return LEAN_HEADER + (block + "\n\n" if block else "") + body


# ── compilation (defer to the domain-agnostic machinery) ──────────────────────
def compile_lean(name, source, timeout=300):
    return _CF.compile_lean(name, source, LEAN_DIR, timeout)


def compile_batch(entries, timeout=300, preamble=""):
    return _CF.compile_batch(entries, LEAN_DIR, LEAN_HEADER, timeout=timeout,
                             preamble=preamble, stem_prefix=_BATCH_STEM)
