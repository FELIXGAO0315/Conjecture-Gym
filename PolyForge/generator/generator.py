"""Generation driver and domain-agnostic helpers (PolyForge v1.0).

This module holds the parts of the generation flow that do not depend on any
particular domain:

  * the deduction-context cache (memoises saturated contexts within one attempt),
  * deterministic proof-step renumbering,
  * the soundness regression over a dataset of feature valuations,
  * record markdown rendering and atomic record writing,
  * the multiprocessing worker entry point, which defers the per-premise-set
    pipeline to the active domain (``domain.process_premise_set``).

Everything domain-specific — premise sampling, the proposition format, the
candidate search and filters, the Lean translation choices, the IRIS features —
lives in the domain (e.g. :mod:`PolyForge.domains.hex.generator`).
"""

from __future__ import annotations

import json
import os
import random
import shutil
from collections import defaultdict
from fractions import Fraction

from ..anvil import deducer as D
from ..anvil.deducer import Context

# The generator version stamped into every newly-written record (shared across
# domains).  Existing records keep whatever version they were written with.
GENERATOR_VERSION = "1.0"

# v0.6.7 §3: the supplement phase writes AT MOST ``floor(S * RO_MAX_RATIO)``
# "rounding_only" records, where S is the main-phase count.
RO_MAX_RATIO = 0.25


# ── deduction cache (§4) ─────────────────────────────────────────────────────
# Memoise saturated contexts by (premises, extra_directions, use_lemmas).  The
# algorithm's sequence of calls is unchanged; identical calls return the identical
# pool, so results are unaffected — only recomputation is avoided.  Fids are
# renumbered deterministically at record-build time, so output is independent of
# how many contexts were actually built.
_CTX_CACHE: dict = {}
_CTX_ORDER: list = []
_CTX_CAP = 256
# Toggle for the performance-equivalence check (POLYFORGE_NOCACHE=1 disables the
# cache; output must be identical with and without it).
USE_CACHE = os.environ.get("POLYFORGE_NOCACHE") != "1"


def _ctx_cache_clear():
    _CTX_CACHE.clear()
    _CTX_ORDER.clear()


def _dir_sig(extra_dirs):
    return tuple(sorted(tuple(sorted((v, int(c)) for v, c in d.items()))
                        for d in (extra_dirs or [])))


def _prem_sig(premises):
    return tuple(sorted((tuple(sorted(pr["coeffs"].items())), pr["rel"],
                         int(pr["rhs"])) for pr in premises))


def cached_context(premises, extra_directions=None, use_lemmas=True):
    if not USE_CACHE:
        ctx = Context(premises=premises, depth=D.DEFAULT_SPLIT_DEPTH,
                      extra_directions=extra_directions, use_lemmas=use_lemmas)
        ctx.saturate()
        return ctx
    key = (_prem_sig(premises), _dir_sig(extra_directions), use_lemmas)
    ctx = _CTX_CACHE.get(key)
    if ctx is not None:
        return ctx
    ctx = Context(premises=premises, depth=D.DEFAULT_SPLIT_DEPTH,
                  extra_directions=extra_directions, use_lemmas=use_lemmas)
    ctx.saturate()
    _CTX_CACHE[key] = ctx
    _CTX_ORDER.append(key)
    if len(_CTX_ORDER) > _CTX_CAP:
        old = _CTX_ORDER.pop(0)
        _CTX_CACHE.pop(old, None)
    return ctx


# ── deterministic fid renumbering (§4) ───────────────────────────────────────
def renumber_steps(tb: list) -> list:
    """Renumber every step's fid (and dep references) to 1,2,3,… in traversal
    order, so the recorded proof is independent of the global fact counter."""
    mapping: dict = {}
    counter = [0]

    def first(steps):
        for s in steps:
            counter[0] += 1
            mapping[s["fid"]] = counter[0]
            if s["rule"] == "case_split":
                for cse in s["cases"]:
                    first(cse["steps"])

    def rewrite(steps):
        for s in steps:
            s["fid"] = mapping[s["fid"]]
            if "deps" in s:
                s["deps"] = [mapping[d] for d in s["deps"]]
            if "prod_factors" in s:          # v1.2 §III.3: remap factor dep fids too
                s["prod_factors"] = [[f[0], f[1], f[2], mapping[f[3]]]
                                     for f in s["prod_factors"]]
            if s["rule"] == "case_split":
                for cse in s["cases"]:
                    rewrite(cse["steps"])

    first(tb)
    rewrite(tb)
    return tb


# ── small generic helpers over proofs / forms ────────────────────────────────
def _primitive_int(coeffs: dict, const: Fraction):
    prim = D._primitive(coeffs, const)
    if prim is None:
        return None
    ic, nc = prim
    return {v: int(c) for v, c in ic.items()}, nc


def _count_derivation_steps(tb: list) -> int:
    n = 0
    for s in tb:
        if s["rule"] in ("combination", "rounding", "conditional", "case_split"):
            n += 1
        if s["rule"] == "case_split":
            for c in s["cases"]:
                n += _count_derivation_steps(c["steps"])
    return n


def _used_inventory(tb: list, acc: set):
    for s in tb:
        if s.get("inventory"):
            acc.add(s["inventory"])
        if s["rule"] == "case_split":
            for c in s["cases"]:
                _used_inventory(c["steps"], acc)


def _used_premise_texts(tb: list, acc: set):
    for s in tb:
        if s["rule"] == "premise":
            acc.add(s["text"])
        if s["rule"] == "case_split":
            for c in s["cases"]:
                _used_premise_texts(c["steps"], acc)


# ── soundness regression ─────────────────────────────────────────────────────
def _pvec_satisfies(vals: dict, premises: list) -> bool:
    for pr in premises:
        lhs = sum(Fraction(c) * vals.get(v, 0) for v, c in pr["coeffs"].items())
        rhs = Fraction(pr["rhs"])
        if pr["rel"] == "=" and lhs != rhs:
            return False
        if pr["rel"] == ">=" and lhs < rhs:
            return False
        if pr["rel"] == "<=" and lhs > rhs:
            return False
    return True


def soundness_check(premises: list, conclusion: dict, objs: list, obj_vars: list):
    """Raise if any dataset object satisfies the premises but violates the
    conclusion (indicates a bug in inventory or deducer).  ``objs`` are the raw
    objects (for the error message) and ``obj_vars`` their exact variable
    valuations."""
    ccoeffs = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
    crhs = Fraction(conclusion["rhs"])
    for obj, vals in zip(objs, obj_vars):
        if not _pvec_satisfies(vals, premises):
            continue
        lhs = sum(c * vals.get(v, 0) for v, c in ccoeffs.items())
        ok = lhs >= crhs if conclusion["rel"] == ">=" else lhs <= crhs
        if not ok:
            raise AssertionError(
                f"SOUNDNESS VIOLATION: object {obj} satisfies premises "
                f"{premises} but violates conclusion {conclusion} "
                f"(lhs={lhs}, rhs={crhs})")


# ── markdown ──────────────────────────────────────────────────────────────────
def _steps_md(steps: list, depth: int) -> list:
    lines = []
    ind = "  " * depth
    for s in steps:
        rule = s["rule"]
        if rule == "premise":
            lines.append(f"{ind}- Premise: `{s['text']}`.")
        elif rule == "assumption":
            lines.append(f"{ind}- Assumption: `{s['text']}`.")
        elif rule == "inventory":
            lines.append(f"{ind}- Inventory `{s['inventory']}`: `{s['text']}`.")
        elif rule == "conditional":
            lines.append(f"{ind}- Inventory theorem `{s['inventory']}` "
                         f"(via `linarith`): `{s['text']}`.")
        elif rule == "combination":
            lines.append(f"{ind}- Linear combination (`linarith`): `{s['text']}`.")
        elif rule == "rounding":
            lines.append(f"{ind}- Integer rounding (`omega`): `{s['text']}`.")
        elif rule == "product":
            pv = s.get("prod_var", "?")
            facs = ", ".join(f"{v} {'≥' if k == 'lower' else '≤'} {b}"
                             for (v, k, b, _d) in s.get("prod_factors", []))
            lines.append(f"{ind}- Product step (`mul_nonneg`) on {pv} "
                         f"from ({facs}): `{s['text']}`.")
        elif rule == "case_split":
            lines.append(f"{ind}- Case split (`by_cases`) on "
                         f"`{s['split_var']}` at threshold {s['split_threshold']}: "
                         f"`{s['text']}`.")
            for i, cse in enumerate(s["cases"], 1):
                lines.append(f"{ind}  - **Case {i}** (`{cse['assume']}`):")
                lines += _steps_md(cse["steps"], depth + 2)
    return lines


def build_md(data: dict) -> str:
    cj = data["conjecture"]
    lines = [f"# {data['id']}", "", "## Statement", "",
             cj["natural_language"], "",
             f"**Formula.** `{cj['formula']}`", "",
             "## Proof", ""]
    lines += _steps_md(data["proof"]["steps"], 0)
    lines += ["", "## Scores", "",
              f"- IRIS: T={data['iris']['T']:.4f}, R={data['iris']['R']:.4f}, "
              f"L={data['iris']['L']:.4f}, score={data['iris']['score']:.4f}",
              f"- hardness: {data['hardness']:.4f}",
              f"- Lean: {data['lean']['status']}"]
    return "\n".join(lines) + "\n"


# ── atomic record writing ────────────────────────────────────────────────────
def write_record(data: dict, lean_src: str, record_dir, lean_working_dir=None):
    """Write to a temp dir first, then rename to C{n}/ atomically."""
    name = data["id"]
    record_dir.mkdir(parents=True, exist_ok=True)
    tmp = record_dir / f".{name}.tmp"
    if tmp.exists():
        shutil.rmtree(tmp)
    tmp.mkdir(parents=True)
    (tmp / f"{name}.json").write_text(json.dumps(data, indent=2, ensure_ascii=False))
    (tmp / f"{name}.md").write_text(build_md(data))
    (tmp / f"{name}.lean").write_text(lean_src)
    final = record_dir / name
    if final.exists():
        shutil.rmtree(final)
    os.replace(tmp, final)
    # the compiled copy lives only in the record; remove the working file that
    # the formalizer left inside the Lean project
    if lean_working_dir is not None:
        lean_working = lean_working_dir / f"{name}.lean"
        if lean_working.exists():
            lean_working.unlink()


# ── multiprocessing worker plumbing (v0.6.4 §II) ──────────────────────────────
# The active domain, set in the parent before the Pool is forked so each worker
# inherits it (copy-on-write) along with its loaded pool, snapshot and lemmas.
_DOMAIN = None


def set_domain(domain):
    global _DOMAIN
    _DOMAIN = domain


def seed_for(idx: int) -> int:
    """Deterministic per-premise-set seed from the base seed and the index (§II.2)."""
    return _DOMAIN.base_seed * 1_000_003 + idx


def worker(idx: int, accept: str = "split_needed"):
    """Top-level (picklable) worker entry.  Returns a tuple whose first element is
    one of ``"ok"`` / ``"soundness"`` describing the outcome.  ``accept`` selects the
    depth_type this call produces.  The domain owns the per-group pipeline."""
    import time as _t
    _ctx_cache_clear()
    seed = seed_for(idx)
    rng = random.Random(seed)
    local_stats = defaultdict(int)
    t0 = _t.time()
    try:
        prop = _DOMAIN.process_premise_set(rng, local_stats, seed, accept)
    except AssertionError as exc:
        return ("soundness", idx, str(exc), dict(local_stats), _t.time() - t0)
    return ("ok", idx, prop, dict(local_stats), _t.time() - t0)
