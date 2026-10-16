#!/usr/bin/env python3
"""PolyForge v1.4.3 §A: cumulative, monotone baseline ladder.

Levels, each a strict superset of the previous (a "solve" = genuine reward 1 via
the oracle verifier path).  A task's ``auto_level`` is the LOWEST level that proves
it (staged evaluation: once a task is solved it is not re-attempted at higher
levels), else ``none``.

  L0  generic tactics only, no library help:
      omega, linarith, nlinarith, nlinarith <;> omega, positivity, aesop.
  U   UNPRIVILEGED automation: the Inventory (GraphLemmas) lemmas are in scope but
      NOT instantiated per task by us — generic automation must use them itself:
      aesop with the unconditional Inventory lemmas registered as safe/unsafe
      forward rules, and a UNIFORM (task-independent) nlinarith/omega hint list of
      the same unconditional lemmas applied to G.  Hammer-style tactics (hammer,
      duper) are NOT in the pinned v4.34.0 toolchain (checked: lake-manifest has
      mathlib/aesop/batteries/… but no duper/hammer), so none is attempted; no
      dependency is added or upgraded.
  L1  U attempts + the applicable LINEAR Inventory facts instantiated per task as
      `have`s (push_cast-normalised), then the L0 arithmetic tactics.
  L2  L1 attempts + all Inventory facts incl. product/nonlinear instantiated, then
      nlinarith with pairwise premise products as hints (<=40).
  L3  L2 attempts + interval_cases on <=2 vars of range width <=12, then {omega,
      nlinarith} with the L2 facts.

Per-attempt timeout 60 s everywhere; same oracle verifier (static + compile + env
diff + type + axiom); parallel across tasks.

Usage: python -m PolyForge.env.baseline_ladder <export_dir> [--record DIR]
       [--nprocs N] [--json OUT]
"""
import json, sys, time
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph import generator as G
from PolyForge.env import verifier as V
# reuse the per-task instantiation helpers (L1/L2/L3 preambles) from the legacy baseline
from PolyForge.env.baseline import (l1_preamble, l2_preamble, l3_prefix, _mk,
                                     TACTICS0, TACTICS2, TACTICS3, MAX_HINTS)

LEVELS = ["L0", "U", "L1", "L2", "L3"]

# ── L0: generic tactics, no library ─────────────────────────────────────────────
L0_TACTICS = ["omega", "linarith", "nlinarith", "nlinarith <;> omega", "positivity", "aesop"]

# ── U: unconditional Inventory lemmas (take only G + typeclass instances) ────────
# Used UNIFORMLY (same for every task) — never selected or instantiated per task.
_UNCOND = [
    "min_le_max_int", "max_le_edges_int", "gallai_int", "card_ge_one_int",
    "max_lt_card_int'", "tau_le_card_sub_one_int'", "chi_ge_one_int'",
    "omega_ge_one_int'", "alpha_ge_one_int'", "alpha_le_card_int", "omega_le_card_int",
    "tau_le_edges_int", "handshake_min_int", "handshake_max_int",
    "two_mul_edges_le_card_sq_sub_card_int", "card_le_alpha_chi_int",
    "omega_le_maxdeg_add_one_int", "omega_le_chi_int", "chi_le_n_int",
]
_HINTS_G = "[" + ", ".join(f"{n} G" for n in _UNCOND) + "]"
_FWD = "[" + ", ".join(_UNCOND) + "]"


def u_candidates():
    """Fixed, task-independent unprivileged-automation attempts."""
    return [
        f"aesop (add safe forward {_FWD})",
        f"aesop (add unsafe 50% forward {_FWD})",
        f"nlinarith {_HINTS_G}",
        f"nlinarith {_HINTS_G} <;> omega",
        f"(try push_cast); nlinarith {_HINTS_G}",
    ]


def level_candidates(level, data):
    """The NEW candidate proof strings introduced at ``level`` for a task whose record
    is ``data`` (may be None for L0/U, which need no per-task instantiation)."""
    if level == "L0":
        return list(L0_TACTICS)
    if level == "U":
        return u_candidates()
    if data is None:
        return []
    try:
        if level == "L1":
            l, n = l1_preamble(data)
            return [_mk("L1", t, l, n) for t in TACTICS0]
        if level == "L2":
            l, n = l2_preamble(data)
            return [_mk("L2", t, l, n) for t in TACTICS2]
        if level == "L3":
            r = l3_prefix(data)
            if r is None:
                return []
            l, n = r
            return [_mk("L3", t, l, n) for t in TACTICS3]
    except Exception:
        return []
    return []


def main(argv):
    export_dir = Path(argv[0])
    rec_dir = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record")
    nprocs, jout = 4, None
    if "--record" in argv:
        rec_dir = Path(argv[argv.index("--record") + 1])
    if "--nprocs" in argv:
        nprocs = int(argv[argv.index("--nprocs") + 1])
    if "--json" in argv:
        jout = Path(argv[argv.index("--json") + 1])

    tasks = [json.loads(l) for l in (export_dir / "tasks.jsonl").read_text().splitlines() if l.strip()]
    recs = {}
    for d in rec_dir.iterdir():
        j = d / f"{d.name}.json"
        if j.exists():
            dd = json.load(open(j)); recs[dd["conjecture"]["formula"]] = dd
    print(f"{len(tasks)} tasks; {len(recs)} records; ladder {LEVELS}", flush=True)

    ver = V.Verifier("graph", nprocs=nprocs, timeout=60.0)
    auto = {t["task_id"]: "none" for t in tasks}
    unsolved = {t["task_id"]: t for t in tasks}
    solved_lists = {lv: [] for lv in LEVELS}
    t_all = time.time()
    for lv in LEVELS:
        cand = []
        for tid, t in list(unsolved.items()):
            data = recs.get(t["formula"])
            for proof in level_candidates(lv, data):
                cand.append((tid, proof))
        if not cand:
            print(f"[{lv}] no candidates for the {len(unsolved)} unsolved tasks", flush=True)
            continue
        t0 = time.time()
        results = ver.verify_batch(cand)
        newly = set()
        for (tid, _p), r in zip(cand, results):
            if r.reward == 1.0:
                newly.add(tid)
        for tid in newly:
            auto[tid] = lv
            solved_lists[lv].append(tid)
            unsolved.pop(tid, None)
        print(f"[{lv}] {len(cand)} candidates on {len(cand)//max(1,len(set(c[0] for c in cand)))}x "
              f"{len(set(c[0] for c in cand))} tasks -> solved {len(newly)} new "
              f"(total solved {sum(len(v) for v in solved_lists.values())}/{len(tasks)}); "
              f"{time.time()-t0:.0f}s", flush=True)
    ver.close()
    print(f"ladder done in {time.time()-t_all:.0f}s", flush=True)

    # cumulative counts (auto_level distribution)
    counts = {lv: sum(1 for v in auto.values() if v == lv) for lv in LEVELS}
    counts["none"] = sum(1 for v in auto.values() if v == "none")
    print("auto_level counts:", counts, flush=True)
    if jout is not None:
        jout.write_text(json.dumps({
            "levels": LEVELS,
            "auto_level": auto,
            "counts": counts,
            "solved_at": {lv: sorted(solved_lists[lv]) for lv in LEVELS},
            "uncond_lemmas": _UNCOND,
        }, indent=2))
        print(f"wrote {jout}", flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
