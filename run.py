"""HexForge entry point.

Usage (run from the Conjecture-Gym root):

    python -m run hexforge          # run until Ctrl+C
    python -m run hexforge N        # stop after N new conjectures

Only conjectures that pass every check *and* whose Lean file compiles are
counted as "new".  On Ctrl+C the conjecture currently being written is finished
before exiting.
"""

from __future__ import annotations

import os
import sys

# Determinism: pin the hash seed so that set/dict iteration over string keys in
# the deduction engine is reproducible across processes.  This makes every run
# with the same seed byte-for-byte reproducible (and isolates the deduction
# cache as a pure speed optimization with identical output).  Must happen before
# anything hashes strings, so re-exec once if it is not already set.
if os.environ.get("PYTHONHASHSEED") != "0":
    os.environ["PYTHONHASHSEED"] = "0"
    os.execv(sys.executable, [sys.executable, "-m", "run", *sys.argv[1:]])

import random
import signal
import time
from collections import defaultdict

from HexForge.generator import generator as G


def _print_summary(stats, sampled, added, elapsed, f2_upper):
    print("\n" + "=" * 60)
    print("HexForge run summary")
    print("=" * 60)
    print(f"  new conjectures written : {added}")
    print(f"  premise sets sampled    : {sampled}")
    print(f"  wall time               : {elapsed:.1f}s")
    print("  discards by reason:")
    for reason in ("empty_premises", "no_p6_canonical", "p6_only_via_f2",
                   "p6_upper_bound", "p6_padding", "too_many_terms",
                   "rounding_only", "proof_reconstruct_failed",
                   "premise_weakening", "linear_only", "not_attained",
                   "too_shallow", "duplicate", "premise_minimized_duplicate",
                   "same_skeleton_worse", "recheck_failed", "compile_failed"):
        print(f"      {reason:28s}: {stats.get(reason, 0)}")
    print(f"  replacements (same skeleton, better) : {stats.get('replacements', 0)}")
    # §5 statistics (not filters)
    ratio = (100.0 * f2_upper / added) if added else 0.0
    print("  statistics:")
    print(f"      records with premise f_2 <= c : {f2_upper} / {added} "
          f"({ratio:.0f}%)")
    print(f"      conjectures skipping pool checks (f_2 >= c, c > 28): "
          f"{stats.get('skipped_pool_checks', 0)}")
    # v0.6.2 §4: direction-enumeration diagnostics
    ns = stats.get("enum_samples", 0)
    avg_dirs = (stats.get("directions_evaluated", 0) / ns) if ns else 0.0
    avg_time = (stats.get("enum_time", 0.0) / ns) if ns else 0.0
    print(f"      direction enumeration: {avg_dirs:.0f} dirs/sample avg, "
          f"{avg_time:.2f}s/sample avg")
    print(f"      proof_reconstruct_failed : "
          f"{stats.get('proof_reconstruct_failed', 0)}")
    print(f"      direction-budget truncations : "
          f"{stats.get('dir_budget_truncated', 0)}")
    # v0.6.2 §2: deductive-depth labels of the written conjectures
    print(f"      depth_type: rounding_only {stats.get('depth_rounding_only', 0)}, "
          f"split_needed {stats.get('depth_split_needed', 0)}")
    if stats.get("compile_msgs"):
        print("  sample compile failures:")
        for nm, msg in stats["compile_msgs"][:3]:
            print(f"      {nm}: {msg}")


def main(argv):
    if len(argv) < 2 or argv[1] != "hexforge":
        print("usage: python -m run hexforge [N]")
        return 1
    target = int(argv[2]) if len(argv) >= 3 else None
    base_seed = int(argv[3]) if len(argv) >= 4 else random.randrange(1 << 30)

    print(f"HexForge v{G.GENERATOR_VERSION}  (base seed {base_seed})")
    print("loading real-polytope pool ...")
    pvecs, features = G.load_pool()
    pvec_vars = [G.vars_from_pvec(pv) for pv in pvecs]
    pool = (pvecs, features, pvec_vars)
    print(f"  {len(pvecs)} real simple 3-polytopes loaded")

    existing_hashes, max_id = G.load_existing_hashes(G.RECORD)
    next_id = max_id + 1
    skel_index = G.build_skeleton_index(G.RECORD, features)   # v0.6
    print(f"  existing record: {len(existing_hashes)} conjectures, "
          f"{len(skel_index)} skeletons, next id C{next_id}")

    stop = {"flag": False}

    def handler(signum, frame):
        stop["flag"] = True
        print("\n[Ctrl+C] finishing current conjecture, then stopping ...")

    signal.signal(signal.SIGINT, handler)

    stats = defaultdict(int)
    sampled = 0
    added = 0
    f2_upper = 0
    t0 = time.time()

    # safety cap: with the strict v0.1 filters, stop and report rather than
    # loosening standards if we sample far more than needed without reaching N
    max_samples = max(400, (target or 0) * 40) if target is not None else None

    while not stop["flag"]:
        if target is not None and added >= target:
            break
        if max_samples is not None and sampled >= max_samples:
            print(f"\n[cap] sampled {sampled} premise sets with only {added} "
                  f"accepted; stopping without loosening filters.")
            break
        sampled += 1
        seed = base_seed * 1_000_003 + sampled
        rng = random.Random(seed)
        try:
            result = G.attempt(rng, pool, next_id, existing_hashes, stats, seed,
                               skel_index)
        except AssertionError as exc:
            print("\n!!! SOUNDNESS FAILURE — stopping immediately !!!")
            print(exc)
            return 2
        if result is None:
            continue
        data = result["data"]
        old_entry = skel_index.get(result["skeleton"])     # before overwrite
        G.write_record(data, result["lean_src"])   # atomic; not interrupted
        if result["mode"] == "replace":
            stats["replacements"] += 1
            print(f"  {data['id']} replaced:")
            print(f"      old formula : {old_entry['formula']}")
            print(f"      new formula : {data['conjecture']['formula']}")
            print(f"      old touch/hardness : {old_entry['touch']} / "
                  f"{old_entry['hardness']:.3f}")
            print(f"      new touch/hardness : {data['touch']} / "
                  f"{data['hardness']:.3f}")
        else:
            added += 1
            next_id += 1
            print(f"  {data['id']}: hardness={data['hardness']:.3f}  "
                  f"iris={data['iris']['score']:.3f}  attained={data['attained']}  "
                  f"inventory={sorted(result['inventory'])}")
        # update the skeleton index with the newly written best-for-skeleton
        skel_index[result["skeleton"]] = {
            "name": result["target"], "formula": data["conjecture"]["formula"],
            "supersedes": data["supersedes"], **result["metrics"]}
        if any([v for v, c in pr["coeffs"].items() if c] == ["f_2"]
               and pr["rel"] == "<=" for pr in data["conjecture"]["premises"]):
            f2_upper += 1

    _print_summary(stats, sampled, added, time.time() - t0, f2_upper)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
