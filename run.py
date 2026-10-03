"""HexForge entry point (v0.6.4 — parallel generation, batched Lean).

Usage (run from the Conjecture-Gym root):

    python -m run hexforge              # run until Ctrl+C
    python -m run hexforge N            # N split_needed, then floor(N/4) rounding_only
    python -m run hexforge --minutes M  # run for M minutes
    python -m run hexforge N --minutes M  # stop at whichever comes first

``N`` is the MAIN-phase target (``split_needed`` records); the SUPPLEMENT phase then
adds AT MOST ``floor(N * RO_MAX_RATIO)`` = ``floor(N/4)`` ``rounding_only`` records.

Options:
    --seed S     base seed (default: random)
    --workers W  number of worker processes (default: auto, see below)

Each premise set is processed in a worker process (sampling, direction
enumeration, proof reconstruction, all checks, the integer counter-model gate,
and scoring).  The main process alone judges skeletons, numbers, compiles (in
batches, so Mathlib loads once per batch), and writes records.  Results are
consumed in strict premise-index order, so the output is independent of the
number of workers.

v0.6.4 §IV: generation runs in two phases.  The MAIN phase produces only
``split_needed`` records (``N`` of them, or until the Ctrl+C / 85%-of-budget);
rounding_only directions are dropped right after enumeration, never reconstructed.
The SUPPLEMENT phase then produces AT MOST ``floor(S * RO_MAX_RATIO)`` ``rounding_only``
records (an upper cap), where ``S`` is the main-phase count (so rounding_only are at
most 20% of the total).  The supplement phase's premise seeds continue the main
phase's index, so the whole record is reproducible regardless of worker count.
"""

from __future__ import annotations

import os
import sys

# Determinism: pin the hash seed so set/dict iteration over string keys in the
# deduction engine is reproducible across processes.  Must happen before anything
# hashes strings, so re-exec once if not already set.  Worker processes are forked
# and inherit this environment.
if os.environ.get("PYTHONHASHSEED") != "0":
    os.environ["PYTHONHASHSEED"] = "0"
    # keep BLAS/OpenMP single-threaded so forked workers don't contend / deadlock
    os.environ.setdefault("OMP_NUM_THREADS", "1")
    os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
    os.environ.setdefault("MKL_NUM_THREADS", "1")
    os.execv(sys.executable, [sys.executable, "-m", "run", *sys.argv[1:]])

import json
import multiprocessing as mp
import signal
import threading
import time
from collections import defaultdict

from HexForge.generator import generator as G
from HexForge.formalizer import formalizer as F

# ── tunables (v0.6.4) ─────────────────────────────────────────────────────────
LEAN_BATCH_SIZE = 20            # §III.1: compile this many theorems at once
BATCH_WAIT_SEC = 60.0           # §III.1: or after this long, compile a partial batch
# Measured incremental RSS per worker is small (~0.15 GiB): the 25k-polytope pool
# is forked copy-on-write and shared, so memory is not the binding constraint on
# this machine.  0.5 GiB/worker keeps a safety margin while letting the core cap
# dominate (cores-2 = 14 here).
PER_WORKER_GB = 0.5             # memory budget assumed per worker (for auto sizing)


# ── worker-count selection (§II.1) ────────────────────────────────────────────
def _total_mem_gb() -> float:
    try:
        with open("/proc/meminfo") as fh:
            for line in fh:
                if line.startswith("MemTotal:"):
                    return int(line.split()[1]) / (1024 * 1024)
    except Exception:
        pass
    return 8.0


def choose_workers(override=None):
    cores = os.cpu_count() or 4
    mem_gb = _total_mem_gb()
    mem_cap = max(1, int(mem_gb * 0.75 / PER_WORKER_GB))
    core_cap = max(1, cores - 2)
    auto = max(1, min(core_cap, mem_cap))
    n = override if override else auto
    basis = (f"cores={cores} (-2 → {core_cap}); mem={mem_gb:.1f} GiB "
             f"(0.75·mem / {PER_WORKER_GB:.1f} GiB per worker → {mem_cap}); "
             f"min = {auto}" + (f"; overridden to {n}" if override else ""))
    return n, basis


# ── memory sampler ────────────────────────────────────────────────────────────
def _rss_bytes(pids, page):
    total = 0
    for pid in pids:
        try:
            with open(f"/proc/{pid}/statm") as fh:
                total += int(fh.read().split()[1]) * page
        except Exception:
            pass
    return total


class MemMonitor(threading.Thread):
    def __init__(self, pool):
        super().__init__(daemon=True)
        self.pool = pool
        self.peak = 0
        self._stop = threading.Event()
        self._page = os.sysconf("SC_PAGE_SIZE")

    def run(self):
        while not self._stop.is_set():
            pids = [os.getpid()]
            try:
                pids += [p.pid for p in self.pool._pool]
            except Exception:
                pass
            self.peak = max(self.peak, _rss_bytes(pids, self._page))
            self._stop.wait(1.0)

    def stop(self):
        self._stop.set()


# ── record scan helpers (difficulty distribution / attainment) ────────────────
def _quantiles(xs):
    """Return (min, p20, p40, p60, p80, max) by nearest-rank; () if empty."""
    if not xs:
        return None
    s = sorted(xs)
    n = len(s)

    def q(p):
        if n == 1:
            return s[0]
        idx = min(n - 1, max(0, int(round(p * (n - 1)))))
        return s[idx]

    return (s[0], q(0.20), q(0.40), q(0.60), q(0.80), s[-1])


def scan_records(record_dir):
    """Return {depth_type: [hardness, ...]} and (n_unknown, n_total)."""
    by_depth = defaultdict(list)
    n_unknown = n_total = 0
    if not record_dir.exists():
        return by_depth, 0, 0
    for d in sorted(record_dir.iterdir()):
        j = d / f"{d.name}.json"
        if not j.exists():
            continue
        data = json.load(open(j))
        n_total += 1
        if data.get("attained") == "unknown":
            n_unknown += 1
        by_depth[data.get("depth_type", "?")].append(data["hardness"])
    return by_depth, n_unknown, n_total


def _init_depth_counts(record_dir):
    """record_depth {name: depth_type}, total, rounding_only count."""
    rd = {}
    if record_dir.exists():
        for d in record_dir.iterdir():
            j = d / f"{d.name}.json"
            if j.exists():
                rd[d.name] = json.load(open(j)).get("depth_type", "split_needed")
    total = len(rd)
    ro = sum(1 for v in rd.values() if v == "rounding_only")
    return rd, total, ro


# ── argument parsing ──────────────────────────────────────────────────────────
def parse_args(argv):
    if len(argv) < 2 or argv[1] != "hexforge":
        return None
    target = minutes = seed = workers = None
    rest = argv[2:]
    i = 0
    while i < len(rest):
        a = rest[i]
        if a == "--minutes":
            minutes = float(rest[i + 1]); i += 2
        elif a == "--seed":
            seed = int(rest[i + 1]); i += 2
        elif a == "--workers":
            workers = int(rest[i + 1]); i += 2
        elif a.isdigit():
            target = int(a); i += 1
        else:
            print(f"unrecognised argument: {a}"); return None
    return {"target": target, "minutes": minutes, "seed": seed, "workers": workers}


def main(argv):
    import random
    opts = parse_args(argv)
    if opts is None:
        print("usage: python -m run hexforge [N] [--minutes M] [--seed S] [--workers W]")
        return 1
    target = opts["target"]
    minutes = opts["minutes"]
    base_seed = opts["seed"] if opts["seed"] is not None else random.randrange(1 << 30)
    n_workers, worker_basis = choose_workers(opts["workers"])

    print(f"HexForge v{G.GENERATOR_VERSION}  (base seed {base_seed})")
    print(f"  N_WORKERS = {n_workers}   [{worker_basis}]")
    if target is not None:
        print(f"  stop after {target} new conjectures")
    if minutes is not None:
        print(f"  time budget {minutes:g} minutes")

    # §I: rebuild HexLemmas if the source changed (before any compile / import)
    status = F.ensure_hexlemmas_fresh()
    print(f"  HexLemmas: {status}")

    print("loading real-polytope pool ...")
    pvecs, features = G.load_pool()
    pvec_vars = [G.vars_from_pvec(pv) for pv in pvecs]
    pool_data = (pvecs, features, pvec_vars)
    print(f"  {len(pvecs)} real simple 3-polytopes loaded")

    existing_hashes, max_id = G.load_existing_hashes(G.RECORD)
    next_id = max_id + 1
    skel_index = G.build_skeleton_index(G.RECORD, features)
    _, total_written, _ = _init_depth_counts(G.RECORD)
    snapshot_hashes = dict(existing_hashes)   # immutable view for workers
    print(f"  existing record: {len(existing_hashes)} conjectures, "
          f"{len(skel_index)} skeletons, next id C{next_id}")

    # share the pool and snapshot with forked workers (copy-on-write)
    G.set_worker_globals(pool_data, snapshot_hashes, base_seed)

    stats = defaultdict(int)
    sampled = 0
    sample_time_total = 0.0
    writes_by_depth = defaultdict(int)       # NEW writes by depth_type
    new_skel_segments = defaultdict(int)     # premise-index//100 -> new skeletons
    batch_count = 0
    batch_time_total = 0.0
    bisection_total = 0

    queue_start = {"t": None}
    disp = {"next": 1, "collect": 1}         # dispatch/collect indices (shared)
    write_index_log = []                     # (name, idx, depth_type, mode) in commit order
    compile_failed_idx = []                  # premise indices whose Lean compile failed

    stop = {"flag": False}
    soundness = {"err": None}

    def handler(signum, frame):
        stop["flag"] = True
        print("\n[Ctrl+C] finishing in-flight work and flushing the compile queue ...")

    signal.signal(signal.SIGINT, handler)

    ctx = mp.get_context("fork")
    wp = ctx.Pool(n_workers)
    mem = MemMonitor(wp)
    mem.start()

    # §I (v0.6.5): dispatch window measured by OUTSTANDING COMPUTE (dispatched but
    # not yet finished); completed results waiting for in-order commit live in a
    # separate buffer and do not occupy the window — so a slow premise set no longer
    # starves the other workers (no head-of-line blocking).  Window 4× workers.
    WINDOW = n_workers * 4
    COMMIT_BUFFER_CAP = 500        # pause dispatch if this many results await commit

    def run_phase(accept, target, deadline):
        """Dispatch / compile / commit loop for ONE phase.  Produces up to ``target``
        new records of depth_type ``accept`` (``target=None`` → until Ctrl+C or the
        deadline).

        Determinism / correctness (the record is exactly the first ``target``
        premise sets, in index order, that pass EVERY check including Lean compile):

        * Worker payloads are collected in strict premise-index order and held in
          ``pending`` (also index order).
        * A batch is compiled with *provisional* names (``HFprov{idx}``); the final
          ``C{n}`` is assigned only at COMMIT, so a compile failure never burns a
          number — the freed slot is filled by the next passing candidate (§rule 1).
        * COMMIT happens in strict index order, only after the batch's compile
          results are known; earlier batches are fully committed first.  Hence the
          decision for candidate ``k`` always has every ``<k`` final result,
          including Lean (§rule 1), independent of how batches were split (§rule 2).
        * Once the ``target``-th new record is committed we stop; higher-index
          candidates (already compiled or still in flight) are discarded and never
          trigger a replacement (§rule 3).  The theorem name is the only thing that
          differs between the batch-compiled source and the written ``C{n}.lean``;
          Lean provability is name-independent and §9.5 re-verifies standalone.

        Dispatch/collect indices in ``disp`` continue across phases so the supplement
        phase's seeds follow the main phase's.  Returns (new_writes, replacements,
        boundary_idx, wall_seconds); the caller resumes at ``boundary_idx + 1``."""
        nonlocal next_id, total_written, sampled, sample_time_total
        nonlocal batch_count, batch_time_total, bisection_total
        phase_t0 = time.time()
        added = replaced = 0
        boundary = {"idx": disp["collect"] - 1}
        done = {"flag": False}            # target slot filled during commit
        pending = []                      # [(idx, prop)] sequenced, awaiting compile+commit
        ready = {}                        # idx -> result tuple: collected, not yet sequenced
        inflight = {}                     # idx -> AsyncResult: dispatched, still computing

        def commit(idx, prop):
            """Decide and write ONE candidate whose Lean compile already succeeded.
            Returns True iff it filled the final target slot (phase should stop)."""
            nonlocal next_id, total_written, added, replaced
            h = prop["hash"]
            if h in existing_hashes:
                stats["premise_minimized_duplicate" if not prop["premises"] else "duplicate"] += 1
                return False
            skel, metrics, dt = prop["skeleton"], prop["metrics"], prop["depth_type"]
            mode, target_name, supersedes, old_entry = "new", None, [], None
            if skel in skel_index:
                ex = skel_index[skel]
                if not G.skeleton_better(metrics, ex):
                    stats["same_skeleton_worse"] += 1
                    return False
                mode, target_name = "replace", ex["name"]
                old_entry = ex
                supersedes = [ex["formula"]] + list(ex.get("supersedes", []))
            if mode == "new":
                target_name = f"C{next_id}"
                next_id += 1
                total_written += 1
            data = G.assemble_data(prop, target_name, supersedes)
            lean_full = F.LEAN_HEADER + F.build_theorem(
                target_name, prop["premises"], prop["disp"], prop["tb"], display=True)
            existing_hashes[h] = target_name
            skel_index[skel] = {"name": target_name,
                                "formula": data["conjecture"]["formula"],
                                "supersedes": supersedes, **metrics}
            G.write_record(data, lean_full)
            if mode == "replace":
                replaced += 1
                write_index_log.append((target_name, idx, dt, "replace"))
                print(f"  {target_name} replaced (idx {idx}): {old_entry['formula']}  ->  "
                      f"{data['conjecture']['formula']}")
                return False
            added += 1
            boundary["idx"] = max(boundary["idx"], idx)
            writes_by_depth[dt] += 1
            new_skel_segments[idx // 100] += 1
            write_index_log.append((target_name, idx, dt, "new"))
            print(f"  {target_name}: {dt}  idx={idx}  "
                  f"hardness={data['hardness']:.3f}  attained={data['attained']}")
            return target is not None and added >= target

        def flush():
            nonlocal batch_count, batch_time_total, bisection_total
            if not pending:
                return
            entries = [(f"HFprov{idx}",
                        F.build_theorem(f"HFprov{idx}", prop["premises"], prop["disp"],
                                        prop["tb"], display=True))
                       for idx, prop in pending]
            t = time.time()
            results, meta = F.compile_batch(entries, timeout=300)
            batch_count += 1
            batch_time_total += time.time() - t
            bisection_total += meta["bisections"]
            for idx, prop in pending:            # strict index order
                if done["flag"]:
                    break                        # target met: ignore idx > boundary
                if not results.get(f"HFprov{idx}"):
                    stats["compile_failed"] += 1
                    compile_failed_idx.append(idx)
                    continue                     # slot stays open for the next passer
                if commit(idx, prop):
                    done["flag"] = True
            pending.clear()
            queue_start["t"] = None

        def dispatch_full():
            return target is not None and added + len(pending) >= target

        def stop_dispatch():
            if stop["flag"] or soundness["err"] or done["flag"]:
                return True
            if dispatch_full():
                return True
            if deadline is not None and time.time() >= deadline:
                return True
            return False

        def should_flush(force):
            if force and pending:
                return True
            if len(pending) >= LEAN_BATCH_SIZE:
                return True
            if pending and queue_start["t"] is not None \
                    and time.time() - queue_start["t"] >= BATCH_WAIT_SEC:
                return True
            if dispatch_full() and pending:
                return True
            return False

        while True:
            halt = stop_dispatch()
            # (1) dispatch to fill the COMPUTE window, unless the commit buffer is
            # full (results already collected/sequenced but not yet committed).
            while (not halt) and len(inflight) < WINDOW \
                    and (len(ready) + len(pending)) < COMMIT_BUFFER_CAP:
                inflight[disp["next"]] = wp.apply_async(G.worker, (disp["next"], accept))
                disp["next"] += 1
            progressed = False
            # (2) collect ANY finished results out of order (frees window slots so a
            # slow premise set can't starve the other workers — §I no HOL blocking).
            for i in [i for i, f in inflight.items() if f.ready()]:
                ready[i] = inflight.pop(i).get()
                progressed = True
            # (3) sequence strictly by premise index from the ready buffer.
            while disp["collect"] in ready:
                tag, idx, payload, lstats, elapsed = ready.pop(disp["collect"])
                disp["collect"] += 1
                sampled += 1
                sample_time_total += elapsed
                for k, v in lstats.items():
                    stats[k] += v
                if tag == "soundness":
                    soundness["err"] = (idx, payload)
                    break
                if payload is not None:
                    pending.append((idx, payload))
                    if queue_start["t"] is None:
                        queue_start["t"] = time.time()
                progressed = True
            if soundness["err"]:
                break
            # (4) compile + commit in index order.
            if should_flush(halt and not inflight and not ready):
                flush()
            if done["flag"]:
                break
            # (5) done when halted and nothing is running or buffered.
            if halt and not inflight and not ready and not pending:
                break
            if not progressed:
                time.sleep(0.02)
        flush()
        # resume the next phase at a deterministic index: everything up to the last
        # new write has been committed; indices dispatched speculatively beyond it
        # are discarded (they used this phase's ``accept``) and re-run next phase.
        disp["collect"] = boundary["idx"] + 1
        disp["next"] = boundary["idx"] + 1
        inflight.clear()
        ready.clear()
        return added, replaced, boundary["idx"], time.time() - phase_t0

    t0 = time.time()
    if minutes is not None:
        # §IV (v0.6.4): 85% of the time budget for the main phase, 15% for supplement.
        main_deadline = t0 + minutes * 60.0 * 0.85
        full_deadline = t0 + minutes * 60.0
    else:
        main_deadline = full_deadline = None

    phase1 = phase2 = None
    try:
        # ── main phase: split_needed only ─────────────────────────────────────
        phase1 = run_phase("split_needed", target, main_deadline)
        S = phase1[0]
        if not soundness["err"]:
            # ── supplement phase: rounding_only, CAP floor(S * RO_MAX_RATIO) ────
            # §3 (v0.6.7): this is an upper cap, not a fixed target — the phase stops
            # at the cap OR the time budget, whichever first (whatever it gets is kept).
            ro_cap = int(S * G.RO_MAX_RATIO)
            if ro_cap > 0:
                stop["flag"] = False      # re-arm after a Ctrl+C-ended main phase
                print(f"\nsupplement phase: up to {ro_cap} rounding_only "
                      f"(cap = floor({S} * {G.RO_MAX_RATIO}))")
                phase2 = run_phase("rounding_only", ro_cap, full_deadline)
            else:
                print(f"\nsupplement phase skipped: S={S} → cap floor("
                      f"{S} * {G.RO_MAX_RATIO}) = 0 rounding_only")
    finally:
        mem.stop()
        wp.terminate()
        wp.join()

    elapsed = time.time() - t0

    if soundness["err"]:
        idx, msg = soundness["err"]
        print("\n!!! SOUNDNESS FAILURE — stopping immediately (premise set "
              f"#{idx}) !!!")
        print(msg)
        return 2

    added = phase1[0] + (phase2[0] if phase2 else 0)
    replaced = phase1[1] + (phase2[1] if phase2 else 0)
    # §rule 1/2: premise-index → record map and the indices skipped by a Lean
    # compile failure (so the record = first-N-passing-by-index can be audited).
    print("\npremise-index → record (commit order):")
    print("  " + (", ".join(f"{n}=idx{ix}({md})" for n, ix, _dt, md in write_index_log)
                  or "(none)"))
    print(f"compile-failure-skipped premise indices: {compile_failed_idx or 'none'}")
    _print_summary(stats, sampled, added, replaced, elapsed, sample_time_total,
                   writes_by_depth, new_skel_segments, batch_count,
                   batch_time_total, bisection_total, mem.peak, n_workers,
                   phase1, phase2)
    _recheck_sample(base_seed)
    return 0


def _recheck_sample(base_seed, k=5):
    """§III.5: randomly pick k records and compile their C{n}.lean standalone,
    confirming that theorems verified inside a batch also compile on their own
    (a batch-vs-standalone disagreement would be flagged here — §rule 2)."""
    import random as _r
    recs = [d for d in G.RECORD.iterdir()
            if d.is_dir() and (d / f"{d.name}.lean").exists()]
    if not recs:
        return
    pick = _r.Random(base_seed).sample(recs, min(k, len(recs)))
    print(f"\n§III.5 standalone re-compile of {len(pick)} random records:")
    bad = []
    for d in sorted(pick, key=lambda d: int(d.name[1:]) if d.name[1:].isdigit() else 0):
        ok, msg = F.compile_lean(d.name, (d / f"{d.name}.lean").read_text())
        print(f"  {d.name}: {'OK' if ok else 'FAIL — ' + msg[:200]}")
        if not ok:
            bad.append(d.name)
    if bad:
        print(f"  !!! standalone compile DISAGREES with batch for: {bad}")


def _print_summary(stats, sampled, added, replaced, elapsed, sample_time_total,
                   writes_by_depth, new_skel_segments, batch_count,
                   batch_time_total, bisection_total, peak_bytes, n_workers,
                   phase1=None, phase2=None):
    by_depth, n_unknown, n_total = scan_records(G.RECORD)
    mins = elapsed / 60.0 if elapsed else 0.0

    print("\n" + "=" * 64)
    print("HexForge v{} run summary".format(G.GENERATOR_VERSION))
    print("=" * 64)

    # §6.1 throughput
    print("throughput:")
    print(f"  new conjectures written : {added}  (+{replaced} in-place replacements)")
    print(f"  premise sets processed  : {sampled}")
    print(f"  wall time               : {elapsed:.1f}s ({mins:.2f} min), "
          f"{n_workers} workers")
    # §IV (v0.6.4): per-phase timing and output
    if phase1 is not None:
        print(f"  main  phase (split_needed) : {phase1[0]} written "
              f"(+{phase1[1]} repl) in {phase1[3]:.1f}s")
    if phase2 is not None:
        print(f"  suppl phase (rounding_only): {phase2[0]} written "
              f"(+{phase2[1]} repl) in {phase2[3]:.1f}s")
    elif phase1 is not None:
        print("  suppl phase (rounding_only): skipped")
    if mins > 0:
        print(f"  writes/min (overall)    : {added / mins:.2f}")
        for dtp in ("split_needed", "rounding_only"):
            print(f"  writes/min ({dtp:13s}): {writes_by_depth.get(dtp, 0) / mins:.2f}  "
                  f"(total {writes_by_depth.get(dtp, 0)})")
    if sampled:
        print(f"  avg worker time / group : {sample_time_total / sampled:.2f}s "
              f"(sum of per-group cpu time / groups)")

    # §6.2 difficulty distribution
    print("difficulty (hardness) distribution over the record:")
    for dtp in ("split_needed", "rounding_only"):
        q = _quantiles(by_depth.get(dtp, []))
        cnt = len(by_depth.get(dtp, []))
        if q:
            print(f"  {dtp:13s} (n={cnt}): min={q[0]:.3f} p20={q[1]:.3f} "
                  f"p40={q[2]:.3f} p60={q[3]:.3f} p80={q[4]:.3f} max={q[5]:.3f}")
        else:
            print(f"  {dtp:13s} (n=0): —")

    # §6.3 skeleton saturation
    print("skeleton saturation (new skeletons per 100 premise sets):")
    if new_skel_segments:
        for seg in sorted(new_skel_segments):
            print(f"  premise sets {seg*100+1:>5}-{seg*100+100:<5}: "
                  f"+{new_skel_segments[seg]} skeletons")
    else:
        print("  (none)")

    # §6.4 attained unknown
    ratio = (100.0 * n_unknown / n_total) if n_total else 0.0
    print(f"attained == 'unknown': {n_unknown} / {n_total} ({ratio:.1f}%)")

    # §6.5 discards
    print("discards by reason:")
    for reason in ("empty_premises", "no_p6_canonical", "p6_upper_bound",
                   "p6_padding", "too_many_terms", "proof_reconstruct_failed",
                   "premise_weakening", "linear_only", "not_attained",
                   "too_shallow", "duplicate", "premise_minimized_duplicate",
                   "same_skeleton_worse", "recheck_failed", "depth_mismatch",
                   "rounding_only_skipped", "split_needed_skipped",
                   "too_slow", "compile_failed"):
        print(f"  {reason:28s}: {stats.get(reason, 0)}")

    # §6.6 memory + Lean batches
    print(f"peak memory (process tree) : {peak_bytes / (1024**3):.2f} GiB")
    print(f"Lean batch compiles        : {batch_count}  "
          f"(avg {batch_time_total / batch_count:.1f}s/batch)" if batch_count
          else "Lean batch compiles        : 0")
    print(f"bisection sub-compiles     : {bisection_total}")


if __name__ == "__main__":
    sys.exit(main(sys.argv))
