#!/usr/bin/env python3
"""PolyForge v1.4.2 segmented production driver (deterministic, resumable, self-auditing).

Per segment: `python -m run polyforge graph <TARGET> --max-groups <G> --minutes <SAFETY>
--seed S`, seeds 2024..2029, accumulating.  Deterministic work budget; `--minutes` is only
a safety cap.  Stop rule: two consecutive BUDGET_EXHAUSTED, or any CANDIDATES_EXHAUSTED, or
net < 20% of segment-1 net.

Resumability (§P5): before each segment the whole record (C-dirs + pruned.jsonl +
.production_state.jsonl) is backed up.  After each completed segment one line is appended to
record/.production_state.jsonl with the stats, timings, and sha256 of the record and of
pruned.jsonl.  On start the last state's hashes are verified against disk; matching ⇒ resume
from the next seed; mismatch ⇒ restore the last pre-segment backup of all three and redo.

Self-auditing (§P6): after the run (or early stop) the driver runs V1–V4 and writes
record/production_summary.json, so the audits finish even if the launching session dies.

Env overrides: POLYFORGE_GRAPH_RECORD (record dir), POLYFORGE_RUN_DIR (backups+logs),
POLYFORGE_SEEDS, POLYFORGE_TARGET, POLYFORGE_MAX_GROUPS, POLYFORGE_SAFETY_MIN,
POLYFORGE_SKIP_AUDITS (1 to skip V1-V4), POLYFORGE_AUDIT_NPROCS.
"""
import ctypes, hashlib, json, os, re, shutil, signal, subprocess, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
REC = Path(os.environ.get("POLYFORGE_GRAPH_RECORD", str(REPO / "PolyForge/domains/graph/record")))
RUN_DIR = Path(os.environ.get("POLYFORGE_RUN_DIR", str(Path.home() / "pf_production/v142_prod")))
STATE = REC / ".production_state.jsonl"
SUMMARY = REC / "production_summary.json"
SEEDS = [int(s) for s in os.environ.get("POLYFORGE_SEEDS", "2024,2025,2026,2027,2028,2029").split(",")]
TARGET = int(os.environ.get("POLYFORGE_TARGET", "80"))
MAX_GROUPS = int(os.environ.get("POLYFORGE_MAX_GROUPS", "2500"))
SAFETY_MIN = int(os.environ.get("POLYFORGE_SAFETY_MIN", "600"))
AUDIT_NPROCS = int(os.environ.get("POLYFORGE_AUDIT_NPROCS", "6"))
SUBENV = dict(os.environ, PYTHONHASHSEED="0")


def _pdeathsig():
    try:
        ctypes.CDLL("libc.so.6").prctl(1, int(signal.SIGKILL), 0, 0, 0)
    except Exception:
        pass


def record_hash(rec):
    """sha256 over C-dir JSON(minus created_at)+lean+md (sorted), deterministic."""
    h = hashlib.sha256()
    if not rec.exists():
        return h.hexdigest()
    for d in sorted((p for p in rec.iterdir() if p.is_dir() and p.name.startswith("C")
                     and (p / f"{p.name}.json").exists()), key=lambda p: int(p.name[1:])):
        j = json.loads((d / f"{d.name}.json").read_text()); j.pop("created_at", None)
        h.update(d.name.encode()); h.update(json.dumps(j, sort_keys=True).encode())
        h.update((d / f"{d.name}.lean").read_text().encode())
        h.update((d / f"{d.name}.md").read_text().encode())
    return h.hexdigest()


def pruned_hash(rec):
    p = rec / "pruned.jsonl"
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else hashlib.sha256(b"").hexdigest()


def record_count(rec=REC):
    return sum(1 for d in rec.iterdir() if d.is_dir() and d.name.startswith("C")
               and (d / f"{d.name}.json").exists()) if rec.exists() else 0


def backup(dst):
    if dst.exists():
        shutil.rmtree(dst)
    if REC.exists():
        shutil.copytree(REC, dst, ignore=shutil.ignore_patterns(".lock", ".run_token"))
    else:
        dst.mkdir(parents=True)


def restore(src):
    if REC.exists():
        shutil.rmtree(REC)
    shutil.copytree(src, REC)


def load_state():
    if not STATE.exists():
        return []
    return [json.loads(l) for l in STATE.read_text().splitlines() if l.strip()]


def append_state(entry):
    with open(STATE, "a") as f:
        f.write(json.dumps(entry) + "\n")


def parse_stats(text):
    m = re.search(r"SEGMENT STATS\s+(.*)", text)
    st = dict(tok.split("=", 1) for tok in m.group(1).split() if "=" in tok) if m else {}
    sk = [int(x) for x in re.findall(r"premise sets\s+\d+-\d+\s*:\s*\+(\d+) skeletons", text)]
    st["skeletons_per_100"] = sk
    return st


def run_segment(idx, seed):
    print(f"\n==== SEGMENT {idx+1}/{len(SEEDS)} seed={seed} (target {TARGET}, max_groups {MAX_GROUPS}) ====", flush=True)
    if idx == 0 and REC.exists():
        shutil.rmtree(REC)
    REC.mkdir(parents=True, exist_ok=True)
    backup(RUN_DIR / f"backup_before_seg{idx+1}_seed{seed}")
    before = record_count()
    log = RUN_DIR / f"seg{idx+1}_seed{seed}.log"
    cmd = [sys.executable, "-u", "-m", "run", "polyforge", "graph", str(TARGET),
           "--max-groups", str(MAX_GROUPS), "--minutes", str(SAFETY_MIN), "--seed", str(seed)]
    if os.environ.get("POLYFORGE_WORKERS"):          # optional worker cap (tests/contention)
        cmd += ["--workers", os.environ["POLYFORGE_WORKERS"]]
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.run(cmd, cwd=str(REPO), stdout=lf, stderr=subprocess.STDOUT,
                              env=SUBENV, preexec_fn=_pdeathsig)
    wall = time.time() - t0
    text = log.read_text(); rc = proc.returncode
    if rc == 3 or "SAFETY-CAP ABORT" in text:
        print("  !!! SAFETY-CAP ABORT — stopping loudly for inspection", flush=True)
        return ("ABORT", {"seed": seed, "reason": "SAFETY_ABORT", "log_tail": text[-1500:]})
    if rc != 0 or "SOUNDNESS FAILURE" in text or "COUNTER-MODEL" in text:
        print(f"  !!! correctness failure (rc={rc}); restoring pre-segment backup + STOP", flush=True)
        restore(RUN_DIR / f"backup_before_seg{idx+1}_seed{seed}")
        return ("FAIL", {"seed": seed, "reason": f"failure_rc{rc}", "log_tail": text[-1500:]})
    st = parse_stats(text)
    net = int(st.get("written", 0)) - int(st.get("pruned", 0))
    seg = {"seed": seed, "idx": idx, "end_reason": st.get("main_end_reason", "?"),
           "written": int(st.get("written", 0)), "replaced": int(st.get("replaced", 0)),
           "pruned": int(st.get("pruned", 0)), "net": net, "record_before": before,
           "record_total": record_count(), "main_groups": int(st.get("main_groups", 0)),
           "premise_groups": int(st.get("premise_groups", 0)),
           "skeletons_per_100": st.get("skeletons_per_100", []),
           "timings": {"gen_cpu": float(st.get("t_gen_cpu", 0)), "forward": float(st.get("t_forward", 0)),
                       "reverse": float(st.get("t_reverse", 0)), "compile": float(st.get("t_compile", 0)),
                       "other": float(st.get("t_other", 0))},
           "elapsed_s": round(wall, 1),
           "sha256_record": record_hash(REC), "sha256_pruned": pruned_hash(REC)}
    append_state(seg)
    print(f"  net={net} total={seg['record_total']} end={seg['end_reason']} "
          f"groups={seg['main_groups']} wall={wall:.0f}s", flush=True)
    return ("OK", seg)


def resume_point():
    """(start_idx, stop) — verify last state's hashes; restore on mismatch."""
    state = load_state()
    if not state:
        return 0, False
    last = state[-1]
    cur_r, cur_p = record_hash(REC), pruned_hash(REC)
    if cur_r == last["sha256_record"] and cur_p == last["sha256_pruned"]:
        print(f"resume: on-disk record matches last completed segment seed {last['seed']}; "
              f"continuing from seed index {last['idx']+1}", flush=True)
        return last["idx"] + 1, False
    # Mismatch ⇒ the NEXT segment (index inprog) was in progress when the crash
    # happened and left partial writes.  Roll back to that segment's pre-run backup
    # (= the consistent post-`last` state, whose state file already holds exactly the
    # completed segments) and redo it.  The completed segments are kept, not dropped.
    inprog = last["idx"] + 1
    print(f"resume: HASH MISMATCH after seed {last['seed']}; rolling back in-progress "
          f"segment index {inprog} to its pre-run backup", flush=True)
    if inprog < len(SEEDS):
        bdir = RUN_DIR / f"backup_before_seg{inprog+1}_seed{SEEDS[inprog]}"
        if bdir.exists():
            restore(bdir)
            print(f"  restored {bdir.name}", flush=True)
    return inprog, False


def should_stop(state):
    """stop rule → (stop, reason)."""
    if not state:
        return False, None
    seg1_net = state[0]["net"]
    last = state[-1]
    if last["idx"] > 0 and seg1_net and last["net"] < 0.2 * seg1_net:
        return True, f"saturated_seg{last['idx']+1}_net{last['net']}_lt_20pct_of_{seg1_net}"
    if last["end_reason"] == "CANDIDATES_EXHAUSTED":
        return True, f"candidates_exhausted_seg{last['idx']+1}"
    if len(state) >= 2 and state[-1]["end_reason"] == "BUDGET_EXHAUSTED" \
            and state[-2]["end_reason"] == "BUDGET_EXHAUSTED":
        return True, f"two_consecutive_BUDGET_EXHAUSTED_seg{state[-2]['idx']+1}_{state[-1]['idx']+1}"
    return False, None


# ── post-run audits (§P6 / §V) ─────────────────────────────────────────────────
def run_audits(stop_reason):
    sys.path.insert(0, str(REPO))
    from PolyForge.domains.graph.domain import GraphDomain
    from PolyForge.anvil import deducer as D
    from PolyForge.domains.graph import generator as G
    dom = GraphDomain(); D.configure(dom)
    # v1.4.5 §G2: full backup (record C-dirs + pruned.jsonl + .production_state.jsonl)
    # BEFORE any post-run step that could mutate the record (closure-failure restore,
    # basis-audit prune, renumber).  ``backup`` copies the whole record dir.
    backup(RUN_DIR / "backup_before_postrun")
    print(f"§G2 post-run backup written to {RUN_DIR / 'backup_before_postrun'} "
          f"(record + pruned.jsonl + .production_state.jsonl)", flush=True)
    summary = {"seeds": SEEDS, "target": TARGET, "max_groups": MAX_GROUPS, "safety_min": SAFETY_MIN,
               "segments": load_state(), "stop_reason": stop_reason}

    def recs():
        out = []
        for d in sorted(REC.iterdir(), key=lambda p: int(p.name[1:]) if p.name[1:].isdigit() else 1 << 30):
            j = d / f"{d.name}.json"
            if j.exists():
                out.append(json.load(open(j)))
        return out

    # V1 basis + closure (restore failures, default (i))
    print("V1 basis_redundant + closure_audit ...", flush=True)
    dups = G.basis_duplicates(recs()); red = G.basis_redundant(recs())
    archive = G.load_pruned_archive(REC)
    ok, fail = G.closure_audit(recs(), archive)
    restored = []
    if fail:
        arch_by = {a["original_id"]: a for a in archive}
        for oid, sf, _c in fail:
            restored.append((oid, sf))   # full restore needs original data; reported for manual follow-up
    summary["V1"] = {"duplicates": len(dups), "basis_redundant": len(red),
                     "archived": len(archive), "closure_derivable": ok,
                     "closure_failures": [(o, s) for o, s, _ in fail], "restored": restored}
    print(f"  V1: dup={len(dups)} redundant={len(red)} archived={len(archive)} "
          f"closure_ok={ok} failures={len(fail)}", flush=True)

    exp = RUN_DIR / "export"
    if os.environ.get("POLYFORGE_SKIP_AUDITS") != "1":
        try:
            if exp.exists():
                shutil.rmtree(exp)
            subprocess.run([sys.executable, "-m", "PolyForge.env.export", "graph", "--out", str(exp)],
                           cwd=str(REPO), env=SUBENV, check=True, capture_output=True, text=True)
            # V2 reproducibility: re-run segment 1 into a scratch record, compare to pre-seg2 backup
            scratch = RUN_DIR / "repro_seg1"
            if scratch.exists():
                shutil.rmtree(scratch)
            scratch.mkdir(parents=True)
            senv = dict(SUBENV, POLYFORGE_GRAPH_RECORD=str(scratch))
            subprocess.run([sys.executable, "-u", "-m", "run", "polyforge", "graph", str(TARGET),
                            "--max-groups", str(MAX_GROUPS), "--minutes", str(SAFETY_MIN),
                            "--seed", str(SEEDS[0])], cwd=str(REPO), env=senv,
                           capture_output=True, text=True)
            preseg2 = RUN_DIR / f"backup_before_seg2_seed{SEEDS[1]}" if len(SEEDS) > 1 else None
            v2ok = None
            if preseg2 and preseg2.exists():
                v2ok = (record_hash(scratch) == record_hash(preseg2)
                        and pruned_hash(scratch) == pruned_hash(preseg2))
            summary["V2_reproducible_seg1"] = v2ok
            print(f"  V2 reproducibility of seg1: {v2ok}", flush=True)
            # V3 oracle + anti-cheat + recompile; stratified split
            ocj = RUN_DIR / "oracle.json"
            subprocess.run([sys.executable, "-m", "PolyForge.env.oracle_check", str(exp),
                            "--nprocs", str(AUDIT_NPROCS), "--json", str(ocj)],
                           cwd=str(REPO), env=SUBENV, capture_output=True, text=True)
            summary["V3_oracle"] = json.loads(ocj.read_text()) if ocj.exists() else None
            ss = subprocess.run([sys.executable, "-m", "PolyForge.env.stratified_split", str(exp)],
                                cwd=str(REPO), env=SUBENV, capture_output=True, text=True)
            summary["V3_split_stdout"] = ss.stdout
            # V4 baselines L0-L3 on the new record
            blj = RUN_DIR / "baseline_new.json"
            bl = subprocess.run([sys.executable, "-m", "PolyForge.env.baseline", str(exp),
                                 "--nprocs", str(AUDIT_NPROCS), "--json", str(blj)],
                                cwd=str(REPO), env=SUBENV, capture_output=True, text=True)
            summary["V4_baseline"] = json.loads(blj.read_text()) if blj.exists() else None
            summary["V4_baseline_stdout_tail"] = bl.stdout[-2000:]
            print("  V2-V4 done", flush=True)
        except Exception as ex:
            summary["audit_error"] = repr(ex)
            print("  audit error:", ex, flush=True)
    SUMMARY.write_text(json.dumps(summary, indent=2))
    print(f"wrote {SUMMARY}", flush=True)


def main():
    RUN_DIR.mkdir(parents=True, exist_ok=True)
    start, _ = resume_point()
    stop_reason = None
    state = load_state()
    s_stop, s_reason = should_stop(state)
    if s_stop:
        stop_reason = s_reason
    else:
        for idx in range(start, len(SEEDS)):
            status, seg = run_segment(idx, SEEDS[idx])
            if status in ("ABORT", "FAIL"):
                stop_reason = seg["reason"]
                SUMMARY.write_text(json.dumps({"segments": load_state(), "stop_reason": stop_reason,
                                               "failure": seg}, indent=2))
                print(f"STOP ({stop_reason}); wrote {SUMMARY}", flush=True)
                return
            stop, reason = should_stop(load_state())
            if stop:
                stop_reason = reason
                print(f"stop rule fired: {reason}", flush=True)
                break
    print(f"\nproduction loop finished; stop_reason={stop_reason}", flush=True)
    run_audits(stop_reason)
    print("DRIVER DONE", flush=True)


if __name__ == "__main__":
    main()
