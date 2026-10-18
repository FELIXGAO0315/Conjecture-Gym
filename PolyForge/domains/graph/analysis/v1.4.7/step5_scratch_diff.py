"""STEP 5 (v1.4.7): scratch diff — v1.4.5-published-code (worktree) vs current code,
2 seeds, --max-groups 150, scratch record dirs only. Per-seed record/archive/replaced_by/
replace_blocked_kept_both, records lost/gained. Heartbeat per gen. Writes v147_step5.json."""
import json, os, re, shutil, subprocess, sys, time
from collections import Counter
from pathlib import Path

NEW = "/home/felix_gao/Conjecture-Gym"
OLD = "/tmp/pf_v145"
SCR = Path("/home/felix_gao/pf_production/v147_scr")
SEEDS = [2024, 2025]


def gen(repo, rec, tag):
    if rec.exists(): shutil.rmtree(rec)
    rec.mkdir(parents=True)
    env = dict(os.environ, PYTHONHASHSEED="0", POLYFORGE_GRAPH_RECORD=str(rec))
    stats = {}
    for s in SEEDS:
        t0 = time.time()
        print(f"[{tag}] seed {s} start", flush=True)
        r = subprocess.run([sys.executable, "-m", "run", "polyforge", "graph", "80",
                            "--max-groups", "150", "--seed", str(s), "--minutes", "90"],
                           cwd=repo, env=env, capture_output=True, text=True, timeout=7200)
        (SCR / f"{tag}_seed{s}.out").write_text(r.stdout[-8000:] + "\n--ERR--\n" + r.stderr[-2000:])
        blocked = len(re.findall(r"replace_blocked_kept_both", r.stdout))
        m = re.search(r"replace_blocked_kept_both['\"]?\s*[:=]\s*(\d+)", r.stdout)
        print(f"[{tag}] seed {s} done {time.time()-t0:.0f}s records={rec_count(rec)}", flush=True)
    return rec


def rec_count(rec):
    return sum(1 for d in rec.iterdir() if d.is_dir() and d.name.startswith("C") and d.name[1:].isdigit())

def recs_by_formula(rec):
    out = {}
    for d in rec.iterdir():
        if d.is_dir() and d.name.startswith("C") and d.name[1:].isdigit():
            data = json.loads((d / f"{d.name}.json").read_text())
            out[data["conjecture"]["formula"]] = data["id"]
    return out

def archive_reasons(rec):
    p = rec / "pruned.jsonl"
    if not p.exists(): return Counter()
    return Counter(json.loads(l)["reason"] for l in p.read_text().splitlines() if l.strip())


SCR.mkdir(parents=True, exist_ok=True)
print("=== gen OLD (v1.4.5-published-code) ===", flush=True); gen(OLD, SCR/"old", "old")
print("=== gen NEW (v1.4.7) ===", flush=True); gen(NEW, SCR/"new", "new")
old_r, new_r = recs_by_formula(SCR/"old"), recs_by_formula(SCR/"new")
old_a, new_a = archive_reasons(SCR/"old"), archive_reasons(SCR/"new")
gained = sorted(set(new_r)-set(old_r)); lost = sorted(set(old_r)-set(new_r))
out = {
  "seeds": SEEDS,
  "old_record_count": len(old_r), "new_record_count": len(new_r),
  "record_growth_pct": round(100*(len(new_r)-len(old_r))/max(1,len(old_r)), 1),
  "old_archive_reasons": dict(old_a), "new_archive_reasons": dict(new_a),
  "new_replaced_by": new_a.get("replaced_by", 0), "old_replaced_by": old_a.get("replaced_by", 0),
  "records_gained_in_new": gained[:40], "records_lost_in_new": lost[:40],
  "n_gained": len(gained), "n_lost": len(lost),
}
Path("/home/felix_gao/pf_production/v147_step5.json").write_text(json.dumps(out, indent=2))
print("STEP5:", json.dumps({k: out[k] for k in ("old_record_count","new_record_count","record_growth_pct",
      "new_replaced_by","old_replaced_by","n_gained","n_lost","new_archive_reasons","old_archive_reasons")}), flush=True)
