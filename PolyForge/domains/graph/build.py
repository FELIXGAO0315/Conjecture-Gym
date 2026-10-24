"""The one graph conjecture generator — build the full training corpus in ONE run.

`python -m run graph` drives all three graph-conjecture sources into a single
Lean-verified corpus, giving the downstream prover VOLUME, QUALITY, and DIFFICULTY together:

  1. curated   — the LP invariant engine under novelty curation (reverse-pruning, lemma
                 library, multi-generation depth) → record/C*        [quality + difficulty]
  2. harvest   — the SAME LP engine with relaxed dedup, parallel      [volume]
                 generate + parallel verify → record_train/T*
  3. parametric— ∀n family theorems (proof paradigms the LP engine    [proof diversity]
                 cannot express) → record_parametric/F*

then merges + dedups all three → output/train_corpus.jsonl (one row per theorem:
statement_lean = PROBLEM, proof_lean = TARGET, lean_full = compilable).

Scheduling (tuned for a 16-core / 15 GB box): curated and harvest each saturate all cores
and are Lean-memory-heavy, so they run in SEQUENCE (running them together would oversubscribe
cores for no throughput gain and risk OOM).  The parametric phase uses a single Lean REPL
(≈1 core), so it runs CONCURRENTLY with the heavy phases — reclaiming the cores that would
otherwise sit idle during it, the only real parallelism win here.  Tune via the CONFIG block.
"""
from __future__ import annotations
import sys, os, glob, json, time, random, shutil, subprocess, gzip
from datetime import datetime
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parents[3]            # repo root (Conjecture-Gym)

# ────────────────────────────── CONFIG ──────────────────────────────
CURATED_GROUPS = 400                    # curated engine work budget (premise groups); 0 → skip, use existing C*
CURATED_SEED   = 2024                   # curated engine base seed (deterministic)
A_SEEDS        = 3000                   # harvest: more seeds → more (saturating) volume
B2_INSTANCES   = (4, 8, 16, 32)         # parametric: a FEW concrete n per ∀n theorem (not padding — the
                                        # value is the distinct parametric theorems + their proof paradigms)
WORKERS        = 14                     # parallel workers per phase (≈ cores − 2)
# ─────────────────────────────────────────────────────────────────────

REC_A     = ROOT / "PolyForge/domains/graph/record_train"          # harvest T*
REC_P     = ROOT / "PolyForge/domains/graph/record"                # curated C*
REC_PARAM = ROOT / "PolyForge/domains/graph/record_parametric"     # parametric F*
OUT       = ROOT / "output" / "train_corpus.jsonl"                 # the GROWING corpus (accumulates across runs)
STATE     = ROOT / "output" / ".corpus_state.json"                 # seed cursors + run log (so runs advance, not repeat)
BACKUPS   = ROOT / "output" / "backups"                            # pre-write backup of the corpus (safety, not clobbered)

# module globals populated by _init() in the parent BEFORE the fork pool is created, so the
# forked harvest/compile workers inherit a ready domain (copy-on-write) without re-loading.
_DOMAIN = None
_POOL = None


def _init():
    global _DOMAIN, _POOL
    if _DOMAIN is not None:
        return
    from PolyForge.domains import load_domain
    d = load_domain("graph")
    d.set_run_context(d.load_pool(), {}, 0, {}, {})
    _DOMAIN, _POOL = d, d.pool


# ── phase 1: curated LP engine (quality + difficulty) ────────────────────────
def run_curated(groups, seed):
    if not groups:
        print("    curated: skipped (CURATED_GROUPS=0) — using existing record/C*", flush=True)
        return
    cmd = [sys.executable, "-m", "run", "polyforge", "graph",
           "--max-groups", str(groups), "--seed", str(seed), "--minutes", "600"]
    print(f"    curated: {' '.join(cmd[2:])}", flush=True)
    subprocess.run(cmd, cwd=str(ROOT))


# ── phase 2: graph LP harvest (volume) — parallel generate + parallel verify ──
def _harvest_worker(args):
    from PolyForge.domains.graph import generator as CG
    seed, tier = args
    try:
        return CG.process_premise_set(random.Random(seed), _POOL, {}, Counter(),
                                      seed, accept=tier, harvest=True) or []
    except Exception:
        return []

def _compile_worker(args):
    ci, chunk = args
    d = _DOMAIN
    names = [f"HFt_{ci}_{i}" for i in range(len(chunk))]
    entries = [(names[i], d.build_theorem(names[i], pr["premises"], pr["disp"],
                                          pr["tb"], display=True)) for i, pr in enumerate(chunk)]
    bc = set()
    for pr in chunk:
        bc |= d.lemma_cnums_in(pr["tb"])
    pre = d.lemma_defs_block(bc, {}) if bc else ""
    try:
        results, _ = d.compile_batch(entries, preamble=pre)
    except Exception:
        return []
    out = []
    for i, pr in enumerate(chunk):
        if results.get(names[i]):
            rid = f"T_{ci}_{i}"
            out.append((rid, json.dumps(d.assemble_data(pr, rid, []), ensure_ascii=False, indent=2),
                        d.build_record_lean(rid, pr["premises"], pr["disp"], pr["tb"], {})))
    return out

def _chunks(L, n):
    for i in range(0, len(L), n):
        yield L[i:i + n]

def run_harvest(n_seeds, nw, seed_start=0):
    import multiprocessing as mp
    t0 = time.time()
    # seeds advance across runs (seed_start) so a later run explores NEW premise sets rather than
    # re-deriving the same deterministic theorems (which would dedup to zero new).
    tasks = [(s, t) for s in range(seed_start, seed_start + n_seeds)
             for t in ("split_needed", "rounding_only")]
    seen = {}
    with mp.get_context("fork").Pool(nw) as p:
        for i, batch in enumerate(p.imap_unordered(_harvest_worker, tasks, chunksize=1)):
            for pr in batch:
                seen.setdefault(pr["hash"], pr)
            if i % 80 == 0:
                print(f"      harvest {i}/{len(tasks)}: {len(seen)} distinct ({time.time()-t0:.0f}s)", flush=True)
    props = list(seen.values())
    print(f"    harvest: {len(props)} distinct in {time.time()-t0:.0f}s; verifying (parallel)…", flush=True)
    for dd in glob.glob(str(REC_A / "T*")):
        shutil.rmtree(dd, ignore_errors=True)
    REC_A.mkdir(exist_ok=True)
    verified = 0
    with mp.get_context("fork").Pool(nw) as p:
        for recs in p.imap_unordered(_compile_worker, list(enumerate(_chunks(props, 40))), chunksize=1):
            for rid, js, lean in recs:
                dd = REC_A / rid; dd.mkdir(exist_ok=True)
                (dd / f"{rid}.json").write_text(js); (dd / f"{rid}.lean").write_text(lean)
                verified += 1
    print(f"    harvest verified: {verified} theorems ({time.time()-t0:.0f}s)", flush=True)
    return verified


# ── phase 4: merge all three sources → jsonl ─────────────────────────────────
def _split_thm(txt):
    i = txt.find("theorem "); body = txt[i:] if i >= 0 else txt
    k = body.find(":=")
    return (body.strip(), "") if k < 0 else (body[:k].strip(), body[k + 2:].strip())

def _graph_row(jf, source):
    d = json.load(open(jf)); lf = jf[:-5] + ".lean"
    full = Path(lf).read_text() if Path(lf).exists() else ""
    stmt, proof = _split_thm(full)
    ps = d.get("proof_stats", {}); tac = ["linarith"]
    if ps.get("case_splits", 0) > 0: tac.append("by_cases")
    if ps.get("product_steps", 0) > 0: tac.append("mul_nonneg/ring")
    if ps.get("roundings", 0) > 0: tac.append("omega")
    return {"id": d["id"], "domain": "graph", "source": source,
            "conjecture_type": "fixed-graph invariant inequality",
            "nl": d["conjecture"].get("formula", ""),
            "statement_lean": stmt, "proof_lean": proof, "lean_full": full,
            "tactics": tac, "difficulty": d.get("hardness"), "verified": True}

def _param_row(jf):
    d = json.load(open(jf)); lf = jf[:-5] + ".lean"
    full = Path(lf).read_text() if Path(lf).exists() else ""
    stmt, proof = _split_thm(full)
    return {"id": d["id"], "domain": "graph-parametric", "source": "parametric",
            "conjecture_type": f"family: {d.get('family', '?')}",
            "nl": d["conjecture"].get("statement_lean", ""),
            "statement_lean": stmt, "proof_lean": proof, "lean_full": full,
            "tactics": [d.get("paradigm", "family")], "difficulty": None, "verified": True}

def _key(r):
    """Dedup key = the theorem's formula / statement (so a theorem is never stored twice)."""
    return r.get("nl") or r.get("statement_lean") or r.get("id")

def run_export():
    """ACCUMULATE: load the existing corpus, then append only theorems whose formula is not
    already present — so train_corpus.jsonl ONLY GROWS (prior runs are never lost).  Backs up the
    corpus before writing.  Returns (all_rows, n_new)."""
    seen, rows = set(), []
    def add(r):
        k = _key(r)
        if not k or k in seen:
            return False
        seen.add(k); rows.append(r); return True
    existing = 0
    if OUT.exists():                                        # prior runs' corpus — kept verbatim
        for line in OUT.read_text().splitlines():
            if line.strip() and add(json.loads(line)):
                existing += 1
    before = len(rows)
    for jf in sorted(glob.glob(str(REC_P / "C*/C*.json"))):   # this run's records (curated wins ties)
        add(_graph_row(jf, "curated"))
    for jf in glob.glob(str(REC_A / "T*/T*.json")):
        add(_graph_row(jf, "harvest"))
    for jf in glob.glob(str(REC_PARAM / "F*/F*.json")):
        add(_param_row(jf))
    n_new = len(rows) - before
    if OUT.exists():                                        # safety backup of the pre-write corpus
        BACKUPS.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d-%H%M%S")
        with gzip.open(BACKUPS / f"train_corpus-{ts}.jsonl.gz", "wt", encoding="utf-8") as b:
            b.write(OUT.read_text())
    OUT.parent.mkdir(exist_ok=True)
    with open(OUT, "w") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(f"    corpus: {existing} existing + {n_new} new = {len(rows)} total → {OUT.name}", flush=True)
    return rows, n_new


def _load_state():
    if STATE.exists():
        try:
            return json.loads(STATE.read_text())
        except Exception:
            pass
    return {"harvest_seed_cursor": 0, "curated_seed": CURATED_SEED, "runs": []}

def _save_state(st):
    STATE.parent.mkdir(exist_ok=True)
    STATE.write_text(json.dumps(st, ensure_ascii=False, indent=2))


def _parametric_proc(instance_ns, q):
    """Run the parametric generator (1 Lean REPL) and hand its summary back via a queue.
    Runs as a separate process so it overlaps the heavy phases without threads-across-fork."""
    from . import parametric as PARAM
    q.put(PARAM.generate(instance_ns=instance_ns, verbose=False))


def build(curated_groups=CURATED_GROUPS, curated_seed=None, a_seeds=A_SEEDS,
          b2_instances=B2_INSTANCES, workers=WORKERS):
    """One graph conjecture generator that ACCUMULATES: curated + harvest + parametric, merged
    into the growing train_corpus.jsonl (dedup by formula).  Seeds advance across runs (via a
    cursor in output/.corpus_state.json) so each run explores new premise sets, not the same ones.
    Parametric (light, 1 REPL) runs CONCURRENTLY with the heavy curated+harvest phases."""
    import multiprocessing as mp
    t0 = time.time()
    st = _load_state()
    seed_start = st["harvest_seed_cursor"]
    cur_seed = curated_seed if curated_seed is not None else st["curated_seed"]
    print("PolyForge — graph conjecture corpus (accumulating)")
    print("=" * 60)
    print(f"    harvest seeds {seed_start}..{seed_start + a_seeds - 1}  ·  curated seed {cur_seed}", flush=True)
    # launch parametric NOW, concurrent with curated+harvest (finishes long before harvest's
    # memory-heavy verify, so it never contends on the tight phase).
    print(f"[parametric] (proof diversity) — ∀n families, instances n={b2_instances[0]}..{b2_instances[-1]} — started concurrently", flush=True)
    pq = mp.get_context("fork").SimpleQueue()
    pproc = mp.get_context("fork").Process(target=_parametric_proc, args=(b2_instances, pq))
    pproc.start()

    print(f"[1/3] curated  (quality + difficulty) — LP engine, {curated_groups} groups…", flush=True)
    run_curated(curated_groups, cur_seed)
    print(f"[2/3] harvest  (volume) — LP engine relaxed, {a_seeds} seeds…", flush=True)
    _init()
    _DOMAIN.ensure_lean_fresh()
    run_harvest(a_seeds, workers, seed_start=seed_start)

    pproc.join()
    rB = pq.get() if not pq.empty() else {"verified": "?", "distinct_parametric_paradigms": "?"}
    print(f"    parametric verified: {rB['verified']}  ({rB['distinct_parametric_paradigms']} paradigms)", flush=True)
    print(f"[3/3] accumulate → {OUT.name}…", flush=True)
    rows, n_new = run_export()

    # advance the cursors so the NEXT run explores fresh seeds, and log this run
    st["harvest_seed_cursor"] = seed_start + a_seeds
    st["curated_seed"] = cur_seed + 1
    st["runs"].append({"harvest_seeds": [seed_start, seed_start + a_seeds - 1],
                       "curated_seed": cur_seed, "new": n_new, "total": len(rows)})
    _save_state(st)

    by = Counter(r["source"] for r in rows)
    print("\n" + "=" * 60)
    print(f"CORPUS GROWN ({time.time()-t0:.0f}s):  +{n_new} new → {len(rows)} total  → {OUT}")
    for s, c in by.most_common():
        print(f"  {c:6}  {s}")
    if n_new == 0:
        print("  (0 new — carrier saturated at these seeds; grow it with new invariants / families,")
        print("   not more runs.  See README → 'Is this infinite?'.)")
    return rows
