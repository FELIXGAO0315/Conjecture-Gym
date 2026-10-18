#!/usr/bin/env python3
"""v1.5 PHASE C6 — cold 319x319 + 231-archive matrix with TWO-SIDED certificates.

Discards the old cache and recomputes everything cold (C1). Every distinct omega
query is keyed on (canonical base+goal, encoding_version, pf_trust_commit,
toolchain), its Lean verdict is three-valued, and it carries a z3 two-sided
certificate (C3/C4): PROVEN must be solver-UNSAT, NOT_PROVEN must yield an integer
witness re-checked in pure Python (pf_trust.certify). Reproduces M1, M2 (both
orders), C3, graph-soundness, monotonicity, UNKNOWN (must be 0) and the loss
attribution (OTHER/PARAM_BUG/REPLACEMENT + the 311 artifact), and diffs every
judgment against v1.4.7. Resumable: the cold cache jsonl is the checkpoint; a
heartbeat is written each batch for the supervisor.
"""
import glob
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

ROOT = "/home/felix_gao/Conjecture-Gym"
sys.path.insert(0, ROOT)
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from pf_trust import lean_batch as LB
from pf_trust import audits as AUD
from pf_trust import certify
from pf_trust import pins
from pf_trust.supervise import Heartbeat, write_checkpoint

PINS = pins.assert_pins()                       # refuse to run on version drift
dom = GraphDomain(); D.configure(dom)

OUTDIR = Path(ROOT) / "analysis" / "v1.5" / "artifacts"
OUTDIR.mkdir(parents=True, exist_ok=True)
COLD_CACHE = OUTDIR / "omega_cold_cache.jsonl"  # C1 cold cache (checkpoint)
CERTS = OUTDIR / "matrix_certs.jsonl"           # persisted two-sided certs / witnesses
OUT = Path(ROOT) / "analysis" / "v1.5" / "matrix_cold.json"
DONE = OUTDIR / "matrix_cold.done"
HB = Heartbeat(os.environ.get("PF_HEARTBEAT", str(OUTDIR / "matrix_cold.hb")))

ENCODING_VERSION = "v1.5"
PF_COMMIT = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"],
                                    cwd=ROOT, text=True).strip()
TOOLCHAIN = PINS["lean_toolchain"] + "+mathlib:" + PINS["mathlib_rev"][:12]

_cache = {}                                     # ckey -> record dict (3-valued + cert)
if COLD_CACHE.exists():
    for ln in COLD_CACHE.read_text().splitlines():
        if ln.strip():
            o = json.loads(ln); _cache[o["k"]] = o
print(f"[init] loaded {len(_cache)} cold cached certs; commit={PF_COMMIT} "
      f"toolchain={TOOLCHAIN}", flush=True)

_runner = LB.lake_runner(str(CC._LEAN_DIR), extra_args=["-D", "maxErrors=100000000"])
_cf = open(COLD_CACHE, "a")
STATE = {"batches": 0, "queries": 0, "unknown": 0, "disagree": 0, "t0": time.time()}


def _ckey(base, goal):
    payload = json.dumps([sorted((sorted(c.items()), r, h) for (c, r, h) in base),
                          [sorted(goal[0].items()), goal[1], goal[2]],
                          ENCODING_VERSION, PF_COMMIT, TOOLCHAIN], sort_keys=True)
    return hashlib.sha256(payload.encode()).hexdigest()


def _lean_verdicts(cases):
    """cases: [(name, facts, goal, vars)] -> {name: Verdict} (three-valued)."""
    goals = [LB.Goal(f"thm_{i}", CC._goal_statement(f, g, v), "intros; omega")
             for i, (_n, f, g, v) in enumerate(cases)]
    res = LB.verify(goals, CC._OMEGA_HEADER, _runner, max_batch=400)
    return {n: res[f"thm_{i}"].verdict for i, (n, _f, _g, _v) in enumerate(cases)}


def entail_many(queries, label=""):
    """queries: [(qk, base, goal, vars)] -> {qk: bool} (True iff Lean PROVEN).
    Fills the cold cache + cert store with the three-valued verdict and the z3
    two-sided certificate. Fail-closed: UNKNOWN maps to False (not entailed)."""
    out, todo = {}, []
    for qk, base, goal, vs in queries:
        ck = _ckey(base, goal)
        if ck in _cache:
            out[qk] = (_cache[ck]["verdict"] == "proven")
        else:
            todo.append((qk, ck, base, goal, vs))
    for i in range(0, len(todo), 400):
        part = todo[i:i + 400]
        verds = _lean_verdicts([(qk, base, goal, vs) for (qk, ck, base, goal, vs) in part])
        for (qk, ck, base, goal, vs) in part:
            v = verds[qk]
            vs_name = v.value                      # "proven"|"not_proven"|"unknown"
            z = certify.entailment_status(base, goal, vs)   # two-sided cert
            # agreement: proven<->entailed, not_proven<->refuted
            lean_entailed = (v is LB.Verdict.PROVEN)
            z_entailed = (z["status"] == "entailed")
            agree = (lean_entailed == z_entailed) and z["status"] != "unknown"
            witness = z.get("witness")
            recheck_ok = (z["recheck"]["ok"] if z.get("recheck") else None)
            rec = {"k": ck, "verdict": vs_name, "z3": z["status"], "agree": agree,
                   "witness": witness, "recheck_ok": recheck_ok}
            # For NOT_PROVEN, persist the (base, goal) too so verify_all can RE-CHECK the
            # witness independently in pure Python (C3). Keeps the cache small otherwise.
            if v is not LB.Verdict.PROVEN and witness is not None:
                rec["base"] = [[sorted(c.items()), r, h] for (c, r, h) in base]
                rec["goal"] = [sorted(goal[0].items()), goal[1], goal[2]]
            _cache[ck] = rec
            _cf.write(json.dumps(rec) + "\n")
            out[qk] = lean_entailed
            STATE["queries"] += 1
            if v is LB.Verdict.UNKNOWN:
                STATE["unknown"] += 1
            if not agree:
                STATE["disagree"] += 1
        _cf.flush()
        STATE["batches"] += 1
        el = time.time() - STATE["t0"]
        HB.beat({"stage": label, "queries": STATE["queries"], "batches": STATE["batches"],
                 "unknown": STATE["unknown"], "disagree": STATE["disagree"]})
        write_checkpoint(OUTDIR / "matrix_cold.ckpt", {"stage": label, **{k: STATE[k] for k in ("queries", "batches", "unknown", "disagree")}})
        print(f"[entail {label}] +{len(part)} ({i+len(part)}/{len(todo)}) "
              f"cache={len(_cache)} q={STATE['queries']} unknown={STATE['unknown']} "
              f"disagree={STATE['disagree']} el={el:.0f}s", flush=True)
    return out


def entail(base, goal, vs):
    return entail_many([("t", base, goal, vs)])["t"]


# ───────────────────────── matrix helpers (ported from step3/step4) ──────────
def base_of(props, numeric):
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    pset, inv, conds = CC.active_restricted_facts(props, params)
    return pset, [CC._ptuple(pr) for pr in numeric] + inv


def disp_fact(v):
    d = v["disp"]
    return ({x: int(k) for x, k in d["coeffs"].items() if int(k) != 0}, CC._norm(d["rel"]), int(d["rhs"]))


def goal_of(v):
    c = v["canon"]
    return ({x: int(k) for x, k in c["coeffs"].items() if int(k) != 0}, c["rel"], int(c["rhs"]))


final = G.load_records(G.RECORD)
archive = G.load_pruned_archive(G.RECORD)
views = [G._record_premise_view(d) for d in final]
vb = {v["id"]: v for v in views}
print(f"[init] {len(final)} records, {len(archive)} archived", flush=True)


def run():
    HB.beat({"stage": "start"})
    # ── 1. usability matrix (param-aware) ──
    print("[stage] usability matrix", flush=True)
    bases = {}; uq = []
    for T in views:
        pset, base = base_of(T["props"], T["numeric"]); bases[T["id"]] = (pset, base)
        tv = sorted({v for f in base for v in f[0]})
        for R in views:
            if R["id"] == T["id"] or not CC.props_dischargeable(R["props"], T["props"], pset):
                continue
            for j, pr in enumerate(R["numeric"]):
                g = CC._ptuple(pr)
                uq.append((f"U|{T['id']}|{R['id']}|{j}", base, g, sorted(set(tv) | set(g[0]))))
    udec = entail_many(uq, "usable")
    usable = {T["id"]: set() for T in views}
    premcount = defaultdict(lambda: defaultdict(int)); premok = defaultdict(lambda: defaultdict(int))
    for (qk, base, goal, vs) in uq:
        _, tid, rid, j = qk.split("|"); premcount[tid][rid] += 1; premok[tid][rid] += 1 if udec[qk] else 0
    for T in views:
        pset, base = bases[T["id"]]
        for R in views:
            if R["id"] == T["id"] or not CC.props_dischargeable(R["props"], T["props"], pset):
                continue
            if not R["numeric"] or premcount[T["id"]][R["id"]] == premok[T["id"]][R["id"]]:
                usable[T["id"]].add(R["id"])

    # ── 2. M1 ──
    print("[stage] M1", flush=True)
    invq = []; recq = []
    for T in views:
        pset, base = bases[T["id"]]; g = goal_of(T); vs = sorted({v for f in base for v in f[0]} | set(g[0]))
        invq.append((f"INV|{T['id']}", base, g, vs))
        facts = list(base) + [disp_fact(vb[r]) for r in sorted(usable[T["id"]])]
        vs2 = sorted({v for f in facts for v in f[0]} | set(g[0]))
        recq.append((f"REC|{T['id']}", facts, g, vs2))
    invd = entail_many(invq, "inv"); recd = entail_many(recq, "rec")
    inv_ent = {T["id"] for T in views if invd[f"INV|{T['id']}"]}
    rec_ent = {T["id"] for T in views if recd[f"REC|{T['id']}"]}
    redundant = [T["id"] for T in views if (T["id"] not in inv_ent) and (T["id"] in rec_ent)]

    # ── 3. M2 both orders ──
    def seq(order):
        present = set(order); cand = set(redundant); removed = []
        for tid in order:
            if tid not in cand or tid not in present:
                continue
            avail = [r for r in usable[tid] if r in present and r != tid]
            facts = list(bases[tid][1]) + [disp_fact(vb[r]) for r in avail]; g = goal_of(vb[tid])
            vs = sorted({v for f in facts for v in f[0]} | set(g[0]))
            if entail_many([(f"M2|{tid}", facts, g, vs)], "m2")[f"M2|{tid}"]:
                present.discard(tid); removed.append(tid)
        return sorted(present, key=lambda x: int(x[1:])), removed
    asc = sorted((v["id"] for v in views), key=lambda x: int(x[1:])); desc = list(reversed(asc))
    print("[stage] M2 asc", flush=True); basis_asc, rem_asc = seq(asc)
    print("[stage] M2 desc", flush=True); basis_desc, rem_desc = seq(desc)

    # ── 4. C3 (param-aware complete closure of archive) ──
    print("[stage] C3", flush=True)
    arch_by = {}
    for i, e in enumerate(archive):
        props = e["props"]; numeric = e["numeric"]
        canon = {"coeffs": {k: int(v) for k, v in e["canonical"]["coeffs"].items()}, "rel": e["canonical"]["rel"], "rhs": int(e["canonical"]["rhs"])}
        pset, base = base_of(props, numeric)
        us = [R for R in views if CC.props_dischargeable(R["props"], props, pset)]
        subq = []
        for R in us:
            for j, pr in enumerate(R["numeric"]):
                g = CC._ptuple(pr); subq.append((f"CU|{i}|{R['id']}|{j}", base, g, sorted({v for f in base for v in f[0]} | set(g[0]))))
        arch_by[i] = (base, canon, us, subq)
    alld = entail_many([q for i in arch_by for q in arch_by[i][3]], "c3usable")
    c3q = []
    for i, (base, canon, us, subq) in arch_by.items():
        pc = defaultdict(int); po = defaultdict(int)
        for (qk, b, g, v) in subq:
            _, ii, rid, j = qk.split("|"); pc[rid] += 1; po[rid] += 1 if alld[qk] else 0
        facts = list(base)
        for R in us:
            if not R["numeric"] or pc[R["id"]] == po[R["id"]]:
                facts.append(disp_fact(R))
        g = ({k: int(v) for k, v in canon["coeffs"].items() if int(v) != 0}, canon["rel"], int(canon["rhs"]))
        vs = sorted({v for f in facts for v in f[0]} | set(g[0]))
        c3q.append((f"C3|{i}", facts, g, vs))
    c3d = entail_many(c3q, "c3")
    c3_fail = [archive[i]["standard_form"] for i in arch_by if not c3d[f"C3|{i}"]]
    c3_ent = sum(1 for i in arch_by if c3d[f"C3|{i}"])

    # ── 5. graph-soundness (C5) ──
    print("[stage] graph soundness", flush=True)
    INV = __import__("PolyForge.domains.graph.inventory", fromlist=["properties_of"])
    pool = json.load(open(G.DATA))["graphs"]
    graphs = [(g, INV.properties_of(g)) for g in pool if g["n"] >= 1]

    def sat(view, g):
        return G._graph_matches(g[0], g[1], view["props"], view["numeric"])
    pairs = [(vb[t], vb[r]) for t in usable for r in usable[t]]
    gsv = AUD.graph_soundness_violations(pairs, lambda t, r: True, graphs, sat)
    gs_viol = [(t["id"], r["id"], g[0].get("atlas_index")) for (t, r, g) in gsv]

    # ── 6. monotonicity (restricted vs complete) ──
    print("[stage] monotonicity", flush=True)
    G.clear_impl_cache()
    mono = []
    for T in views:
        tv = {"props": T["props"], "pset": bases[T["id"]][0],
              "params": {p["name"]: p.get("param") for p in T["props"] if "param" in p}, "numeric": T["numeric"]}
        for R in views:
            if R["id"] == T["id"]:
                continue
            if G._premises_imply(tv, {"props": R["props"], "numeric": R["numeric"]}):
                if R["id"] not in usable[T["id"]]:
                    mono.append((T["id"], R["id"]))

    # ── 7. realizability of refuted witnesses (C5, informational) ──
    # A witness is a model over the base invariants where the premises hold and the
    # goal fails. It is "realizable" if some real pool graph has exactly those
    # invariant values (a genuine simple-3-polytope/graph counterexample) rather than
    # only an arithmetic one. Informational: does NOT change any verdict.
    print("[stage] realizability", flush=True)
    real_counts = realizability_counts(graphs)

    # ── 8. loss attribution (ported step4) ──
    print("[stage] loss attribution", flush=True)
    attribution = loss_attribution(bases, usable, views, c3_fail, c3_ent)

    # ── diffs vs v1.4.7 ──
    v147 = json.load(open("/home/felix_gao/pf_production/v147_step3.json"))
    old_m1 = set(v147["M1"]["ids"]); new_m1 = set(redundant)
    old_c3 = set(v147["C3"]["failures"]); new_c3 = set(c3_fail)

    out = {
        "pins": PINS, "encoding_version": ENCODING_VERSION, "pf_commit": PF_COMMIT, "toolchain": TOOLCHAIN,
        "totals": {"distinct_queries": len(_cache), "unknown": STATE["unknown"],
                   "disagreements_lean_vs_z3": STATE["disagree"]},
        "two_sided": two_sided_summary(),
        "M1": {"count": len(redundant), "ids": sorted(new_m1, key=lambda x: int(x[1:])), "inv_entailed": len(inv_ent)},
        "M2": {"asc_basis": len(basis_asc), "asc_removed": rem_asc, "desc_basis": len(basis_desc), "desc_removed": rem_desc},
        "C3": {"entailed": c3_ent, "total": len(archive), "failures": c3_fail},
        "graph_soundness_violations": gs_viol,
        "monotonicity_violations": mono,
        "UNKNOWN": {"count": STATE["unknown"]},
        "realizability": real_counts,
        "loss_attribution": attribution,
        "diff_vs_v147": {
            "M1_only_old": sorted(old_m1 - new_m1), "M1_only_new": sorted(new_m1 - old_m1), "M1_disagree": len(old_m1 ^ new_m1),
            "C3_only_old": sorted(old_c3 - new_c3), "C3_only_new": sorted(new_c3 - old_c3), "C3_disagree": len(old_c3 ^ new_c3),
            "M2_asc_old": v147["M2"]["asc_basis"], "M2_desc_old": v147["M2"]["desc_basis"],
            "per_judgment_compared": len(views) + len(archive),
            "per_judgment_disagree": len(old_m1 ^ new_m1) + len(old_c3 ^ new_c3),
        },
    }
    OUT.write_text(json.dumps(out, indent=2))
    _cf.close()
    # write the cert store fresh from the (complete) cache: every distinct query with
    # its three-valued verdict, z3 status, agreement, and (for NOT_PROVEN) the witness
    # + base/goal so the re-check can be re-run independently.
    with open(CERTS, "w") as cfout:
        for rec in _cache.values():
            cfout.write(json.dumps(rec) + "\n")
    DONE.write_text(json.dumps({"ts": int(time.time()), "queries": len(_cache)}))
    print("MATRIX_COLD DONE:", json.dumps({k: out[k] for k in ("totals", "two_sided")}), flush=True)
    print(json.dumps({"M1": out["M1"]["count"], "M2": [out["M2"]["asc_basis"], out["M2"]["desc_basis"]],
                      "C3": [c3_ent, len(archive)], "UNKNOWN": STATE["unknown"],
                      "disagree": STATE["disagree"], "per_judgment_disagree": out["diff_vs_v147"]["per_judgment_disagree"],
                      "attribution": attribution["attribution"]}), flush=True)


def realizability_counts(graphs):
    """For every distinct refuted witness in the cold cache, decide whether a real
    pool graph realizes it exactly (over the base invariants in the witness).
    Defensive: never crashes the matrix (informational C5)."""
    INV = __import__("PolyForge.domains.graph.inventory", fromlist=["VARS"])
    base_vars = set(INV.VARS)
    counts = {"checked": 0, "realizable": 0, "arithmetic_only": 0, "error": None}
    try:
        real = []
        for gg, _props in graphs:
            real.append({k: int(gg[k]) for k in base_vars if k in gg})
        for rec in _cache.values():
            w = rec.get("witness")
            if rec["verdict"] != "not_proven" or not w:
                continue
            mk = {k: int(v) for k, v in w.items() if k in base_vars}
            if not mk:
                continue
            counts["checked"] += 1
            hit = any(all(rt.get(k) == val for k, val in mk.items()) for rt in real)
            counts["realizable" if hit else "arithmetic_only"] += 1
    except Exception as e:                       # informational only
        counts["error"] = f"{type(e).__name__}: {e}"
    return counts


def two_sided_summary():
    proven = notp = unk = 0
    proven_unsat = notp_witness = notp_witness_ok = disagree = 0
    for rec in _cache.values():
        if rec["verdict"] == "proven":
            proven += 1
            if rec["z3"] == "entailed":
                proven_unsat += 1
        elif rec["verdict"] == "not_proven":
            notp += 1
            if rec.get("witness"):
                notp_witness += 1
                if rec.get("recheck_ok"):
                    notp_witness_ok += 1
        else:
            unk += 1
        if not rec["agree"]:
            disagree += 1
    return {"proven": proven, "proven_solver_unsat_confirmed": proven_unsat,
            "not_proven": notp, "not_proven_with_witness": notp_witness,
            "not_proven_witness_recheck_ok": notp_witness_ok,
            "unknown": unk, "disagreements": disagree}


# ── loss attribution (ported from step4_attribution.py) ──
def _entailed_by(props, numeric, canon, ctx_views):
    pset, base = base_of(props, numeric)
    us = [R for R in ctx_views if CC.props_dischargeable(R["props"], props, pset)]
    uq = []
    for ri, R in enumerate(us):
        for j, pr in enumerate(R["numeric"]):
            g = CC._ptuple(pr); uq.append((f"{ri}|{j}", base, g, sorted({v for f in base for v in f[0]} | set(g[0]))))
    ud = entail_many(uq, "attr_usable")
    pc = defaultdict(int); po = defaultdict(int)
    for (qk, b, g, v) in uq:
        ri, j = qk.split("|"); pc[ri] += 1; po[ri] += 1 if ud[qk] else 0
    facts = list(base)
    for ri, R in enumerate(us):
        if not R["numeric"] or pc[str(ri)] == po[str(ri)]:
            facts.append(disp_fact(R))
    g = ({k: int(v) for k, v in canon["coeffs"].items() if int(v) != 0}, canon["rel"], int(canon["rhs"]))
    vs = sorted({v for f in facts for v in f[0]} | set(g[0]))
    return entail(facts, g, vs)


_PROPS = {"is_tree", "is_connected", "is_acyclic", "is_bipartite", "not_bipartite",
          "has_cycle", "nontrivial", "is_regular", "is_k_edge_connected"}


def _pexpr(s):
    s = s.strip().replace("- ", "+ -"); co = {}; k = 0
    for t in s.split(" + "):
        t = t.strip()
        if not t:
            continue
        if "*" in t:
            a, v = t.split("*"); co[v.strip()] = co.get(v.strip(), 0) + int(a)
        elif t.lstrip("-").isdigit():
            k += int(t)
        else:
            neg = t.startswith("-"); v = t.lstrip("-"); co[v] = co.get(v, 0) + (-1 if neg else 1)
    return co, k


def _pineq(s):
    for rel in (">=", "<=", "="):
        if rel in s:
            l, r = s.split(rel, 1); lc, lk = _pexpr(l); rc, rk = _pexpr(r)
            co = {v: lc.get(v, 0) - rc.get(v, 0) for v in set(lc) | set(rc) if lc.get(v, 0) - rc.get(v, 0)}
            return {"coeffs": co, "rel": ("=" if rel == "=" else rel), "rhs": rk - lk}


def _pform(f):
    m = re.match(r"if \((.*)\), then \((.*)\)$", f.strip())
    if not m:
        return None
    props = []; numeric = []
    for cl in re.findall(r"\(([^()]*(?:\([^()]*\))?[^()]*)\)", m.group(1)):
        cl = cl.strip(); pm = re.match(r"([a-z_]+)(?:\((\d+)\))?$", cl)
        if pm and pm.group(1) in _PROPS:
            p = {"name": pm.group(1)}
            if pm.group(2) is not None:
                p["param"] = int(pm.group(2))
            props.append(p)
        else:
            numeric.append(_pineq(cl))
    return props, numeric, _pineq(m.group(2))


def loss_attribution(bases, usable, views, c3_fail, c3_ent):
    # 1. 8-loss @ reconstructed 311
    targets = json.load(open("/home/felix_gao/pf_production/restore_targets.json"))
    rkeys = set()
    for t in targets:
        c = {"coeffs": {k: int(v) for k, v in t["canonical"]["coeffs"].items()}, "rel": t["canonical"]["rel"], "rhs": int(t["canonical"]["rhs"])}
        rkeys.add(G.content_key(t["props"], t["numeric"], c))
    be = [e for e in archive if e["reason"] == "pruned_basis_audit"][0]
    c191 = {"id": "C191recon", "conjecture": {"formula": be["standard_form"], "properties_premises": be["props"],
            "numeric_premises": be["numeric"], "conclusion": be["canonical"], "canonical_form": be["canonical"]}}
    v311 = [G._record_premise_view(d) for d in final if G.record_content_key(d) not in rkeys] + [G._record_premise_view(c191)]
    loss8 = []
    for t in targets:
        c = {"coeffs": {k: int(v) for k, v in t["canonical"]["coeffs"].items()}, "rel": t["canonical"]["rel"], "rhs": int(t["canonical"]["rhs"])}
        pset, base = base_of(t["props"], t["numeric"])
        g = ({k: int(v) for k, v in c["coeffs"].items() if int(v) != 0}, c["rel"], int(c["rhs"]))
        vs = sorted({v for f in base for v in f[0]} | set(g[0]))
        inv_only = entail(base, g, vs)
        ent = _entailed_by(t["props"], t["numeric"], c, v311)
        loss8.append({"formula": t["standard_form"], "inv_entailed": inv_only, "entailed_311": ent,
                      "verdict": "entailed" if ent else "loss"})
    n_loss = sum(1 for x in loss8 if x["verdict"] == "loss")
    n_art = sum(1 for x in loss8 if x["verdict"] == "entailed")
    # 3. replacement losses
    olds = set()
    for lg in glob.glob("/home/felix_gao/pf_production/v142_prod/seg*_seed*.log"):
        for ln in open(lg):
            mm = re.search(r"replaced \(idx \d+\): (.+?)  ->  ", ln)
            if mm:
                olds.add(mm.group(1).strip())
    for d in final:
        for s in (d.get("supersedes") or []):
            olds.add(s)
    repl = []
    for f in sorted(olds):
        pr = _pform(f)
        if pr is None:
            repl.append({"formula": f, "recovered": False}); continue
        props, numeric, concl = pr
        c = {"coeffs": {k: int(v) for k, v in concl["coeffs"].items()}, "rel": concl["rel"], "rhs": int(concl["rhs"])}
        if c["rel"] == "<=":
            c = {"coeffs": {k: -v for k, v in c["coeffs"].items()}, "rel": ">=", "rhs": -c["rhs"]}
        ent = _entailed_by(props, numeric, c, views)
        repl.append({"formula": f, "recovered": True, "entailed_by_319": ent})
    repl_loss = [r for r in repl if r.get("recovered") and not r.get("entailed_by_319")]
    # 4. name-only prune scan
    nameonly = []
    for e in archive:
        if e["reason"] != "pruned_by_newer":
            continue
        used = e.get("certificate", {}).get("records_used", []) or []
        for uid in used:
            urec = next((d for d in final if d["id"] == uid), None)
            if urec is None:
                continue
            up = urec["conjecture"]["properties_premises"]
            pset = G.property_closure({p["name"] for p in e["props"]})
            name_ok = {p["name"] for p in up}.issubset(pset)
            param_ok = CC.props_dischargeable(up, e["props"], pset)
            if name_ok and not param_ok:
                nameonly.append({"pruned": e.get("original_id"), "used": uid, "std": e["standard_form"]}); break
    return {"loss8_311": loss8, "n_loss8": n_loss, "n_artifact": n_art,
            "C3_failures": c3_fail, "C3_shortfall": len(archive) - c3_ent,
            "replacement_recovered": sum(1 for r in repl if r.get("recovered")),
            "replacement_losses": len(repl_loss),
            "replacement_loss_formulas": [r["formula"] for r in repl_loss],
            "attribution": {"OTHER_311_losses": n_loss, "PARAM_BUG_C3_gaps": len(c3_fail),
                            "REPLACEMENT": len(repl_loss), "total": n_loss + len(c3_fail) + len(repl_loss)},
            "name_only_pruned_published": {"count": len(nameonly), "cases": nameonly},
            "published_records_pruned_name_only": 0}


if __name__ == "__main__":
    run()
