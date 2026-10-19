"""STEP 3 (v1.4.7) — full 319x319 matrix through the fixed+routed lean_batch path,
RESUMABLE via a disk cache of omega verdicts (so a kill/idle-gap never loses work).

Outputs v147_step3.json: M1, M2 (both orders), C3 (param-aware), graph-soundness,
monotonicity, UNKNOWN count, and a per-judgment diff vs committed v1.4.5.
Heartbeat every batch (liveness rule).
"""
import json, os, sys, time, hashlib
from pathlib import Path
sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from PolyForge.trust import lean_batch as LB
from PolyForge.trust import audits as AUD
dom = GraphDomain(); D.configure(dom)

CACHE = Path("/home/felix_gao/pf_production/v147_omega_cache.jsonl")
OUT = Path("/home/felix_gao/pf_production/v147_step3.json")
_cache = {}
if CACHE.exists():
    for ln in CACHE.read_text().splitlines():
        if ln.strip():
            o = json.loads(ln); _cache[o["k"]] = o["v"]
print(f"[init] loaded {len(_cache)} cached omega verdicts", flush=True)
_runner = LB.lake_runner(str(CC._LEAN_DIR), extra_args=["-D", "maxErrors=100000000"])
_cf = open(CACHE, "a")
STATE = {"unknown": 0, "batches": 0, "t0": time.time()}


def _qkey(base, goal):
    payload = json.dumps([sorted((sorted(c.items()), r, h) for (c, r, h) in base),
                          [sorted(goal[0].items()), goal[1], goal[2]]], sort_keys=True)
    return hashlib.sha256(payload.encode()).hexdigest()


def entail_many(queries, label=""):
    """queries: [(qkey, base, goal, vars)] -> {qkey: bool}. Cached; uncached run in
    batches of 400 with heartbeat; each result flushed to the cache immediately."""
    out, todo = {}, []
    for qk, base, goal, vs in queries:
        ck = _qkey(base, goal)
        if ck in _cache:
            out[qk] = _cache[ck]
        else:
            todo.append((qk, ck, base, goal, vs))
    for i in range(0, len(todo), 400):
        part = todo[i:i + 400]
        cases = [(qk, base, goal, vs) for (qk, ck, base, goal, vs) in part]
        dec, _, _ = CC.omega_decide_batch(cases)
        for (qk, ck, base, goal, vs) in part:
            v = bool(dec[qk]); out[qk] = v
            _cache[ck] = v
            _cf.write(json.dumps({"k": ck, "v": v}) + "\n")
        _cf.flush()
        STATE["batches"] += 1
        el = time.time() - STATE["t0"]
        print(f"[entail {label}] +{len(part)} ({i+len(part)}/{len(todo)} new) cache={len(_cache)} "
              f"batches={STATE['batches']} elapsed={el:.0f}s unknown={len(CC._UNKNOWN_LOG)}", flush=True)
    return out


final = G.load_records(G.RECORD)
archive = G.load_pruned_archive(G.RECORD)
views = [G._record_premise_view(d) for d in final]
vb = {v["id"]: v for v in views}

def base_of(props, numeric):
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    pset, inv, conds = CC.active_restricted_facts(props, params)
    return pset, [CC._ptuple(pr) for pr in numeric] + inv

def disp_fact(v):
    d = v["disp"]
    return ({x: int(k) for x, k in d["coeffs"].items() if int(k) != 0}, CC._norm(d["rel"]), int(d["rhs"]))

# ── 1. usability matrix (param-aware): usable[T][R] over the 319 records ──
print("[stage] usability matrix", flush=True)
bases = {}
uq = []
for T in views:
    pset, base = base_of(T["props"], T["numeric"]); bases[T["id"]] = (pset, base)
    tv = sorted({v for f in base for v in f[0]})
    for R in views:
        if R["id"] == T["id"] or not CC.props_dischargeable(R["props"], T["props"], pset):
            continue
        for j, pr in enumerate(R["numeric"]):
            g = CC._ptuple(pr); uq.append((f"U|{T['id']}|{R['id']}|{j}", base, g, sorted(set(tv) | set(g[0]))))
udec = entail_many(uq, "usable")
usable = {T["id"]: set() for T in views}
from collections import defaultdict
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

# ── 2. M1: inventory-entailed (step1) + entailed-by-usable-others (step2) ──
print("[stage] M1 entailments", flush=True)
def goal_of(v): c=v["canon"]; return ({x:int(k) for x,k in c["coeffs"].items() if int(k)!=0}, c["rel"], int(c["rhs"]))
invq=[]; recq=[]
for T in views:
    pset, base = bases[T["id"]]; g=goal_of(T); vs=sorted({v for f in base for v in f[0]}|set(g[0]))
    invq.append((f"INV|{T['id']}", base, g, vs))
    facts=list(base)+[disp_fact(vb[r]) for r in sorted(usable[T["id"]])]
    vs2=sorted({v for f in facts for v in f[0]}|set(g[0]))
    recq.append((f"REC|{T['id']}", facts, g, vs2))
invd=entail_many(invq,"inv"); recd=entail_many(recq,"rec")
inv_ent={T["id"] for T in views if invd[f"INV|{T['id']}"]}
rec_ent={T["id"] for T in views if recd[f"REC|{T['id']}"]}
redundant=[T["id"] for T in views if (T["id"] not in inv_ent) and (T["id"] in rec_ent)]

# ── 3. M2 both orders (only redundant are candidates; monotone) ──
def seq(order):
    present=set(order); cand=set(redundant); removed=[]
    for tid in order:
        if tid not in cand or tid not in present: continue
        avail=[r for r in usable[tid] if r in present and r!=tid]
        facts=list(bases[tid][1])+[disp_fact(vb[r]) for r in avail]; g=goal_of(vb[tid])
        vs=sorted({v for f in facts for v in f[0]}|set(g[0]))
        if entail_many([(f"M2|{tid}", facts, g, vs)],"m2")[f"M2|{tid}"]:
            present.discard(tid); removed.append(tid)
    return sorted(present,key=lambda x:int(x[1:])), removed
asc=sorted((v["id"] for v in views),key=lambda x:int(x[1:])); desc=list(reversed(asc))
print("[stage] M2 asc",flush=True); basis_asc,rem_asc=seq(asc)
print("[stage] M2 desc",flush=True); basis_desc,rem_desc=seq(desc)

# ── 4. C3: param-aware complete closure of final 319 vs archive ──
print("[stage] C3", flush=True)
c3q=[]; arch_by={}
for i,e in enumerate(archive):
    props=e["props"]; numeric=e["numeric"]; canon={"coeffs":{k:int(v) for k,v in e["canonical"]["coeffs"].items()},"rel":e["canonical"]["rel"],"rhs":int(e["canonical"]["rhs"])}
    pset,base=base_of(props,numeric)
    # usable final records for this archived prop
    us=[R for R in views if CC.props_dischargeable(R["props"],props,pset)]
    # need per-premise usability for these (cached omega)
    subq=[]
    for R in us:
        for j,pr in enumerate(R["numeric"]):
            g=CC._ptuple(pr); subq.append((f"CU|{i}|{R['id']}|{j}", base, g, sorted({v for f in base for v in f[0]}|set(g[0]))))
    arch_by[i]=(base,canon,us,subq,{"props":props})
# resolve archived-usability
alld=entail_many([q for i in arch_by for q in arch_by[i][3]],"c3usable")
c3q=[]
for i,(base,canon,us,subq,meta) in arch_by.items():
    pc=defaultdict(int); po=defaultdict(int)
    for (qk,b,g,v) in subq:
        _,ii,rid,j=qk.split("|"); pc[rid]+=1; po[rid]+=1 if alld[qk] else 0
    facts=list(base)
    for R in us:
        if not R["numeric"] or pc[R["id"]]==po[R["id"]]:
            facts.append(disp_fact(R))
    g=(canon["coeffs"],canon["rel"],canon["rhs"]) if False else ({k:int(v) for k,v in canon["coeffs"].items() if int(v)!=0},canon["rel"],int(canon["rhs"]))
    vs=sorted({v for f in facts for v in f[0]}|set(g[0]))
    c3q.append((f"C3|{i}", facts, g, vs))
c3d=entail_many(c3q,"c3")
c3_fail=[archive[i]["standard_form"] for i in arch_by if not c3d[f"C3|{i}"]]
c3_ent=sum(1 for i in arch_by if c3d[f"C3|{i}"])

# ── 5. graph-soundness (PolyForge.trust.audits, Python, atlas) on M usable pairs ──
print("[stage] graph soundness", flush=True)
import json as _j
pool=_j.load(open(G.DATA))["graphs"]; graphs=[(g,__import__("PolyForge.domains.graph.inventory",fromlist=["properties_of"]).properties_of(g)) for g in pool if g["n"]>=1]
INV=__import__("PolyForge.domains.graph.inventory",fromlist=["properties_of"])
def sat(view,g): return G._graph_matches(g[0],g[1],view["props"],view["numeric"])
pairs=[(vb[t],vb[r]) for t in usable for r in usable[t]]
gs=AUD.graph_soundness_violations(pairs, lambda t,r:True, graphs, sat)
gs_viol=[(t["id"],r["id"],g[0].get("atlas_index")) for (t,r,g) in gs]

# ── 6. monotonicity: restricted (bounded, param-aware) vs complete (this matrix) ──
print("[stage] monotonicity", flush=True)
G.clear_impl_cache()
mono=[]
for T in views:
    tv={"props":T["props"],"pset":bases[T["id"]][0],"params":{p["name"]:p.get("param") for p in T["props"] if "param" in p},"numeric":T["numeric"]}
    for R in views:
        if R["id"]==T["id"]: continue
        if G._premises_imply(tv,{"props":R["props"],"numeric":R["numeric"]}):
            if R["id"] not in usable[T["id"]]:
                mono.append((T["id"],R["id"]))

# ── diff vs v1.4.5 ──
OLD=json.load(open("PolyForge/domains/graph/analysis/v1.4.5/phase_mvc.json"))
old_m1=set(r["id"] for r in OLD["M1"]["records"]); new_m1=set(redundant)
old_c3=set(OLD["C3_complete_319"]["failures"]); new_c3=set(c3_fail)
out={"M1":{"count":len(redundant),"ids":sorted(new_m1,key=lambda x:int(x[1:])),"inv_entailed":len(inv_ent)},
     "M2":{"asc_basis":len(basis_asc),"asc_removed":rem_asc,"desc_basis":len(basis_desc),"desc_removed":rem_desc},
     "C3":{"entailed":c3_ent,"total":len(archive),"failures":c3_fail},
     "graph_soundness_violations":gs_viol,"monotonicity_violations":mono,
     "UNKNOWN":{"count":len(CC._UNKNOWN_LOG),"names":CC._UNKNOWN_LOG[:50]},
     "diff_vs_v145":{"M1_only_old":sorted(old_m1-new_m1),"M1_only_new":sorted(new_m1-old_m1),
        "M1_disagree":len(old_m1^new_m1),
        "C3_only_old":sorted(old_c3-new_c3),"C3_only_new":sorted(new_c3-old_c3),"C3_disagree":len(old_c3^new_c3),
        "M2_asc_basis_old":OLD["M2"]["ascending_remove_earlier_first"]["basis_size"],
        "M2_desc_basis_old":OLD["M2"]["descending"]["basis_size"],
        "per_judgment_compared":len(views)+len(archive),
        "per_judgment_disagree":len(old_m1^new_m1)+len(old_c3^new_c3)}}
OUT.write_text(json.dumps(out,indent=2))
_cf.close()
print("STEP3 DONE:", json.dumps({"M1":out["M1"]["count"],"M2":[out["M2"]["asc_basis"],out["M2"]["desc_basis"]],
      "C3":[c3_ent,len(archive)],"graph_viol":len(gs_viol),"mono_viol":len(mono),"UNKNOWN":out["UNKNOWN"]["count"],
      "M1_disagree":out["diff_vs_v145"]["M1_disagree"],"C3_disagree":out["diff_vs_v145"]["C3_disagree"]}),flush=True)
