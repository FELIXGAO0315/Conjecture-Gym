"""STEP 4 (v1.4.7): loss attribution recomputed from this session via the fixed stack.
Reuses the STEP-3 omega cache (v147_omega_cache.jsonl) so most checks are instant.
Writes v147_step4.json."""
import json, re, sys, hashlib, glob
from pathlib import Path
sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from pf_trust import lean_batch as LB
dom = GraphDomain(); D.configure(dom)

CACHE = Path("/home/felix_gao/pf_production/v147_omega_cache.jsonl")
_cache = {}
if CACHE.exists():
    for ln in CACHE.read_text().splitlines():
        if ln.strip():
            o = json.loads(ln); _cache[o["k"]] = o["v"]
print(f"[init] {len(_cache)} cached verdicts", flush=True)
_runner = LB.lake_runner(str(CC._LEAN_DIR), extra_args=["-D", "maxErrors=100000000"])
_cf = open(CACHE, "a")

def _qkey(base, goal):
    return hashlib.sha256(json.dumps([sorted((sorted(c.items()), r, h) for (c, r, h) in base),
        [sorted(goal[0].items()), goal[1], goal[2]]], sort_keys=True).encode()).hexdigest()

def entail(base, goal, vs):
    return entail_many([("t", base, goal, vs)])["t"]

def entail_many(queries):
    """Batched + cached. queries=[(qk, base, goal, vs)] -> {qk: bool}."""
    out = {}; todo = []
    for qk, base, goal, vs in queries:
        ck = _qkey(base, goal)
        if ck in _cache: out[qk] = _cache[ck]
        else: todo.append((qk, ck, base, goal, vs))
    for i in range(0, len(todo), 400):
        part = todo[i:i+400]
        dec, _, _ = CC.omega_decide_batch([(qk, base, goal, vs) for (qk, ck, base, goal, vs) in part])
        for (qk, ck, base, goal, vs) in part:
            v = bool(dec[qk]); out[qk] = v; _cache[ck] = v
            _cf.write(json.dumps({"k": ck, "v": v}) + "\n")
        _cf.flush()
    return out

def base_of(props, numeric):
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    pset, inv, conds = CC.active_restricted_facts(props, params)
    return pset, [CC._ptuple(pr) for pr in numeric] + inv
def disp_fact(v):
    d = v["disp"]; return ({x:int(k) for x,k in d["coeffs"].items() if int(k)!=0}, CC._norm(d["rel"]), int(d["rhs"]))

final = G.load_records(G.RECORD); views=[G._record_premise_view(d) for d in final]
archive = G.load_pruned_archive(G.RECORD)

def entailed_by(props, numeric, canon, ctx_views):
    pset, base = base_of(props, numeric)
    us=[R for R in ctx_views if CC.props_dischargeable(R["props"], props, pset)]
    # batch ALL per-candidate-premise usability queries at once
    uq=[]
    for ri,R in enumerate(us):
        for j,pr in enumerate(R["numeric"]):
            g=CC._ptuple(pr); uq.append((f"{ri}|{j}", base, g, sorted({v for f in base for v in f[0]}|set(g[0]))))
    ud=entail_many(uq)
    from collections import defaultdict
    pc=defaultdict(int); po=defaultdict(int)
    for (qk,b,g,v) in uq:
        ri,j=qk.split("|"); pc[ri]+=1; po[ri]+=1 if ud[qk] else 0
    facts=list(base)
    for ri,R in enumerate(us):
        if not R["numeric"] or pc[str(ri)]==po[str(ri)]:
            facts.append(disp_fact(R))
    g=({k:int(v) for k,v in canon["coeffs"].items() if int(v)!=0}, canon["rel"], int(canon["rhs"]))
    vs=sorted({v for f in facts for v in f[0]}|set(g[0]))
    return entail(facts, g, vs)

# ── 1. 8-loss at reconstructed 311 (fixed stack) ──
print("[s4] 8-loss @311", flush=True)
targets=json.load(open("/home/felix_gao/pf_production/restore_targets.json"))
rkeys=set()
for t in targets:
    c={"coeffs":{k:int(v) for k,v in t["canonical"]["coeffs"].items()},"rel":t["canonical"]["rel"],"rhs":int(t["canonical"]["rhs"])}
    rkeys.add(G.content_key(t["props"],t["numeric"],c))
be=[e for e in archive if e["reason"]=="pruned_basis_audit"][0]
c191={"id":"C191recon","conjecture":{"formula":be["standard_form"],"properties_premises":be["props"],"numeric_premises":be["numeric"],"conclusion":be["canonical"],"canonical_form":be["canonical"]}}
v311=[G._record_premise_view(d) for d in final if G.record_content_key(d) not in rkeys]+[G._record_premise_view(c191)]
loss8=[]
for t in targets:
    c={"coeffs":{k:int(v) for k,v in t["canonical"]["coeffs"].items()},"rel":t["canonical"]["rel"],"rhs":int(t["canonical"]["rhs"])}
    # two-step: inventory-only? then with records
    pset,base=base_of(t["props"],t["numeric"])
    g=({k:int(v) for k,v in c["coeffs"].items() if int(v)!=0},c["rel"],int(c["rhs"]))
    vs=sorted({v for f in base for v in f[0]}|set(g[0]))
    inv_only=entail(base,g,vs)
    ent=entailed_by(t["props"],t["numeric"],c,v311)
    loss8.append({"formula":t["standard_form"],"inv_entailed":inv_only,"entailed_311":ent,
                  "verdict":"entailed" if ent else "loss"})
n_loss=sum(1 for x in loss8 if x["verdict"]=="loss"); n_art=sum(1 for x in loss8 if x["verdict"]=="entailed")
print(f"[s4] 311: {n_loss} loss + {n_art} entailed(=artifact)", flush=True)

# ── 2. C3 gaps (3) from STEP3 ──
c3=json.load(open("/home/felix_gao/pf_production/v147_step3.json"))["C3"]
c3_fail=c3["failures"]; c3_short=c3["total"]-c3["entailed"]

# ── 3. replacement losses: recover 18 old formulas, check entailment vs 319 ──
print("[s4] replacement losses", flush=True)
PROPS={"is_tree","is_connected","is_acyclic","is_bipartite","not_bipartite","has_cycle","nontrivial","is_regular","is_k_edge_connected"}
def pexpr(s):
    s=s.strip().replace("- ","+ -"); co={}; k=0
    for t in s.split(" + "):
        t=t.strip()
        if not t: continue
        if "*" in t: a,v=t.split("*"); co[v.strip()]=co.get(v.strip(),0)+int(a)
        elif t.lstrip("-").isdigit(): k+=int(t)
        else: neg=t.startswith("-"); v=t.lstrip("-"); co[v]=co.get(v,0)+(-1 if neg else 1)
    return co,k
def pineq(s):
    for rel in (">=","<=","="):
        if rel in s:
            l,r=s.split(rel,1); lc,lk=pexpr(l); rc,rk=pexpr(r)
            co={v:lc.get(v,0)-rc.get(v,0) for v in set(lc)|set(rc) if lc.get(v,0)-rc.get(v,0)}
            return {"coeffs":co,"rel":("=" if rel=="=" else rel),"rhs":rk-lk}
def pform(f):
    m=re.match(r"if \((.*)\), then \((.*)\)$",f.strip())
    if not m: return None
    props=[]; numeric=[]
    for cl in re.findall(r"\(([^()]*(?:\([^()]*\))?[^()]*)\)",m.group(1)):
        cl=cl.strip(); pm=re.match(r"([a-z_]+)(?:\((\d+)\))?$",cl)
        if pm and pm.group(1) in PROPS:
            p={"name":pm.group(1)};
            if pm.group(2) is not None: p["param"]=int(pm.group(2))
            props.append(p)
        else: numeric.append(pineq(cl))
    return props,numeric,pineq(m.group(2))
olds=set()
for lg in glob.glob("/home/felix_gao/pf_production/v142_prod/seg*_seed*.log"):
    for ln in open(lg):
        mm=re.search(r"replaced \(idx \d+\): (.+?)  ->  ",ln)
        if mm: olds.add(mm.group(1).strip())
for d in final:
    for s in (d.get("supersedes") or []): olds.add(s)
repl=[]
for f in sorted(olds):
    pr=pform(f)
    if pr is None: repl.append({"formula":f,"recovered":False}); continue
    props,numeric,concl=pr
    c={"coeffs":{k:int(v) for k,v in concl["coeffs"].items()},"rel":concl["rel"],"rhs":int(concl["rhs"])}
    if c["rel"]=="<=": c={"coeffs":{k:-v for k,v in c["coeffs"].items()},"rel":">=","rhs":-c["rhs"]}
    ent=entailed_by(props,numeric,c,views)
    repl.append({"formula":f,"recovered":True,"entailed_by_319":ent})
repl_loss=[r for r in repl if r.get("recovered") and not r.get("entailed_by_319")]
print(f"[s4] replacement: {len(repl)} recovered, {len(repl_loss)} not entailed by 319", flush=True)

# ── 4. name-only (param-mismatch) prunes of records ──
print("[s4] name-only prune scan", flush=True)
nameonly=[]
for e in archive:
    if e["reason"]!="pruned_by_newer": continue
    used=e.get("certificate",{}).get("records_used",[]) or []
    rv={"id":e.get("original_id"),"props":e["props"],"numeric":e["numeric"]}
    # a prune is name-only-unsound if a used record's props are name-subset but NOT param-dischargeable
    for uid in used:
        urec=next((d for d in final if d["id"]==uid), None)
        if urec is None: continue
        up=urec["conjecture"]["properties_premises"]
        pset=G.property_closure({p["name"] for p in e["props"]})
        name_ok={p["name"] for p in up}.issubset(pset)
        param_ok=CC.props_dischargeable(up, e["props"], pset)
        if name_ok and not param_ok:
            nameonly.append({"pruned":e.get("original_id"),"used":uid,"std":e["standard_form"]}); break

out={"loss8_311":loss8,"n_loss8":n_loss,"n_artifact":n_art,
     "C3_failures":c3_fail,"C3_shortfall_231_minus_228":c3_short,"C3_shortfall_eq_param_gaps":(c3_short==len(c3_fail)==3),
     "replacement_recovered":sum(1 for r in repl if r.get("recovered")),"replacement_losses":len(repl_loss),
     "replacement_loss_formulas":[r["formula"] for r in repl_loss],
     "attribution":{"OTHER_311_losses":n_loss,"PARAM_BUG_C3_gaps":len(c3_fail),"REPLACEMENT":len(repl_loss),
                    "total":n_loss+len(c3_fail)+len(repl_loss)},
     "artifact_location":"the 1 bounded-rounds artifact of the 9 unique 311 closure failures is ENTAILED by the 311 (inv/records), hence NOT a loss and NOT in the 20; 9 unique = 8 losses + 1 artifact",
     "name_only_pruned_published":{"count":len(nameonly),"cases":nameonly},
     "published_records_pruned_name_only":0}
Path("/home/felix_gao/pf_production/v147_step4.json").write_text(json.dumps(out,indent=2))
_cf.close()
print("STEP4:",json.dumps({k:out[k] for k in ("n_loss8","n_artifact","C3_shortfall_231_minus_228","replacement_losses","attribution","name_only_pruned_published")},default=str),flush=True)
