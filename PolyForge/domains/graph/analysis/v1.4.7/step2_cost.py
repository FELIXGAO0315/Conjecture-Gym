import sys, time, json, secrets, tempfile, os; sys.path.insert(0,".")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from pf_trust import lean_batch as LB
dom=GraphDomain(); D.configure(dom)
LEAN="PolyForge/domains/graph/lean"; HDR=CC._OMEGA_HEADER
runner=LB.lake_runner(LEAN, extra_args=["-D","maxErrors=100000000"])

# build REAL usability-omega cases from the 319x319 workload
recs=G.load_records(G.RECORD); views=[G._record_premise_view(d) for d in recs]
cases=[]  # (facts, goal, vars) per (T,R,premise)
for T in views:
    params={p["name"]:p.get("param") for p in T["props"] if "param" in p}
    pset,base,conds=CC.active_restricted_facts(T["props"],params) if hasattr(CC,"active_restricted_facts") else (None,[],[])
    base=[CC._ptuple(pr) for pr in T["numeric"]]+base
    tvars=sorted({v for f in base for v in f[0]})
    for R in views:
        if R["id"]==T["id"] or not CC.props_dischargeable(R["props"],T["props"],pset): continue
        for pr in R["numeric"]:
            g=CC._ptuple(pr); cases.append((base,g,sorted(set(tvars)|set(g[0]))))
        if len(cases)>=2400: break
    if len(cases)>=2400: break
print(f"built {len(cases)} real usability-omega cases from the matrix workload",flush=True)

def time_batch(batch):
    goals=[LB.Goal(f"thm_{i}", CC._goal_statement(f,g,v), "intros; omega") for i,(f,g,v) in enumerate(batch)]
    tag=secrets.token_hex(8); src,exp=LB.render_batch(HDR,goals,tag)
    t0=time.time(); rc,out=LB._timed_group_run(["lake","env","lean","-D","maxErrors=100000000"]+[__import__("os")],cwd=LEAN,timeout=600) if False else (0,"")
    # proper run:
    fd,path=tempfile.mkstemp(suffix=".lean",prefix="pf_s2_",dir=LEAN); open(path,"w").write(src)
    t0=time.time(); rc,out=LB._timed_group_run(["lake","env","lean","-D","maxErrors=100000000",path],cwd=LEAN,timeout=600); dt=time.time()-t0
    os.remove(path)
    rows=LB.parse_summary(out,tag,exp)
    prov=sum(1 for g in goals if rows and rows[g.name].verdict is LB.Verdict.PROVEN) if rows else -1
    cap="maximum number of errors" in out
    return dt, prov, len(goals), (rows is not None), cap

# import baseline: header+summary+1 trivial goal
print("measuring import baseline (cold first)...",flush=True)
imp_dt,_,_,_,_=time_batch(cases[:1])
print(f"import+1goal baseline: {imp_dt:.1f}s (includes cold Mathlib on FIRST call)",flush=True)
res={"n_cases_built":len(cases),"import_baseline_s":round(imp_dt,1),"batches":[]}
for b in range(5):
    batch=cases[b*400:(b+1)*400]
    if not batch: break
    dt,prov,n,trusted,cap=time_batch(batch)
    elab=max(0.0,dt-imp_dt)
    row={"batch":b,"n_goals":n,"wall_s":round(dt,1),"import_est_s":round(imp_dt,1),
         "elaboration_est_s":round(elab,1),"true_proven":prov,"false":n-prov if prov>=0 else None,
         "trusted_single_pass":trusted,"maxErrors_cap_hit":cap,"bisection_reruns":0 if trusted else "split"}
    res["batches"].append(row)
    print(f"[batch {b}] {n} goals wall={dt:.1f}s elab~{elab:.1f}s true/false={prov}/{n-prov} trusted={trusted} cap={cap}",flush=True)
json.dump(res, open("/home/felix_gao/pf_production/v147_step2.json","w"),indent=2)
print("STEP2 DONE",flush=True)
