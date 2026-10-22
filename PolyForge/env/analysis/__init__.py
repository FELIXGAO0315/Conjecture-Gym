"""One-off / analysis & audit tools (NOT the core RL env).
baseline, stratified_split — run-summary analyses invoked by scripts/run_production.py
oracle_check              — trust oracle (reference proofs → reward 1; cheats → 0)
closure_validate, record_audit — audit harnesses (exercised by tests/)
The CORE RL environment stays in env/: tasks, verifier, reward, export, evaluate."""
