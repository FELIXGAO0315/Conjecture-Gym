"""Analysis & audit tools (not the core verifier).
baseline, stratified_split — run-summary analyses / reproducible splits (used by tasks)
oracle_check              — trust oracle (reference proofs → reward 1; cheats → 0)
closure_validate, record_audit — audit harnesses (exercised by tests/)
The core verification code stays in env/: tasks, verifier, closure_complete."""
