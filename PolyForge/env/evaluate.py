"""PolyForge pass@k evaluation (v1.3 §V).

Reads a ``predictions.jsonl`` (one object per line, ``{"task_id", "completions"}``
where ``completions`` is a list of model attempts), verifies every attempt, and
reports pass@1 and pass@k overall and broken down by difficulty tier and by
train/test split, plus the distribution of verifier statuses.

pass@k uses the standard unbiased estimator (Chen et al. 2021): for a task with
``n`` attempts of which ``c`` pass,

    pass@k = 1 - C(n-c, k) / C(n, k).
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

from .reward import extract_proof
from .verifier import Verifier


def pass_at_k(n: int, c: int, k: int) -> float:
    """Unbiased estimate of the probability that at least one of k samples (drawn
    without replacement from n attempts, c of which pass) is correct."""
    if k > n:
        k = n
    if n - c < k:
        return 1.0
    # 1 - C(n-c, k)/C(n, k), computed stably as a product
    prob_all_fail = 1.0
    for i in range(k):
        prob_all_fail *= (n - c - i) / (n - i)
    return 1.0 - prob_all_fail


def evaluate(predictions_path: Path, domain: str, nprocs: int = 1,
             k: int | None = None, verifier: Verifier | None = None, **vk) -> dict:
    preds = []
    with open(predictions_path) as f:
        for line in f:
            line = line.strip()
            if line:
                preds.append(json.loads(line))

    V = verifier or Verifier(domain, nprocs=nprocs, **vk)
    tasks = V.tasks()
    own = verifier is None

    # flatten every (task, attempt) into one verification batch
    flat = []            # (pred_index, status-if-no-proof or None, task_id, proof)
    for pi, p in enumerate(preds):
        for comp in p.get("completions", []):
            proof = extract_proof(comp or "")
            flat.append((pi, proof, p["task_id"]))

    items = [(tid, proof) for (_pi, proof, tid) in flat if proof is not None]
    results = V.verify_batch(items) if items else []
    if own:
        V.close()

    # stitch results back, injecting no_proof_found for empty extractions
    ri = 0
    per_task_pass = defaultdict(list)     # task_id -> list of bool
    status_counts = Counter()
    for (pi, proof, tid) in flat:
        if proof is None:
            status_counts["no_proof_found"] += 1
            per_task_pass[tid].append(False)
        else:
            res = results[ri]; ri += 1
            status_counts[res.status] += 1
            per_task_pass[tid].append(res.reward >= 1.0)

    # determine k = number of attempts (use the max seen if not given)
    attempts_per = {p["task_id"]: len(p.get("completions", [])) for p in preds}
    K = k or (max(attempts_per.values()) if attempts_per else 1)

    def bucket(filter_fn):
        p1, pk, m = [], [], 0
        for tid, passes in per_task_pass.items():
            t = tasks.get(tid)
            if t is None or not filter_fn(t):
                continue
            n = len(passes)
            c = sum(passes)
            p1.append(pass_at_k(n, c, 1))
            pk.append(pass_at_k(n, c, K))
            m += 1
        return {"n_tasks": m,
                "pass@1": round(sum(p1) / m, 4) if m else None,
                f"pass@{K}": round(sum(pk) / m, 4) if m else None}

    report = {
        "k": K,
        "n_predictions": len(preds),
        "overall": bucket(lambda t: True),
        "by_difficulty": {d: bucket(lambda t, d=d: t["difficulty"] == d)
                          for d in ("easy", "medium", "hard")},
        "by_split": {s: bucket(lambda t, s=s: t["split"] == s)
                     for s in ("train", "test")},
        "status_distribution": dict(status_counts),
    }
    return report


def _main(argv=None):
    ap = argparse.ArgumentParser(description="PolyForge pass@k evaluation")
    ap.add_argument("domain")
    ap.add_argument("predictions", help="predictions.jsonl")
    ap.add_argument("--nprocs", type=int, default=1)
    ap.add_argument("--k", type=int, default=None)
    args = ap.parse_args(argv)
    report = evaluate(Path(args.predictions), args.domain, nprocs=args.nprocs, k=args.k)
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    _main()
