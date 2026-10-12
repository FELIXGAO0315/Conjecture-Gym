"""PolyForge task format (v1.3 §II).

A *task* is the unit the RL environment trains and evaluates on: one PolyForge
record, reshaped into a self-contained, verifier-ready object.  The reasoning /
filtering pipeline and the records themselves are not modified here — tasks are a
read-only projection of the record plus a few derived fields (a stable id, a
difficulty tier, a skeleton, a train/test split).

Field summary (see the README for the full contract):

* ``task_id``          ``<domain>-<12 hex>`` — sha256 of the domain and the
                       whitespace-normalised Lean statement (with the theorem
                       name replaced by a fixed placeholder, so the id depends
                       only on the mathematics, not the record number).
* ``domain``, ``source`` (record id + generator version, informational only).
* ``formula``, ``canonical_form``, ``natural_language``.
* ``lean_header``      import / open block (fixed, prepended by the verifier).
* ``lean_statement``   the theorem signature ending in ``:= by`` (no proof); the
                       theorem is renamed ``thm_<12 hex>`` so the name is stable.
* ``theorem_name``.
* ``reference_proof``  PolyForge's own proof (the part after ``by``).
* ``natural_language_proof`` the rendered (v1.3) proof steps.
* ``difficulty`` (easy/medium/hard), ``hardness``, ``depth_type``,
  ``proof_stats``, ``inventory_used``.
* ``skeleton``         premise skeleton (properties + constant-free premise
                       shapes) + canonical-conclusion variable set and direction.
* ``split``            ``train`` or ``test``.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, asdict, field
from pathlib import Path

from ..generator.generator import _steps_md

_ROOT = Path(__file__).resolve().parents[1]           # .../PolyForge


# ── domain registry ───────────────────────────────────────────────────────────
@dataclass(frozen=True)
class DomainConfig:
    name: str
    record_dir: Path
    lean_dir: Path
    # the command that loads the domain's Lean environment in the REPL once
    repl_preamble: str


DOMAINS = {
    "graph": DomainConfig(
        name="graph",
        record_dir=_ROOT / "domains" / "graph" / "record",
        lean_dir=_ROOT / "domains" / "graph" / "lean",
        repl_preamble="import Mathlib\nimport GraphLemmas\nopen SimpleGraph\nopen PolyForge.Graph",
    ),
}


def domain_config(domain: str) -> DomainConfig:
    if domain not in DOMAINS:
        raise ValueError(f"unknown / unsupported domain {domain!r}; "
                         f"supported: {sorted(DOMAINS)}")
    return DOMAINS[domain]


# ── Lean parsing & statement canonicalisation ─────────────────────────────────
_WS = re.compile(r"\s+")
_THM_RE = re.compile(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def _normalize_ws(s: str) -> str:
    return _WS.sub(" ", s).strip()


def parse_lean(text: str):
    """Split a record ``.lean`` file into (header, theorem_name, signature, proof).

    ``signature`` runs from ``theorem`` through the theorem's ``:= by`` (inclusive);
    ``proof`` is everything after it (dedented).  Relies on the record convention
    that the theorem body is introduced by ``:= by`` and signatures contain no
    ``:=`` — so the first ``:= by`` in the file is the theorem's."""
    m = _THM_RE.search(text)
    if not m:
        raise ValueError("no `theorem` declaration found")
    thm_start = m.start()
    name = m.group(1)
    header = text[:thm_start].rstrip()
    rest = text[thm_start:]
    by_idx = rest.find(":= by")
    if by_idx < 0:
        raise ValueError("no `:= by` found for the theorem")
    signature = rest[:by_idx + len(":= by")]
    proof = rest[by_idx + len(":= by"):]
    # dedent the proof body to a canonical 0-indent (the verifier re-indents by 2)
    proof = proof.strip("\n")
    lines = proof.split("\n")
    indents = [len(ln) - len(ln.lstrip()) for ln in lines if ln.strip()]
    common = min(indents) if indents else 0
    proof = "\n".join(ln[common:] if ln.strip() else "" for ln in lines).strip("\n")
    return header, name, signature, proof


def canonical_statement(signature: str) -> str:
    """Whitespace-normalised signature with the theorem name replaced by a fixed
    placeholder, so the task id depends only on the mathematics."""
    neutral = _THM_RE.sub("theorem __thm__", signature, count=1)
    return _normalize_ws(neutral)


def task_id_for(domain: str, signature: str) -> str:
    h = hashlib.sha256((domain + "\n" + canonical_statement(signature)).encode()).hexdigest()
    return f"{domain}-{h[:12]}"


def _rename_theorem(signature: str, new_name: str) -> str:
    return _THM_RE.sub(f"theorem {new_name}", signature, count=1)


# ── skeleton (v1.3 §II.7) ──────────────────────────────────────────────────────
def skeleton(record: dict) -> str:
    """A stable identifier that groups conjectures differing only in constants.

    Built from the premise skeleton (property names + each numeric premise's
    constant-free coefficient shape and relation) and the canonical-form
    conclusion's variable set and direction."""
    cj = record["conjecture"]
    props = sorted(p["name"] for p in cj.get("properties_premises", []))
    prem_shapes = sorted(
        [sorted([k, int(v)] for k, v in pr["coeffs"].items()), pr["rel"]]
        for pr in cj.get("numeric_premises", [])
    )
    canon = cj.get("canonical_form") or cj["conclusion"]
    concl_vars = sorted(k for k, v in canon["coeffs"].items() if int(v) != 0)
    sk = {
        "props": props,
        "premises": prem_shapes,
        "conclusion_vars": concl_vars,
        "conclusion_dir": canon["rel"],
    }
    return json.dumps(sk, sort_keys=True, separators=(",", ":"))


def skeleton_hash(sk: str) -> str:
    return hashlib.sha256(sk.encode()).hexdigest()


# ── difficulty tiers (v1.3 §II, hardness tertiles) ────────────────────────────
def difficulty_thresholds(hardness: list[float]) -> tuple[float, float]:
    """Return (t1, t2), the 1/3 and 2/3 quantiles of the hardness values, so that
    easy = h <= t1, medium = t1 < h <= t2, hard = h > t2."""
    xs = sorted(hardness)
    if not xs:
        return 0.0, 0.0

    def q(p):
        if len(xs) == 1:
            return xs[0]
        idx = p * (len(xs) - 1)
        lo = int(idx)
        frac = idx - lo
        hi = min(lo + 1, len(xs) - 1)
        return xs[lo] + frac * (xs[hi] - xs[lo])

    return q(1 / 3), q(2 / 3)


def difficulty_of(hardness: float, thresholds: tuple[float, float]) -> str:
    t1, t2 = thresholds
    if hardness <= t1:
        return "easy"
    if hardness <= t2:
        return "medium"
    return "hard"


_TIER_TEST_PROB = {"easy": 0.1, "medium": 0.2, "hard": 0.4}
_TIER_RANK = {"easy": 0, "medium": 1, "hard": 2}


# ── task construction ──────────────────────────────────────────────────────────
@dataclass
class Task:
    task_id: str
    domain: str
    source: dict
    formula: str
    canonical_form: str
    natural_language: str
    lean_header: str
    lean_statement: str
    theorem_name: str
    reference_proof: str
    natural_language_proof: str
    difficulty: str
    hardness: float
    depth_type: str
    proof_stats: dict
    inventory_used: list
    skeleton: str
    split: str = "unassigned"

    def to_dict(self) -> dict:
        return asdict(self)


def _render_nl_proof(record: dict) -> str:
    return "\n".join(_steps_md(record["proof"]["steps"], 0))


def _load_records(cfg: DomainConfig):
    out = []
    if not cfg.record_dir.exists():
        return out
    for d in sorted(cfg.record_dir.iterdir(),
                    key=lambda p: (int(p.name[1:]) if p.name[1:].isdigit() else 1 << 30, p.name)):
        jf = d / f"{d.name}.json"
        lf = d / f"{d.name}.lean"
        if jf.exists() and lf.exists():
            out.append((json.loads(jf.read_text()), lf.read_text()))
    return out


def build_tasks(domain: str, split_seed: int = 1337) -> list[Task]:
    """Build every task for ``domain`` from its records, assign difficulty tiers
    (hardness tertiles) and a reproducible skeleton-based train/test split.

    Raises on a task_id collision (two distinct statements hashing equal)."""
    cfg = domain_config(domain)
    records = _load_records(cfg)
    hardness = [float(r["hardness"]) for r, _ in records]
    thr = difficulty_thresholds(hardness)

    tasks: list[Task] = []
    seen: dict[str, str] = {}
    for record, lean_text in records:
        header, name, signature, proof = parse_lean(lean_text)
        tid = task_id_for(domain, signature)
        if tid in seen and seen[tid] != canonical_statement(signature):
            raise RuntimeError(f"task_id collision {tid}: {seen[tid]!r} vs "
                               f"{canonical_statement(signature)!r}")
        seen[tid] = canonical_statement(signature)
        thm_name = f"thm_{tid.split('-')[1]}"
        lean_statement = _rename_theorem(signature, thm_name)
        cj = record["conjecture"]
        tasks.append(Task(
            task_id=tid,
            domain=domain,
            source={"record": record["id"],
                    "generator_version": record["generator"]["version"]},
            formula=cj["formula"],
            canonical_form=cj.get("canonical_form", {}).get("text", cj["conclusion"]["text"]),
            natural_language=cj["natural_language"],
            lean_header=header,
            lean_statement=lean_statement,
            theorem_name=thm_name,
            reference_proof=proof,
            natural_language_proof=_render_nl_proof(record),
            difficulty=difficulty_of(float(record["hardness"]), thr),
            hardness=float(record["hardness"]),
            depth_type=record.get("depth_type", ""),
            proof_stats=record.get("proof_stats", {}),
            inventory_used=record.get("proof", {}).get("inventory_used", []),
            skeleton=skeleton(record),
        ))

    assign_splits(tasks, split_seed)
    return tasks


def assign_splits(tasks: list[Task], seed: int) -> None:
    """v1.3 §VI.2: group tasks by skeleton; a whole group goes to test with a
    probability set by its hardest tier (hard 0.4, medium 0.2, easy 0.1), decided
    by the skeleton hash so the split is reproducible and leak-free (same skeleton
    never straddles the split)."""
    groups: dict[str, list[Task]] = {}
    for t in tasks:
        groups.setdefault(t.skeleton, []).append(t)
    for sk, members in groups.items():
        hardest = max(members, key=lambda t: _TIER_RANK[t.difficulty]).difficulty
        prob = _TIER_TEST_PROB[hardest]
        h = hashlib.sha256(f"{seed}:{sk}".encode()).hexdigest()
        # map the hash to a uniform value in [0, 1)
        u = int(h[:16], 16) / float(1 << 64)
        split = "test" if u < prob else "train"
        for t in members:
            t.split = split


# ── jsonl IO ───────────────────────────────────────────────────────────────────
def dump_jsonl(tasks: list[Task], path: Path) -> None:
    with open(path, "w") as f:
        for t in tasks:
            f.write(json.dumps(t.to_dict(), ensure_ascii=False, sort_keys=True) + "\n")


def load_task_dicts(path: Path) -> list[dict]:
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out


def tasks_by_id(tasks) -> dict:
    out = {}
    for t in tasks:
        d = t.to_dict() if isinstance(t, Task) else t
        out[d["task_id"]] = d
    return out
