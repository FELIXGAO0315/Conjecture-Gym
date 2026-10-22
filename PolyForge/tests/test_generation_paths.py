"""v1.5 PHASE D — exercise every new generation-path rule end-to-end (scratch only).

Replacement (a safe replace / b new-doesn't-imply-old / c injected UNKNOWN / d crash),
parameter awareness (generator._premises_imply and _avail_for), and the discard logger.
Real-Lean replacement cases are skipped if the toolchain is unavailable.
"""
import copy
import json
import shutil
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
import sys
sys.path.insert(0, str(ROOT))

from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from PolyForge.env import discardlog
from PolyForge.env.replace_gate import replace_decision

dom = GraphDomain(); D.configure(dom)

LEAN_OK = shutil.which("lake") is not None and (CC._LEAN_DIR / "lean-toolchain").exists()
real_lean = pytest.mark.skipif(not LEAN_OK, reason="real Lean toolchain not available")

REAL_RECORD = ROOT / "PolyForge/domains/graph/record/C9/C9.json"


def _load_real():
    return json.loads(REAL_RECORD.read_text())


def _put_old(tmp_path, data):
    """Write a record to a scratch record_dir and point the domain at it."""
    rd = tmp_path / "record"
    (rd / data["id"]).mkdir(parents=True, exist_ok=True)
    (rd / data["id"] / f"{data['id']}.json").write_text(json.dumps(data))
    dom.record_dir = rd
    return rd


def P(name, param=None):
    return {"name": name} if param is None else {"name": name, "param": param}


def _view(props, numeric=None):
    pset = G.property_closure({p["name"] for p in props})
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    return {"id": None, "props": props, "pset": pset, "params": params, "numeric": numeric or []}


# ─────────────────────── replacement (a): safe replace ──────────────────────
@real_lean
def test_replacement_a_safe_replace_with_certificate(tmp_path):
    old = _load_real(); old["id"] = "OLD1"
    _put_old(tmp_path, old)
    new = copy.deepcopy(old); new["id"] = "NEW1"       # identical statement -> new entails old
    assert dom.may_replace("OLD1", new) is True
    # archive the replaced record and confirm a certified replaced_by entry is written
    dom.archive_replacement("OLD1", new)
    pruned = (dom.record_dir / "pruned.jsonl")
    entries = [json.loads(l) for l in pruned.read_text().splitlines() if l.strip()] if pruned.exists() else []
    repl = [e for e in entries if e.get("reason") == "replaced_by"]
    assert repl, "a safe replace must archive a replaced_by entry"
    assert repl[-1].get("replacer_key") or repl[-1].get("certificate"), "entry carries replacer key / certificate"


# ─────────────────── replacement (b): new does not imply old ────────────────
@real_lean
def test_replacement_b_new_weaker_keeps_both(tmp_path):
    old = _load_real(); old["id"] = "OLD2"
    _put_old(tmp_path, old)
    new = copy.deepcopy(old); new["id"] = "NEW2"
    # weaken the new record's conclusion (rhs 12 -> 8): it no longer implies the old
    for key in ("conclusion", "canonical_form"):
        new["conjecture"][key] = dict(new["conjecture"][key]); new["conjecture"][key]["rhs"] = 8
    assert dom.may_replace("OLD2", new) is False, "a weaker new must NOT replace the old (keep both)"


# ─────────────── replacement (c): injected UNKNOWN -> keep both ─────────────
def test_replacement_c_injected_unknown_keeps_both(tmp_path, monkeypatch):
    old = _load_real(); old["id"] = "OLD3"
    _put_old(tmp_path, old)
    new = copy.deepcopy(old); new["id"] = "NEW3"       # identical -> WOULD replace if PROVEN
    # simulate the omega checker returning UNKNOWN (maps to not-entailed): keep both
    monkeypatch.setattr(CC, "omega_decide_batch", lambda cases: ({n: False for (n, *_ ) in cases}, "", ""))
    assert dom.may_replace("OLD3", new) is False, "UNKNOWN must never replace (keep both)"


# ─────────────── replacement (d): crash inside may_replace -> keep both ─────
def test_replacement_d_crash_keeps_both():
    class Boom:
        def may_replace(self, old_id, new_data):
            raise RuntimeError("boom inside may_replace")
    discardlog.enable(capture_mem=True); discardlog.reset_mem()
    assert replace_decision(Boom(), "OLDX", {"id": "NEWX"}) is False
    recs = discardlog.records()
    assert any(r["reason"] == "may_replace_crash_keep_both" for r in recs)
    discardlog.enable(None)  # disable again


def test_replace_decision_missing_may_replace_defaults_allow():
    class NoGate:
        pass
    discardlog.enable(capture_mem=True); discardlog.reset_mem()
    assert replace_decision(NoGate(), "X", {}) is True       # legacy allow (hex unchanged)
    # v1.5 audit: the latent legacy-allow path is now OBSERVABLE, not silent
    assert any(r["reason"] == "no_may_replace_legacy_allow" for r in discardlog.records())
    discardlog.enable(None)


# ─────────────────────── parameter awareness ────────────────────────────────
def test_param_premises_imply_is_regular_exact():
    G.clear_impl_cache()
    assert G._premises_imply(_view([P("is_regular", 2)]), _view([P("is_regular", 3)])) is False
    assert G._premises_imply(_view([P("is_regular", 2)]), _view([P("is_regular", 2)])) is True


def test_param_premises_imply_k_edge_connected_monotone():
    G.clear_impl_cache()
    # k'=2 discharges k=1 (2 >= 1); k'=1 does NOT discharge k=2
    assert G._premises_imply(_view([P("is_k_edge_connected", 2)]),
                             _view([P("is_k_edge_connected", 1)])) is True
    assert G._premises_imply(_view([P("is_k_edge_connected", 1)]),
                             _view([P("is_k_edge_connected", 2)])) is False


def test_param_non_parametric_lattice_still_prunes():
    G.clear_impl_cache()
    # is_tree => is_connected, is_acyclic (lattice intact)
    assert G._premises_imply(_view([P("is_tree")]), _view([P("is_connected")])) is True
    assert G._premises_imply(_view([P("is_tree")]), _view([P("is_acyclic")])) is True
    # a regular-degree mismatch is not rescued by the lattice
    assert G._premises_imply(_view([P("is_tree")]), _view([P("is_regular", 3)])) is False


def test_param_avail_for_selects_dischargeable_records():
    # T is 3-edge-connected; candidate records require various properties.
    T = _view([P("is_k_edge_connected", 3)])
    cand = [
        {"id": "R_ok", "props": [P("is_k_edge_connected", 2)], "numeric": [],
         "pset": G.property_closure({"is_k_edge_connected"}), "params": {"is_k_edge_connected": 2},
         "disp": {"coeffs": {"m": 1}, "rel": ">=", "rhs": 0}},
        {"id": "R_bad", "props": [P("is_k_edge_connected", 4)], "numeric": [],
         "pset": G.property_closure({"is_k_edge_connected"}), "params": {"is_k_edge_connected": 4},
         "disp": {"coeffs": {"m": 1}, "rel": ">=", "rhs": 0}},
        {"id": "R_reg", "props": [P("is_regular", 3)], "numeric": [],
         "pset": G.property_closure({"is_regular"}), "params": {"is_regular": 3},
         "disp": {"coeffs": {"m": 1}, "rel": ">=", "rhs": 0}},
    ]
    avail_ids = {E["id"] for E in G._avail_for(T, cand)}
    assert "R_ok" in avail_ids               # 3-edge-conn discharges 2-edge-conn
    assert "R_bad" not in avail_ids          # 3 does NOT discharge 4
    assert "R_reg" not in avail_ids          # not regular -> is_regular(3) not dischargeable


# ─────────────────────── discard logging ────────────────────────────────────
def test_discard_logger_records_every_discard(tmp_path):
    log = tmp_path / "discards.jsonl"
    discardlog.enable(str(log), capture_mem=True); discardlog.reset_mem()
    discardlog.record("main_commit_check", "redundant_vs_record_main", {"hash": "abc"})
    discardlog.record("skeleton", "same_skeleton_worse", {"skeleton": "S", "incumbent": "C1"})
    discardlog.record("replace", "replace_blocked_kept_both", {"incumbent": "C2"})
    recs = discardlog.records()
    assert {r["reason"] for r in recs} == {
        "redundant_vs_record_main", "same_skeleton_worse", "replace_blocked_kept_both"}
    assert all("stage" in r and "inputs" in r for r in recs)
    on_disk = [json.loads(l) for l in log.read_text().splitlines() if l.strip()]
    assert len(on_disk) == 3
    discardlog.enable(None)


def test_discard_logger_is_noop_when_disabled():
    discardlog.enable(None); discardlog.reset_mem()
    discardlog.record("x", "y", {})          # must not raise, must not record
    assert discardlog.records() == []
