#!/usr/bin/env python3
"""PolyForge v1.4.3 §B: content-keyed certificate traceability.

Display ids (C1…) are contiguous labels and change on every renumber; a certificate
written at prune time references records by the id they *then* had, which a later
renumber may reassign.  This module makes every reference content-addressed.

  §B2 migrate      add the stable content ``key`` to every record JSON and every
                   pruned.jsonl entry; keep the original fields under ``orig``.
  §B3 resolve      map each historical display-id reference in a certificate to a key
                   by CERTIFICATE MATCHING: the referenced proposition must be one
                   whose displayed/canonical conclusion is the inequality the step
                   uses AND whose premises are usable under the pruned proposition's
                   premises, searched over (final record ∪ archive).  Reports each
                   reference as resolved-uniquely / ambiguous / unresolved.
  §B4 replay       verify each resolved certificate by CHECKING the recorded linear
                   combination + rounding steps arithmetically (not by re-deriving).

Usage:
  python -m PolyForge.env.trace_keys [--record DIR] [--apply] [--json OUT]
    (without --apply: dry-run report only; with --apply: writes keys into records
     and rewrites pruned.jsonl in place, preserving originals under ``orig``.)
"""
import json, re, sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G

dom = GraphDomain(); D.configure(dom)

_TOKEN = re.compile(r"([+-]?\s*\d+(?:/\d+)?)\s*(?:\*\s*([A-Za-z_][A-Za-z0-9_]*))?")


def _frac(s):
    return Fraction(s.replace(" ", ""))


def parse_form(text):
    """Parse ``"c1*v1 + c2*v2 + … + k REL rhs"`` into ``{coeffs, rel, rhs}`` with the
    LHS constant folded into rhs.  Coefficients and constants may be rationals (e.g.
    ``-28/3`` in a pre-rounding combination); values are ``Fraction``."""
    for rel in (">=", "<=", "==", "="):
        if rel in text:
            lhs, rhs = text.split(rel, 1)
            coeffs = {}; const = Fraction(0)
            for m in _TOKEN.finditer(lhs):
                c = _frac(m.group(1))
                if m.group(2):
                    coeffs[m.group(2)] = coeffs.get(m.group(2), Fraction(0)) + c
                else:
                    const += c                        # bare constant term
            return {"coeffs": coeffs,
                    "rel": (">=" if rel == ">" else "==" if rel == "=" else rel),
                    "rhs": _frac(rhs.strip()) - const}  # coeffs·x + const REL r -> coeffs·x REL r-const
    raise ValueError(f"no relation in {text!r}")


def _nf(coeffs, rel, rhs):
    items, rel2, const = G._norm_form(coeffs, rel, rhs)
    return (tuple(tuple(x) for x in items), rel2, const)   # hashable


# ── candidate index over final record ∪ archive ────────────────────────────────
# reasons for an archive entry that was once a COMMITTED record (so it can legitimately
# be referenced by a certificate); forward rejects (redundant_vs_record) never were.
_ONCE_COMMITTED = {"pruned_by_newer", "pruned_basis_audit"}


def _forms_from(props, extra_concls):
    """Normalised reference-forms from a set of conclusion dicts."""
    forms = set()
    for c in extra_concls:
        try:
            forms.add(_nf(c["coeffs"], c["rel"], c["rhs"]))
        except Exception:
            pass
    return forms


def build_index(final_records, archive_entries):
    """``norm_form -> [candidate]``.  A proposition is referenceable only if it was a
    committed record: the final records, plus archive entries once committed
    (``pruned_by_newer`` / ``pruned_basis_audit``).  Forward rejections
    (``redundant_vs_record``) were never records and are excluded."""
    idx = defaultdict(list)
    seen = set()

    def add(props, numeric, canon, concls, key, label):
        pset = G.property_closure({p["name"] for p in props})
        cand = {"key": key, "label": label, "props": props, "pset": pset,
                "numeric": numeric, "params": {p["name"]: p.get("param") for p in props if "param" in p}}
        for f in _forms_from(props, concls):
            idx[f].append(cand)

    for d in final_records:
        props, numeric, canon = G._record_props_canon(d)
        params = {p["name"]: p.get("param") for p in props if "param" in p}
        concls = [canon, d["conjecture"]["conclusion"]]          # canonical + stored display
        try:
            concls.append(G.display_form(canon, props, params))
        except Exception:
            pass
        add(props, numeric, canon, concls, G.record_content_key(d), d["id"])
    for e in archive_entries:
        if e.get("reason") not in _ONCE_COMMITTED:
            continue
        props = e["props"]; numeric = e["numeric"]; canon = e["canonical"]
        key = e.get("key") or G.content_key(props, numeric, canon)
        if key in seen:
            continue
        seen.add(key)
        params = {p["name"]: p.get("param") for p in props if "param" in p}
        concls = [canon]
        try:
            concls.append(G.display_form(canon, props, params))
        except Exception:
            pass
        add(props, numeric, canon, concls, key, f"archive:{e.get('original_id')}")
    return idx


def _usable_under(entry_props, entry_numeric, cand):
    """True if ``cand``'s premises are usable under the pruned entry's premises
    (restricted criterion), matching ``_avail_for``."""
    epset = G.property_closure({p["name"] for p in entry_props})
    if not {p["name"] for p in cand["props"]}.issubset(epset):
        return False
    D.set_lemmas({})
    G.DED.set_active_inventory(epset, {p["name"]: p.get("param") for p in entry_props if "param" in p})
    with G._restricted_inventory():
        return all(G._restricted_entails(entry_numeric, pr) for pr in cand["numeric"])


# ── §B3 resolve ────────────────────────────────────────────────────────────────
def resolve_entry(entry, idx):
    """Resolve every ``rule=='record'`` step id in ``entry``'s certificate to a key.
    Returns ``(resolutions, status)`` where ``resolutions`` maps the display id to a
    dict {key, candidates, kind} and ``kind`` ∈ {unique, ambiguous, unresolved}."""
    out = {}
    for s in entry["certificate"]["steps"]:
        if s.get("rule") != "record":
            continue
        rid = s.get("id")
        f = _nf(**parse_form(s["text"]))
        cands = idx.get(f, [])
        # disambiguate by usability under the pruned entry's premises
        usable = [c for c in cands if _usable_under(entry["props"], entry["numeric"], c)]
        pool = usable if usable else cands
        keys = sorted({c["key"] for c in pool})
        if len(keys) == 1:
            kind = "unique"; key = keys[0]
        elif len(keys) == 0:
            kind = "unresolved"; key = None
        else:
            kind = "ambiguous"; key = None
        out[rid] = {"key": key, "kind": kind, "form_text": s["text"],
                    "candidate_keys": keys, "candidate_labels": sorted({c["label"] for c in pool})}
    return out


# ── §B4 replay: check the recorded combination + rounding arithmetically ─────────
def _as_ge(coeffs, rel, rhs):
    """Return (coeffs_dict, const) for the ``coeffs·x + const >= 0`` form (== kept as
    two >=); used to evaluate a recorded linear combination exactly."""
    c = {v: Fraction(x) for v, x in coeffs.items()}
    k = Fraction(-rhs)
    if rel == "<=":
        return ({v: -x for v, x in c.items()}, -k)
    return (c, k)


def replay_certificate(entry, resolutions, idx_by_key):
    """§B4: replay the certificate steps. Returns (ok, detail).

    Atom facts (premise/record/inventory/conditional/assumption/lemma) are parsed to
    ``coeffs·x + const >= 0`` forms; each ``linarith`` step's recorded multipliers are
    applied to the atom facts gathered since the last derived step, and the exact sum
    must equal the step's recorded form; each ``rounding`` step must floor the previous
    form's constant.  The final derived form must entail the entry's canonical
    conclusion."""
    from itertools import combinations, permutations
    pool = []           # (coeffs, const, rel) every atom AND every derived result so far
    derived = None      # (coeffs, const) last derived
    for s in entry["certificate"]["steps"]:
        rule = s.get("rule")
        if rule in ("premise", "record", "inventory", "conditional", "assumption", "lemma"):
            pf = parse_form(s["text"])
            c, k = _as_ge(pf["coeffs"], pf["rel"], pf["rhs"])
            pool.append((c, k, pf["rel"]))
        elif rule == "linarith":
            mults = [Fraction(m) for m in s.get("mults", [])]
            tf = parse_form(s["text"]); tg, tk = _as_ge(tf["coeffs"], tf["rel"], tf["rhs"])
            # the recorded mults are GIVEN; search only which pool facts they apply to
            # (the flat trace loses the dep→mult mapping for multi-combination DAGs).
            match = _match_combination(mults, pool, tg, tk)
            if match is None:
                return False, f"combination != recorded text ({s['text']})"
            derived = (tg, tk); pool.append((tg, tk, ">="))
        elif rule == "rounding":
            if derived is None and pool:
                derived = pool[-1][:2]
            c, k = derived
            from math import floor
            prim = D._primitive({v: x for v, x in c.items() if x != 0}, Fraction(k))
            if prim is None:
                return False, "rounding on empty form"
            ic, kc = prim
            fk = Fraction(floor(kc))
            tf = parse_form(s["text"])
            if not _same_form(ic, fk, *_as_ge(tf["coeffs"], tf["rel"], tf["rhs"])):
                return False, f"rounding != recorded text ({s['text']})"
            derived = (ic, fk); pool.append((ic, fk, ">="))
    if derived is None:
        if len(pool) == 1:
            derived = pool[-1][:2]
        else:
            return False, "no derived conclusion"
    canon = entry["canonical"]
    gc, gk = _as_ge(canon["coeffs"], canon["rel"], canon["rhs"])
    return (_entails_form(derived, (gc, gk)), "ok")


def _match_combination(mults, pool, tg, tk):
    """Is there an assignment of the GIVEN multipliers ``mults`` to a size-``len(mults)``
    subset of ``pool`` (facts) whose exact linear combination equals the recorded target
    form ``(tg, tk)``?  Multipliers on a ``>=`` fact must be non-negative; an ``==`` fact
    may take any sign.  Returns the matching index tuple or None.  (A bounded check of
    the recorded certificate, not a search for multipliers.)"""
    from itertools import combinations, permutations
    k = len(mults)
    if k == 0 or k > len(pool):
        return None
    for idxs in combinations(range(len(pool)), k):
        facts = [pool[i] for i in idxs]
        for perm in set(permutations(range(k))):
            ok = True
            combo = {}; const = Fraction(0)
            for mi, fi in enumerate(perm):
                m = mults[mi]; (c, kk, rel) = facts[fi]
                if m < 0 and rel != "==":
                    ok = False; break
                for v, x in c.items():
                    combo[v] = combo.get(v, Fraction(0)) + m * x
                const += m * kk
            if ok and _same_form(combo, const, tg, tk):
                return idxs
    return None


def _same_form(c1, k1, c2, k2):
    """Exact equality of two ``coeffs·x + const >= 0`` forms up to a positive scale
    (zero coefficients are ignored)."""
    p1 = D._primitive({v: Fraction(x) for v, x in c1.items() if x != 0}, Fraction(k1))
    p2 = D._primitive({v: Fraction(x) for v, x in c2.items() if x != 0}, Fraction(k2))
    if p1 is None or p2 is None:
        return p1 == p2
    (ic1, kc1), (ic2, kc2) = p1, p2
    return (sorted((v, int(x)) for v, x in ic1.items()) == sorted((v, int(x)) for v, x in ic2.items())
            and kc1 == kc2)


def _entails_form(derived, goal):
    """Does ``derived`` (coeffs·x+const>=0) entail ``goal`` (same shape)?  True iff the
    variable parts are equal (up to positive scale) and derived's bound is at least as
    strong.  (The certificate's final combination should reproduce the goal exactly.)"""
    c1, k1 = derived; c2, k2 = goal
    p1 = D._primitive({v: Fraction(x) for v, x in c1.items() if x != 0}, Fraction(k1))
    p2 = D._primitive({v: Fraction(x) for v, x in c2.items() if x != 0}, Fraction(k2))
    if p1 is None or p2 is None:
        return p1 == p2
    (ic1, kc1), (ic2, kc2) = p1, p2
    if sorted((v, int(x)) for v, x in ic1.items()) != sorted((v, int(x)) for v, x in ic2.items()):
        return False
    # form is ``coeffs·x + const >= 0`` ⟺ ``coeffs·x >= -const``; a smaller const is a
    # stronger bound, so derived entails goal iff derived's const <= goal's const.
    return kc1 <= kc2


# ── driver ───────────────────────────────────────────────────────────────────
def run(record_dir, apply=False, jout=None):
    record_dir = Path(record_dir)
    final = G.load_records(record_dir)
    archive = G.load_pruned_archive(record_dir)
    idx = build_index(final, archive)
    idx_by_key = {}
    for cands in idx.values():
        for c in cands:
            idx_by_key[c["key"]] = c

    n_refs = n_unique = n_amb = n_unres = 0
    n_replay_ok = n_replay_fail = 0
    ambiguous_cases = []; unresolved_cases = []; replay_fail = []
    resolved_archive = []
    for e in archive:
        res = resolve_entry(e, idx)
        for rid, info in res.items():
            n_refs += 1
            if info["kind"] == "unique":
                n_unique += 1
            elif info["kind"] == "ambiguous":
                n_amb += 1
                ambiguous_cases.append({"entry": e.get("original_id"), "ref_id": rid, **info})
            else:
                n_unres += 1
                unresolved_cases.append({"entry": e.get("original_id"), "ref_id": rid, **info})
        ok, detail = replay_certificate(e, res, idx_by_key)
        if ok:
            n_replay_ok += 1
        else:
            n_replay_fail += 1
            replay_fail.append({"entry": e.get("original_id"), "standard_form": e.get("standard_form"),
                                "detail": detail})
        # build the resolved archive entry (key + resolved refs; originals under orig)
        e2 = dict(e)
        e2["key"] = e.get("key") or G.content_key(e["props"], e["numeric"], e["canonical"])
        steps2 = []
        for s in e["certificate"]["steps"]:
            s2 = dict(s)
            if s.get("rule") == "record":
                info = res.get(s.get("id"), {})
                s2["key"] = info.get("key")
                s2["resolution"] = info.get("kind")
            steps2.append(s2)
        used_keys = []
        for uid in e["certificate"].get("records_used", []):
            info = res.get(uid)
            used_keys.append(info.get("key") if info else None)
        e2["certificate"] = dict(e["certificate"])
        e2["certificate"]["steps"] = steps2
        e2["certificate"]["records_used_keys"] = used_keys
        e2["replay_ok"] = ok
        e2["orig"] = {"original_id": e.get("original_id"),
                      "records_used": e["certificate"].get("records_used")}
        resolved_archive.append(e2)

    summary = {
        "n_records": len(final), "n_archive": len(archive),
        "n_references": n_refs, "resolved_unique": n_unique,
        "ambiguous": n_amb, "unresolved": n_unres,
        "replay_ok": n_replay_ok, "replay_fail": n_replay_fail,
        "ambiguous_cases": ambiguous_cases, "unresolved_cases": unresolved_cases,
        "replay_failures": replay_fail,
    }
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ("ambiguous_cases", "unresolved_cases", "replay_failures")}, indent=2))
    if ambiguous_cases:
        print(f"\n{len(ambiguous_cases)} AMBIGUOUS references:")
        for a in ambiguous_cases:
            print(f"  entry {a['entry']} ref {a['ref_id']} '{a['form_text']}' -> {a['candidate_labels']}")
    if unresolved_cases:
        print(f"\n{len(unresolved_cases)} UNRESOLVED references:")
        for a in unresolved_cases:
            print(f"  entry {a['entry']} ref {a['ref_id']} '{a['form_text']}'")
    if replay_fail:
        print(f"\n{len(replay_fail)} REPLAY FAILURES:")
        for a in replay_fail[:40]:
            print(f"  entry {a['entry']} '{a['standard_form']}': {a['detail']}")

    if jout:
        Path(jout).write_text(json.dumps(summary, indent=2))
        print(f"\nwrote {jout}")

    if apply:
        _apply(record_dir, final, resolved_archive)
    return summary


def _apply(record_dir, final, resolved_archive):
    """Write keys into record JSONs (adds ``key`` + ``provenance_keys``; originals kept
    implicitly — only new fields added) and rewrite pruned.jsonl with resolved refs."""
    for d in final:
        jf = record_dir / d["id"] / f"{d['id']}.json"
        data = json.loads(jf.read_text())
        props, numeric, canon = G._record_props_canon(data)
        key = G.content_key(props, numeric, canon)
        promoted = data.get("promoted_from")
        new = {}
        for k, v in data.items():
            new[k] = v
            if k == "id":                       # insert key/provenance right after id
                new["key"] = key
                new["provenance_keys"] = {
                    "self": key,
                    "instance_of": data.get("instance_of"),
                    "promoted_from": (G.content_key(props, numeric, promoted) if promoted else None),
                }
        jf.write_text(json.dumps(new, indent=2, ensure_ascii=False))
    with open(record_dir / "pruned.jsonl", "w") as f:
        for e in resolved_archive:
            f.write(json.dumps(e, ensure_ascii=False) + "\n")
    print(f"applied: keys written to {len(final)} records and {len(resolved_archive)} archive entries")


def _main(argv):
    rec = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record")
    if "--record" in argv:
        rec = Path(argv[argv.index("--record") + 1])
    jout = argv[argv.index("--json") + 1] if "--json" in argv else None
    run(rec, apply="--apply" in argv, jout=jout)


if __name__ == "__main__":
    _main(sys.argv[1:])
