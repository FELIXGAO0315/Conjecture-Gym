"""v1.5 PHASE B — adversarial hardening of PolyForge.engine.soundness (Python-logic tests).

Covers B1 (name collision / nonce namespacing), B2 (summary spoofing),
B3 (parser fuzz), B4 (mandatory canaries), B5 (split/bisection termination +
singleton→UNKNOWN), B7 (axiom whitelist), B8 (the trailing-tab regression).
B6 (timeouts, no orphans) lives in test_runner_timeout.py.

Real-toolchain versions of B1/B4/B7 are in test_hardening_real.py.
"""
import random

import pytest

from PolyForge.engine.soundness.lean_batch import (
    ALLOWED_AXIOMS, Goal, Rendered, Verdict, canary_name, parse_summary,
    render_batch, verify,
)
from PolyForge.engine.soundness.tests.fake_lean import make_runner

HEADER = "import Mathlib"
NONCE = "0123456789abcdef0123456789abcdef"


def _frame(nonce, rows):
    """Build a summary string with the given (name, status, axioms_field) rows."""
    body = "\n".join(f"{n}\t{s}\t{a}" for (n, s, a) in rows)
    return f"x.lean:9:0: info: PF_BEGIN_{nonce}\n{body}\nPF_END_{nonce}\n"


# ─────────────────────────── B1: name collision ─────────────────────────────
def test_b1_names_are_nonce_namespaced():
    # A goal named to collide with a Mathlib constant is declared under the nonce,
    # and the summary looks up the NONCE-namespaced name, never the bare one.
    r = render_batch(HEADER, [Goal("Nat", "(2 : Int) ≤ 1", "omega")], NONCE)
    assert f"theorem pf{NONCE}_Nat :" in r.source
    assert "theorem Nat :" not in r.source
    assert f"pf{NONCE}_Nat" in r.expected and "Nat" not in r.expected
    assert r.name_map[f"pf{NONCE}_Nat"] == "Nat"


def test_b1_bare_colliding_name_in_summary_is_rejected():
    # If something reported the BARE colliding name as PRESENT with empty axioms
    # (as a real Mathlib lemma would look), parse_summary rejects it: no nonce.
    rows = [("Nat", "PRESENT", ""),                     # spoofed real lemma, no nonce
            (canary_name("true", NONCE), "PRESENT", "propext")]
    assert parse_summary(_frame(NONCE, rows), NONCE, [r[0] for r in rows]) is None


def test_b1_collision_with_false_statement_is_not_proven():
    # End-to-end through the fake runner: a goal named "Nat" with a FALSE statement is
    # NOT_PROVEN (the nonce-namespaced declaration fails; the real Nat is never consulted).
    res = verify([Goal("Nat", "(2 : Int) ≤ 1", "omega")], HEADER, make_runner("ok"))
    assert res["Nat"].verdict is Verdict.NOT_PROVEN


# ─────────────────────────── B2: summary spoofing ───────────────────────────
def test_b2_fake_present_line_in_error_is_not_parsed():
    # An error message that contains a fake PRESENT line (outside the frame, no nonce)
    # must not be parsed; only the framed, nonce-bearing block counts.
    g = Goal("g", "(2 : Int) ≤ 1", "omega")   # false

    def spoof_runner(src, timeout):
        rc, out = make_runner("ok")(src, timeout)
        # inject a convincing but UNFRAMED fake proof line for g
        return rc, (f"error: note pf{NONCE}_g\tPRESENT\tpropext\n" + out)

    res = verify([g], HEADER, spoof_runner)
    assert res["g"].verdict is Verdict.NOT_PROVEN


def test_b2_duplicate_frame_is_untrusted():
    rows = [(canary_name("true", NONCE), "PRESENT", "propext")]
    one = _frame(NONCE, rows)
    assert parse_summary(one + one, NONCE, [rows[0][0]]) is None   # two frames


def test_b2_extra_and_duplicate_rows_untrusted():
    tname = f"pf{NONCE}_t"
    base = [(tname, "PRESENT", "propext")]
    # extra unexpected row
    extra = base + [(f"pf{NONCE}_sneaky", "PRESENT", "")]
    assert parse_summary(_frame(NONCE, extra), NONCE, [tname]) is None
    # duplicate row for the same name
    dup = base + [(tname, "PRESENT", "")]
    assert parse_summary(_frame(NONCE, dup), NONCE, [tname]) is None


# ─────────────────────────── B3: parser fuzz ────────────────────────────────
def _expected_verdict(status, axioms):
    if status == "MISSING":
        return Verdict.NOT_PROVEN
    return Verdict.PROVEN if set(axioms) <= ALLOWED_AXIOMS else Verdict.NOT_PROVEN


def test_b3_parser_fuzz():
    # {0,1,many axioms} x {PRESENT,ABSENT} x whitespace/CRLF/trailing-tab x unicode.
    rng = random.Random(0xC0FFEE)
    allowed = list(ALLOWED_AXIOMS)
    disallowed = ["sorryAx", "myCustomAxiom", "Nat.strongRecOn.ax"]
    unicode_bits = ["", "α", "Δ", "π", "ℤ", "₃"]
    for trial in range(400):
        n = rng.choice([0, 1, 2, 5])
        want = {}
        rows = []
        for i in range(n):
            uni = rng.choice(unicode_bits)
            name = f"pf{NONCE}_g{i}{uni}"
            status = rng.choice(["PRESENT", "MISSING"])
            k = rng.choice([0, 1, 3])
            pool = allowed + (disallowed if rng.random() < 0.5 else [])
            axioms = rng.sample(pool, min(k, len(pool))) if k else []
            want[name] = _expected_verdict(status, axioms)
            axfield = ",".join(axioms)
            line = f"{name}\t{status}\t{axfield}"
            # whitespace / CRLF / trailing-tab variants (line-level only). Leading
            # indentation is spaces (a leading TAB would be genuine corruption — an
            # empty first column — and parse_summary correctly fails closed on it).
            # The trailing-tab (empty-axioms) case is exercised whenever axioms == [].
            deco = rng.choice(["", "  "])         # leading spaces
            tail = rng.choice(["", "   ", "\r"])  # trailing ws / CR (not a new tab)
            rows.append(deco + line + tail)
        eol = rng.choice(["\n", "\r\n"])
        body = eol.join([f"PF_BEGIN_{NONCE}", *rows, f"PF_END_{NONCE}"]) + eol
        out = "x.lean:1:0: info: " + body
        got = parse_summary(out, NONCE, list(want))
        assert got is not None, (trial, repr(out))
        for name, wv in want.items():
            assert got[name].verdict is wv, (trial, name, got[name], wv)


# ─────────────────────────── B4: mandatory canaries ─────────────────────────
@pytest.mark.parametrize("bad,wrong_ax", [
    ("zero", "sorryAx"),       # zero-axiom canary misreported with a bad axiom
    ("stdax", None),           # standard-axioms canary misreported as MISSING
    ("true", "sorryAx"),
])
def test_b4_any_canary_misread_untrusts_batch(bad, wrong_ax):
    g = Goal("g", "(0 : Int) ≤ 1", "omega")   # genuinely provable

    def tamper_runner(src, timeout):
        rc, out = make_runner("ok")(src, timeout)
        cname = canary_name(bad, _extract_nonce(src))
        lines = out.splitlines()
        new = []
        for ln in lines:
            if ln.startswith(cname + "\t"):
                if wrong_ax is None:
                    new.append(f"{cname}\tMISSING\t")
                else:
                    new.append(f"{cname}\tPRESENT\t{wrong_ax}")
            else:
                new.append(ln)
        return rc, "\n".join(new)

    res = verify([g], HEADER, tamper_runner, max_batch=4)
    # the tampered canary makes every batch (and its singleton splits) untrusted
    assert res["g"].verdict is Verdict.UNKNOWN


def _extract_nonce(src):
    import re
    return re.search(r"PF_BEGIN_([0-9a-f]+)", src).group(1)


# ─────────────────────────── B5: split / bisection ──────────────────────────
def test_b5_always_untrusted_terminates_and_is_unknown():
    # An injected always-untrusted runner must (a) terminate and (b) yield UNKNOWN for
    # every goal — never PROVEN. Termination: verify() halves on distrust to singletons.
    def untrusted(src, timeout):
        return 1, "garbage with no trustworthy summary"

    gs = [Goal(f"g{i}", "(1 : Int) ≤ 2", "omega") for i in range(37)]
    res = verify(gs, HEADER, untrusted, max_batch=64)
    assert set(res) == {g.name for g in gs}
    assert all(r.verdict is Verdict.UNKNOWN for r in res.values())
    assert not any(r.verdict is Verdict.PROVEN for r in res.values())


def test_b5_bisection_isolates_one_bad_goal():
    # A runner that is only untrustworthy when a specific goal is present. Bisection must
    # isolate it (UNKNOWN) while still classifying the others.
    bad = "g13"

    def choosy(src, timeout):
        if f"pf" in src and f"_{bad} :" in src:
            return 1, "no summary (this chunk contains the poison goal)"
        return make_runner("ok")(src, timeout)

    gs = [Goal(f"g{i}", f"({i} : Int) ≤ {i + 1}", "omega") for i in range(20)]  # all true
    res = verify(gs, HEADER, choosy, max_batch=20)
    assert res[bad].verdict is Verdict.UNKNOWN
    others = [res[g.name].verdict for g in gs if g.name != bad]
    assert all(v is Verdict.PROVEN for v in others), others


# ─────────────────────────── B7: axiom whitelist ────────────────────────────
def test_b7_allowed_axiom_set_is_exact():
    assert ALLOWED_AXIOMS == frozenset({"propext", "Classical.choice", "Quot.sound"})


@pytest.mark.parametrize("axioms,verdict", [
    ("", Verdict.PROVEN),
    ("propext", Verdict.PROVEN),
    ("propext,Classical.choice,Quot.sound", Verdict.PROVEN),
    ("sorryAx", Verdict.NOT_PROVEN),
    ("propext,sorryAx", Verdict.NOT_PROVEN),
    ("myCustomAxiom", Verdict.NOT_PROVEN),
    ("Classical.choice,myCustomAxiom", Verdict.NOT_PROVEN),
])
def test_b7_disallowed_axioms_are_not_proven(axioms, verdict):
    name = f"pf{NONCE}_g"
    rows = [(name, "PRESENT", axioms)]
    got = parse_summary(_frame(NONCE, rows), NONCE, [name])
    assert got is not None
    assert got[name].verdict is verdict


# ─────────────────────────── B8: trailing-tab regression ────────────────────
def _buggy_parse(output, nonce, expected):
    """The v1.4.6 parser: strip() (which eats the trailing tab of a zero-axiom line)."""
    begin, end = f"PF_BEGIN_{nonce}", f"PF_END_{nonce}"
    if output.count(begin) != 1 or output.count(end) != 1:
        return None
    body = output.split(begin, 1)[1].split(end, 1)[0]
    rows = {}
    for raw in body.splitlines():
        line = raw.strip()                       # <-- THE BUG: strips the trailing tab too
        if not line:
            continue
        cols = line.split("\t")
        if len(cols) != 3 or cols[1] not in ("PRESENT", "MISSING"):
            return None                          # zero-axiom line drops to 2 cols -> None
        rows[cols[0]] = cols
    if set(rows) != set(expected):
        return None
    return rows


def test_b8_zero_axiom_line_breaks_old_parser_not_new():
    name = f"pf{NONCE}_g"
    rows = [(name, "PRESENT", "")]               # zero-axiom PROVEN -> trailing tab
    out = _frame(NONCE, rows)
    # new parser: handles it (PROVEN)
    good = parse_summary(out, NONCE, [name])
    assert good is not None and good[name].verdict is Verdict.PROVEN
    # reintroduced bug: drops the whole batch (returns None)
    assert _buggy_parse(out, NONCE, [name]) is None


def test_b8_canary_zero_would_break_every_batch_under_old_parser():
    # B4+B8: the zero-axiom canary forces the trailing-tab line into EVERY batch, so the
    # old parser would have dropped (untrusted) every batch — the fuzz/canary now catch it.
    gs = [Goal("g", "(0 : Int) ≤ 1", "omega")]
    r = render_batch(HEADER, gs, NONCE)
    _rc, out = make_runner("ok")(r.source, 10)
    assert parse_summary(out, NONCE, r.expected) is not None          # new: fine
    assert _buggy_parse(out, NONCE, r.expected) is None               # old: whole batch lost
