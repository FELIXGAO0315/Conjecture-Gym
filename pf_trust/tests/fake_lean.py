"""A simulated Lean front end for testing the Python logic only.

It understands goals of the form `(a : Int) ≤ b` proved by `omega`, adds failed
theorems to the environment with sorryAx (Lean's error recovery), and can
simulate the maxErrors failure modes. It does NOT test real Lean behaviour;
`lean_batch.selftest` does that against the real toolchain.
"""
import re

THM = re.compile(r"^theorem (\S+) : \((-?\d+) : Int\) ≤ (-?\d+) := by", re.M)
NAMES = re.compile(r"let names : List Name := \[(.*?)\]")
BEGIN = re.compile(r'"(PF_BEGIN_[0-9a-f]+)"')
END = re.compile(r'"(PF_END_[0-9a-f]+)"')


def make_runner(mode="ok", max_errors=100):
    """mode: 'ok' | 'truncate' (stop reporting errors after max_errors, keep going)
             | 'abort' (stop processing after max_errors errors) | 'broken_summary'"""
    def run(src, timeout):
        env, out, n_err = {}, [], 0
        for m in THM.finditer(src):
            name, a, b = m.group(1), int(m.group(2)), int(m.group(3))
            ok = a <= b
            env[name] = ["propext"] if ok else ["sorryAx"]
            if not ok:
                n_err += 1
                if n_err <= max_errors or mode == "ok":
                    out.append(f"f.lean:1:0: error: omega could not prove the goal ({name})")
                elif mode == "abort":
                    return 1, "\n".join(out)
        if mode == "broken_summary":
            out.append("f.lean:9:0: error: unknown identifier 'collectAxioms'")
            return 1, "\n".join(out)
        names = [n.strip().lstrip("`") for n in NAMES.search(src).group(1).split(",")]
        lines = []
        for n in names:
            if n in env:
                lines.append(f"{n}\tPRESENT\t{','.join(env[n])}")
            else:
                lines.append(f"{n}\tMISSING\t")
        begin, end = BEGIN.search(src).group(1), END.search(src).group(1)
        out.append("f.lean:99:0: info: " + "\n".join([begin, *lines, end]))
        return (1 if n_err else 0), "\n".join(out)
    return run


def old_method(src, output):
    """The v1.4.4 decision rule: proven iff no error mentions the goal."""
    return {m.group(1): f"({m.group(1)})" not in output for m in THM.finditer(src)}
