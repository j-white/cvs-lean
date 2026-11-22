"""Run every reproduction script and tabulate the paper's numbers against them.

Each script runs in its own process; its full output is saved to
out/<script>.txt.  Tab-separated lines '@@ claim paper reproduced status'
(see claims.py) are collected into one table.

Exit status is non-zero only if a script crashes.  A DIFFERS row is
information, not failure.  A failed assertion inside a script is reported
as a DIFFERS row, not as a crash.
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = ["staircase", "truncation", "two_atom"]


def main():
    os.makedirs(os.path.join(HERE, "out"), exist_ok=True)
    rows, timings, crashed = [], [], []
    for name in SCRIPTS:
        t0 = time.time()
        p = subprocess.run([sys.executable, f"{name}.py"], cwd=HERE,
                           capture_output=True, text=True)
        dt = time.time() - t0
        with open(os.path.join(HERE, "out", f"{name}.txt"), "w") as fh:
            fh.write(p.stdout)
            if p.stderr:
                fh.write("\n--- stderr ---\n" + p.stderr)
        got = [ln.split("\t")[1:] for ln in p.stdout.splitlines() if ln.startswith("@@\t")]
        for g in got:
            rows.append([name] + g)
        if p.returncode == 0:
            if not got:
                rows.append([name, f"{name}.py checks", "pass", "asserts pass", "MATCH"])
            state = "ok"
        elif "AssertionError" in p.stderr:
            last = p.stderr.strip().splitlines()[-1]
            rows.append([name, f"{name}.py assertion", "pass", last[:60], "DIFFERS"])
            state = "assert"
        else:
            rows.append([name, f"{name}.py", "-", "CRASH", "CRASH"])
            crashed.append(name)
            state = "CRASH"
        timings.append((name, dt, state))
        print(f"ran {name:<11} {dt:7.1f}s  {state}", flush=True)

    w = [max(len(r[i]) for r in rows) for i in range(5)]
    w = [min(x, 72) for x in w]
    hdr = ["script", "claim", "paper", "reproduced", "status"]
    line = "  ".join(h.ljust(x) for h, x in zip(hdr, w))
    print("\n" + line + "\n" + "-" * len(line))
    for r in rows:
        print("  ".join(c[:x].ljust(x) for c, x in zip(r, w)))
    n = {s: sum(1 for r in rows if r[4] == s) for s in ("MATCH", "DIFFERS", "CRASH")}
    print(f"\n{n['MATCH']} MATCH, {n['DIFFERS']} DIFFERS, {n['CRASH']} CRASH;"
          f" total {sum(t for _, t, _ in timings):.0f}s"
          f" (slowest: {max(timings, key=lambda t: t[1])[0]}"
          f" {max(t for _, t, _ in timings):.0f}s). Full output in out/.")
    sys.exit(1 if crashed else 0)


if __name__ == "__main__":
    main()
