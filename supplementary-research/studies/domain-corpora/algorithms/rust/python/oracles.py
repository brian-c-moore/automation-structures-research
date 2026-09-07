"""Shared oracle dispatcher.

Protocol: read one JSON object {"algo": str, "inputs": [ ... ]} from
stdin, write one JSON list of outputs (one per input, in order) to
stdout. One process per algorithm (batched).

The eight named modules are mandatory. Import failure is fatal because a
missing oracle invalidates the advertised comparison set.
"""
import sys
import os
import json
import phase1
import phase2
import phase3
import phase4
import phase5
import phase6
import phase7
import phase8

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

ORACLES = {}
for _module in (phase1, phase2, phase3, phase4, phase5, phase6, phase7, phase8):
    ORACLES.update(_module.ORACLES)


def main():
    req = json.loads(sys.stdin.read())
    algo = req["algo"]
    fn = ORACLES.get(algo)
    if fn is None:
        sys.stderr.write("unknown algo: %s (have: %s)\n"
                         % (algo, sorted(ORACLES)))
        sys.exit(1)
    out = [fn(inp) for inp in req["inputs"]]
    sys.stdout.write(json.dumps(out))


if __name__ == "__main__":
    main()
