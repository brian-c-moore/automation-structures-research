"""Shared oracle dispatcher.

Protocol: read one JSON object {"algo": str, "inputs": [ ... ]} from
stdin, write one JSON list of outputs (one per input, in order) to
stdout. One process per algorithm (batched).

The exact executable subset uses the hashes, symmetric, MAC, and KDF
modules. Import failure is fatal because a missing oracle invalidates the
comparison rather than reducing its scope silently.

Cryptography wire format: byte inputs and outputs are hex strings
(per `Value::Bytes` JSON encoding in `src/value.rs`). Each oracle
parses input hex with `bytes.fromhex(...)` and returns `.hex()`.
"""
import sys
import os
import json
from hashes import ORACLES as HASH_ORACLES
from symmetric import ORACLES as SYMMETRIC_ORACLES
from mac import ORACLES as MAC_ORACLES
from kdf import ORACLES as KDF_ORACLES

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

ORACLES = {
    **HASH_ORACLES,
    **SYMMETRIC_ORACLES,
    **MAC_ORACLES,
    **KDF_ORACLES,
}


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
