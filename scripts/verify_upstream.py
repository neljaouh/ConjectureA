#!/usr/bin/env python3
"""Check that every vendored upstream Lean file is byte-identical to the
version recorded in the upstream source manifests (UPSTREAM/M1, UPSTREAM/M2),
and list the files that are original to this repository.

Exit status 0 iff every vendored file matches a manifest entry.
"""
import hashlib, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def manifest_hashes():
    h = {}
    for pkg in ("M1", "M2"):
        with open(os.path.join(ROOT, "UPSTREAM", pkg, "source-manifest.json")) as f:
            m = json.load(f)
            # M1 lists its files under "source_files", M2 under "files".
            for e in m.get("source_files", []) + m.get("files", []):
                h.setdefault(e["path"], (e["sha256"], pkg))
    return h

def sha256(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

def main():
    expected = manifest_hashes()
    ours, verified, bad = [], {"M1": 0, "M2": 0}, []
    for dp, dn, fn in os.walk(ROOT):
        dn[:] = [d for d in dn if d not in (".lake", ".git", "UPSTREAM")]
        for name in fn:
            if not name.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dp, name), ROOT)
            if rel in expected:
                want, pkg = expected[rel]
                if sha256(os.path.join(ROOT, rel)) == want:
                    verified[pkg] += 1
                else:
                    bad.append(rel)
            else:
                ours.append(rel)
    print(f"upstream files verified against manifests: M1={verified['M1']} M2={verified['M2']}")
    for b in bad:
        print(f"MISMATCH {b}")
    print(f"files original to this repository: {len(ours)}")
    for o in sorted(ours):
        print(f"  {o}")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
