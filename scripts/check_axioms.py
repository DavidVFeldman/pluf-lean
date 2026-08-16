#!/usr/bin/env python3
"""Axiom audit for the pluf-lean CI.

Reads the `lake build` log and verifies that every contract theorem's
`#print axioms` line is present and uses only whitelisted axioms; also scans
the Lean sources for forbidden tokens outside comments.

Exit code 0 iff everything passes. Run from the repository root:
    python3 scripts/check_axioms.py build.log
"""
import re
import sys
from pathlib import Path

WHITELIST = {"propext", "Classical.choice", "Quot.sound"}

CONTRACT_THEOREMS = [
    # Part A
    "PlufWO1.not_mem_union_of_not_mem",
    "PlufWO1.sigmaQ_of_partition_selectors",
    "PlufWO1.sigmaQ_of_partition_selectors\u2080",
    "PlufWO1.partition_selectors_of_sigmaQ",
    "PlufWO1.minima_mem_of_fodor",
    "PlufWO1.sigmaQ_of_fodor",
    "PlufWO1.exists_transversal_not_mem",
    # Part B
    "PlufWO1.constraintVec_apply",
    "PlufWO1.constraintVec_ne_zero",
    "PlufWO1.mem_block_iff",
    "PlufWO1.isClosed_block",
    "PlufWO1.inner_constraintVec_eq_zero_of_disjoint",
    "PlufWO1.mem_W_iff",
    "PlufWO1.thin",
    # Part C
    "PlufWO1.closure_span_inter_block",
    "PlufWO1.noblock",
    # WO-2, Part D
    "PlufWO2.countable_supp",
    "PlufWO2.coordCLM_apply",
    "PlufWO2.mem_block_iff",
    "PlufWO2.isClosed_block",
    "PlufWO2.evec_mem_block",
    # WO-2, Parts E and F
    "PlufWO2.exact_paving",
    "PlufWO2.exact_dichotomy",
    "PlufWO2.block_filter_decides",
]

FORBIDDEN = ["sorry", "admit", "native_decide"]

def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    src = re.sub(r"--.*", "", src)
    return src

def main(logpath: str) -> int:
    ok = True
    log = Path(logpath).read_text(encoding="utf-8")

    # 1. Every contract theorem has an axiom line within the whitelist.
    for thm in CONTRACT_THEOREMS:
        pat = re.compile(re.escape(f"'{thm}'") + r"\s+depends on axioms:\s*\[([^\]]*)\]")
        m = pat.search(log)
        if not m:
            print(f"FAIL missing axiom line for {thm}")
            ok = False
            continue
        axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
        bad = axioms - WHITELIST
        if bad:
            print(f"FAIL {thm} uses non-whitelisted axioms: {sorted(bad)}")
            ok = False
        else:
            print(f"OK   {thm}: {sorted(axioms)}")

    # 2. Nothing in the log mentions sorryAx (belt and braces).
    if "sorryAx" in log:
        print("FAIL build log mentions sorryAx")
        ok = False

    # 3. Source scan for forbidden tokens outside comments; bare `axiom`
    #    declarations are forbidden too.
    for f in sorted(Path("RequestProject").glob("*.lean")):
        s = strip_comments(f.read_text(encoding="utf-8"))
        for tok in FORBIDDEN:
            if re.search(r"\b" + tok + r"\b", s):
                print(f"FAIL forbidden token '{tok}' in {f}")
                ok = False
        if re.search(r"^\s*axiom\b", s, flags=re.M):
            print(f"FAIL axiom declaration in {f}")
            ok = False

    print("AUDIT " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "build.log"))
