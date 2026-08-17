# Work Order WO-9 — pluf project (Feldman–Wilce)

**The harvest commission.** WO-7a proved eleven probes and closed target (d);
this work order converts that probe material into a contracted, stable API that
WO-10 through WO-15 will be written against. Estimated by the census at ~0.5
commission.

**Ground truth:** this tarball (`pluf-wo9.tar.gz`). Contract: `PlufWO9.lean`.
References: `REPORT-WO7a.md` (included) is the census this commission harvests;
`paper1.pdf` and `paper2.pdf` are included for the statements of Paper I
Proposition 2.3 and Paper II Proposition 6.1.

**Base:** the WO-7a artifact (149 theorems; CI runs #1–#8; full project under
`base/`). `PlufWO9.lean` imports `RequestProject.PlufWO7a`.
**`PlufWO7a.lean` is the census record: do not edit or delete it.** All prior
theorems must remain green.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## A different shape of commission

Most items here already have proofs in `PlufWO7a.lean`. What is being
commissioned is not the mathematics but the **interface**: stable names,
minimal hypotheses, docstrings saying what each item is for, and statements
shaped for the consumers named below. Several contract entries are therefore
written as `True`-valued placeholders: for each, **replace the placeholder
with the real statement, prove it, and report the signature chosen.** The
signature is the deliverable.

Consumers to design against:
- **B/C** (essential spectrum; approximate-eigenvector substitute) → WO-13,
  WO-14 (Paper I §5: ampleness, escape, the blocking lemma).
- **D** (general `HilbertBasis` blocks) → WO-10 (Paper II Prop 6.1) and
  WO-12 (Paper II Thm 5.4, which enumerates *all* bases).
- **E** (ω₁ combinator) → WO-12 and WO-13.

Where a shape choice is genuinely open, prefer the one that keeps the caller's
side short, and report the alternative you rejected.

## Protocol (binding; as WO-1–WO-8)

Census first. Report-rather-than-repair with the codified license. No
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per contract theorem
(including the items whose statements you supply); whitelist `propext`,
`Classical.choice`, `Quot.sound`. CH is a hypothesis, never an axiom.
Partial order if needed: A → D → E → B → C.

## Item notes

**Part A (target (d), paper-facing).** A1 drops the oddness hypothesis the
probe retained as unused. A2 asks for the honest packaging of the two regimes
— the triple argument for `PlufWO1.H` (WO-6) and the principality argument in
finite dimension — as one statement or two named corollaries; report which.
The invitation to generalize the triple to arbitrary orthonormal bases (giving
non-separable infinite-dimensional spaces) is optional: prove it if cheap,
report if not, and do not claim it otherwise.

**Part B.** Re-site `essSpec` as the stable name. B2's statement is
deliberately left as a placeholder because the census found it needs weaker
hypotheses than the paper's argument uses: state it with the minimal
hypotheses actually required and say what they are.

**Part C.** The most important interface decision in the commission. C2's
tolerance clause will be the hypothesis shape of every ampleness and escape
lemma in WO-13/WO-14, so its form matters more than its strength. Choose the
form the proofs will want and justify the choice in the report.

**Part D.** D1's `blockB` supersedes the standard-basis block for
basis-relative work; D2's agreement lemma is what lets the existing 149
theorems transfer without restatement — if only a bridging isometry is
available rather than definitional agreement, supply the isometry and report,
since WO-12 will need to move results across it. D4 is the corrected Q2 **and
must not be generalized**: the arbitrary-index form is false and the census
formalized the counterexample.

**Part E.** E1 hides the universe lifting inside; E2 exposes one step function
and one invariant, with no successor/limit split (per the census). Report the
final signatures verbatim in the report — the next two commissions quote them.

## Deliverables

Census; compiling artifact with all prior theorems green; `#print axioms` for
every contract item including those whose statements you supplied; and a
report whose **first section is a signature table**: for each contracted item,
the final statement as elaborated, so that WO-10 onward can be written against
it without reading the source.

## Context

Campaign position: Papers I–IV are verified except Paper I §5, Paper II
Theorem 5.4, and Paper II Propositions 5.5 and 6.1. The census's recommended
order is WO-9 (this), WO-10 (target (a)), WO-11 (cardinal infrastructure),
WO-12 (Paper II Thm 5.4), WO-13/14/15 (Paper I §5 in three parts), with the
standing recommendation that the blocking lemma be quarantined as a named
hypothesis rather than formalized if the budget binds. Numbering drift is
recorded in §7 of the census report: Paper I's CH theorem is **5.7**, the
blocking lemma **5.6**, the interval statement **Proposition 5.9**; Paper II's
chain statement is **Proposition 6.1**.
