# Work Order WO-15 — pluf project (Feldman–Wilce)

**THE FINAL COMMISSION.** Paper I, Theorem 5.7 (under CH, a nonprincipal pluf
every member of which is ample — hence no round slices for `T`) and
Proposition 5.9 (the set of `φ(T)` over the state face is the whole interval
`[1/16, 1]`).

On completion, every assertion of Papers I–IV is machine-checked and the
campaign's target is met: total verification modulo the four quarantined
classical imports (Mathias, Marcus–Spielman–Srivastava, Blecher–Weaver,
Rowbottom), each of which appears only as a named hypothesis.

**Ground truth:** this tarball (`pluf-wo15.tar.gz`). Contract:
`PlufWO15.lean`. Paper source: `paper1.pdf`, Theorem 5.7 and Proposition 5.9,
with their proofs — read them; the contract docstrings restate both.
Included reports: **`REPORT-WO12.md` (read first — its recursion section is
binding, see below)**, `REPORT-WO14.md`, `REPORT-WO13.md`, `REPORT-WO11.md`.

**Base:** the merged tree after WO-12 and WO-14 (233 theorems; CI runs
#1–#13; full project under `base/`). `PlufWO15.lean` imports
`RequestProject.PlufWO14` and `RequestProject.PlufWO12`. All prior theorems
must remain green; `PlufWO7a.lean` is the census record, not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-14)

Census first. Report-rather-than-repair with the codified license. No
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per contract
theorem; whitelist `propext`, `Classical.choice`, `Quot.sound`. CH is a
hypothesis, never an axiom. Partial order: A → B → C → D.

## Two settled matters — do not rederive

**1. The recursion pattern.** WO-12 established it in anger and its report is
definitive:
* `PlufWO9.exists_omega1_chain` **does not fit** — its step map cannot see
  the stage index, and stages need the whole set of earlier values rather
  than a supremum. Do not attempt it.
* Use well-founded recursion on `Ordinal` with the stage choice in a `dite`
  (`WellFounded.fix` + `WellFounded.fix_eq`), proving the stage invariant
  **afterwards** by `Ordinal.induction` over the history. No successor/limit
  split is needed — the history formulation absorbs both.
* Pin the universe (`Ordinal.{0}` annotations) or `(aleph 1).ord`'s universe
  is left as a metavariable.
* Keep the history and the stage predicate as top-level definitions.
`PlufWO12/PartB.lean` is the worked precedent; read it before drafting B1.

**2. The room argument.** WO-11's C3 is FALSE in its orthogonality-based
forms (H is separable; a countable set can have dense span) and was repaired
to the **algebraic (Baire) escape** statement about the SPAN of a countable
set. There is no "infinite-dimensional orthogonal complement of a countable
set" to be had. Every room argument in this commission must go through finite
codimension — WO-14's `finCodim_of_constraints`, WO-13's C2 — not through a
countable-set escape.

## Item notes

**Part A — the stage step.** A1 internalizes the paper's three cases so that
Part B never branches at run time; this is the main structural decision of
the commission and it is deliberate. Case III consumes
`PlufWO14.blocking_lemma` (unconditional, merged): its hypotheses are exactly
countability, directedness (from meet-closure), ampleness of members, and a
`q` with `q ⊓ p` not ample — plus `hGN`, which is the negation of Case I and
is available. WO-14 flags `hGN` unused, but the contract prints it: supply it.

If requiring `⊤ ∈ F` as a field of `Admissible` is cleaner than carrying it
as a side hypothesis, do that and REPORT — Case II needs `p = ⊤ ⊓ p` to be
ample.

A2 is the limit bookkeeping; state it in the form B1 actually consumes
(countable index with directedness, or ordinal-indexed monotone) and report.

**Part B.** Per the settled pattern. The `a`-th closed subspace comes from
`PlufWO11.exists_enum_closedSubspaces`.

**Part C.** C1 is the upward closure of the union; maximality via
`PlufWO6.isPluf_of_criterion` fed by the decision property. C2 is WO-13's B1′
radii applied memberwise, plus the RSP failure from the constant gap.

**Part D.** D2 is the substance: Hahn–Banach off the two-dimensional
`span {I, T}`, dominated by the sublinear upper-limit functional that WO-6
already built for `face_nonempty` (and which WO-6 established is defined on
all of `B(H)`, not merely the self-adjoints). The independence of `I` and `T`
is immediate — `T`'s diagonal takes two values — but prove it if not
available. The contract fixes D2's conclusion, not its route; restate the
domination step if another shape is cleaner, and report.

## Deliverables

Census; compiling artifact with all 233 prior theorems green; `#print axioms`
for every contract theorem; report with the `Admissible`/`⊤` packaging
decision, the A2 form, the B1 recursion as implemented (noting any divergence
from WO-12's pattern), and the D2 route.

## Context — and what follows

This closes the campaign. After a green CI run the ledger will record every
theorem of Papers I–IV as machine-checked, with the four classical imports
quarantined by name and never discharged. Remaining known gaps, all recorded
and none formalization debt: the four imports themselves; and the open
mathematics (the Rigidity Conjecture at ω, the EPP/maximality/σ-Q
equivalences, mixed products, and Question 6.2 of Paper II on the Lebesgue
chain).
