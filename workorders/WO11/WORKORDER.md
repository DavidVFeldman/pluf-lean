# Work Order WO-11 — pluf project (Feldman–Wilce)

**The shared cardinal infrastructure**, paid once and consumed by both
remaining transfinite commissions (WO-12: Paper II Theorem 5.4; WO-15:
Paper I Theorem 5.7 and Proposition 5.9). Small, self-contained, and
deliberately free of analysis.

**Ground truth:** this tarball (`pluf-wo11.tar.gz`). Contract:
`PlufWO11.lean`. `REPORT-WO9.md` and `REPORT-WO10.md` are included: the
WO-9 signature table (especially E1/E2, the CH enumeration and the ω₁
combinator) is the API this commission must dovetail with.

**Base:** the WO-10 artifact (181 theorems; CI runs #1–#10; full project
under `base/`). `PlufWO11.lean` imports `RequestProject.PlufWO10`. All
prior theorems must remain green; `PlufWO7a.lean` is the census record and
is not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-10)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment +
marked minimal repair; ratification at audit). No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` per contract theorem; whitelist `propext`,
`Classical.choice`, `Quot.sound`. CH is a hypothesis, never an axiom, and
appears only in Part B. Partial order: A → C → B.

## Two standing instructions specific to this commission

**1. No analysis.** Every item should follow from separability of `H`, the
existence of its standard basis, and cardinal arithmetic. If an item starts
to demand genuine Hilbert-space argument, the contract is probably wrong —
REPORT rather than push through.

**2. Concreteness is deliberate.** Everything is stated at `PlufWO1.H`
rather than at an abstract separable space. The two previous commissions
each caught a false contract of the form "every separable complete space
has an ℕ-indexed Hilbert basis" (`E = ℝ` refutes it). A general form needs
`¬ FiniteDimensional` plus separability and should be *derived from* the
concrete statement, not substituted for it. Generalize only if cheap, and
report.

## Item notes

**Part A.** The upper bounds are all `𝔠 ^ ℵ₀ = 𝔠` via separability; the
lower bounds are free to be whatever is shortest. For A1 the blocks
`block S`, `S ⊆ ℕ`, are probably the cheapest injection (they need only
`PlufWO1.mem_block_iff`); for A3 the `{0,1}`-diagonal operators serve both
the operator and the self-adjoint counts at once. Report the routes.

**Part B.** If WO-9's `exists_enumeration_of_CH` (E1) already delivers a
general "set of size 𝔠 is enumerated by the countable ordinals," then B1–B3
are instantiations and should say so. If E1's shape does not fit — for
instance if it is stated for types rather than subtypes, or if the universe
lifting it hides is in the wrong place — REPORT that, since WO-12 and WO-15
will consume whichever form this commission fixes. The enumeration shape
(surjection from `{o // o < ω₁}`) is contracted as stated because it is
what a stagewise recursion wants; a bijection or an `Ordinal.enum`-based
form is acceptable if better, with the change reported.

**Part C.** C1 and C2 are the stage bookkeeping. C3's statement is left as
a placeholder deliberately: state the form the recursions want. The minimum
is that the closed span of a countable set is not all of `H`; the stronger
and more useful form is that its orthogonal complement is
infinite-dimensional, which is what Paper I §5's ampleness arguments need.
Supply the stronger form if it is no harder, and report which was proved —
WO-13 and WO-15 will be written against it.

## Deliverables

Census; compiling artifact with all 181 prior theorems green;
`#print axioms` for every contract theorem including C3 as supplied; report
with the A-route choices, the B/E1 dovetailing verdict, and the C3 form.

## Context

Remaining after this commission: **WO-12** (Paper II Theorem 5.4 — the ω₁
recursion, on the cheaper of the two transfinite targets, consuming B2 and
the WO-10 `blockB`/intimacy API), **WO-13** (Paper I §5's ZFC lemmas:
ampleness, upward inheritance, escape — consuming WO-9's essential-spectrum
and approximate-eigenvector API and this commission's C3), **WO-14** (the
blocking lemma, the hardest item remaining, with a standing recommendation
to quarantine it as a named hypothesis if the budget binds), and **WO-15**
(the CH recursion assembling Theorem 5.7 and Proposition 5.9, consuming B3
and WO-14). WO-11 and WO-13 are independent of one another and may run in
parallel.
