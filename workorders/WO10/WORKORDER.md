# Work Order WO-10 — pluf project (Feldman–Wilce)

**Target (a) of the WO-7a census**, estimated there at ~0.5 commission:
Paper II's Proposition 5.5 (one-witness reduction) and Proposition 6.1
("Chains never suffice"), together with the two pieces of new machinery they
need — the Zorn extension theorem for plufs, and relative orthogonal
complements of a countable nested chain. Closing this closes a whole target.

**Ground truth:** this tarball (`pluf-wo10.tar.gz`). Contract:
`PlufWO10.lean`. Paper source: `paper2.pdf`, §§5–6 (note the numbering: the
reduction is **Proposition 5.5**, the chain statement **Proposition 6.1**).
`REPORT-WO9.md` is included: its signature table is the API this commission
is written against.

**Base:** the WO-9 artifact (168 theorems; CI runs #1–#9; full project under
`base/`). `PlufWO10.lean` imports `RequestProject.PlufWO9`. All prior
theorems must remain green; `PlufWO7a.lean` remains the census record and is
not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-9)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment + marked
minimal repair; ratification at audit). No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` per contract theorem; whitelist `propext`,
`Classical.choice`, `Quot.sound`. Partial order: A → C → B → D → E.

## The one open design question

**E1's basis quantifier.** Paper II's Theorem 5.2 is mechanized
(`PlufWO5.diagonalizable_iff_intimate`, discharged for genuine plufs as
`PlufWO6.diagonalizable_iff_intimate_pluf`) *for the standard basis*.
Proposition 5.5 quantifies over **all** orthonormal bases. The bridge is the
basis-relative form of Theorem 5.2 — the same statement with `PlufWO9.blockB b`
in place of `block`. The census's Q4/D-group results suggest this is cheap,
because Theorem 5.2's proof uses only the lattice identities of blocks
(`blockB b B ⊓ blockB b A = blockB b (B ∩ A)`, monotonicity, and that
complementary blocks meet trivially), all of which hold at an arbitrary basis.

**If it is cheap, prove it as item E0 and use it.** If it is not, state E1 for
a fixed basis and REPORT the gap explicitly — do NOT silently specialize the
printed proposition. This is the one place in the commission where the
contracted statement could quietly drift from the paper's.

## Item notes

**Part A.** A1 is the standard Zorn argument; the only clause needing care in
the chain step is closure under meets, via directedness of the chain. Note
`PlufWO6.IsPluf`'s maximality clause is phrased as an intermediate-family
condition; deriving it from Zorn-maximality may be smoother through
`PlufWO6.isPluf_of_criterion`. A2 is the form Proposition 5.5 consumes.

**Part B.** B1's statement is left open (`True`) deliberately: state the
decomposition in whatever ℕ-indexed orthogonal-family shape WO-9's corrected
countable-decomposition theorem consumes, and report it. B2 needs
separability — contract it as a hypothesis; report whether it is automatic in
the intended application (it is, in `PlufWO1.H`).

**Part C.** `blockB_inf_blockB` should be proved and exported on its own:
WO-12 will want it. C1 and C2 are short.

**Part D.** D1 is the printed Proposition 6.1, with the conclusion in the
form Proposition 5.5's hypothesis negates.

**Part E.** See the design question above. Nonprincipality goes through
`PlufWO6.principal_iff_sInf_ne_bot`; existence through A2.

## Deliverables

Census; compiling artifact with all 168 prior theorems green; `#print axioms`
for every contract theorem (including E0 if taken); report with the B1 shape,
the E0 verdict and its consequences for E1's statement, and the
reconciliation of `IntimateB` at the standard basis with `PlufWO5.Intimate`.

## Context

Campaign position: Papers I–IV verified except Paper I §5, Paper II
Theorem 5.4, and Paper II Propositions 5.5/6.1 — the last of which this
commission closes. Remaining after WO-10, per the census's recommended
order: WO-11 (cardinal infrastructure: `#{closed subspaces} = 𝔠`,
`#{orthonormal bases} = 𝔠`, CH enumeration — a shared prerequisite paid
once), WO-12 (Paper II Theorem 5.4, the ω₁-recursion, exercising the pattern
on the cheaper of the two transfinite targets), then WO-13/14/15 (Paper I §5
in three parts, with the standing recommendation to quarantine the blocking
lemma as a named hypothesis if the budget binds).
