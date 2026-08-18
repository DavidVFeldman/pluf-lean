# Work Order WO-17 — pluf project (Feldman, Wilce)

**The remainder of Paper V.** Sections 4, 5 and 6 — the scrawl axioms, the
finite-rank classification, and the model space — completing the verification
of the paper. On delivery, every assertion of Papers I–V is machine-checked,
with the classical imports quarantined by name and the open questions left
open.

**Ground truth:** this tarball (`pluf-wo17.tar.gz`). Contract:
`PlufWO17.lean`. Paper source: `paper5.pdf` — **note that Example 6.2 has been
rewritten since the WO-16 census**; the included PDF is current and the
contract follows the new proof. Also included: `REPORT-WO16.md`, whose census
verdicts this work order responds to, and `PAPERS.md`.

**Base:** the tree after WO-16 (261 theorems; CI runs #1–#15; full project
under `base/`). `PlufWO17.lean` imports `RequestProject.PlufWO16`. All 261
prior theorems must remain green; `PlufWO7a.lean` is the census record and is
not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-16)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment + marked
minimal repair; ratification at audit). No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` per contract theorem; whitelist `propext`,
`Classical.choice`, `Quot.sound`. Partial order: C → A → B.

## Two responses to the WO-16 census

That census recommended leaving Sections 4 and 6 alone. This work order
overrides both recommendations, for reasons that have changed since:

**1. The matroid vocabulary is defined here, not imported.** The census found
Mathlib's `Matroid` has no constructor from a circuit family, and no scrawls,
cofinitary duals or representability. None of that is needed. Every assertion
of Paper V is about families of subsets of ℕ and about kernels of matrices, and
Part A defines `IsCircuitFamily`, `IndepOf`, `HasSM` and `IsScrawlFamily` from
scratch in a dozen lines. **Do not import `Mathlib.Data.Matroid`, and do not
attempt to construct a `Matroid` instance.** If a later Mathlib supplies the
constructor, bridging is one lemma and is not this commission's business.

**2. Example 6.2 no longer needs Vandermonde.** The census correctly reported
that generalized Vandermonde positivity is absent from Mathlib and that the
printed proof depended on it. The paper has since been rewritten: the
determinant and Cramer's rule are replaced by a dimension count against the
exponential-sum zero lemma (Lemma 6.1 of the current PDF). The only analytic
input is now Rolle's theorem. Part C is contracted against that proof.

## Item notes

**Part C (do first; it is self-contained).** C1 is the one genuinely new
analytic item: induction on the number of exponents, dividing by the first
exponential and applying Rolle. Its contracted form is the sharp negative one
— `m` distinct zeros is impossible — because that is what C2 consumes; if a
`Set.Finite` plus cardinality form is more natural to prove, prove that and
derive the contracted form, reporting both. C2 is the dimension count. Note
the summability hypothesis of the paper's example plays no part in the support
claim and is deliberately absent from the contract. C3 is the conditional; its
hypothesis is Paper V's open Question 9.3 and is supplied, not proved.

**Part A.** A1 is WO-16's `exists_supp_sUnion` restated in the new vocabulary
— cite, do not reprove. A2 is the finite correction term; the hypothesis
`p ∈ supp (u q) ↔ p = q` is what makes the coefficients well defined.

**Part B.** `AroKaHyp` must be stated about `T(W)` for finite-dimensional
`W ⊆ (ℕ → ℝ)`, as the source states it, and NOT about the support family of a
closed subspace of `ℓ²`. The transfer is B1 and B2, and the census identified
B2 — support-preserving realization inside `ℓ²` by a diagonal rescaling — as
the item carrying content. B1 will need whatever coercion `PlufWO16` uses from
`H` to `ℕ → ℝ`; if no such map is exported, introduce one and report it.
B3 should also report whether Mathlib's finite-dimensional-implies-closed
lemma applies in the form needed.

## Deliverables

Census; compiling artifact with all 261 prior theorems green; `#print axioms`
for every contract theorem; report with the C1 form actually proved, the
coercion used in B1, the rescaling in B2, and any finding on the vocabulary
definitions of Part A.

## Context

After this commission the residue of Paper V is exactly two items, both by
design: the quarantined hypothesis `AroKaHyp`, which is a theorem of the
literature and is never to be discharged here; and Question 9.3, which is open
mathematics. That is the same shape as Papers I–IV, where Mathias, MSS,
Blecher–Weaver and Rowbottom are quarantined and the Rigidity Conjecture, the
EPP equivalences and the Lebesgue chain question remain open.
