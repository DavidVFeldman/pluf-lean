# Work Order WO-4 — pluf project (Feldman–Wilce)

**Ground truth:** this tarball (`pluf-wo4.tar.gz`). Contract: `PlufWO4.lean`.
Paper source: Paper IV of the series ("Exact paving for Fubini products of
normal measures"), included in this tarball as `paper4.pdf` — the docstrings
sketch every proof, and the paper carries them in full, in particular the
pattern case analyses of Sections 3–4 that are the mathematical heart of
items A1 and C2.

**Base:** WO-3 artifact (CI runs #1–#3 green; full project under `base/`).
`PlufWO4.lean` imports `RequestProject.PlufWO3`. Reuse everything; all 39
prior theorems must remain green.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-3, plus the WO-3 codification)

Census first. Report-rather-than-repair, with the codified license: if a
contract statement is false, formalize a counterexample where feasible,
preserve the contract verbatim in a comment, and you MAY supply a minimally
repaired statement clearly marked as such — ratification happens at audit.
This license matters doubly here: items A1 and C2 formalize finite pattern
case analyses performed by hand, and **checking them is a purpose of this
commission** — a missing or wrongly analyzed pattern is a finding, not a
failure. No `sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per
contract theorem; whitelist `propext`, `Classical.choice`, `Quot.sound`.
Partial completion reported item by item; if the commission is too large for
one run, complete in the order A → B → C → D and return what is green.

## Items and notes

**Part A.** `RowbottomFor` is the hypothesis form of Rowbottom's theorem;
simultaneous homogenization of finitely many colorings is finite-product
bookkeeping. A1's conclusion is stated on ordered coordinates; restating on
`Fin 2`-tuples or `Sym2` is fine if the library prefers it (report). The
universe of `V` is yours to manage.

**Part B.** Check the census for an existing Fubini/`Ultrafilter.prod`
object before constructing one; if constructing, the section-largeness
definition in `mem_fubini_iff` is the contract. B4 is WO-1's certified A3
argument with countability deleted — expect near-verbatim reuse. B6 is the
isomorphism-invariance of a purely combinatorial property; `Ultrafilter.map`
along an `Equiv`. B7 composes B4–B6. B8 instantiates A1; off-triangle points
of a partition piece are irrelevant once the selector is intersected into a
triangle set.

**Part C.** C2 is the centerpiece and the largest single item: the
membership-pattern analysis over increasing triples and quadruples. Organize
the finitely many patterns however the proof is cleanest (a helper lemma
schema for "fix x, free y upward" and "fix x with an uncountable pivot, free
y below" is one route); the paper's enumeration is the reference. C4–C6
carry an explicit refactoring license (see the docstring): refactor the
WO-2/WO-3 internals to a paving-parametrized core with the old theorems as
instances, or prove fresh EPP versions reusing the auxiliary lemmas — your
choice, reported, with the 39 staying green. C7 is assembly.

**Part D.** D1 generalizes WO-1's `thin` (same one-line argument with
`F.card` functionals; the rank bound against a finite cardinal). D2a/D2b are
glue; D2 is their contrapositive assembly. D3 is the one genuinely new
analytic item: Baire category in the complete space `R ⊓ block S`. Mathlib
has `BaireSpace` for complete pseudometrizable spaces and the
proper-closed-subspace-has-empty-interior circle; the countable union runs
over `Finset ℕ`. If the rank-vs-finrank bookkeeping in D1/D2b/D3 fights the
stated forms, restate with `Module.finrank` or `FiniteDimensional` and
report; the mathematical content is the finite bound.

## Deliverables

Census; compiling artifact with all 39 prior theorems green; `#print axioms`
for the 22 WO-4 contract theorems; item-by-item report including the C4–C6
refactoring decision, any pattern-analysis findings in A1/C2, and any
restatements under the codified license.

## Context

This commission mechanizes Paper IV: with it, the series' κ-front is
verified end to end under quarantined classical hypotheses (Rowbottom,
Fodor), including the answer to Paper III's Question 5.5 — a maximal
projection filter from an ultrafilter isomorphic to no normal measure — and
the ω-front's rigidity conjecture acquires machine-checked constraints
(D1–D3) alongside WO-1's. The campaign document `CAMPAIGN.md` in this
tarball maps the remaining commissions toward total verification of all
four papers.
