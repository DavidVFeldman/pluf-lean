# Work Order WO-3 — pluf project (Feldman–Wilce)

**Ground truth:** this tarball (`pluf-wo3.tar.gz`). Contract: `PlufWO3.lean`.
Paper sources: Corollary 2.2, Corollary 3.2 (filter half), and Proposition 5.3
(Hilbert half) of Paper III; proofs sketched in docstrings.

**Base:** the WO-2 artifact (repo `pluf-lean`, CI runs #1–#2 green; the full
project is included under `base/`). `PlufWO3.lean` imports
`RequestProject.PlufWO2`. **Reuse, don't duplicate**: `PlufWO2.block`/`evec`/
`hasSum_evec_smul`/`hasSum_coord_smul`/`inner_eq_coord_mul`/
`block_le_of_evec_mem`/`exact_paving`/`block_filter_decides`,
`PlufWO1.IsPartialSelector`, and WO-1's Part B techniques (the constraint-
vector summability estimate and the C2 two-point witness transplant to κ).
All 24 prior theorems must remain green.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; identical to WO-1/WO-2)

Census first; report-rather-than-repair (false-looking statements come back
as reports, idiom/naming/universe bookkeeping free and reported); no
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per contract theorem,
whitelist `propext`, `Classical.choice`, `Quot.sound`; partial completion
reported item by item. No large-cardinal machinery: `DiagInt`,
`CountableSmall`, `CountablyComplete`, and the generic intersection-closure
hypothesis of H2 are hypotheses, so everything is ZFC.

## Items

**Part G (required).** G1: bisection; countable completeness intersects the
nested decided halves. G2: the docstring's route reuses `inner_eq_coord_mul`
with `P := T` — the one point of care is pushing the ℓ²-expansion through
`⟪·, x⟫` and comparing the resulting `∑ (x β)² d β` against
`∑ (x β)² = ‖x‖²`; summability of the weighted series follows from
boundedness of the diagonal entries by `‖T‖` (or simply from `|d β| ≤ |L|+ε`
on the shrunken set, which suffices and avoids operator-norm API — prover's
choice, route reported). No self-adjointness hypothesis: report if one turns
out to be genuinely needed rather than adding it.

**Part H (required; mostly routine).** H1 is three small lemmas (properness
uses only nonemptiness of ultrafilter members plus `evec_mem_block`). H2 is
generic over the index type — this is deliberate: it captures κ-completeness
with no cardinal arithmetic; instantiation notes live in the docstring. H3:
D1 (`countable_supp`) plus `CountableSmall` produce the excluding member.
H4: unfold `block_filter_decides`.

**Part I (required; the substantive part).** I1: the constraint vector of a
countable set via an injection into ℕ furnished by `Set.Countable`
(`memℓp` by comparison of the squared coordinates with the geometric series
composed with the injection — `Summable.comp_injective` or kin; WO-1's
`memlp_constraint` is the ℕ-template). The *choice* of injection is internal
and unconstrained; the contract is the specification lemmas (support exactly
the piece; nonnegative coordinates — if a different normalization is
cleaner, restate I1c and report). I2: a point of a nonempty `S` lies in some
piece by the cover; `evec α` then pairs nontrivially with that constraint
(strict positivity of the coordinate on the support). I3 both directions as
sketched; the (⇐) direction's "single surviving term" is a `tsum` over a
subsingleton intersection, or a `hasSum_single` in the WO-2 style. I4:
assembly of I2, I3(⇒ via contraposition), and `PhiU` membership.

## Deliverables

Census; compiling artifact extending the WO-2 project with all 24 prior
theorems green; `#print axioms` for the 14 WO-3 contract theorems (root file
= `PlufWO3.lean`, importing the chain so one build runs all three audits);
item-by-item report including the G2 summability route and any I1c
restatement.

## Context

With WO-3, every lattice-level assertion of Paper III is machine-checked:
paving and dichotomy (WO-2), flattening and the full filter packaging of
Φ(U) (Parts G–H), and the σ-Q necessity witness in both its combinatorial
(WO-1) and Hilbert (Part I) halves. What remains of the paper is its
state-theoretic Sections 4–5, which consume Blecher–Weaver's excision theory
and are out of scope until that theory exists in Mathlib.
