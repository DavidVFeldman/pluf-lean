# Work Order WO-1 — pluf project (Feldman–Wilce)

**Project:** Maximal filters in the projection lattice of a Hilbert space ("plufs").
**Commissioners:** David Feldman (UNH), Alexander Wilce (Susquehanna).
**Ground truth:** this tarball (`pluf-wo1.tar.gz`). The mathematical contract is the
set of statements in `PlufWO1.lean`; the paper sources of the results are Paper II
(Lemma 3.6, Proposition 3.7) and Paper III (Lemma 5.2, Proposition 5.3) of the pluf
series, whose proofs are sketched in the docstrings.

**Toolchain:** `leanprover/lean4:v4.28.0` with the matching Mathlib release.

## Protocol (binding)

1. **Census first.** Before proving anything, return a census: for each item
   (A1–A4, B1a–B1d, B2, C1, C2), the relevant existing Mathlib API (exact names),
   an assessment (routine / moderate / hard / blocked), and any statement-level
   concerns. Wait-free items may be dispatched in the same run after the census.
2. **Report rather than repair.** Renaming, restating in idiomatic Mathlib form,
   splitting into auxiliary lemmas, and strengthening hypotheses that are provably
   implied are all fine. Any change to *mathematical content* — weakening a
   conclusion, adding a hypothesis not derivable from the stated ones, altering a
   definition's meaning — is not: report the obstruction and stop on that item.
   In particular, if a statement is false as written, we want to know, not to
   receive a repaired cousin.
3. **Closure discipline.** No `sorry`, `admit`, `axiom`, or `native_decide`
   anywhere in the final artifact. Every theorem must come with `#print axioms`
   output; the whitelist is `propext`, `Classical.choice`, `Quot.sound`. A single
   self-contained file (or a small file set with a root import) that compiles
   under the stated toolchain is the deliverable; partial completion is fine and
   should be reported item by item.
4. **No new axioms for large cardinals.** Part A deliberately axiomatizes nothing:
   the Fodor property and countable-set avoidance are *hypotheses* of the theorems,
   so no measurable-cardinal machinery is needed or wanted.

## Items and priorities

### Part A — σ-Q-point combinatorics (required; expected routine-to-moderate)

- **A1** `not_mem_union_of_not_mem`: locate in Mathlib (`Ultrafilter.union_mem_iff`
  or kin) or prove in-line.
- **A2 / A2′** Equivalence of the function form and the partition form of the
  σ-Q-point property. Direction A2′ uses the least-element-of-my-piece map;
  well-foundedness of `<` supplies minima.
- **A3 / A3′** The heart of Part A: Fodor property + no countable set in `U` ⇒
  partial selectors for every countable-piece partition (indeed the set of
  piece-minima lies in `U`), hence σ-Q. The docstring carries the complete
  four-line paper proof.
- **A4** Transversal escape via two disjoint transversals. Uses choice twice and
  A1 once.

Universe note: the partition index `ι` is taken in `Type` in the statements to
avoid universe plumbing; lifting to `Type*` is welcome if free, not required.

### Part B — witness subspace and thinness (required; expected moderate)

- **B1a–B1d** Infrastructure: the constraint vector with weights `2^{-(n+1)}`
  (membership in `lp _ 2` is a geometric-series estimate; `lp.single`
  superposition or `Memℓp` directly, at your discretion); the block of a set as
  a closed submodule with the stated membership characterization (an
  intersection of kernels of coordinate functionals is one natural route); the
  disjoint-support orthogonality lemma B1d, which is a `tsum` computation.
- **B2** `thin` — the mathematical target of Part B. The proof factors through:
  the functional `⟪·, constraintVec (A k)⟫` is injective on `R ⊓ block (A k)`
  (kernel elements land in `R ⊓ W A = ⊥` via B1d), and an injective linear map
  into `ℝ` bounds `Module.rank` by `1` (`LinearMap.rank_le_of_injective` /
  `rank_le_one_iff` circle).

### Part C — stretch (attempt after A and B; report freely)

- **C1** The block-intersection identity for closed spans of disjointly
  supported families. This is the one genuinely analytic item: the forward
  inclusion needs the orthonormal expansion of elements of the closed span
  (normalize the `ρ i`; `Orthonormal` + Hilbert-space series API) and
  continuity of coordinate functionals on `lp _ 2`. If the closed-span
  formulation fights the available API, an acceptable weakening — *report it
  as such* — is the same identity with both sides' algebraic spans and the
  conclusion of C2 adjusted accordingly; but the closed-span version is the
  contract.
- **C2** `noblock` — assembles C1, A1, A4, and the explicit two-point witness
  `(2^{-(n'+1)})⁻¹`-weighted combination described in the docstring. The
  combinatorial half is Part A technology; the analytic half is C1.

## Deliverables

1. Census (item-by-item, with Mathlib citations).
2. Compiling artifact(s) under `v4.28.0`, sorry/admit/axiom/native_decide-free.
3. `#print axioms` for every theorem, whitelist as above.
4. Item-by-item report: proved / proved-with-noted-restatement / blocked-with-reason.

## Context for the curious prover

Part A: "σ-Q-point" is the κ-analogue of the Q-point property (countable-to-one
replacing finite-to-one); A3 is the linearly-motivated half of a pinching theorem
(normal ⇒ σ-Q ⇒ [necessary for maximality of the block filter on ℓ²(κ)]). Part B/C:
`W A` is the witness subspace showing block filters of non-selective ultrafilters
are non-maximal; B2 and C2 are rigidity results constraining how a maximal filter
extending the block filter could avoid `W A` — evidence for the conjecture that it
cannot, i.e., that `W A` is a *forced member* of every maximalization.
