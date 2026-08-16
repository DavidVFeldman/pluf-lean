# Work Order WO-2 — pluf project (Feldman–Wilce)

**Project:** Maximal filters in the projection lattice of a Hilbert space.
**Ground truth:** this tarball (`pluf-wo2.tar.gz`). The mathematical contract is
`PlufWO2.lean`; paper sources are Theorem 2.1, Theorem 3.1 and Corollary 3.2 of
Paper III of the pluf series, whose proofs are sketched in the docstrings.

**Base:** WO-2 builds on the WO-1 artifact (repository `pluf-lean`, commit
`1be8bac`, CI-green with the standard axiom audit). The tarball includes the
full WO-1 project; `PlufWO2.lean` imports `RequestProject.PartC`. Reuse the
`PlufWO1` namespace freely; do not duplicate its lemmas.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as in the included
`lake-manifest.json`. Do not bump either.

## Protocol (binding; identical to WO-1)

1. **Census first** — item-by-item Mathlib API, feasibility, statement concerns.
2. **Report rather than repair** — idiom and naming free; mathematical content
   frozen; false-looking statements come back as reports.
3. **Closure discipline** — no `sorry`/`admit`/`axiom`/`native_decide`;
   `#print axioms` per contract theorem; whitelist `propext`,
   `Classical.choice`, `Quot.sound`. Partial completion reported item by item.
4. **No large-cardinal machinery** — `DiagInt` and `CountableSmall` are
   hypotheses; every theorem is a ZFC statement about arbitrary ultrafilters
   on a well-ordered type. (The `[WellFoundedLT κ]` instance is inherited from
   the WO-1 section conventions and is likely unused outside `DiagInt`'s
   order; `omit` freely where unused, as in WO-1's A4.)

## Items

**Part D — infrastructure at κ (required; expected routine).**
D1 countable supports (the load-bearing triviality: `Memℓp` ⇒ summable squares
⇒ countable support; `Summable.countable_support` or kin). D2/D3 are the
κ-generalizations of WO-1's `coordCLM` / `block` / `mem_block_iff` /
`isClosed_block`. **Refactoring choice is yours and must be reported:** either
generalize the WO-1 Part B definitions to an arbitrary index type and
re-derive the ℕ instances (preferred if cheap — it keeps one notion of block
in the codebase), or define fresh κ-versions in `PlufWO2` and leave Part B
untouched. Either way WO-1's sixteen theorems must remain green. D4 is glue.

**Part E — exact paving (required; the heart; expected moderate).**
E1 as stated. The adjoint is `ContinuousLinearMap.adjoint` (Hilbert space
instance on `lp _ 2` is in Mathlib via the `l2Space` file). The inner-product
orientation in the conclusion is `⟪T (evec α), evec β⟫`; deriving the
symmetric vanishing `⟪T (evec β), evec α⟫ = 0` inside the proof goes through
the adjoint as in the docstring. Note the diagonal intersection is taken over
the *strict* order `α < β`; the conclusion is symmetrized by running the
argument for both `α < β` and `β < α`.

**Part F — exact dichotomy (required; expected moderate, one analytic point).**
F2/F3 as stated. The one analytic point is the expansion
`P x = ∑' α, c α • g α` for `x ∈ block S₀` and its cross-term-free
consequence; the docstring records two admissible routes (tsum of squares, or
a coordinate-rigidity functional in the style of WO-1's C1) — prover's
choice, route reported. `Wᗮ` is closed hence complete, so
`Submodule.starProjection` applies as in WO-1's Part C.

## Deliverables

1. Census.
2. Compiling artifact under the pinned toolchain, extending the WO-1 project,
   with WO-1 still green.
3. `#print axioms` for every WO-2 contract theorem (D1, D2 `coordCLM_apply`,
   D3 both, D4, E1, F2, F3), whitelist as above; root file updated to audit
   them alongside WO-1's.
4. Item-by-item report, including the D2/D3 refactoring decision and the F2
   route taken.

## Context

E1 is Anderson paving with error zero: the entire analytic content of
Marcus–Spielman–Srivastava, along a diagonal-intersection-closed ultrafilter,
is one diagonal intersection. F2 says incidence and angle coincide on a
measure-one set of coordinates — the exact collapse that makes the block
filter of a normal measure a maximal filter (Paper III, Corollary 3.2), and
the reason the pluf theory softens at measurable dimension. With WO-1's
σ-Q results, this WO completes the machine-checked core of Paper III's
positive direction; the remaining gap there (σ-Q sufficiency, Question 5.5)
is open mathematics, not formalization debt.
