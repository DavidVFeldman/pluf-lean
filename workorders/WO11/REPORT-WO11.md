# REPORT — Work Order WO-11 (pluf project, Feldman–Wilce)

**Deliverable.** `RequestProject/PlufWO11.lean` (namespace `PlufWO11`),
together with this report. No other file of the base artifact was edited;
`PlufWO7a.lean` is untouched.

**Toolchain.** `leanprover/lean4:v4.28.0`, Mathlib as pinned in the base
artifact. Base: the WO-10 artifact, unmodified. Full-project build green,
all prior theorems included.

**Headline.**

* Part A (A1–A4) and Part C's C1, C2 are delivered **as contracted** and
  proved.
* Part B (B1–B3) is delivered as contracted and is, as the work order
  anticipated, a **pure instantiation of WO-9's E1**; the only mismatch is
  cosmetic and is absorbed by a one-line bridge (`enumShift`). Verdict in
  §3.
* **C3 is REPORTED FALSE in both of the forms its placeholder proposes**,
  and handled under the codified counterexample license: the verbatim
  contract text is preserved in a comment, two counterexamples are
  formalized, and a marked minimal repair is supplied under the contracted
  name. Ratification requested at audit. Details in §4.
* No `sorry`, `admit`, `axiom` or `native_decide` in the artifact (the
  string `sorry` occurs only inside the block comment that quotes the C3
  contract verbatim, following the WO-7a/WO-10 precedent). Every audited
  item reports exactly `[propext, Classical.choice, Quot.sound]`.
* Two **cheap generalizations** were taken and are reported in §5; nothing
  else generalized cheaply.

---

## 1. Census

Census metric as in WO-9/WO-10: audited contract theorems
(`#print axioms` lines).

| | count |
|---|---|
| base (WO-10 artifact) | 181 |
| added by WO-11 | 18 |
| total | 199 |

The 18 audited items of WO-11 are: `mk_closedSubspaces`,
`mk_hilbertBases`, `mk_continuousLinearMaps`, `mk_selfAdjoint`,
`exists_enum_closedSubspaces`, `exists_enum_hilbertBases`,
`exists_enum_selfAdjoint`, `countable_Iio_of_lt_omega1`,
`countable_iUnion_Iio`, `exists_orthogonal_of_countable` (C3 as supplied),
`span_ne_top_of_countable`, `exists_notMem_of_countable_closed_proper`,
`orthogonal_ne_bot_of_isClosed_ne_top`,
`exists_orthogonal_of_countable_false`,
`closedSpan_countable_eq_top_counterexample`,
`orthogonal_finiteDimensional_counterexample`,
`mk_eq_continuum_of_hilbertBasis`,
`mk_continuousLinearMaps_of_hilbertBasis`.

What the base already supplied, and was reused rather than re-proved:

| needed | taken from the base |
|---|---|
| the standard basis of `H` | `PlufWO9.stdHilbertBasis` |
| blocks and their membership test | `PlufWO1.block`, `PlufWO1.mem_block_iff`, `PlufWO1.isClosed_block`, `PlufWO1.constraintVec_apply` |
| basis-relative blocks | `PlufWO9.blockB`, `PlufWO9.mem_blockB_iff`, `PlufWO9.basis_mem_blockB`, `PlufWO9.blockB_stdBasis_eq` |
| orthogonal projections onto closed subspaces | `PlufWO8.hasOrthogonalProjection_of_isClosed` |
| infinite-dimensionality criteria; finite blocks | `PlufWO5.not_finite_of_orthonormal`, `PlufWO5.finite_block` |
| the CH enumeration | `PlufWO9.exists_enumeration_of_CH` (E1) |

## 2. Part A — the routes taken

Everything rests on two pieces of shared infrastructure in §A0 of the
file: `mk_H` (`#H = 𝔠`, from `#H ≤ #(ℕ → ℝ) = 𝔠^ℵ₀ = 𝔠` and the injection
`r ↦ r • e₀`), and `clm_ext_stdBasis` — a continuous linear map out of `H`
is determined by its values on the standard basis. The latter is the only
"separability" input used anywhere in Part A: no countable dense subset is
ever chosen, and no Hilbert-space analysis beyond the density of the span
of the standard basis appears.

* **A1, upper.** `M ↦ Submodule.starProjection M` (`projOf`) injects the
  closed subspaces into `H →L[ℝ] H`; injectivity is
  `Submodule.starProjection_eq_self_iff`. Composing with A3's upper bound
  gives `≤ 𝔠`. (This replaces the contract's suggested "choose a countable
  dense subset of `M`" route, which needs separability of each subspace as
  a subtype; the projection route needs nothing beyond the base's
  `PlufWO8.hasOrthogonalProjection_of_isClosed`.)
* **A1, lower.** The suggested block route: `S ↦ PlufWO1.block S`. The
  separating vectors are the constraint vectors `PlufWO1.constraintVec {n}`
  (`constraintVec {n} ∈ block U ↔ n ∈ U`), so only `PlufWO1.mem_block_iff`
  and `PlufWO1.constraintVec_apply` are used. `#(Set ℕ) = 2^ℵ₀ = 𝔠`.
* **A2, upper.** `b ↦ (fun n => b.repr (e n))` into `ℕ → H`. Injectivity:
  the two `repr`s agree on the standard basis, hence agree as continuous
  linear maps, hence as isometry equivalences; and `HilbertBasis` is a
  one-field structure over its `repr`.
* **A2, lower.** **Not** the contract's rotations. The reindexings of the
  standard basis along `Equiv.Perm ℕ` already give `𝔠` bases
  (`Cardinal.mk_perm_eq_two_power`: `#(Equiv.Perm ℕ) = 2^ℵ₀ = 𝔠`), built by
  `HilbertBasis.mk` from the reindexed orthonormal family — the range, and
  therefore the density of the span, is unchanged. The work order's
  parenthetical "(no: those are only countably many)" applies to the
  *finitary* permutations; the full permutation group of ℕ has size `𝔠`.
  This avoids constructing any rotation by hand.
* **A3/A4, upper.** `T ↦ (fun n => T (e n))` into `ℕ → H`; the
  self-adjoint count is the subtype bound.
* **A3/A4, lower.** The scalar multiples `r • 1`, which are self-adjoint
  (`IsSelfAdjoint.all r` smul `IsSelfAdjoint.one`), so a single family
  serves both counts. Cheaper than the suggested `{0,1}`-diagonal
  operators, which would have to be constructed.

## 3. Part B — the E1 dovetailing verdict

**E1 fits, and B1–B3 are instantiations, not new proofs.**
`PlufWO9.exists_enumeration_of_CH` is stated for a type `α : Type` with
`#α = 𝔠` and CH as a hypothesis, and returns a surjection from
`Set.Iio (Ordinal.omega 1)`. Assessment against the two failure modes the
work order flagged:

* *Types vs subtypes*: not a problem. E1 quantifies over an arbitrary
  `α : Type`, and each of the three sets counted here is already a `Type`
  (two of them subtypes, which are types). No restatement was needed.
* *Universe lifting in the wrong place*: not a problem. E1 handles the
  lifting internally and every type here lives in `Type 0`, so the call
  sites see no `ULift`.

The single mismatch is cosmetic: E1's index type is
`Set.Iio (Ordinal.omega 1)` and the WO-11 contract's is
`{o : Ordinal // o < (Cardinal.aleph 1).ord}`. These agree by
`Cardinal.ord_aleph`, and `PlufWO11.enumShift` is the bridge (it takes
`#α = 𝔠` and CH and returns the contracted shape). **Recommendation for
WO-12/WO-15:** consume `enumShift`, and state stage indices as
`{o : Ordinal // o < (aleph 1).ord}`; the `Ordinal.omega 1` form remains
available and is definitionally the same subtype.

B1–B3 are then literally `enumShift hCH mk_closedSubspaces`,
`enumShift hCH mk_hilbertBases`, `enumShift hCH mk_selfAdjoint`.

CH is carried as the section variable `hCH : continuum = aleph 1` with an
explicit `include hCH`; it appears in Part B only, and never as an axiom.

## 4. Part C — C1, C2, and the C3 report

**C1, C2** are as contracted. C1 follows the WO-9 pattern
(`Cardinal.countable_iff_lt_aleph_one`, `Ordinal.mk_Iio_ordinal`,
`Ordinal.isInitial_omega`), converted from `(aleph 1).ord` by
`Cardinal.ord_aleph`. C2 is C1 plus `Set.Countable.biUnion`, named as the
work order requested so the recursions can cite it directly.

**C3 is false as proposed, in both of its proposed forms.** The
placeholder's prose asserts that the closed span of a countable set of
vectors is a *proper* closed subspace ("at minimum"), with the stronger
demand that its orthogonal complement be infinite-dimensional. But `H` is
*separable*, and separability is exactly what makes countable sets able to
have dense span:

* `closedSpan_countable_eq_top_counterexample` and
  `exists_orthogonal_of_countable_false`: the standard basis is countable
  and its closed span is `⊤`; hence its orthogonal complement is `⊥`,
  refuting both the minimum form and the stronger form at once.
* `orthogonal_finiteDimensional_counterexample`: the failure is not only
  at the degenerate case. Delete one basis vector — the set
  `{e_n : n ≠ 0}` is countable, its closed span *is* proper, and its
  orthogonal complement is one-dimensional. So even after repairing the
  "proper" clause, the infinite-dimensional complement that Paper I §5's
  ampleness arguments were expected to draw from C3 is not available from
  countability alone.

This is a genuine contract error rather than a proof difficulty, and it
matters downstream: **WO-13 and WO-15 must not be written against an
orthogonality-based C3.** Ampleness will have to draw its room from a
structural hypothesis on the accumulated data (for example, that the
stage-`α` data lies in a block `blockB b S` with `Sᶜ` infinite, for which
the base already supplies `PlufWO5.not_finite_block` and the `blockB`
API), not from mere countability.

**Marked minimal repair, supplied under the contracted name.** What
survives, and what a stagewise recursion can actually use, is the
*algebraic* escape lemma:

* `span_ne_top_of_countable`: the span of a countable set of vectors is
  never all of `H`. Proof: write the set as `range f`, exhaust its span by
  the increasing family of finite-dimensional (hence closed, hence proper,
  since `H` is infinite-dimensional) subspaces `span (f '' Iic n)`, and
  apply Baire — no Hilbert-space analysis, in the spirit of the work
  order's standing instruction.
* `exists_notMem_of_countable_closed_proper`: the Baire step in reusable
  form — a countable family of proper closed subspaces never covers `H`.
* `exists_orthogonal_of_countable` (**the contracted name; the form
  supplied**): for every countable `s` and every *finite* `t`, some vector
  escapes `span (s ∪ t)`. This is the "infinite codimension" upgrade, free
  because `s ∪ t` is still countable.
* `orthogonal_ne_bot_of_isClosed_ne_top`: the orthogonal-complement
  statement in the only form in which it is true — for a *closed*
  subspace, properness is exactly nontriviality of the complement.

**Which form was proved, in one line:** the algebraic (Baire) escape form,
not the orthogonal one; the orthogonal one is false in `H`.

## 5. Generality

Two generalizations were cheap and are derived from the concrete
statements, as instructed:

* `mk_eq_continuum_of_hilbertBasis`: `#E = 𝔠` for any real inner product
  space `E` with a `HilbertBasis ℕ ℝ E`, by transporting `mk_H` along
  `b.repr`.
* `mk_continuousLinearMaps_of_hilbertBasis`: likewise `#(E →L[ℝ] E) = 𝔠`,
  by `ContinuousLinearEquiv.arrowCongr`.

Both are hypothesized on the *existence of the ℕ-indexed basis*, which is
the correction the previous two commissions established (separability plus
completeness is refuted by `E = ℝ`). The remaining counts (closed
subspaces, Hilbert bases) would require transporting those *sets* along
the identification, which is more work than the concrete proofs; they were
left concrete, as the work order permits.

## 6. Axiom audit

`#print axioms` is emitted in the file for all 18 items listed in §1;
each reports exactly `[propext, Classical.choice, Quot.sound]`.
