# WO-8 Report — pluf project (Feldman–Wilce), Paper III §§4–5 and Paper I §6

Artifact: `RequestProject/PlufWO8.lean` (contract roll-up) together with the
development modules `RequestProject/PlufWO8/{Limits,Proj,Singular,Additive,Face,BW,Compacts}.lean`.

Toolchain: `leanprover/lean4:v4.28.0`, Mathlib pinned as in `lake-manifest.json`.

## 0. Status

* `lake build` (default targets) succeeds.
* No `sorry`, `admit`, `axiom`, `@[implemented_by]` or `native_decide` occurs
  anywhere in the artifact.
* `#print axioms` is emitted for every completed contract theorem. The build
  emits **133** axiom-audit lines in total — the **115** of the base (WO-1–WO-6)
  roll-ups, all still green, plus the **18** of WO-8. Every one of the 133
  reports exactly `[propext, Classical.choice, Quot.sound]`; nothing outside the
  whitelist appears.
* Quarantine respected: the Blecher–Weaver theory enters only through the
  `PlufWO8.BWPackage` structure of Part E, as named hypotheses.
  Marcus–Spielman–Srivastava does not appear anywhere, and no item needed it.

## 1. Census

### What the base artifact supplied (reused, not rebuilt)

* `PlufWO2`: `Hk`, `evec`, `block`, `supp`, `countable_supp`, `CountableSmall`,
  `DiagInt` — the ℓ²(κ) scaffolding and the smallness predicates.
* `PlufWO3`: `PhiU`, `exists_ulim` (existence of bounded ultrafilter limits),
  `quadratic_flat`, `PhiU_decides`, `PhiU_nonprincipal`.
* `PlufWO6`: `IsState` and its API (`IsState.mono`, `IsState.compress`,
  `IsState.starProjection_le_one`), `IsPluf`, `isPluf_of_criterion`,
  `principal_of_finiteDimensional`, the face machinery.

### What Mathlib supplied

* `Submodule.starProjection` and the orthogonal-projection calculus
  (`starProjection_apply`, minimality of the distance to a complete subspace,
  `HasOrthogonalProjection` for complete/finite-dimensional submodules).
* `LinearMap.mkContinuous`, `Ultrafilter` and `Filter.Tendsto` API,
  `HasSum`/`tsum` API, `IsCompactOperator` and total boundedness of the image
  of a neighbourhood of `0`.

### What had to be built here

* `PlufWO8.Limits`: an explicit `ULim` predicate for the ultrafilter limit of a
  bounded real family, with the arithmetic (uniqueness, additivity, scalar
  multiplication, monotonicity, the bound) needed to make `phiLim` linear and
  bounded; `diag`, `phiLim`, `phiLimCLM`, `isState_phiLimCLM`.
* `PlufWO8.Proj`: the shared projection calculus used throughout —
  `hasOrthogonalProjection_of_isClosed`, `norm_starProjection_le_of_le`,
  `inner_starProjection_le_of_le`, `inner_starProjection_nonneg`,
  `state_starProjection_mono`.
* `PlufWO8.Singular`, `PlufWO8.Additive`, `PlufWO8.Face`, `PlufWO8.BW`: the
  mathematics of Parts B, C, D/F and E respectively.
* `PlufWO8.Compacts`: finite-rank approximation of a compact operator from a
  finite ε/2-net (see item B below); `phiLim_eq_zero_of_range_le`,
  `phiLim_compactOperator_eq_zero`.

### Confirmed absent from Mathlib (consistent with the WO-5/WO-6 censuses)

* Finite-rank approximation of compact operators on a Hilbert space, and the
  `HilbertBasis` assembly/reindexing at a general index type. Neither was
  needed: see item B.

## 2. Elaboration finding (the one structural finding of this commission)

`Submodule.starProjection` carries the instance argument
`[M.HasOrthogonalProjection]`. For a submodule of a complete space this is
synthesized only when a closedness (or finiteness) hypothesis **for that
submodule** is in scope *as a binder*. Several contracted statements form
`M.starProjection` at a point where the relevant closedness is not a binder,
and therefore do **not elaborate**. In each case the contract text is preserved
verbatim in a comment and a marked minimal repair is returned:

| Contract item | Repair |
| --- | --- |
| C1, C2, C3 | added instance binders `[∀ n, (q n).HasOrthogonalProjection]`, `[Q.HasOrthogonalProjection]` |
| `oneSet` | the conjunction `IsClosed M ∧ φ P_M = 1` replaced by the dependent pair `∃ _hc : IsClosed (M : Set E), φ M.starProjection = 1` |
| `BWPackage.excision` | the bounded existential `∃ M ∈ oneSet φ, …` replaced by the corresponding dependent pair |
| E4 | the anonymous arrow `Module.Finite ℝ ↥M → …` replaced by the named binder `∀ (M) (_hM : Module.Finite ℝ ↥M), …` |

Each repair is propositionally the contracted statement; no hypothesis was
weakened and no conclusion was weakened.

No contract item turned out to be **false**; the counterexample branch of the
report-rather-than-repair license was not exercised.

## 3. Item-by-item report

### Part A — the ultrafilter-limit state

* **A1** `PlufWO8.phiLim` is defined in `PlufWO8/Limits.lean` with the contracted
  signature, by WO-3's `exists_ulim` applied to the diagonal
  `α ↦ ⟪T e_α, e_α⟫` with the bound `‖T‖`. The contracted defining property is
  returned as `phiLim_spec`. The countable-completeness argument `hcc` is
  carried exactly as contracted, although WO-3's route makes it unnecessary for
  *existence*; it is genuinely used downstream (Parts B, C, D, F).
* **A2** Bundling shape (prover's choice, reported): the functional is
  `PlufWO8.phiLimCLM`, obtained from `LinearMap.mkContinuous` with constant `1`
  from the bound `|φ T| ≤ ‖T‖`; `PlufWO8.isState_phiLimCLM` is `IsState` of it.
  The contract theorem `isState_phiLim` is the existential form and is
  witnessed by that pair.

### Part B — singularity

* **B1** `phiLim_rankOne_eq_zero`, by the countable-support argument
  (`PlufWO2.countable_supp` against `CountableSmall`).
* **B2** `phiLim_finiteDimensional_eq_zero`, as contracted (finite-dimensional
  projections).
* **Delivered in addition, as invited.** The compact-operator statement the
  paper asserts is returned as `phiLim_compact_eq_zero`, via the intermediate
  finite-rank-*operator* form `phiLim_finiteRank_eq_zero` (Cauchy–Schwarz for
  the form `(A,B) ↦ φ(A*B)` at a null projection).
  **Reported:** no Hilbert basis and no finite-rank-density theorem was needed,
  which matters because Mathlib has neither. Instead, total boundedness of the
  image of the unit ball gives a finite ε/2-net; the orthogonal projection onto
  its span is within ε of the operator precisely because the projection
  minimizes distance (`PlufWO8.exists_finiteDimensional_approx`). Continuity of
  `φ` then finishes. So the compact form was indeed cheap.

### Part C — countable additivity

* **C1** `phiLim_iSup_eq_zero`, returned (with the instance-binder repair).
  **Route report:** the contracted `ε 2⁻ⁿ` estimate is not used. For a positive
  operator, a vanishing `U`-limit of the diagonal already forces the diagonal to
  vanish *identically* on a member of `U`: intersect the countably many members
  `{α | d α ≤ 1/(m+1)}` using countable completeness. On the countable
  intersection the expansion of the diagonal of `Q` is a sum of zeros.
* **C2** `phiLim_iSup`, the `tsum` form, returned **in full** — the bookkeeping
  was not disproportionate. The values `a n = φ(P_{q n})` are nonnegative with
  partial sums bounded by `φ(P_Q)`, hence summable, and the contracted `ε 2⁻ⁿ`
  argument squeezes the diagonal of `Q` between `∑' a ± ε` on a member of `U`.
* **C3** `phiLim_iSup_eq_zero_generic`, the generic-index `<κ`-additive form,
  returned. **Route report:** the contracted countability hypothesis `hctble` is
  **not used**. Countable completeness alone already gives
  `{α | ⟪q i e_α, e_α⟫ = 0} ∈ U` for each single `i`, and the hypothesis `hU`
  intersects these over `ι`; the deliberately weak ε-approximation hypothesis
  then bounds the diagonal of `Q` by every `ε > 0`. `hctble` is retained in the
  statement because the contract asks for it, and produces an unused-variable
  warning that is deliberate. Mathlib offers nothing cleaner than the
  contracted ε-approximation for this shape, so the hypothesis was not
  restated.

### Part D — purity, derived not assumed

* **D1** `phiLim_mem_face`: `phiLim` takes the value 1 at every block projection
  with `S ∈ U`, hence at every closed member of `Φ(U)` by monotonicity of a
  state.
* **D2** `phiLim_pure`, returned in the contracted "uniqueness in the face"
  phrasing. **Route report:** the proof does not go through
  `rsp_all_iff_face_subsingleton`. It establishes more, namely that every state
  in the face of `Φ(U)` *equals* `phiLim` at every operator
  (`PlufWO8.eq_phiLim_of_mem_face`), by flattening (`PlufWO3.quadratic_flat`)
  together with compression (`PlufWO6.IsState.compress`). Extremality in
  Mathlib's `Set.extremePoints` sense is not asserted; WO-6's `face_isFace`
  converts the returned uniqueness into that statement if it is wanted verbatim.

### Part E — Theorem 4.2 (countably additive pure states give plufs)

All four items are returned. `oneSet` and `BWPackage` carry the minimal repairs
of §2; the package bundles exactly the two Blecher–Weaver facts (σ-filtration of
the 1-set, excision) and nothing else. The E-items are proved in
`PlufWO8/BW.lean` inside `namespace Internal` and re-exported by the roll-up, to
keep the roll-up names clash-free.

* **E1** `oneSet_upward` (monotonicity of a state), `oneSet_inf` (from the
  σ-filtration clause), `bot_notMem_oneSet` (properness).
  **Route report:** for properness neither `hφ` nor `[Nontrivial E]` is needed —
  `P_⊥ = 0` and `φ 0 = 0 ≠ 1` for any linear functional. Both are retained as
  contracted.
* **E2** `exists_oneSet_inf_eq_bot`, the paper's excision computation: a nonzero
  `v` in `M ⊓ N` would give `1 = ⟪p P_M p v, v⟫/‖v‖² = φ(P_M)`.
  **Route report:** `hφ` is not needed (only the excision identity is); retained
  as contracted.
* **E3** `isPluf_oneSet`, assembling E1/E2 with WO-6's criterion.
  `[Nontrivial E]` is genuinely needed here, per the WO-6 ratifications.
* **E4** `oneSet_nonprincipal`, with the naming repair of §2.
  **Route report:** `hφ` and `[Nontrivial E]` are not needed here; retained as
  contracted.

The deliberate unused-hypothesis warnings from E1/E2/E4 (and from C3's
`hctble`) are the only warnings the WO-8 modules emit, and each is documented in
the corresponding docstring.

### Part F — assembly at κ

* **F1** `oneSet_phiLim_eq_PhiU`: the 1-set of the limit state is exactly
  `{M | M ∈ Φ(U) ∧ IsClosed M}`. `⊇` is D1. `⊆`: if `φ P_M = 1`, flattening at
  `L = 1` with tolerances `1/(n+1)`, intersected by countable completeness,
  produces a `U`-set whose block is fixed by `P_M`, so `M ∈ Φ(U)`
  (`PlufWO8.mem_PhiU_of_phiLim_starProjection_eq_one`).

## 4. Scalar finding

**No item needed ℂ.** Every argument used only positivity, the quadratic form,
and countable/κ-completeness, exactly as the work order anticipated; the whole
artifact is over ℝ. In particular the excision computation of E2 and the
flattening arguments of D2/F1 are scalar-agnostic as written.

## 5. Recommendation

Nothing in WO-8 required the infrastructure recorded as absent by the WO-5/WO-6
censuses (essential spectrum, `HilbertBasis` assembly and reindexing) — the
compact-operator item, the one place where it might have been expected, was
discharged by a net argument instead. The recommendation of the work order
therefore stands unchanged: **a scoping census WO-7a is the appropriate next
step**, before any proof obligations toward Paper I §5, Paper II Theorem 5.4 and
Propositions 5.5–5.6, or Paper I Proposition 2.3 in odd finite dimension, are
contracted.
