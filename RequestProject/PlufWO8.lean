/-
  PlufWO8.lean — Work Order 8 for the pluf project (Feldman–Wilce).

  Scope: the state-theoretic sections of Paper III, and the Paper I §6
  residue:
    (A) the ultrafilter-limit state φ_U on the bounded operators of
        ℓ²(κ): that it is a state, its value on projections, and the
        diagonal formula;
    (B) singularity: φ_U annihilates the rank-one projections, hence the
        compacts, by κ-completeness against countable supports;
    (C) countable additivity of φ_U (Paper III, Theorem 4.1), and the
        <κ-additive strengthening in the generic index form used
        throughout this project;
    (D) purity of φ_U, obtained from WO-6's face machinery rather than
        assumed: the face of Φ(U) is a singleton and φ_U belongs to it;
    (E) Theorem 4.2 (countably additive pure states give plufs),
        parametrized by the Blecher–Weaver package — regularity,
        σ-filtration of the 1-set, excision, and determination by the
        1-set — supplied as named hypotheses, so the theorem is ZFC;
    (F) the nonprincipality clause and the Paper I §6 restatement.

  Quarantined classical imports, as named hypotheses only: the
  Blecher–Weaver excision/regularity package (Part E). Nothing else.
  Marcus–Spielman–Srivastava does NOT appear: the point of Paper III §4 is
  that the existence statements avoid it.

  Base: the WO-6 artifact (CI runs #1–#6 green, 115 theorems). Reuse
  PlufWO1–PlufWO6 freely — in particular `PlufWO2.{Hk, evec, block,
  supp, countable_supp}`, `PlufWO3.{PhiU, exists_ulim, PhiU_decides,
  PhiU_nonprincipal}`, `PlufWO6.{IsState, stateFace, face_nonempty,
  face_iff_sandwich, rsp_all_iff_face_subsingleton, maximality_criterion,
  principal_of_finiteDimensional}`, and `PlufWO6.States` API
  (`IsState.mono`, `IsState.compress`, `IsState.starProjection_le_one`).
  All 115 prior theorems must remain green.

  NOTE ON SCALARS. The project works over ℝ. Paper III's §§4–5 are stated
  over ℂ in the literature; the arguments contracted here are
  scalar-agnostic (they use only positivity, the quadratic form, and
  countable/κ-completeness). Report if any item genuinely needs ℂ.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  ---------------------------------------------------------------------
  DELIVERY NOTE (WO-8).

  This file is the contract roll-up. The mathematics is developed in the
  modules imported below:

    RequestProject.PlufWO8.Limits    the predicate `ULim` and its
                                     calculus; `phiLim`, `phiLimCLM`
                                     and `IsState` of it (Part A)
    RequestProject.PlufWO8.Proj      the shared projection calculus
    RequestProject.PlufWO8.Singular  the countable-support argument
                                     (Part B)
    RequestProject.PlufWO8.Additive  countable additivity (Part C)
    RequestProject.PlufWO8.Face      the face and purity computations,
                                     and the block identification
                                     (Parts D and F)
    RequestProject.PlufWO8.BW        `oneSet`, `BWPackage` and
                                     Theorem 4.2 (Part E)

  CENSUS AND FINDINGS (see also `WO8-REPORT.md`).

  1. Elaboration finding (affects C1, C2, C3, `oneSet`, `BWPackage`,
     E1's upward clause and E4's singularity hypothesis).
     `Submodule.starProjection` carries the instance argument
     `[M.HasOrthogonalProjection]`, which for a submodule of a complete
     space is synthesized only when a closedness (or finiteness)
     hypothesis for that submodule is in scope as a *binder*. Several
     contracted statements form `M.starProjection` for a submodule whose
     closedness is not in scope at that point, and therefore do not
     elaborate. Each such statement is preserved verbatim in a comment
     and returned in a marked minimal repair: an added instance binder,
     or the replacement of a bounded existential/conjunction by the
     equivalent dependent pair.

  2. `phiLim` is defined (in `PlufWO8.Limits`) by WO-3's `exists_ulim`
     applied to the diagonal, with the bound `‖T‖`; `hcc` is carried as
     contracted although WO-3's route makes it unnecessary for existence.

  3. A2 bundling: the functional is `PlufWO8.phiLimCLM`, obtained from
     `LinearMap.mkContinuous` with constant `1`, and `IsState` of it is
     `PlufWO8.isState_phiLimCLM`.

  4. C1 and C3 are proved by a route shorter than the contracted
     `ε 2⁻ⁿ` argument: for a positive operator, a vanishing `U`-limit of
     the diagonal already forces the diagonal to vanish identically on a
     member of `U` (intersect the countably many sets
     `{α | d α ≤ 1/(n+1)}`). C3's countability hypothesis `hctble` is
     consequently not used; it is retained because the contract asks for
     it. C2 is returned in full, by the `ε 2⁻ⁿ` argument.

  5. D2 is returned in the contracted "uniqueness in the face" phrasing.
     The proof establishes more, namely that every state in the face of
     `Φ(U)` *equals* `phiLim` (`PlufWO8.eq_phiLim_of_mem_face`); the
     route is WO-3's `quadratic_flat` together with
     `PlufWO6.IsState.compress`, and does not pass through
     `rsp_all_iff_face_subsingleton`. `Set.extremePoints` is not used.

  6. B2 is returned as contracted (finite-rank projections). The
     compact-operator statement the paper actually asserts is returned in
     addition, as `phiLim_compact_eq_zero` below, together with the
     intermediate finite-rank-operator form
     `phiLim_finiteRank_eq_zero`. REPORTED: no Hilbert basis and no
     finite-rank-density theorem was needed. Mathlib has neither the
     finite-rank approximation of compact operators nor the
     `HilbertBasis` assembly recorded as absent by the WO-5/WO-6
     censuses; instead, total boundedness of the image of the unit ball
     supplies a finite `ε/2`-net, and the projection onto its span is
     within `ε` of the operator because the orthogonal projection
     minimizes distance (`PlufWO8.exists_finiteDimensional_approx`).

  7. Scalars: no item needed ℂ. Everything below is over ℝ.
-/
import RequestProject.PlufWO8.Face
import RequestProject.PlufWO8.BW
import RequestProject.PlufWO8.Compacts

open Set PlufWO2 PlufWO3 PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {κ : Type*} [LinearOrder κ]

/-! ### Part A: the ultrafilter-limit state -/

/-  A1, contract statement, preserved verbatim:

noncomputable def phiLim (U : Ultrafilter κ) (hcc : PlufWO3.CountablyComplete U)
    (T : Hk κ →L[ℝ] Hk κ) : ℝ

    Returned as `PlufWO8.phiLim` in `RequestProject.PlufWO8.Limits`, with
    the same signature; `phiLim_spec` below is the contracted defining
    property. -/

/-- A1. The defining property of `phiLim`: it is the `U`-limit of the
    diagonal. -/
theorem phiLim_spec (U : Ultrafilter κ) (hcc : PlufWO3.CountablyComplete U)
    (T : Hk κ →L[ℝ] Hk κ) :
    ∀ ε > 0, {α | |inner (𝕜 := ℝ) (T (evec α)) (evec α) - phiLim U hcc T| ≤ ε} ∈ U :=
  uLim_phiLim (hcc := hcc) T

/-- A2. `phiLim` is a state in the sense of WO-6 (`PlufWO6.IsState`),
    bundled as `PlufWO8.phiLimCLM` via `LinearMap.mkContinuous` with the
    bound `|φ T| ≤ ‖T‖`. -/
theorem isState_phiLim (U : Ultrafilter κ) (hcc : PlufWO3.CountablyComplete U) :
    ∃ φ : (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ, PlufWO6.IsState φ ∧
      ∀ T, φ T = phiLim U hcc T :=
  ⟨phiLimCLM U hcc, isState_phiLimCLM, fun _ => rfl⟩

/-! ### Part B: singularity -/

/-- B1. The limit state annihilates the rank-one projections: the
    diagonal of the projection onto `ℝ ∙ v` is supported on the
    (countable) support of `v`, which is `U`-small. -/
theorem phiLim_rankOne_eq_zero (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (hsmall : PlufWO2.CountableSmall U) (v : Hk κ) :
    phiLim U hcc ((ℝ ∙ v).starProjection) = 0 :=
  phiLim_starProjection_singleton_eq_zero (hcc := hcc) hsmall v

/-- B2 (singularity, finite-rank form). `phiLim` annihilates every
    projection onto a finite-dimensional subspace. -/
theorem phiLim_finiteDimensional_eq_zero (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (hsmall : PlufWO2.CountableSmall U)
    (M : Submodule ℝ (Hk κ)) (hM : Module.Finite ℝ ↥M) :
    phiLim U hcc M.starProjection = 0 :=
  phiLim_starProjection_finite_eq_zero (hcc := hcc) hsmall M hM

/-! ### Part C: countable additivity -/

/-  C1, contract statement, preserved verbatim:

theorem phiLim_iSup_eq_zero (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (q : ℕ → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    (hq0 : ∀ n, phiLim U hcc (q n).starProjection = 0)
    (hexp : ∀ x : Hk κ, HasSum (fun n => inner (𝕜 := ℝ) ((q n).starProjection x) x)
      (inner (𝕜 := ℝ) (Q.starProjection x) x)) :
    phiLim U hcc Q.starProjection = 0

    Does not elaborate (finding 1): the projections `(q n).starProjection`
    and `Q.starProjection` are formed for submodules with no closedness
    hypothesis in scope. Marked minimal repair: the two instance binders
    `[∀ n, (q n).HasOrthogonalProjection]` and
    `[Q.HasOrthogonalProjection]`. -/

/-- C1 (Paper III, Theorem 4.1, countable additivity), minimal repair:
    instance binders for the projections. Pairwise orthogonal null
    projections expanding to `Q` force `phiLim Q = 0`.

    Route report: instead of the contracted `ε 2⁻ⁿ` estimate, the proof
    uses that for each `n` the set `{α | ⟪q n e_α, e_α⟫ = 0}` is already
    a member of `U` (countable completeness applied to the sets
    `{α | ⟪q n e_α, e_α⟫ ≤ 1/(m+1)}`); on the countable intersection the
    expansion of the diagonal of `Q` is a sum of zeros. -/
theorem phiLim_iSup_eq_zero (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (q : ℕ → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    [∀ n, (q n).HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hq0 : ∀ n, phiLim U hcc (q n).starProjection = 0)
    (hexp : ∀ x : Hk κ, HasSum (fun n => inner (𝕜 := ℝ) ((q n).starProjection x) x)
      (inner (𝕜 := ℝ) (Q.starProjection x) x)) :
    phiLim U hcc Q.starProjection = 0 :=
  phiLim_starProjection_eq_zero_of_hasSum (hcc := hcc) q Q hq0 hexp

/-  C2, contract statement, preserved verbatim:

theorem phiLim_iSup (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (q : ℕ → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    (hexp : ∀ x : Hk κ, HasSum (fun n => inner (𝕜 := ℝ) ((q n).starProjection x) x)
      (inner (𝕜 := ℝ) (Q.starProjection x) x)) :
    phiLim U hcc Q.starProjection = ∑' n, phiLim U hcc (q n).starProjection

    Same elaboration finding, same marked minimal repair. -/

/-- C2 (countable additivity, general form), minimal repair: instance
    binders for the projections. Returned in full: the values
    `a n = phiLim (q n)` are nonnegative with partial sums bounded by
    `phiLim Q` (hence summable), and the `ε 2⁻ⁿ` argument squeezes the
    diagonal of `Q` between `∑' a ± ε` on a member of `U`. -/
theorem phiLim_iSup (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (q : ℕ → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    [∀ n, (q n).HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hexp : ∀ x : Hk κ, HasSum (fun n => inner (𝕜 := ℝ) ((q n).starProjection x) x)
      (inner (𝕜 := ℝ) (Q.starProjection x) x)) :
    phiLim U hcc Q.starProjection = ∑' n, phiLim U hcc (q n).starProjection :=
  phiLim_starProjection_tsum (hcc := hcc) q Q hexp

/-  C3, contract statement, preserved verbatim:

theorem phiLim_iSup_eq_zero_generic (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U) {ι : Type*}
    (hU : ∀ s : ι → Set κ, (∀ i, s i ∈ U) → (⋂ i, s i) ∈ U)
    (q : ι → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    (hq0 : ∀ i, phiLim U hcc (q i).starProjection = 0)
    (hctble : ∀ α : κ, {i | inner (𝕜 := ℝ) ((q i).starProjection (evec α)) (evec α) ≠ 0}.Countable)
    (hexp : ∀ x : Hk κ, ∀ ε > 0, ∃ F : Finset ι,
      inner (𝕜 := ℝ) (Q.starProjection x) x
        ≤ (∑ i ∈ F, inner (𝕜 := ℝ) ((q i).starProjection x) x) + ε) :
    phiLim U hcc Q.starProjection = 0

    Same elaboration finding, same marked minimal repair. -/

/-- C3 (the `<κ`-additive form, generic index), minimal repair: instance
    binders for the projections.

    Route report: `hctble` is not used. Countable completeness alone
    already gives `{α | ⟪q i e_α, e_α⟫ = 0} ∈ U` for each single `i`, and
    `hU` intersects these over `ι`; the ε-approximation hypothesis then
    bounds the diagonal of `Q` by every `ε > 0`. The hypothesis is
    retained because the contract asks for it. -/
theorem phiLim_iSup_eq_zero_generic (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U) {ι : Type*}
    (hU : ∀ s : ι → Set κ, (∀ i, s i ∈ U) → (⋂ i, s i) ∈ U)
    (q : ι → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    [∀ i, (q i).HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hq0 : ∀ i, phiLim U hcc (q i).starProjection = 0)
    (hctble : ∀ α : κ, {i | inner (𝕜 := ℝ) ((q i).starProjection (evec α)) (evec α) ≠ 0}.Countable)
    (hexp : ∀ x : Hk κ, ∀ ε > 0, ∃ F : Finset ι,
      inner (𝕜 := ℝ) (Q.starProjection x) x
        ≤ (∑ i ∈ F, inner (𝕜 := ℝ) ((q i).starProjection x) x) + ε) :
    phiLim U hcc Q.starProjection = 0 :=
  phiLim_starProjection_eq_zero_generic (hcc := hcc) hU q Q hq0 hexp

/-! ### Part D: purity, from the face -/

/-- D1. `phiLim` lies in the state face of `Φ(U)`: it takes the value 1
    at every block projection with `S ∈ U`, hence at every member by
    monotonicity. -/
theorem phiLim_mem_face (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U) (φ : (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ)
    (hφ : PlufWO6.IsState φ) (hval : ∀ T, φ T = phiLim U hcc T)
    (M : Submodule ℝ (Hk κ)) (hM : M ∈ PhiU U) (hMc : IsClosed (M : Set (Hk κ))) :
    φ M.starProjection = 1 := by
  haveI : M.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hMc
  exact eq_one_of_mem_PhiU (hcc := hcc) φ hφ hval M hM

/-- D2 (purity of φ_U; Paper III, Theorem 4.1, purity clause). Any two
    states taking the value `1` on the closed members of `Φ(U)` coincide:
    the face of `Φ(U)` is a singleton, and (by D1) `phiLim` is its
    element, so `phiLim` is pure.

    Route report: rather than `rsp_all_iff_face_subsingleton`, the proof
    shows directly that a state in the face agrees with `phiLim` at every
    operator (`PlufWO8.eq_phiLim_of_mem_face`), by flattening
    (`PlufWO3.quadratic_flat`) and compression
    (`PlufWO6.IsState.compress`). Extremality in Mathlib's
    `Set.extremePoints` sense is not asserted; WO-6's `face_isFace`
    converts this uniqueness into the extremality statement. -/
theorem phiLim_pure (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U) (hdiag : PlufWO2.DiagInt U)
    (hsmall : PlufWO2.CountableSmall U)
    (φ ψ : (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ)
    (hφ : PlufWO6.IsState φ) (hψ : PlufWO6.IsState ψ)
    (hfφ : ∀ M ∈ PhiU U, ∀ hM : IsClosed (M : Set (Hk κ)), φ M.starProjection = 1)
    (hfψ : ∀ M ∈ PhiU U, ∀ hM : IsClosed (M : Set (Hk κ)), ψ M.starProjection = 1) :
    φ = ψ := by
  ext T
  rw [eq_phiLim_of_mem_face (hcc := hcc) hdiag hsmall φ hφ hfφ T,
    eq_phiLim_of_mem_face (hcc := hcc) hdiag hsmall ψ hψ hfψ T]

/-! ### Part E: countably additive pure states give plufs -/

section BlecherWeaver

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-  The contract statements of `oneSet` and of the `BWPackage` field
    `excision` are preserved verbatim in `RequestProject.PlufWO8.BW`,
    where the marked minimal repairs (dependent pairs in place of the
    conjunction and of the bounded existential) are made; see finding 1.
    `PlufWO8.oneSet` and `PlufWO8.BWPackage` below are those. -/

/-  E1 (upward clause), contract statement, preserved verbatim:

theorem oneSet_upward (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (M : Submodule ℝ E) (hM : M ∈ oneSet φ) (N : Submodule ℝ E)
    (hN : IsClosed (N : Set E)) (hMN : M ≤ N) : N ∈ oneSet φ

    Elaborates once `oneSet` is repaired; returned verbatim. -/

/-- E1 (upward closure of the 1-set), by monotonicity of a state. -/
theorem oneSet_upward (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (M : Submodule ℝ E) (hM : M ∈ oneSet φ) (N : Submodule ℝ E)
    (hN : IsClosed (N : Set E)) (hMN : M ≤ N) : N ∈ oneSet φ :=
  Internal.oneSet_upward hφ hM hN hMN

/-- E1 (binary meets), from the σ-filtration clause of the package. -/
theorem oneSet_inf (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hBW : BWPackage φ) (M : Submodule ℝ E) (hM : M ∈ oneSet φ)
    (N : Submodule ℝ E) (hN : N ∈ oneSet φ) : M ⊓ N ∈ oneSet φ :=
  Internal.oneSet_inf hφ hBW hM hN

/-- E1 (properness). Route report: neither `hφ` nor `[Nontrivial E]` is
    needed — `P_⊥ = 0` and `φ 0 = 0 ≠ 1` for any linear functional. Both
    are retained because the contract asks for them. -/
theorem bot_notMem_oneSet (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    [Nontrivial E] : (⊥ : Submodule ℝ E) ∉ oneSet φ :=
  Internal.bot_notMem_oneSet

/-- E2 (the excision step; Paper III, Theorem 4.2, maximality). If a
    closed subspace `M` is not in the 1-set, an excising projection for
    `P_M` gives a member of the 1-set meeting `M` trivially: a nonzero
    `v` in the intersection would give `1 = ⟪p P_M p v, v⟫/‖v‖² = φ(P_M)`.
    Route report: `hφ` is not needed (only the excision identity is), but
    is retained as contracted. -/
theorem exists_oneSet_inf_eq_bot (φ : (E →L[ℝ] E) →L[ℝ] ℝ)
    (hφ : PlufWO6.IsState φ) (hBW : BWPackage φ)
    (M : Submodule ℝ E) (hMc : IsClosed (M : Set E)) (hM : M ∉ oneSet φ) :
    ∃ N ∈ oneSet φ, M ⊓ N = ⊥ :=
  Internal.exists_oneSet_inf_eq_bot hBW hMc hM

/-- E3 (Theorem 4.2). The 1-set of a state satisfying the package is a
    pluf, in WO-6's sense `PlufWO6.IsPluf`. -/
theorem isPluf_oneSet (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hBW : BWPackage φ) [Nontrivial E] :
    PlufWO6.IsPluf (oneSet φ) :=
  Internal.isPluf_oneSet hφ hBW

/-  E4, contract statement, preserved verbatim:

theorem oneSet_nonprincipal (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hBW : BWPackage φ) [Nontrivial E]
    (hsing : ∀ M : Submodule ℝ E, Module.Finite ℝ ↥M → φ M.starProjection = 0) :
    ∀ v : E, v ≠ 0 → ∃ M ∈ oneSet φ, v ∉ M

    Does not elaborate (finding 1): in `Module.Finite ℝ ↥M → …` the
    finiteness hypothesis is an arrow, not a binder, so it is not in
    scope for the instance search at `M.starProjection`. Marked minimal
    repair: name the hypothesis, `∀ (M) (_hM : Module.Finite ℝ ↥M), …`. -/

/-- E4 (nonprincipality for singular states), minimal repair: the
    finiteness hypothesis is named. If `φ` annihilates every
    finite-dimensional projection, its 1-set contains no line, hence the
    pluf is nonprincipal in the sense that
    `PlufWO6.principal_of_finiteDimensional` excludes. Route report:
    `hφ` and `[Nontrivial E]` are not needed, but are retained as
    contracted. -/
theorem oneSet_nonprincipal (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hBW : BWPackage φ) [Nontrivial E]
    (hsing : ∀ (M : Submodule ℝ E) (_hM : Module.Finite ℝ ↥M), φ M.starProjection = 0) :
    ∀ v : E, v ≠ 0 → ∃ M ∈ oneSet φ, v ∉ M :=
  Internal.oneSet_nonprincipal hBW hsing

end BlecherWeaver

/-! ### Part F: assembly at κ (Paper I §6 restatement) -/

/-- F1. At a measurable-type ultrafilter, the 1-set of the limit state is
    exactly the block filter `Φ(U)` (intersected with closedness) — the
    statement Paper I's §6 summarizes and Paper III's §4 proves.

    (`⊇` is D1. `⊆`: if `φ P_M = 1` then flattening at `L = 1` with
    tolerances `1/(n+1)`, intersected by countable completeness, produces
    a `U`-set whose block is fixed by `P_M`, so `M ∈ Φ(U)`.) -/
theorem oneSet_phiLim_eq_PhiU (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U) (hdiag : PlufWO2.DiagInt U)
    (hsmall : PlufWO2.CountableSmall U)
    (φ : (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hval : ∀ T, φ T = phiLim U hcc T) :
    oneSet φ = {M | M ∈ PhiU U ∧ IsClosed (M : Set (Hk κ))} := by
  ext M
  constructor
  · intro hM
    have hMc : IsClosed (M : Set (Hk κ)) := isClosed_of_mem_oneSet hM
    haveI : M.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hMc
    have h1 : phiLim U hcc M.starProjection = 1 := by
      rw [← hval]
      exact starProjection_eq_one_of_mem_oneSet hM
    exact ⟨mem_PhiU_of_phiLim_starProjection_eq_one (hcc := hcc) hdiag hsmall M h1, hMc⟩
  · rintro ⟨hmem, hMc⟩
    haveI : M.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hMc
    exact mem_oneSet hMc (eq_one_of_mem_PhiU (hcc := hcc) φ hφ hval M hmem)

/-! ### Delivered in addition to the contract -/

/-- Strengthening of B2 (reported): `phiLim` annihilates every operator
    with finite-dimensional range, not merely the projections.
    (Cauchy–Schwarz for the form `(A, B) ↦ φ(A* B)` at the null
    projection `P_M`.) -/
theorem phiLim_finiteRank_eq_zero (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (hsmall : PlufWO2.CountableSmall U)
    (M : Submodule ℝ (Hk κ)) (hM : Module.Finite ℝ ↥M)
    (T : Hk κ →L[ℝ] Hk κ) (hrange : ∀ x, T x ∈ M) :
    phiLim U hcc T = 0 :=
  phiLim_eq_zero_of_range_le (hcc := hcc) hsmall hM hrange

/-- The compact-operator form of Part B, delivered in addition to the
    contracted finite-rank form: `phiLim` vanishes on the compacts, as
    Paper III states. (Finite-rank approximation via a finite net of the
    image of the unit ball; see finding 6.) -/
theorem phiLim_compact_eq_zero (U : Ultrafilter κ)
    (hcc : PlufWO3.CountablyComplete U)
    (hsmall : PlufWO2.CountableSmall U)
    (T : Hk κ →L[ℝ] Hk κ) (hT : IsCompactOperator T) :
    phiLim U hcc T = 0 :=
  phiLim_compactOperator_eq_zero (hcc := hcc) hsmall T hT

/-! ### Axiom audit for the WO-8 contract theorems -/

#print axioms phiLim_spec
#print axioms isState_phiLim
#print axioms phiLim_rankOne_eq_zero
#print axioms phiLim_finiteDimensional_eq_zero
#print axioms phiLim_iSup_eq_zero
#print axioms phiLim_iSup
#print axioms phiLim_iSup_eq_zero_generic
#print axioms phiLim_mem_face
#print axioms phiLim_pure
#print axioms oneSet_upward
#print axioms oneSet_inf
#print axioms bot_notMem_oneSet
#print axioms exists_oneSet_inf_eq_bot
#print axioms isPluf_oneSet
#print axioms oneSet_nonprincipal
#print axioms oneSet_phiLim_eq_PhiU
#print axioms phiLim_finiteRank_eq_zero
#print axioms phiLim_compact_eq_zero

end PlufWO8
