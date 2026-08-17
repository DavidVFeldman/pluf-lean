/-
  PlufWO13/Basic.lean — Work Order 13: operator-free infrastructure.

  Generic Hilbert-space material used by the contract file
  `RequestProject/PlufWO13.lean`: elementary identities for orthogonal
  projections, the emptiness of the (Weyl-sequence) essential spectrum in
  finite dimensions, and the finite-codimension bookkeeping that translates
  the contract's quotient hypothesis
  `Module.Finite ℝ (↥V ⧸ W.comap V.subtype)` into the two forms the proofs
  consume (finite-dimensionality of the orthocomplement of `W` inside `V`,
  both as a subspace of `↥V` and as the subspace `V ⊓ Wᗮ` of the ambient
  space).

  Nothing here mentions the operator `T`; the namespace is `PlufWO13.Aux`.
-/
import RequestProject.PlufWO10

open Set

namespace PlufWO13.Aux

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Elementary identities for orthogonal projections -/

theorem inner_starProjection_self (K : Submodule ℝ E) [K.HasOrthogonalProjection] (y : E) :
    inner (𝕜 := ℝ) (K.starProjection y) y = ‖K.starProjection y‖ ^ 2 := by
  have h0 : inner (𝕜 := ℝ) (K.starProjection y) (y - K.starProjection y) = 0 :=
    (Submodule.mem_orthogonal K _).mp (K.sub_starProjection_mem_orthogonal y) _
      (K.starProjection_apply_mem y)
  have hsub := inner_sub_right (𝕜 := ℝ) (K.starProjection y) y (K.starProjection y)
  rw [h0] at hsub
  have hself : inner (𝕜 := ℝ) (K.starProjection y) (K.starProjection y)
      = ‖K.starProjection y‖ ^ 2 := real_inner_self_eq_norm_sq _
  linarith

theorem norm_sub_starProjection_sq (K : Submodule ℝ E) [K.HasOrthogonalProjection] (y : E) :
    ‖y - K.starProjection y‖ ^ 2 = ‖y‖ ^ 2 - ‖K.starProjection y‖ ^ 2 := by
  have hy : K.starProjection y + (y - K.starProjection y) = y := by abel
  have h0 : inner (𝕜 := ℝ) (K.starProjection y) (y - K.starProjection y) = 0 :=
    (Submodule.mem_orthogonal K _).mp (K.sub_starProjection_mem_orthogonal y) _
      (K.starProjection_apply_mem y)
  have hnorm := norm_add_sq_real (K.starProjection y) (y - K.starProjection y)
  rw [hy, h0] at hnorm
  linarith

theorem norm_starProjection_le (K : Submodule ℝ E) [K.HasOrthogonalProjection] (y : E) :
    ‖K.starProjection y‖ ≤ ‖y‖ := by
  have h := norm_sub_starProjection_sq K y
  nlinarith [norm_nonneg (y - K.starProjection y), norm_nonneg y,
    norm_nonneg (K.starProjection y)]

/-- Projecting first onto a larger subspace changes nothing. -/
theorem starProjection_starProjection_of_le {W V : Submodule ℝ E}
    [W.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hWV : W ≤ V) (z : E) :
    W.starProjection (V.starProjection z) = W.starProjection z := by
  have hmem : z - V.starProjection z ∈ Wᗮ :=
    (Submodule.orthogonal_le hWV) (V.sub_starProjection_mem_orthogonal z)
  have h0 : W.starProjection (z - V.starProjection z) = 0 :=
    (W.starProjection_apply_eq_zero_iff).mpr hmem
  have h := map_sub (W.starProjection) z (V.starProjection z)
  rw [h0] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The difference of the projections onto `W ≤ V` lands in `V ⊓ Wᗮ`. -/
theorem sub_starProjection_mem_inf_orthogonal {W V : Submodule ℝ E}
    [W.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hWV : W ≤ V) (z : E) :
    V.starProjection z - W.starProjection z ∈ V ⊓ Wᗮ := by
  refine ⟨Submodule.sub_mem _ (V.starProjection_apply_mem z) (hWV (W.starProjection_apply_mem z)),
    ?_⟩
  simp only [SetLike.mem_coe]
  rw [Submodule.mem_orthogonal']
  intro w hw
  have h1 : inner (𝕜 := ℝ) (V.starProjection z) w = inner (𝕜 := ℝ) z w := by
    rw [V.inner_starProjection_left_eq_right z w,
      (V.starProjection_eq_self_iff).mpr (hWV hw)]
  have h2 : inner (𝕜 := ℝ) (W.starProjection z) w = inner (𝕜 := ℝ) z w := by
    rw [W.inner_starProjection_left_eq_right z w, (W.starProjection_eq_self_iff).mpr hw]
  rw [inner_sub_left, h1, h2, sub_self]

/-! ### The essential spectrum is empty in finite dimensions -/

/-- In a finite-dimensional space there is no weakly null sequence of unit
    vectors, so the Weyl-sequence essential spectrum of every operator is
    empty. -/
theorem essSpec_eq_empty_of_finiteDimensional [CompleteSpace E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) : PlufWO9.essSpec A = ∅ := by
  ext lam
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx1, hxw, -⟩
  have hfin : Module.Finite ℝ ↥(⊤ : Submodule ℝ E) := by
    have : FiniteDimensional ℝ ↥(⊤ : Submodule ℝ E) := inferInstance
    exact this
  have h := PlufWO9.tendsto_norm_proj_finiteDimensional_of_weaklyNull
    (⊤ : Submodule ℝ E) hfin x hxw
  have hx : ∀ n, ‖(⊤ : Submodule ℝ E).starProjection (x n)‖ = 1 := by
    intro n
    rw [Submodule.starProjection_top]
    simpa using hx1 n
  simp only [hx] at h
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at h01

end Hilbert

/-! ### Finite codimension bookkeeping -/

section FinCodim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The orthocomplement, inside `↥V`, of the copy of `W` in `V`, is
    finite-dimensional as soon as `W` has finite codimension in `V`. -/
theorem finite_orthogonal_comap {W V : Submodule ℝ E} (hW : IsClosed (W : Set E))
    (hV : IsClosed (V : Set E))
    (hfc : Module.Finite ℝ (↥V ⧸ (W.comap V.subtype))) :
    haveI : CompleteSpace ↥V := hV.completeSpace_coe
    Module.Finite ℝ ↥((W.comap V.subtype)ᗮ) := by
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  haveI hcl : IsClosed ((W.comap V.subtype : Submodule ℝ ↥V) : Set ↥V) := by
    have : ((W.comap V.subtype : Submodule ℝ ↥V) : Set ↥V) = V.subtype ⁻¹' (W : Set E) := rfl
    rw [this]
    exact hW.preimage (by continuity)
  haveI : CompleteSpace ↥(W.comap V.subtype) := hcl.completeSpace_coe
  have hcompl : IsCompl (W.comap V.subtype) ((W.comap V.subtype)ᗮ) :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  exact Module.Finite.equiv (Submodule.quotientEquivOfIsCompl _ _ hcompl)

/-- The same statement, transported to the ambient space: `V ⊓ Wᗮ` is
    finite-dimensional. -/
theorem finite_inf_orthogonal {W V : Submodule ℝ E} (hW : IsClosed (W : Set E))
    (hV : IsClosed (V : Set E)) (hWV : W ≤ V)
    (hfc : Module.Finite ℝ (↥V ⧸ (W.comap V.subtype))) :
    Module.Finite ℝ ↥(V ⊓ Wᗮ) := by
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  have hfin := finite_orthogonal_comap hW hV hfc
  have hmap : Submodule.map V.subtype ((W.comap V.subtype)ᗮ) = V ⊓ Wᗮ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Submodule.mem_inf]
      refine ⟨x.2, ?_⟩
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hwV : (⟨w, hWV hw⟩ : ↥V) ∈ W.comap V.subtype := hw
      have := (Submodule.mem_orthogonal _ x).mp hx ⟨w, hWV hw⟩ hwV
      simpa [Submodule.coe_inner] using this
    · rintro ⟨hzV, hzW⟩
      refine ⟨⟨z, hzV⟩, ?_, rfl⟩
      show (⟨z, hzV⟩ : ↥V) ∈ (W.comap V.subtype)ᗮ
      rw [Submodule.mem_orthogonal]
      rintro ⟨w, hwV⟩ hw
      have : inner (𝕜 := ℝ) w z = 0 := (Submodule.mem_orthogonal _ z).mp hzW w hw
      simpa [Submodule.coe_inner] using this
  have := Module.Finite.equiv
    (Submodule.equivMapOfInjective V.subtype (Submodule.injective_subtype V)
      ((W.comap V.subtype)ᗮ))
  rw [hmap] at this
  exact this

omit [CompleteSpace E] in
/-- If `N` has finite codimension in the whole space, then `K ⊓ N` has finite
    codimension in `K`. -/
theorem finite_quotient_of_finite_quotient {K N : Submodule ℝ E}
    (h : Module.Finite ℝ (E ⧸ N)) :
    Module.Finite ℝ (↥K ⧸ ((K ⊓ N).comap K.subtype)) := by
  have hle : ((K ⊓ N).comap K.subtype) ≤ Submodule.comap K.subtype N := by
    intro x hx
    exact hx.2
  set f : (↥K ⧸ ((K ⊓ N).comap K.subtype)) →ₗ[ℝ] (E ⧸ N) :=
    Submodule.mapQ _ _ K.subtype hle with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H k =>
      have hk : (k : E) ∈ N := by
        have : f (Submodule.Quotient.mk k) = 0 := hx
        rw [hf, Submodule.mapQ_apply] at this
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      have : k ∈ ((K ⊓ N).comap K.subtype) := ⟨k.2, hk⟩
      exact (Submodule.Quotient.mk_eq_zero _).mpr this
  haveI : IsNoetherian ℝ (E ⧸ N) := by
    haveI : Module.Finite ℝ (E ⧸ N) := h
    infer_instance
  exact Module.Finite.of_injective f hinj

end FinCodim

end PlufWO13.Aux
