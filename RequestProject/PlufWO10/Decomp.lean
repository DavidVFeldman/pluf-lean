/-
  PlufWO10/Decomp.lean — Work Order 10, auxiliary machinery for Part B.

  Two ingredients that the contract file consumes:

  * `PlufWO10.exists_hilbertBasis_of_orthogonal_family`, the variant of
    WO-9's D4 (`PlufWO9.exists_countable_hilbertBasis_of_decomposition`)
    whose span hypothesis is *density* — in the equivalent form
    `(⨆ n, N n)ᗮ = ⊥` — rather than the algebraic identity
    `⨆ n, N n = ⊤`.  A decomposition of a Hilbert space into an infinite
    orthogonal family of closed subspaces never satisfies the algebraic
    form, so D4 as printed cannot be applied to the chain decomposition of
    Part B; the proof below is WO-9's, with the one use of `hspan`
    replaced.  Together with the `ℕ`-indexed refinement
    `exists_hilbertBasis_nat_of_orthogonal_family` this is what Part B
    consumes.

  * `PlufWO10.eq_blockB_of_basis_mem_or_orthogonal`: a closed subspace each
    of whose basis vectors lies either in it or in its orthocomplement is
    the block of the set of the former.
-/
import RequestProject.PlufWO9

open Set

namespace PlufWO10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### From an orthogonal family with dense span to a Hilbert basis -/

/-- The density variant of WO-9's D4: a countable family of pairwise
    orthogonal closed subspaces whose join is *dense* (stated as
    `(⨆ n, N n)ᗮ = ⊥`) carries a Hilbert basis each of whose vectors lies
    in one of the subspaces. -/
theorem exists_hilbertBasis_of_orthogonal_family [TopologicalSpace.SeparableSpace E]
    (N : ℕ → Submodule ℝ E) (hcl : ∀ n, IsClosed ((N n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ N m, ∀ y ∈ N n, inner (𝕜 := ℝ) x y = 0)
    (hperp : (⨆ n, N n)ᗮ = ⊥) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E), ∀ i, ∃ n, b i ∈ N n := by
  classical
  haveI hcomp : ∀ n, CompleteSpace ↥(N n) := fun n => (hcl n).completeSpace_coe
  have h : ∀ n, ∃ (w : Set ↥(N n)) (b : HilbertBasis w ℝ ↥(N n)), ⇑b = ((↑) : w → ↥(N n)) :=
    fun n => exists_hilbertBasis ℝ ↥(N n)
  choose w bb hbb using h
  have hworth : ∀ n, Orthonormal ℝ ((↑) : w n → ↥(N n)) := by
    intro n; rw [← hbb n]; exact (bb n).orthonormal
  have hcount : ∀ n, (w n).Countable := fun n => PlufWO9.countable_of_orthonormal (w n) (hworth n)
  haveI : ∀ n, Countable ↥(w n) := fun n => (hcount n).to_subtype
  let J : Type _ := Σ n : ℕ, ↥(w n)
  haveI : Countable J := by infer_instance
  let v : J → E := fun p => ((p.2 : ↥(N p.1)) : E)
  have hvmem : ∀ p : J, v p ∈ N p.1 := fun p => (p.2 : ↥(N p.1)).2
  have hv : Orthonormal ℝ v := by
    constructor
    · rintro ⟨n, i⟩
      simpa [v] using (hworth n).1 i
    · rintro ⟨n, i⟩ ⟨m, j⟩ hij
      by_cases hnm : n = m
      · subst hnm
        have hne : i ≠ j := by rintro rfl; exact hij rfl
        simpa [v, Submodule.coe_inner] using (hworth n).2 hne
      · exact horth hnm _ (hvmem ⟨n, i⟩) _ (hvmem ⟨m, j⟩)
  have perp : ∀ y : E, (∀ p, inner (𝕜 := ℝ) y (v p) = 0) → ∀ n, ∀ z ∈ N n,
      inner (𝕜 := ℝ) y z = 0 := by
    intro y hy n z hz
    set φ : ↥(N n) →L[ℝ] ℝ := (innerSL ℝ y).comp ((N n).subtypeL) with hφ
    have h1 : ∀ i : w n, φ (bb n i) = 0 := by
      intro i
      rw [hφ]
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerSL_apply_apply]
      rw [hbb n]
      exact hy ⟨n, i⟩
    have h2 : HasSum (fun i => (bb n).repr ⟨z, hz⟩ i • bb n i) ⟨z, hz⟩ :=
      (bb n).hasSum_repr ⟨z, hz⟩
    have h3 : HasSum (fun i => (bb n).repr ⟨z, hz⟩ i • φ (bb n i)) (φ ⟨z, hz⟩) := by
      simpa using h2.mapL φ
    have h4 : φ ⟨z, hz⟩ = 0 := by
      have h5 : HasSum (fun _ : w n => (0:ℝ)) (φ ⟨z, hz⟩) := by simpa [h1] using h3
      simpa using h5.unique hasSum_zero
    simpa [hφ] using h4
  have hbot : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ p, inner (𝕜 := ℝ) y (v p) = 0 := by
      intro p
      have hp := hy (v p) (Submodule.subset_span ⟨p, rfl⟩)
      rw [real_inner_comm]; exact hp
    have hle : ∀ n, N n ≤ (Submodule.span ℝ {y})ᗮ := by
      intro n x hx u hu
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [real_inner_smul_left, perp y hy' n x hx, mul_zero]
    have hmem : y ∈ (⨆ n, N n)ᗮ := by
      intro u hu
      have h1 := iSup_le hle hu
      have h0 : inner (𝕜 := ℝ) y u = 0 := h1 y (Submodule.mem_span_singleton_self y)
      rw [real_inner_comm]; exact h0
    rw [hperp] at hmem
    simpa using hmem
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat J
  let e : J ≃ ↥(Set.range f) := Equiv.ofInjective f hf
  have hv' : Orthonormal ℝ fun i : ↥(Set.range f) => v (e.symm i) :=
    hv.comp _ e.symm.injective
  have hrange : Set.range (fun i : ↥(Set.range f) => v (e.symm i)) = Set.range v := by
    rw [show (fun i : ↥(Set.range f) => v (e.symm i)) = (v ∘ e.symm) from rfl, Set.range_comp,
      e.symm.range_eq_univ, Set.image_univ]
  refine ⟨↥(Set.range f), inferInstance,
    HilbertBasis.mkOfOrthogonalEqBot hv' (by rw [hrange]; exact hbot), fun i => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact ⟨(e.symm i).1, hvmem (e.symm i)⟩

omit [CompleteSpace E] in
/-- A Hilbert basis indexed by a finite type forces finite dimension. -/
theorem finiteDimensional_of_hilbertBasis_finite {ι : Type*} [Finite ι]
    (b : HilbertBasis ι ℝ E) : FiniteDimensional ℝ E := by
  haveI : FiniteDimensional ℝ ↥(Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have hclosed : IsClosed ((Submodule.span ℝ (Set.range b) : Submodule ℝ E) : Set E) :=
    Submodule.closed_of_finiteDimensional _
  have htop : Submodule.span ℝ (Set.range b) = ⊤ := by
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact b.dense_span
  have hfin : Module.Finite ℝ E := by
    refine Module.finite_def.mpr ?_
    rw [← htop]
    exact Submodule.fg_span (Set.finite_range b)
  exact hfin

/-- `ℕ`-indexed refinement: over a separable infinite-dimensional Hilbert
    space, the basis produced by `exists_hilbertBasis_of_orthogonal_family`
    can be reindexed by `ℕ`. -/
theorem exists_hilbertBasis_nat_of_orthogonal_family [TopologicalSpace.SeparableSpace E]
    (hinf : ¬ FiniteDimensional ℝ E)
    (N : ℕ → Submodule ℝ E) (hcl : ∀ n, IsClosed ((N n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ N m, ∀ y ∈ N n, inner (𝕜 := ℝ) x y = 0)
    (hperp : (⨆ n, N n)ᗮ = ⊥) :
    ∃ b : HilbertBasis ℕ ℝ E, ∀ i, ∃ n, b i ∈ N n := by
  obtain ⟨ι, hcount, b, hb⟩ := exists_hilbertBasis_of_orthogonal_family N hcl horth hperp
  haveI : Countable ι := hcount
  haveI : Infinite ι := by
    rw [← not_finite_iff_infinite]
    intro hfi
    exact hinf (finiteDimensional_of_hilbertBasis_finite b)
  obtain ⟨e⟩ : Nonempty (ι ≃ ℕ) := inferInstance
  obtain ⟨b', hb'⟩ := PlufWO9.hilbertBasis_reindex b e
  refine ⟨b', fun i => ?_⟩
  obtain ⟨n, hn⟩ := hb (e.symm i)
  refine ⟨n, ?_⟩
  have hbi := hb' (e.symm i)
  rw [Equiv.apply_symm_apply] at hbi
  rw [hbi]
  exact hn

/-! ### Recognizing a subspace as a block -/

/-- If every basis vector lies either in the closed subspace `M` or in its
    orthogonal complement, then `M` is the block of the indices of the
    former. -/
theorem eq_blockB_of_basis_mem_or_orthogonal {ι : Type*} (b : HilbertBasis ι ℝ E)
    (M : Submodule ℝ E) (hM : IsClosed (M : Set E))
    (hdich : ∀ i, b i ∈ M ∨ b i ∈ Mᗮ) :
    M = PlufWO9.blockB b {i | b i ∈ M} := by
  apply le_antisymm
  · intro x hx
    rw [PlufWO9.mem_blockB_iff_inner]
    intro i hi
    have hbi : b i ∈ Mᗮ := (hdich i).resolve_left (by simpa using hi)
    exact hbi x hx
  · refine Submodule.topologicalClosure_minimal _ ?_ hM
    rw [Submodule.span_le]
    rintro y ⟨i, hi, rfl⟩
    exact hi

end PlufWO10
