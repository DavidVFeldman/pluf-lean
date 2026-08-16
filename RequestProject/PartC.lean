/-
  PartC.lean — Part C of Work Order 1 for the pluf project (Feldman–Wilce):
  the block-intersection identity for disjointly supported families and the
  no-disjointly-supported-blocker proposition.
-/
import RequestProject.PartB

open Set

namespace PlufWO1

section Hilbert

noncomputable section

/-! ### Part C: no disjointly supported blocker -/

/-- Support of a vector. -/
def supp (x : H) : Set ℕ := {n | (x : ∀ _ : ℕ, ℝ) n ≠ 0}

theorem notMem_supp_iff (x : H) (n : ℕ) : n ∉ supp x ↔ (x : ∀ _ : ℕ, ℝ) n = 0 := by
  simp [supp]

/-- Vectors with disjoint supports are orthogonal. -/
theorem inner_eq_zero_of_disjoint_supp {x y : H} (h : Disjoint (supp x) (supp y)) :
    inner (𝕜 := ℝ) x y = 0 := by
  rw [lp.inner_eq_tsum]
  have hz : ∀ n : ℕ, inner (𝕜 := ℝ) ((x : ∀ _ : ℕ, ℝ) n) ((y : ∀ _ : ℕ, ℝ) n) = 0 := by
    intro n
    rcases Classical.em (n ∈ supp x) with hn | hn
    · have : n ∉ supp y := fun hy => (Set.disjoint_left.mp h hn) hy
      rw [(notMem_supp_iff y n).mp this]
      simp
    · rw [(notMem_supp_iff x n).mp hn]
      simp
  rw [tsum_congr hz, tsum_zero]

/-- A continuous linear functional vanishing on a set vanishes on the closed
    span of that set. -/
theorem eq_zero_of_mem_closure_span {G : Set H} (F : H →L[ℝ] ℝ) (hF : ∀ v ∈ G, F v = 0)
    {x : H} (hx : x ∈ (Submodule.span ℝ G).topologicalClosure) : F x = 0 := by
  have hle : (Submodule.span ℝ G).topologicalClosure ≤ LinearMap.ker (F : H →ₗ[ℝ] ℝ) :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (fun v hv => by simpa using hF v hv)) F.isClosed_ker
  simpa using hle hx

/-- The key coordinate identity: on the closed span of a disjointly supported
    family, every vector is a scalar multiple of `ρ i` in the coordinates
    belonging to the support of `ρ i`. -/
theorem coord_smul_eq_inner_smul {ι : Type*} (ρ : ι → H)
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => supp (ρ i))))
    {x : H} (hx : x ∈ (Submodule.span ℝ (Set.range ρ)).topologicalClosure)
    (i : ι) {n : ℕ} (hn : n ∈ supp (ρ i)) :
    (x : ∀ _ : ℕ, ℝ) n * ‖ρ i‖ ^ 2
      = inner (𝕜 := ℝ) x (ρ i) * ((ρ i : ∀ _ : ℕ, ℝ) n) := by
  set F : H →L[ℝ] ℝ :=
    (‖ρ i‖ ^ 2) • coordCLM n - ((ρ i : ∀ _ : ℕ, ℝ) n) • (innerSL ℝ (ρ i)) with hFdef
  have hFapply : ∀ z : H, F z
      = ‖ρ i‖ ^ 2 * (z : ∀ _ : ℕ, ℝ) n - ((ρ i : ∀ _ : ℕ, ℝ) n) * inner (𝕜 := ℝ) z (ρ i) := by
    intro z
    simp only [hFdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      coordCLM_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_comm]
  have hFzero : ∀ v ∈ Set.range ρ, F v = 0 := by
    rintro v ⟨j, rfl⟩
    rw [hFapply]
    rcases eq_or_ne j i with rfl | hji
    · rw [real_inner_self_eq_norm_sq]
      ring
    · have h1 : (ρ j : ∀ _ : ℕ, ℝ) n = 0 := by
        have : n ∉ supp (ρ j) := fun hnj => Set.disjoint_left.mp (hdisj hji) hnj hn
        exact (notMem_supp_iff _ _).mp this
      have h2 : inner (𝕜 := ℝ) (ρ j) (ρ i) = 0 :=
        inner_eq_zero_of_disjoint_supp (hdisj hji)
      rw [h1, h2]
      ring
  have := eq_zero_of_mem_closure_span F hFzero hx
  rw [hFapply] at this
  linarith [this]

/-- C1 (structure of block intersections for disjointly supported spans).
    If the `ρ i` are nonzero with pairwise disjoint supports, then the
    closed span meets a block exactly in the closed span of the wholly
    supported generators.  Stated in the contract's closed-span form.

    Note: the hypothesis `hρ` (nonvanishing of the generators) is part of the
    contract but turns out not to be needed for this identity; it is retained
    as stated. -/
theorem closure_span_inter_block {ι : Type} (ρ : ι → H)
    (hρ : ∀ i, ρ i ≠ 0)
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => supp (ρ i))))
    (S : Set ℕ) :
    (Submodule.span ℝ (Set.range ρ)).topologicalClosure ⊓ block S =
      (Submodule.span ℝ {v | ∃ i, v = ρ i ∧ supp (ρ i) ⊆ S}).topologicalClosure := by
  classical
  set G : Set H := {v | ∃ i, v = ρ i ∧ supp (ρ i) ⊆ S} with hG
  set K : Submodule ℝ H := (Submodule.span ℝ G).topologicalClosure with hK
  have hGsub : G ⊆ Set.range ρ := by rintro v ⟨i, rfl, -⟩; exact ⟨i, rfl⟩
  have hKle1 : K ≤ (Submodule.span ℝ (Set.range ρ)).topologicalClosure := by
    apply Submodule.topologicalClosure_minimal
    · exact le_trans (Submodule.span_mono hGsub) (Submodule.le_topologicalClosure _)
    · exact Submodule.isClosed_topologicalClosure _
  have hKle2 : K ≤ block S := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro v ⟨i, rfl, hsub⟩
      rw [SetLike.mem_coe, mem_block_iff]
      intro n hn
      by_contra hne
      exact hn (hsub hne)
    · exact isClosed_block S
  refine le_antisymm ?_ (le_inf hKle1 hKle2)
  rintro x ⟨hxc, hxb⟩
  -- `x` is orthogonal to every generator not wholly supported in `S`
  have hbad : ∀ i, ¬ (supp (ρ i) ⊆ S) → inner (𝕜 := ℝ) x (ρ i) = 0 := by
    intro i hi
    obtain ⟨n, hn, hnS⟩ := Set.not_subset.mp hi
    have hxn : (x : ∀ _ : ℕ, ℝ) n = 0 := (mem_block_iff S x).mp hxb n hnS
    have hkey := coord_smul_eq_inner_smul ρ hdisj hxc i hn
    rw [hxn, zero_mul] at hkey
    have hρn : (ρ i : ∀ _ : ℕ, ℝ) n ≠ 0 := hn
    exact (mul_eq_zero.mp hkey.symm).resolve_right hρn
  -- orthogonal projection onto `K`
  haveI : CompleteSpace K :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ G)).completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance
  set y : H := x - K.starProjection x with hy
  have hyK : y ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hpK : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
  have hyortho : ∀ i, inner (𝕜 := ℝ) y (ρ i) = 0 := by
    intro i
    by_cases hi : supp (ρ i) ⊆ S
    · have hmem : ρ i ∈ K := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl, hi⟩)
      have := hyK (ρ i) hmem
      rw [real_inner_comm] at this
      exact this
    · -- `ρ i` is orthogonal to `K`, so it suffices that `x ⊥ ρ i`
      have hgen : ∀ v ∈ G, (innerSL ℝ (ρ i)) v = 0 := by
        rintro v ⟨j, rfl, hj⟩
        have hji : j ≠ i := by
          rintro rfl
          exact hi hj
        simpa using inner_eq_zero_of_disjoint_supp (hdisj hji).symm
      have h0 := eq_zero_of_mem_closure_span (innerSL ℝ (ρ i)) hgen hpK
      simp only [innerSL_apply_apply] at h0
      have hxi := hbad i hi
      rw [hy, inner_sub_left, hxi, real_inner_comm (ρ i) (K.starProjection x), h0]
      ring
  have hyspan : y ∈ (Submodule.span ℝ (Set.range ρ)).topologicalClosure :=
    Submodule.sub_mem _ hxc (hKle1 hpK)
  have hyy : inner (𝕜 := ℝ) y y = 0 := by
    refine eq_zero_of_mem_closure_span (innerSL ℝ y) ?_ hyspan
    rintro v ⟨i, rfl⟩
    simpa using (real_inner_comm y (ρ i)) ▸ hyortho i
  have hy0 : y = 0 := inner_self_eq_zero.mp hyy
  have : x = K.starProjection x := by
    have := sub_eq_zero.mp (hy ▸ hy0)
    exact this
  rw [this]
  exact hpK

/-- The standard basis vector `e n` of `H`. -/
def evec (n : ℕ) : H := lp.single 2 n (1 : ℝ)

@[simp] theorem evec_apply (n m : ℕ) :
    (evec n : ∀ _ : ℕ, ℝ) m = if m = n then (1:ℝ) else 0 := by
  rw [evec, lp.single_apply]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

theorem evec_ne_zero (n : ℕ) : evec n ≠ 0 := by
  intro h
  have : (evec n : ∀ _ : ℕ, ℝ) n = 0 := by rw [h]; rfl
  rw [evec_apply] at this
  simp at this

/-- A vector with singleton support is a nonzero multiple of a basis vector. -/
theorem eq_smul_evec_of_supp_singleton {x : H} {n : ℕ} (h : supp x = {n}) :
    x = ((x : ∀ _ : ℕ, ℝ) n) • evec n := by
  apply lp.ext
  funext m
  have hx : (((x : ∀ _ : ℕ, ℝ) n) • evec n : H) m
      = ((x : ∀ _ : ℕ, ℝ) n) * (evec n : ∀ _ : ℕ, ℝ) m := rfl
  rw [hx, evec_apply]
  by_cases hm : m = n
  · subst hm; simp
  · rw [if_neg hm, mul_zero]
    have : m ∉ supp x := by rw [h]; simpa using hm
    exact (notMem_supp_iff x m).mp this

theorem inner_evec_constraintVec (n : ℕ) (A : Set ℕ) :
    inner (𝕜 := ℝ) (evec n) (constraintVec A) = (constraintVec A : ∀ _ : ℕ, ℝ) n := by
  rw [evec, lp.inner_single_left]
  simp

/-- C2 (No disjointly supported blocker; Paper II, Proposition 3.7).
    Hypotheses: `A` a partition of ℕ into pairwise disjoint nonempty pieces
    covering ℕ, with no partial selector in the ultrafilter `U`; `ρ` a family
    of nonzero vectors with pairwise disjoint supports whose closed span `R`
    meets `W A` trivially.  Conclusion: some `S ∈ U` has `R ⊓ block S = ⊥`.

    Note: the contract hypotheses `hneA` (pieces nonempty) and `hcover`
    (pieces cover ℕ) turn out not to be needed — nonemptiness of the two
    relevant pieces comes for free from the points witnessing the failure of
    the partial-selector property — but they are retained as stated. -/
theorem noblock (U : Ultrafilter ℕ) (A : ℕ → Set ℕ)
    (hdisjA : Pairwise (Function.onFun Disjoint A))
    (hneA : ∀ k, (A k).Nonempty) (hcover : (⋃ k, A k) = univ)
    (hsel : ∀ S ∈ U, ¬ IsPartialSelector S A)
    {ι : Type} (ρ : ι → H) (hρ : ∀ i, ρ i ≠ 0)
    (hdisjρ : Pairwise (Function.onFun Disjoint (fun i => supp (ρ i))))
    (hRW : (Submodule.span ℝ (Set.range ρ)).topologicalClosure ⊓ W A = ⊥) :
    ∃ S ∈ U,
      (Submodule.span ℝ (Set.range ρ)).topologicalClosure ⊓ block S = ⊥ := by
  classical
  set R : Submodule ℝ H := (Submodule.span ℝ (Set.range ρ)).topologicalClosure with hR
  -- Every generator has nonempty support.
  have hsuppne : ∀ i, (supp (ρ i)).Nonempty := by
    intro i
    by_contra h
    apply hρ i
    apply lp.ext
    funext n
    have : n ∉ supp (ρ i) := fun hn => h ⟨n, hn⟩
    exact (notMem_supp_iff _ _).mp this
  -- the set of singleton-support points
  set Ds : Set ℕ := {n | ∃ i, supp (ρ i) = {n}} with hDs
  have hevec : ∀ (i : ι) (n : ℕ), supp (ρ i) = {n} → evec n ∈ R := by
    intro i n hi
    set c : ℝ := (ρ i : ∀ _ : ℕ, ℝ) n with hc
    have hne : c ≠ 0 := by
      have : n ∈ supp (ρ i) := by rw [hi]; rfl
      exact this
    have hsm : ρ i = c • evec n := eq_smul_evec_of_supp_singleton hi
    have hmem : ρ i ∈ R := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    have hev : evec n = c⁻¹ • ρ i := by
      rw [hsm, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hev]
    exact Submodule.smul_mem _ _ hmem
  have hDssel : IsPartialSelector Ds A := by
    intro k n hn m hm
    by_contra hnm
    obtain ⟨i, hi⟩ := hn.1
    obtain ⟨j, hj⟩ := hm.1
    -- the explicit two-point witness
    set v : H := ((2:ℝ) ^ (n+1)) • evec n - ((2:ℝ) ^ (m+1)) • evec m with hv
    have hvR : v ∈ R :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ (hevec i n hi))
        (Submodule.smul_mem _ _ (hevec j m hj))
    have hvW : v ∈ W A := by
      rw [mem_W_iff]
      intro l
      rw [hv, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        inner_evec_constraintVec, inner_evec_constraintVec,
        constraintVec_apply, constraintVec_apply]
      rcases eq_or_ne l k with rfl | hlk
      · rw [if_pos hn.2, if_pos hm.2]
        field_simp
        norm_num
      · have hnl : n ∉ A l := fun h => Set.disjoint_left.mp (hdisjA hlk) h hn.2
        have hml : m ∉ A l := fun h => Set.disjoint_left.mp (hdisjA hlk) h hm.2
        rw [if_neg hnl, if_neg hml]
        ring
    have hv0 : v = 0 := by
      have : v ∈ R ⊓ W A := ⟨hvR, hvW⟩
      rw [hRW] at this
      simpa using this
    have hcoord : (v : ∀ _ : ℕ, ℝ) n = (2:ℝ) ^ (n+1) := by
      have h1 : (v : ∀ _ : ℕ, ℝ) n
          = ((2:ℝ) ^ (n+1)) * (evec n : ∀ _ : ℕ, ℝ) n
            - ((2:ℝ) ^ (m+1)) * (evec m : ∀ _ : ℕ, ℝ) n := rfl
      rw [h1, evec_apply, evec_apply, if_pos rfl, if_neg hnm]
      ring
    rw [hv0] at hcoord
    have : (0:ℝ) = (2:ℝ) ^ (n+1) := hcoord
    have h2 : (0:ℝ) < (2:ℝ) ^ (n+1) := by positivity
    linarith
  have hDsU : Ds ∉ U := fun hmem => hsel Ds hmem hDssel
  -- the multi-point supports
  have h2pt : ∀ i : {i : ι // ¬ ∃ n, supp (ρ i) = {n}},
      ∃ a b, a ∈ supp (ρ i.1) ∧ b ∈ supp (ρ i.1) ∧ a ≠ b := by
    rintro ⟨i, hi⟩
    have hnsub : ¬ (supp (ρ i)).Subsingleton := by
      intro hsub
      obtain ⟨n, hn⟩ := hsuppne i
      exact hi ⟨n, hsub.eq_singleton_of_mem hn⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hnsub
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨D₁, hD₁cov, hD₁U⟩ :=
    exists_transversal_not_mem U (fun i : {i : ι // ¬ ∃ n, supp (ρ i) = {n}} => supp (ρ i.1))
      (by
        intro i j hij
        exact hdisjρ (fun h => hij (Subtype.ext h)))
      h2pt
  set D : Set ℕ := Ds ∪ D₁ with hD
  have hDU : D ∉ U := not_mem_union_of_not_mem U hDsU hD₁U
  refine ⟨Dᶜ, Ultrafilter.compl_mem_iff_notMem.mpr hDU, ?_⟩
  -- no generator is supported inside `Dᶜ`
  have hnone : ∀ i, ¬ (supp (ρ i) ⊆ Dᶜ) := by
    intro i hsub
    by_cases hi : ∃ n, supp (ρ i) = {n}
    · obtain ⟨n, hn⟩ := hi
      have hnmem : n ∈ supp (ρ i) := by rw [hn]; rfl
      have : n ∈ Ds := ⟨i, hn⟩
      exact (hsub hnmem) (Or.inl this)
    · obtain ⟨n, hn₁, hn₂⟩ := hD₁cov ⟨i, hi⟩
      exact (hsub hn₂) (Or.inr hn₁)
  rw [closure_span_inter_block ρ hρ hdisjρ]
  have hempty : {v : H | ∃ i, v = ρ i ∧ supp (ρ i) ⊆ Dᶜ} = ∅ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, rfl, hi⟩
    exact hnone i hi
  rw [hempty, Submodule.span_empty]
  exact le_antisymm
    (Submodule.topologicalClosure_minimal _ le_rfl (by simp))
    bot_le

end

end Hilbert

end PlufWO1
