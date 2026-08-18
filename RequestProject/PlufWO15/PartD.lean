/-
  PlufWO15/PartD.lean — Work Order 15, Part D: Paper I, Proposition 5.9.

  Route for D2 (reported): rather than building the two-dimensional
  functional on `span {I, T}` by hand, the domination step is fed to
  WO-6's `exists_state_with_value`, which is precisely the Hahn–Banach
  dominated extension along the ray through a single operator against the
  sublinear functional `PlufWO6.plimsup σ A = sInf (upper A '' σ)` on all
  of `B(H)` (the machinery WO-6 built for `face_nonempty`). The needed
  domination is the paper's two-case computation:
  `plimsup σ (k • T) = k` for `k ≥ 0` and `= k / 16` for `k ≤ 0`, since
  every member is ample. Linear independence of `I` and `T` is then not
  needed at all: the normalization `φ I = 1` is part of `IsState` and is
  supplied by WO-6.
-/
import RequestProject.PlufWO15.PartC

open Set Cardinal PlufWO13

namespace PlufWO15

/-- Scaling by a nonnegative constant scales the lower Rayleigh value. -/
theorem lower_smul_of_nonneg {d : ℝ} (hd : 0 ≤ d) (A : H →L[ℝ] H)
    (M : Submodule ℝ H) : PlufWO6.lower (d • A) M = d * PlufWO6.lower A M := by
  have h1 : PlufWO6.upper (-(d • A)) M = -PlufWO6.lower (d • A) M :=
    PlufWO6.upper_neg (T := d • A) M
  have h2 : -(d • A) = d • (-A) := by
    rw [smul_neg]
  rw [h2, PlufWO6.upper_smul hd, PlufWO6.upper_neg] at h1
  linarith

/-- On an all-ample family the upper Rayleigh value of `k • T`, `k ≥ 0`,
    is constantly `k`. -/
theorem image_upper_smul_nonneg {σ : Set (Submodule ℝ H)}
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty) {k : ℝ} (hk : 0 ≤ k) :
    PlufWO6.upper (k • T) '' σ = {k} := by
  obtain ⟨M₀, hM₀⟩ := hne
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨M₀, hM₀, ?_⟩, ?_⟩
  · rw [PlufWO6.upper_smul hk, upper_eq_one_of_ample (hamp M₀ hM₀), mul_one]
  · rintro r ⟨M, hM, rfl⟩
    rw [PlufWO6.upper_smul hk, upper_eq_one_of_ample (hamp M hM), mul_one]

/-- On an all-ample family the upper Rayleigh value of `k • T`, `k ≤ 0`,
    is constantly `k / 16`. -/
theorem image_upper_smul_nonpos {σ : Set (Submodule ℝ H)}
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty) {k : ℝ} (hk : k ≤ 0) :
    PlufWO6.upper (k • T) '' σ = {k / 16} := by
  have key : ∀ M ∈ σ, PlufWO6.upper (k • T) M = k / 16 := by
    intro M hM
    have hneg : k • T = -((-k) • T) := by
      rw [neg_smul, neg_neg]
    rw [hneg, PlufWO6.upper_neg, lower_smul_of_nonneg (by linarith : (0:ℝ) ≤ -k),
      lower_eq_sixteenth_of_ample (hamp M hM)]
    ring
  obtain ⟨M₀, hM₀⟩ := hne
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨M₀, hM₀, key M₀ hM₀⟩, ?_⟩
  rintro r ⟨M, hM, rfl⟩
  exact key M hM

/-- The two pluf-limits of `T` along an all-ample family. -/
theorem image_upper_eq {σ : Set (Submodule ℝ H)}
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty) :
    PlufWO6.upper T '' σ = {1} := by
  have h := image_upper_smul_nonneg hamp hne (k := 1) zero_le_one
  rwa [one_smul] at h

theorem image_lower_eq {σ : Set (Submodule ℝ H)}
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty) :
    PlufWO6.lower T '' σ = {1/16} := by
  obtain ⟨M₀, hM₀⟩ := hne
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨M₀, hM₀, lower_eq_sixteenth_of_ample (hamp M₀ hM₀)⟩, ?_⟩
  rintro r ⟨M, hM, rfl⟩
  exact lower_eq_sixteenth_of_ample (hamp M hM)

/-- D1 (⊆), as consumed by D3. -/
theorem face_apply_mem_Icc_aux {σ : Set (Submodule ℝ H)} (hσ : PlufWO6.IsPluf σ)
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty)
    (φ : (H →L[ℝ] H) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hface : ∀ M ∈ σ, ∀ _hM : IsClosed (M : Set H), φ M.starProjection = 1) :
    φ T ∈ Icc (1/16 : ℝ) 1 := by
  have h := (PlufWO6.face_iff_sandwich σ hσ φ hφ).mp hface T T_selfAdjoint
  rw [image_lower_eq hamp hne, image_upper_eq hamp hne, csSup_singleton,
    csInf_singleton] at h
  exact ⟨h.1, h.2⟩

/-- D2 (⊇), as consumed by D3. -/
theorem exists_face_state_apply_eq_aux {σ : Set (Submodule ℝ H)} (hσ : PlufWO6.IsPluf σ)
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty)
    {r : ℝ} (hr : r ∈ Icc (1/16 : ℝ) 1) :
    ∃ φ : (H →L[ℝ] H) →L[ℝ] ℝ, PlufWO6.IsState φ ∧
      (∀ M ∈ σ, ∀ _hM : IsClosed (M : Set H), φ M.starProjection = 1) ∧
      φ T = r := by
  haveI := PlufWO6.nontrivial_H
  refine PlufWO6.exists_state_with_value hσ T r ?_
  intro k
  rcases le_total 0 k with hk | hk
  · have : PlufWO6.plimsup σ (k • T) = k := by
      rw [PlufWO6.plimsup_eq, image_upper_smul_nonneg hamp hne hk, csInf_singleton]
    rw [this]
    nlinarith [hr.2]
  · have : PlufWO6.plimsup σ (k • T) = k / 16 := by
      rw [PlufWO6.plimsup_eq, image_upper_smul_nonpos hamp hne hk, csInf_singleton]
    rw [this]
    nlinarith [hr.1]

/-- D3 (Paper I, Proposition 5.9), as consumed by the contract. -/
theorem face_values_eq_Icc_aux (hCH : continuum = aleph 1) :
    ∃ σ : Set (Submodule ℝ H), PlufWO6.IsPluf σ ∧
      (∀ v : H, v ≠ 0 → ∃ M ∈ σ, v ∉ M) ∧
      (∀ M ∈ σ, Ample M) ∧
      {r : ℝ | ∃ φ : (H →L[ℝ] H) →L[ℝ] ℝ, PlufWO6.IsState φ ∧
        (∀ M ∈ σ, ∀ _hM : IsClosed (M : Set H), φ M.starProjection = 1) ∧
        φ T = r} = Icc (1/16 : ℝ) 1 := by
  haveI := PlufWO6.nontrivial_H
  obtain ⟨σ, hσ, hnp, hamp⟩ := exists_pluf_all_ample_aux hCH
  have hne : σ.Nonempty := hσ.nonempty
  refine ⟨σ, hσ, hnp, hamp, ?_⟩
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨φ, hφ, hface, rfl⟩
    exact face_apply_mem_Icc_aux hσ hamp hne φ hφ hface
  · intro hr
    exact exists_face_state_apply_eq_aux hσ hamp hne hr

end PlufWO15
