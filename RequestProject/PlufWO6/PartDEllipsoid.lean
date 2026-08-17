/-
  PlufWO6/PartDEllipsoid.lean — Work Order 6, Part D, the ellipsoid form
  of Lemma 3.1.

  The work order rules the ellipsoid phrasing of Lemma 3.1 a separate item
  ("report rather than silently substitute"), and the contracted Part D is
  returned in the Rayleigh form in `PartD.lean`.  This file DELIVERS the
  ellipsoid phrasing as well, so that no substitution is involved: for a
  coercive positive `T` — the paper's "positive with bounded inverse" —
  the minor and major radii of the slice `E_T ∩ M` of the ellipsoid
  `E_T = {x : ⟨T x, x⟩ = 1}` are `uT(M)^{-1/2}` and `lT(M)^{-1/2}`, and
  the eccentricity of the slice is `sqrt (uT(M) / lT(M))`.  This is
  Lemma 3.1 verbatim, and it identifies the paper's round-slice property
  (eccentricity → 1 along the filter) with the contracted Rayleigh form.
-/
import RequestProject.PlufWO6.PartD

open Set

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Ellipsoid

variable (T : E →L[ℝ] E)

/-- The ellipsoid of a positive operator, sliced by a subspace:
    `E_T ∩ M = {x ∈ M : ⟨T x, x⟩ = 1}`. -/
def ellipsoidSlice (M : Submodule ℝ E) : Set E :=
  {x | x ∈ M ∧ inner (𝕜 := ℝ) (T x) x = 1}

/-- The minor radius of the slice. -/
noncomputable def minorRadius (M : Submodule ℝ E) : ℝ :=
  sInf ((fun x : E => ‖x‖) '' ellipsoidSlice T M)

/-- The major radius of the slice. -/
noncomputable def majorRadius (M : Submodule ℝ E) : ℝ :=
  sSup ((fun x : E => ‖x‖) '' ellipsoidSlice T M)

/-- The eccentricity of the slice. -/
noncomputable def eccentricity (M : Submodule ℝ E) : ℝ :=
  majorRadius T M / minorRadius T M

variable {T}

omit [CompleteSpace E] in
/-- The quadratic form scales quadratically. -/
theorem inner_smul_self (a : ℝ) (x : E) :
    inner (𝕜 := ℝ) (T (a • x)) (a • x) = a ^ 2 * inner (𝕜 := ℝ) (T x) x := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

omit [CompleteSpace E] in
/-- Every Rayleigh value of a coercive `T` is at least the coercivity
    constant. -/
theorem le_of_mem_rayleighSet {c : ℝ}
    (hcoer : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x)
    {M : Submodule ℝ E} {q : ℝ} (hq : q ∈ rayleighSet T M) : c ≤ q := by
  obtain ⟨x, ⟨-, hx1⟩, rfl⟩ := hq
  have := hcoer x
  rwa [hx1, one_pow, mul_one] at this

omit [CompleteSpace E] in
/-- The radii of the slice are exactly the inverse square roots of the
    Rayleigh values. -/
theorem norm_image_ellipsoidSlice {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x) (M : Submodule ℝ E) :
    (fun x : E => ‖x‖) '' ellipsoidSlice T M
      = (fun q : ℝ => (Real.sqrt q)⁻¹) '' rayleighSet T M := by
  ext r
  constructor
  · rintro ⟨x, ⟨hxM, hx1⟩, rfl⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx1
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    refine ⟨inner (𝕜 := ℝ) (T (‖x‖⁻¹ • x)) (‖x‖⁻¹ • x), ⟨‖x‖⁻¹ • x, ⟨M.smul_mem _ hxM, ?_⟩, rfl⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hn)]
    · show (Real.sqrt (inner (𝕜 := ℝ) (T (‖x‖⁻¹ • x)) (‖x‖⁻¹ • x)))⁻¹ = ‖x‖
      rw [inner_smul_self, hx1, mul_one,
        show (‖x‖⁻¹) ^ 2 = (‖x‖ ^ 2)⁻¹ by rw [inv_pow],
        Real.sqrt_inv, Real.sqrt_sq hn.le, inv_inv]
  · rintro ⟨q, ⟨y, ⟨hyM, hy1⟩, rfl⟩, rfl⟩
    set q : ℝ := inner (𝕜 := ℝ) (T y) y with hq
    have hqpos : 0 < q := lt_of_lt_of_le hc (le_of_mem_rayleighSet hcoer ⟨y, ⟨hyM, hy1⟩, rfl⟩)
    have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
    refine ⟨(Real.sqrt q)⁻¹ • y, ⟨M.smul_mem _ hyM, ?_⟩, ?_⟩
    · rw [inner_smul_self, ← hq, inv_pow, Real.sq_sqrt hqpos.le,
        inv_mul_cancel₀ (ne_of_gt hqpos)]
    · show ‖(Real.sqrt q)⁻¹ • y‖ = (Real.sqrt (inner (𝕜 := ℝ) (T y) y))⁻¹
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hsq, hy1, mul_one, ← hq]

omit [CompleteSpace E] in
/-- Lemma 3.1, minor radius: `m(E_T ∩ M) = uT(M)^{-1/2}`. -/
theorem minorRadius_eq {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x)
    {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    minorRadius T M = (Real.sqrt (upper T M))⁻¹ := by
  classical
  set f : ℝ → ℝ := fun q => (Real.sqrt (max q c))⁻¹ with hf
  have hanti : Antitone f := by
    intro a b hab
    have hca : 0 < max a c := lt_of_lt_of_le hc (le_max_right _ _)
    have hsa : 0 < Real.sqrt (max a c) := Real.sqrt_pos.mpr hca
    have hle : Real.sqrt (max a c) ≤ Real.sqrt (max b c) :=
      Real.sqrt_le_sqrt (max_le_max hab le_rfl)
    exact inv_anti₀ hsa hle
  have hcont : ∀ a : ℝ, ContinuousAt f a := by
    intro a
    have hca : 0 < max a c := lt_of_lt_of_le hc (le_max_right _ _)
    have hsa : Real.sqrt (max a c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hca)
    exact ContinuousAt.inv₀
      ((Real.continuous_sqrt.continuousAt).comp
        ((continuous_id.max continuous_const).continuousAt)) hsa
  have hAne : (rayleighSet T M).Nonempty := rayleighSet_nonempty hM
  have hAbdd : BddAbove (rayleighSet T M) := rayleighSet_bddAbove M
  have hagree : ∀ q ∈ rayleighSet T M, f q = (Real.sqrt q)⁻¹ := by
    intro q hq
    rw [hf]
    simp only
    rw [max_eq_left (le_of_mem_rayleighSet hcoer hq)]
  have hsup : c ≤ sSup (rayleighSet T M) := by
    obtain ⟨q, hq⟩ := hAne
    exact le_trans (le_of_mem_rayleighSet hcoer hq) (le_csSup hAbdd hq)
  have himg : f '' rayleighSet T M = (fun x : E => ‖x‖) '' ellipsoidSlice T M := by
    rw [norm_image_ellipsoidSlice hc hcoer M]
    exact Set.image_congr hagree
  have hmap := hanti.map_csSup_of_continuousAt (hcont _) hAne hAbdd
  rw [himg] at hmap
  rw [minorRadius, ← hmap, hf]
  simp only
  rw [max_eq_left hsup, upper_eq]

omit [CompleteSpace E] in
/-- Lemma 3.1, major radius: `M(E_T ∩ M) = lT(M)^{-1/2}`. -/
theorem majorRadius_eq {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x)
    {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    majorRadius T M = (Real.sqrt (lower T M))⁻¹ := by
  classical
  set f : ℝ → ℝ := fun q => (Real.sqrt (max q c))⁻¹ with hf
  have hanti : Antitone f := by
    intro a b hab
    have hca : 0 < max a c := lt_of_lt_of_le hc (le_max_right _ _)
    have hsa : 0 < Real.sqrt (max a c) := Real.sqrt_pos.mpr hca
    have hle : Real.sqrt (max a c) ≤ Real.sqrt (max b c) :=
      Real.sqrt_le_sqrt (max_le_max hab le_rfl)
    exact inv_anti₀ hsa hle
  have hcont : ∀ a : ℝ, ContinuousAt f a := by
    intro a
    have hca : 0 < max a c := lt_of_lt_of_le hc (le_max_right _ _)
    have hsa : Real.sqrt (max a c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hca)
    exact ContinuousAt.inv₀
      ((Real.continuous_sqrt.continuousAt).comp
        ((continuous_id.max continuous_const).continuousAt)) hsa
  have hAne : (rayleighSet T M).Nonempty := rayleighSet_nonempty hM
  have hAbdd : BddBelow (rayleighSet T M) := rayleighSet_bddBelow' M
  have hagree : ∀ q ∈ rayleighSet T M, f q = (Real.sqrt q)⁻¹ := by
    intro q hq
    rw [hf]
    simp only
    rw [max_eq_left (le_of_mem_rayleighSet hcoer hq)]
  have hinf : c ≤ sInf (rayleighSet T M) :=
    le_csInf hAne (fun q hq => le_of_mem_rayleighSet hcoer hq)
  have himg : f '' rayleighSet T M = (fun x : E => ‖x‖) '' ellipsoidSlice T M := by
    rw [norm_image_ellipsoidSlice hc hcoer M]
    exact Set.image_congr hagree
  have hmap := hanti.map_csInf_of_continuousAt (hcont _) hAne hAbdd
  rw [himg] at hmap
  rw [majorRadius, ← hmap, hf]
  simp only
  rw [max_eq_left hinf, lower_eq]

omit [CompleteSpace E] in
/-- Lemma 3.1, eccentricity: `r(E_T ∩ M) = sqrt (uT(M) / lT(M))`. -/
theorem eccentricity_eq {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x)
    {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    eccentricity T M = Real.sqrt (upper T M / lower T M) := by
  have hlow : c ≤ lower T M :=
    le_csInf (rayleighSet_nonempty hM) (fun q hq => le_of_mem_rayleighSet hcoer hq)
  have hlpos : 0 < lower T M := lt_of_lt_of_le hc hlow
  have hupos : 0 < upper T M := lt_of_lt_of_le hlpos (lower_le_upper_self hM)
  rw [eccentricity, minorRadius_eq hc hcoer hM, majorRadius_eq hc hcoer hM]
  have hsu : 0 < Real.sqrt (upper T M) := Real.sqrt_pos.mpr hupos
  have hsl : 0 < Real.sqrt (lower T M) := Real.sqrt_pos.mpr hlpos
  have hrw : (Real.sqrt (lower T M))⁻¹ / (Real.sqrt (upper T M))⁻¹
      = Real.sqrt (upper T M) / Real.sqrt (lower T M) := by
    field_simp
  rw [hrw, ← Real.sqrt_div hupos.le]

/-! ### The two phrasings of the round-slice property agree -/

variable (T)

/-- The paper's round-slice property in the ellipsoid phrasing: the slices
    of `E_T` along the filter have eccentricity tending to `1`. -/
def RSPEcc (π : Set (Submodule ℝ E)) (T : E →L[ℝ] E) : Prop :=
  ∀ ε > 0, ∃ M ∈ π, eccentricity T M < 1 + ε

variable {T}

omit [CompleteSpace E] in
/-- For a coercive positive `T` the contracted Rayleigh form of the
    round-slice property and the paper's ellipsoid form agree.  This is
    what Lemma 3.1 is for, and it is why Part D may be contracted in the
    Rayleigh form without loss. -/
theorem rsp_iff_rspEcc {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x)
    (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    RSP π T ↔ RSPEcc π T := by
  have hlow : ∀ M ∈ π, c ≤ lower T M := by
    intro M hM
    exact le_csInf (rayleighSet_nonempty (hπ.ne_bot hM))
      (fun q hq => le_of_mem_rayleighSet hcoer hq)
  constructor
  · intro h ε hε
    obtain ⟨M, hM, hosc⟩ := h (c * ε) (by positivity)
    refine ⟨M, hM, ?_⟩
    have hbot : M ≠ ⊥ := hπ.ne_bot hM
    have hl : c ≤ lower T M := hlow M hM
    have hlpos : 0 < lower T M := lt_of_lt_of_le hc hl
    have hdiv : upper T M / lower T M < (1 + ε) ^ 2 := by
      rw [div_lt_iff₀ hlpos]
      nlinarith [mul_le_mul_of_nonneg_right hl hε.le,
        mul_nonneg hlpos.le (mul_nonneg hε.le hε.le)]
    rw [eccentricity_eq hc hcoer hbot]
    exact (Real.sqrt_lt' (by linarith)).mpr hdiv
  · intro h ε hε
    set K : ℝ := ‖T‖ with hK
    have hK0 : 0 ≤ K := norm_nonneg T
    set η : ℝ := min 1 (ε / (3 * (K + 1))) with hη
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηε : η ≤ ε / (3 * (K + 1)) := min_le_right _ _
    obtain ⟨M, hM, hecc⟩ := h η hηpos
    refine ⟨M, hM, ?_⟩
    have hbot : M ≠ ⊥ := hπ.ne_bot hM
    have hl : c ≤ lower T M := hlow M hM
    have hlpos : 0 < lower T M := lt_of_lt_of_le hc hl
    have hlK : lower T M ≤ K := le_trans (le_abs_self _) (abs_lower_le_norm hbot)
    rw [eccentricity_eq hc hcoer hbot] at hecc
    have hdiv : upper T M / lower T M < (1 + η) ^ 2 :=
      (Real.sqrt_lt' (by linarith)).mp hecc
    rw [div_lt_iff₀ hlpos] at hdiv
    have hstep : lower T M * (2 * η + η ^ 2) < ε := by
      have h3 : 2 * η + η ^ 2 ≤ 3 * η := by nlinarith
      have h4 : 3 * η ≤ ε / (K + 1) := by
        have hKpos : (0 : ℝ) < K + 1 := by linarith
        calc 3 * η ≤ 3 * (ε / (3 * (K + 1))) := by linarith
          _ = ε / (K + 1) := by field_simp
      have h5 : lower T M * (2 * η + η ^ 2) ≤ K * (ε / (K + 1)) := by
        have h6 : 0 ≤ 2 * η + η ^ 2 := by positivity
        calc lower T M * (2 * η + η ^ 2) ≤ K * (2 * η + η ^ 2) :=
              mul_le_mul_of_nonneg_right hlK h6
          _ ≤ K * (ε / (K + 1)) := by
              refine mul_le_mul_of_nonneg_left (le_trans h3 h4) hK0
      have h7 : K * (ε / (K + 1)) < ε := by
        rw [mul_div_assoc'] at *
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < K + 1)]
        nlinarith
      linarith
    nlinarith

end Ellipsoid

end PlufWO6
