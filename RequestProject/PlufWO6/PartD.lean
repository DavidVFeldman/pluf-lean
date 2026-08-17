/-
  PlufWO6/PartD.lean — Work Order 6, Part D: radii, gaps and the
  round-slice property (Paper I, Lemma 3.1 and Proposition 3.2), in the
  Rayleigh form contracted.

  D2 is returned with the same minimal repair as A1 (`E ≠ 0`): over the
  zero space the empty family is a pluf, the two sides of the gap
  criterion are `sSup ∅ = sInf ∅`, i.e. `0 = 0`, while `RSP` fails for
  want of a member.

  The file closes with the general-position Rayleigh calculus (no
  positivity hypothesis) that Part E needs.
-/
import RequestProject.PlufWO6.PartA

open Set
open scoped Classical Pointwise

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Part D: radii, gaps, and the round-slice property -/

section Slices

variable (T : E →L[ℝ] E)

/-- Upper and lower Rayleigh values of `T` on a nonzero closed subspace. -/
noncomputable def upper (M : Submodule ℝ E) : ℝ :=
  sSup ((fun x => inner (𝕜 := ℝ) (T x) x) '' {x ∈ M | ‖x‖ = 1})

noncomputable def lower (M : Submodule ℝ E) : ℝ :=
  sInf ((fun x => inner (𝕜 := ℝ) (T x) x) '' {x ∈ M | ‖x‖ = 1})

/-- The set of Rayleigh values of `T` on the unit sphere of `M`. -/
def rayleighSet (M : Submodule ℝ E) : Set ℝ :=
  (fun x => inner (𝕜 := ℝ) (T x) x) '' {x ∈ M | ‖x‖ = 1}

omit [CompleteSpace E] in
theorem upper_eq (M : Submodule ℝ E) : upper T M = sSup (rayleighSet T M) := rfl

omit [CompleteSpace E] in
theorem lower_eq (M : Submodule ℝ E) : lower T M = sInf (rayleighSet T M) := rfl

variable {T}

omit [CompleteSpace E] in
/-- On a nonzero subspace there is a unit vector, so the Rayleigh set is
    nonempty. -/
theorem rayleighSet_nonempty {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    (rayleighSet T M).Nonempty := by
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  refine ⟨inner (𝕜 := ℝ) (T (‖v‖⁻¹ • v)) (‖v‖⁻¹ • v), ⟨‖v‖⁻¹ • v, ⟨M.smul_mem _ hvM, ?_⟩, rfl⟩⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]

omit [CompleteSpace E] in
/-- The Rayleigh set is bounded above by the operator norm. -/
theorem rayleighSet_bddAbove (M : Submodule ℝ E) : BddAbove (rayleighSet T M) := by
  refine ⟨‖T‖, ?_⟩
  rintro a ⟨x, ⟨-, hx1⟩, rfl⟩
  calc inner (𝕜 := ℝ) (T x) x ≤ ‖T x‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ := by rw [hx1]; ring

omit [CompleteSpace E] in
/-- For a positive operator the Rayleigh set is bounded below by `0`. -/
theorem rayleighSet_bddBelow (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x)
    (M : Submodule ℝ E) : BddBelow (rayleighSet T M) := by
  refine ⟨0, ?_⟩
  rintro a ⟨x, -, rfl⟩
  exact hpos x

omit [CompleteSpace E] in
theorem rayleighSet_mono {M N : Submodule ℝ E} (h : M ≤ N) :
    rayleighSet T M ⊆ rayleighSet T N := by
  rintro a ⟨x, ⟨hxM, hx1⟩, rfl⟩
  exact ⟨x, ⟨h hxM, hx1⟩, rfl⟩

omit [CompleteSpace E] in
/-- Every Rayleigh value on `M` is at most `upper T M`. -/
theorem le_upper {M : Submodule ℝ E} {a : ℝ} (ha : a ∈ rayleighSet T M) :
    a ≤ upper T M :=
  le_csSup (rayleighSet_bddAbove M) ha

omit [CompleteSpace E] in
/-- Every Rayleigh value on `M` is at least `lower T M`, for positive `T`. -/
theorem lower_le (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x)
    {M : Submodule ℝ E} {a : ℝ} (ha : a ∈ rayleighSet T M) :
    lower T M ≤ a :=
  csInf_le (rayleighSet_bddBelow hpos M) ha

omit [CompleteSpace E] in
/-- `upper` is monotone. -/
theorem upper_mono {M N : Submodule ℝ E} (hMbot : M ≠ ⊥) (h : M ≤ N) :
    upper T M ≤ upper T N :=
  csSup_le_csSup (rayleighSet_bddAbove N) (rayleighSet_nonempty hMbot) (rayleighSet_mono h)

omit [CompleteSpace E] in
/-- `lower` is antitone. -/
theorem lower_mono (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x)
    {M N : Submodule ℝ E} (hMbot : M ≠ ⊥) (h : M ≤ N) :
    lower T N ≤ lower T M :=
  csInf_le_csInf (rayleighSet_bddBelow hpos N) (rayleighSet_nonempty hMbot)
    (rayleighSet_mono h)

variable (T)

omit [CompleteSpace E] in
/-- D1 (directedness). Along a filter, lower values never exceed upper
    values: for `M, N ∈ π` the meet is a member and is nonzero. -/
theorem lower_le_upper (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x)
    (M : Submodule ℝ E) (hM : M ∈ π) (N : Submodule ℝ E) (hN : N ∈ π) :
    lower T M ≤ upper T N := by
  obtain ⟨a, ha⟩ := rayleighSet_nonempty (T := T) (hπ.inf_ne_bot hM hN)
  exact le_trans (lower_le hpos (rayleighSet_mono inf_le_left ha))
    (le_upper (rayleighSet_mono inf_le_right ha))

/-- The round-slice property for `T`: the Rayleigh quotient is asymptotically
    constant along the filter. (The paper phrases RSP through the
    eccentricity of the ellipsoid slice; Lemma 3.1 identifies that with the
    ratio of the Rayleigh values, so this is the same property. If the
    ellipsoid phrasing is wanted verbatim, that is a separate item — REPORT
    rather than assume.) -/
def RSP (π : Set (Submodule ℝ E)) (T : E →L[ℝ] E) : Prop :=
  ∀ ε > 0, ∃ M ∈ π, upper T M - lower T M < ε

end Slices

/-! ### General-position Rayleigh calculus

The contract's Part D carries a positivity hypothesis `hpos` throughout.
For Part E the same calculus is needed for arbitrary self-adjoint (indeed
arbitrary bounded) operators, where the Rayleigh set is still bounded — by
`‖T‖` on both sides.  These are the contract lemmas' general counterparts;
the contract forms above are special cases of them. -/

section GeneralPosition

variable {S T : E →L[ℝ] E}

omit [CompleteSpace E]

/-- Every Rayleigh value of `T` is bounded in absolute value by `‖T‖`. -/
theorem abs_le_norm_of_mem_rayleighSet {M : Submodule ℝ E} {a : ℝ}
    (ha : a ∈ rayleighSet T M) : |a| ≤ ‖T‖ := by
  obtain ⟨x, ⟨-, hx1⟩, rfl⟩ := ha
  calc |inner (𝕜 := ℝ) (T x) x| ≤ ‖T x‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ := by rw [hx1]; ring

/-- The Rayleigh set is bounded below by `-‖T‖`, with no positivity
    hypothesis. -/
theorem rayleighSet_bddBelow' (M : Submodule ℝ E) : BddBelow (rayleighSet T M) :=
  ⟨-‖T‖, fun _ ha => (abs_le.mp (abs_le_norm_of_mem_rayleighSet ha)).1⟩

/-- General form of `lower_le`. -/
theorem lower_le' {M : Submodule ℝ E} {a : ℝ} (ha : a ∈ rayleighSet T M) :
    lower T M ≤ a :=
  csInf_le (rayleighSet_bddBelow' M) ha

/-- General form of `lower_mono`. -/
theorem lower_mono' {M N : Submodule ℝ E} (hMbot : M ≠ ⊥) (h : M ≤ N) :
    lower T N ≤ lower T M :=
  csInf_le_csInf (rayleighSet_bddBelow' N) (rayleighSet_nonempty hMbot) (rayleighSet_mono h)

/-- `lower T M ≤ upper T M` on a nonzero subspace. -/
theorem lower_le_upper_self {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    lower T M ≤ upper T M := by
  obtain ⟨a, ha⟩ := rayleighSet_nonempty (T := T) hM
  exact le_trans (lower_le' ha) (le_upper ha)

/-- General form of `lower_le_upper`. -/
theorem lower_le_upper' {π : Set (Submodule ℝ E)} (hπ : IsPluf π)
    {M : Submodule ℝ E} (hM : M ∈ π) {N : Submodule ℝ E} (hN : N ∈ π) :
    lower T M ≤ upper T N := by
  obtain ⟨a, ha⟩ := rayleighSet_nonempty (T := T) (hπ.inf_ne_bot hM hN)
  exact le_trans (lower_le' (rayleighSet_mono inf_le_left ha))
    (le_upper (rayleighSet_mono inf_le_right ha))

theorem abs_upper_le_norm {M : Submodule ℝ E} (hM : M ≠ ⊥) : |upper T M| ≤ ‖T‖ := by
  obtain ⟨a, ha⟩ := rayleighSet_nonempty (T := T) hM
  refine abs_le.mpr ⟨?_, csSup_le ⟨a, ha⟩ (fun b hb =>
    (abs_le.mp (abs_le_norm_of_mem_rayleighSet hb)).2)⟩
  exact le_trans (abs_le.mp (abs_le_norm_of_mem_rayleighSet ha)).1 (le_upper ha)

theorem abs_lower_le_norm {M : Submodule ℝ E} (hM : M ≠ ⊥) : |lower T M| ≤ ‖T‖ := by
  obtain ⟨a, ha⟩ := rayleighSet_nonempty (T := T) hM
  refine abs_le.mpr ⟨le_csInf ⟨a, ha⟩ (fun b hb =>
    (abs_le.mp (abs_le_norm_of_mem_rayleighSet hb)).1), ?_⟩
  exact le_trans (lower_le' ha) (abs_le.mp (abs_le_norm_of_mem_rayleighSet ha)).2

/-- The Rayleigh bound in unnormalized form. -/
theorem inner_le_upper_mul (M : Submodule ℝ E) {y : E} (hy : y ∈ M) :
    inner (𝕜 := ℝ) (T y) y ≤ upper T M * ‖y‖ ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
    have hx1 : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hmem : inner (𝕜 := ℝ) (T ((‖y‖⁻¹ : ℝ) • y)) ((‖y‖⁻¹ : ℝ) • y) ∈ rayleighSet T M :=
      ⟨(‖y‖⁻¹ : ℝ) • y, ⟨M.smul_mem _ hy, hx1⟩, rfl⟩
    have hval : inner (𝕜 := ℝ) (T ((‖y‖⁻¹ : ℝ) • y)) ((‖y‖⁻¹ : ℝ) • y)
        = (‖y‖⁻¹ * ‖y‖⁻¹) * inner (𝕜 := ℝ) (T y) y := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    have h := le_upper hmem
    rw [hval] at h
    have hsq : (0:ℝ) < ‖y‖ ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hsq)
    calc inner (𝕜 := ℝ) (T y) y
        = ‖y‖ ^ 2 * ((‖y‖⁻¹ * ‖y‖⁻¹) * inner (𝕜 := ℝ) (T y) y) := by field_simp
      _ ≤ ‖y‖ ^ 2 * upper T M := hmul
      _ = upper T M * ‖y‖ ^ 2 := by ring

/-- The lower Rayleigh bound in unnormalized form. -/
theorem lower_mul_le_inner (M : Submodule ℝ E) {y : E} (hy : y ∈ M) :
    lower T M * ‖y‖ ^ 2 ≤ inner (𝕜 := ℝ) (T y) y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
    have hx1 : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hmem : inner (𝕜 := ℝ) (T ((‖y‖⁻¹ : ℝ) • y)) ((‖y‖⁻¹ : ℝ) • y) ∈ rayleighSet T M :=
      ⟨(‖y‖⁻¹ : ℝ) • y, ⟨M.smul_mem _ hy, hx1⟩, rfl⟩
    have hval : inner (𝕜 := ℝ) (T ((‖y‖⁻¹ : ℝ) • y)) ((‖y‖⁻¹ : ℝ) • y)
        = (‖y‖⁻¹ * ‖y‖⁻¹) * inner (𝕜 := ℝ) (T y) y := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    have h := lower_le' hmem
    rw [hval] at h
    have hsq : (0:ℝ) < ‖y‖ ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hsq)
    calc lower T M * ‖y‖ ^ 2 = ‖y‖ ^ 2 * lower T M := by ring
      _ ≤ ‖y‖ ^ 2 * ((‖y‖⁻¹ * ‖y‖⁻¹) * inner (𝕜 := ℝ) (T y) y) := hmul
      _ = inner (𝕜 := ℝ) (T y) y := by field_simp

/-- Subadditivity of the upper Rayleigh value. -/
theorem upper_add_le {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    upper (S + T) M ≤ upper S M + upper T M := by
  refine csSup_le (rayleighSet_nonempty hM) ?_
  rintro a ⟨x, ⟨hxM, hx1⟩, rfl⟩
  show inner (𝕜 := ℝ) ((S + T) x) x ≤ upper S M + upper T M
  have h : inner (𝕜 := ℝ) ((S + T) x) x
      = inner (𝕜 := ℝ) (S x) x + inner (𝕜 := ℝ) (T x) x := by
    simp [inner_add_left]
  rw [h]
  exact add_le_add (le_upper ⟨x, ⟨hxM, hx1⟩, rfl⟩) (le_upper ⟨x, ⟨hxM, hx1⟩, rfl⟩)

theorem rayleighSet_smul (c : ℝ) (M : Submodule ℝ E) :
    rayleighSet (c • T) M = c • rayleighSet T M := by
  ext a
  simp only [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨inner (𝕜 := ℝ) (T x) x, ⟨x, hx, rfl⟩, ?_⟩
    simp [real_inner_smul_left]
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [real_inner_smul_left]⟩

theorem rayleighSet_neg (M : Submodule ℝ E) :
    rayleighSet (-T) M = -rayleighSet T M := by
  ext a
  simp only [Set.mem_neg]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, hxa⟩
    refine ⟨x, hx, ?_⟩
    show inner (𝕜 := ℝ) ((-T) x) x = a
    have hxa' : inner (𝕜 := ℝ) (T x) x = -a := hxa
    have hneg : inner (𝕜 := ℝ) ((-T) x) x = -inner (𝕜 := ℝ) (T x) x := by simp
    rw [hneg, hxa', neg_neg]

theorem upper_smul {c : ℝ} (hc : 0 ≤ c) (M : Submodule ℝ E) :
    upper (c • T) M = c * upper T M := by
  rw [upper_eq, upper_eq, rayleighSet_smul, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

/-- Negation swaps the two Rayleigh values. -/
theorem upper_neg (M : Submodule ℝ E) : upper (-T) M = -lower T M := by
  rw [upper_eq, lower_eq, rayleighSet_neg, Real.sSup_neg]

theorem lower_neg (M : Submodule ℝ E) : lower (-T) M = -upper T M := by
  have h := upper_neg (T := -T) M
  rw [neg_neg] at h
  linarith [h]

/-- On a nonzero subspace the identity has the single Rayleigh value `1`. -/
theorem rayleighSet_one {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    rayleighSet (ContinuousLinearMap.id ℝ E) M = {1} := by
  ext a
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, ⟨-, hx1⟩, rfl⟩
    simp [hx1]
  · intro ha
    obtain ⟨b, x, ⟨hxM, hx1⟩, hb⟩ := rayleighSet_nonempty
      (T := ContinuousLinearMap.id ℝ E) hM
    exact ⟨x, ⟨hxM, hx1⟩, by simp [hx1, ha]⟩

theorem upper_one {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    upper (ContinuousLinearMap.id ℝ E) M = 1 := by
  rw [upper_eq, rayleighSet_one hM, csSup_singleton]

theorem lower_one {M : Submodule ℝ E} (hM : M ≠ ⊥) :
    lower (ContinuousLinearMap.id ℝ E) M = 1 := by
  rw [lower_eq, rayleighSet_one hM, csInf_singleton]

/-- D2 in general position: no positivity hypothesis.  RSP for `T` holds
    iff the supremum of the lower Rayleigh values equals the infimum of the
    upper ones. -/
theorem rsp_iff_sup_eq_inf' [Nontrivial E] (T : E →L[ℝ] E)
    (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    RSP π T ↔ sSup (lower T '' π) = sInf (upper T '' π) := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  have hAne : (lower T '' π).Nonempty := ⟨lower T M₀, M₀, hM₀, rfl⟩
  have hBne : (upper T '' π).Nonempty := ⟨upper T M₀, M₀, hM₀, rfl⟩
  have hAB : ∀ a ∈ lower T '' π, ∀ b ∈ upper T '' π, a ≤ b := by
    rintro a ⟨M, hM, rfl⟩ b ⟨N, hN, rfl⟩
    exact lower_le_upper' hπ hM hN
  have hAbdd : BddAbove (lower T '' π) := ⟨upper T M₀, fun a ha => hAB a ha _ ⟨M₀, hM₀, rfl⟩⟩
  have hBbdd : BddBelow (upper T '' π) := ⟨lower T M₀, fun b hb => hAB _ ⟨M₀, hM₀, rfl⟩ b hb⟩
  have hle : sSup (lower T '' π) ≤ sInf (upper T '' π) :=
    csSup_le hAne (fun a ha => le_csInf hBne (fun b hb => hAB a ha b hb))
  constructor
  · intro hrsp
    refine le_antisymm hle ?_
    by_contra hcon
    push_neg at hcon
    set ε : ℝ := sInf (upper T '' π) - sSup (lower T '' π) with hε
    obtain ⟨M, hM, hMlt⟩ := hrsp ε (by simp only [hε]; linarith)
    have h1 : sInf (upper T '' π) ≤ upper T M := csInf_le hBbdd ⟨M, hM, rfl⟩
    have h2 : lower T M ≤ sSup (lower T '' π) := le_csSup hAbdd ⟨M, hM, rfl⟩
    simp only [hε] at hMlt
    linarith
  · intro heq ε hε
    obtain ⟨a, ⟨M, hM, rfl⟩, hMa⟩ :
        ∃ a ∈ lower T '' π, sSup (lower T '' π) - ε / 2 < a :=
      exists_lt_of_lt_csSup hAne (by linarith)
    obtain ⟨b, ⟨N, hN, rfl⟩, hNb⟩ :
        ∃ b ∈ upper T '' π, b < sInf (upper T '' π) + ε / 2 :=
      exists_lt_of_csInf_lt hBne (by linarith)
    refine ⟨M ⊓ N, hπ.inf_mem M hM N hN, ?_⟩
    have hbot : M ⊓ N ≠ ⊥ := hπ.inf_ne_bot hM hN
    have hu : upper T (M ⊓ N) ≤ upper T N := upper_mono hbot inf_le_right
    have hl : lower T M ≤ lower T (M ⊓ N) := lower_mono' hbot inf_le_left
    rw [heq] at hMa
    linarith

/-  D2, contract statement, preserved verbatim:

theorem rsp_iff_sup_eq_inf (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x) :
    RSP π T ↔
      sSup (lower T '' π) = sInf (upper T '' π)

    As with A1 this fails over the zero space: there `π = ∅` is a pluf,
    both sides of the right-hand equation are `sSup ∅ = sInf ∅ = 0`, and
    `RSP ∅ T` is false. The marked minimal repair adds `[Nontrivial E]`. -/

/-- D2 (Proposition 3.2; the gap criterion), minimal repair: `E ≠ 0`.
    RSP for `T` holds iff the supremum of the lower values equals the
    infimum of the upper values.  The contracted positivity hypothesis
    `hpos` is retained as contracted, though `rsp_iff_sup_eq_inf'` shows
    that it is not needed. -/
theorem rsp_iff_sup_eq_inf [Nontrivial E] (T : E →L[ℝ] E)
    (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x) :
    RSP π T ↔
      sSup (lower T '' π) = sInf (upper T '' π) :=
  rsp_iff_sup_eq_inf' T π hπ

end GeneralPosition

end PlufWO6
