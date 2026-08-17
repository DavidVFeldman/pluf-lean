/-
  PlufWO6/PartE.lean — Work Order 6, Part E: the face of the state space
  cut out by a pluf (Paper I, Proposition 3.4 and its corollaries).

  GATE VERDICT (recorded in REPORT-WO6.md): the infrastructure Mathlib
  provides is SUFFICIENT, and Part E is delivered in full.  What is used:

  * `exists_extension_of_le_sublinear` — Hahn–Banach dominated extension
    for a sublinear `N : V → ℝ` on a real vector space.  This is exactly
    the form the paper's argument needs, applied to the sublinear
    functional `plimsup π T = ⨅_{M ∈ π} upper T M` on all of `B(E)` (not
    merely on the self-adjoint part: the Rayleigh form only sees the
    symmetric part of an operator, so no restriction is necessary).
  * `LinearMap.mkContinuous` — to package the extension as an element of
    the dual, the bound being `|g T| ≤ ‖T‖`.
  * `ContinuousLinearMap.adjoint`, `Submodule.starProjection`,
    `isSelfAdjoint_starProjection`, `Submodule.isIdempotentElem_starProjection`,
    `Submodule.inner_starProjection_left_eq_right`,
    `Submodule.starProjection_eq_self_iff` — the projection calculus.

  Mathlib has no `State` structure for a general real `B(E)` (its C⋆-algebra
  state theory is for `StarOrderedRing`s and does not apply verbatim to a
  real Hilbert space's operator algebra), so the contracted `IsState`
  shape is retained; see `PlufWO6/States.lean`.  Banach–Alaoglu
  (`WeakDual.isCompact_polar` and kin) is available but is NOT needed:
  E1's nonemptiness is obtained by Hahn–Banach directly, and E3's face
  property is elementary.  The weak-* closedness/convexity half of the
  paper's Proposition 3.4 is a statement about the weak-* topology that
  the contract does not ask for; E3 as contracted is the face property.

  As in Parts A, C and D, the results need `E ≠ 0`: over the zero space
  `π = ∅` is a pluf and no functional is normalized on it.
-/
import RequestProject.PlufWO6.States

open Set
open scoped Classical Pointwise

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The sublinear functional of a pluf -/

section Plimsup

variable (π : Set (Submodule ℝ E))

/-- The pluf-limsup of `T`: the infimum of the upper Rayleigh values along
    the filter. -/
noncomputable def plimsup (T : E →L[ℝ] E) : ℝ := sInf (upper T '' π)

omit [CompleteSpace E] in
theorem plimsup_eq (T : E →L[ℝ] E) : plimsup π T = sInf (upper T '' π) := rfl

/-- The pluf-liminf of `T`: the supremum of the lower Rayleigh values. -/
noncomputable def pliminf (T : E →L[ℝ] E) : ℝ := sSup (lower T '' π)

variable {π}

omit [CompleteSpace E]

theorem upper_image_bddBelow (hπ : IsPluf π) (T : E →L[ℝ] E) :
    BddBelow (upper T '' π) := by
  refine ⟨-‖T‖, ?_⟩
  rintro a ⟨M, hM, rfl⟩
  exact (abs_le.mp (abs_upper_le_norm (hπ.ne_bot hM))).1

theorem upper_image_bddAbove (hπ : IsPluf π) (T : E →L[ℝ] E) :
    BddAbove (upper T '' π) := by
  refine ⟨‖T‖, ?_⟩
  rintro a ⟨M, hM, rfl⟩
  exact (abs_le.mp (abs_upper_le_norm (hπ.ne_bot hM))).2

theorem lower_image_bddAbove (hπ : IsPluf π) (T : E →L[ℝ] E) :
    BddAbove (lower T '' π) := by
  refine ⟨‖T‖, ?_⟩
  rintro a ⟨M, hM, rfl⟩
  exact (abs_le.mp (abs_lower_le_norm (hπ.ne_bot hM))).2

theorem lower_image_bddBelow (hπ : IsPluf π) (T : E →L[ℝ] E) :
    BddBelow (lower T '' π) := by
  refine ⟨-‖T‖, ?_⟩
  rintro a ⟨M, hM, rfl⟩
  exact (abs_le.mp (abs_lower_le_norm (hπ.ne_bot hM))).1

theorem plimsup_le_upper (hπ : IsPluf π) {T : E →L[ℝ] E} {M : Submodule ℝ E}
    (hM : M ∈ π) : plimsup π T ≤ upper T M :=
  csInf_le (upper_image_bddBelow hπ T) ⟨M, hM, rfl⟩

theorem lower_le_pliminf (hπ : IsPluf π) {T : E →L[ℝ] E} {M : Submodule ℝ E}
    (hM : M ∈ π) : lower T M ≤ pliminf π T :=
  le_csSup (lower_image_bddAbove hπ T) ⟨M, hM, rfl⟩

theorem pliminf_le_plimsup [Nontrivial E] (hπ : IsPluf π) (T : E →L[ℝ] E) :
    pliminf π T ≤ plimsup π T := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  refine csSup_le ⟨lower T M₀, M₀, hM₀, rfl⟩ ?_
  rintro a ⟨M, hM, rfl⟩
  refine le_csInf ⟨upper T M₀, M₀, hM₀, rfl⟩ ?_
  rintro b ⟨N, hN, rfl⟩
  exact lower_le_upper' hπ hM hN

/-- Negation swaps the two pluf-limits. -/
theorem plimsup_neg (T : E →L[ℝ] E) : plimsup π (-T) = -pliminf π T := by
  have himg : upper (-T) '' π = -(lower T '' π) := by
    ext a
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact ⟨M, hM, by rw [upper_neg, neg_neg]⟩
    · rintro ⟨M, hM, hMa⟩
      exact ⟨M, hM, by rw [upper_neg, hMa, neg_neg]⟩
  rw [plimsup, pliminf, himg, Real.sInf_neg]

theorem pliminf_neg (T : E →L[ℝ] E) : pliminf π (-T) = -plimsup π T := by
  have h := plimsup_neg (π := π) (-T)
  rw [neg_neg] at h
  linarith [h]

theorem plimsup_smul {c : ℝ} (hc : 0 ≤ c) (T : E →L[ℝ] E) :
    plimsup π (c • T) = c * plimsup π T := by
  have himg : upper (c • T) '' π = c • (upper T '' π) := by
    ext a
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact ⟨upper T M, ⟨M, hM, rfl⟩, by rw [upper_smul hc, smul_eq_mul]⟩
    · rintro ⟨b, ⟨M, hM, rfl⟩, rfl⟩
      exact ⟨M, hM, by rw [upper_smul hc, smul_eq_mul]⟩
  rw [plimsup, plimsup, himg, Real.sInf_smul_of_nonneg hc, smul_eq_mul]

theorem plimsup_zero [Nontrivial E] (hπ : IsPluf π) : plimsup π (0 : E →L[ℝ] E) = 0 := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  have himg : upper (0 : E →L[ℝ] E) '' π = {0} := by
    ext a
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨M, hM, rfl⟩
      have hz : rayleighSet (0 : E →L[ℝ] E) M = {0} := by
        ext b
        simp only [Set.mem_singleton_iff]
        constructor
        · rintro ⟨x, -, rfl⟩; simp
        · intro hb
          obtain ⟨d, x, hx, -⟩ := rayleighSet_nonempty (T := (0 : E →L[ℝ] E)) (hπ.ne_bot hM)
          exact ⟨x, hx, by simp [hb]⟩
      rw [upper_eq, hz, csSup_singleton]
    · intro ha
      refine ⟨M₀, hM₀, ?_⟩
      have hz : rayleighSet (0 : E →L[ℝ] E) M₀ = {0} := by
        ext b
        simp only [Set.mem_singleton_iff]
        constructor
        · rintro ⟨x, -, rfl⟩; simp
        · intro hb
          obtain ⟨d, x, hx, -⟩ := rayleighSet_nonempty (T := (0 : E →L[ℝ] E)) (hπ.ne_bot hM₀)
          exact ⟨x, hx, by simp [hb]⟩
      rw [upper_eq, hz, csSup_singleton, ha]
  rw [plimsup, himg, csInf_singleton]

theorem plimsup_one [Nontrivial E] (hπ : IsPluf π) :
    plimsup π (ContinuousLinearMap.id ℝ E) = 1 := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  have himg : upper (ContinuousLinearMap.id ℝ E) '' π = {1} := by
    ext a
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact upper_one (hπ.ne_bot hM)
    · intro ha
      exact ⟨M₀, hM₀, by rw [upper_one (hπ.ne_bot hM₀), ha]⟩
  rw [plimsup, himg, csInf_singleton]

theorem pliminf_one [Nontrivial E] (hπ : IsPluf π) :
    pliminf π (ContinuousLinearMap.id ℝ E) = 1 := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  have himg : lower (ContinuousLinearMap.id ℝ E) '' π = {1} := by
    ext a
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact lower_one (hπ.ne_bot hM)
    · intro ha
      exact ⟨M₀, hM₀, by rw [lower_one (hπ.ne_bot hM₀), ha]⟩
  rw [pliminf, himg, csSup_singleton]

/-- Subadditivity: the essential use of the filter property. -/
theorem plimsup_add_le [Nontrivial E] (hπ : IsPluf π) (S T : E →L[ℝ] E) :
    plimsup π (S + T) ≤ plimsup π S + plimsup π T := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨u, ⟨M, hM, rfl⟩, hu⟩ : ∃ u ∈ upper S '' π, u < plimsup π S + ε / 2 :=
    exists_lt_of_csInf_lt ⟨upper S M₀, M₀, hM₀, rfl⟩
      (by rw [← plimsup_eq]; linarith)
  obtain ⟨v, ⟨N, hN, rfl⟩, hv⟩ : ∃ v ∈ upper T '' π, v < plimsup π T + ε / 2 :=
    exists_lt_of_csInf_lt ⟨upper T M₀, M₀, hM₀, rfl⟩
      (by rw [← plimsup_eq]; linarith)
  have hmem : M ⊓ N ∈ π := hπ.inf_mem M hM N hN
  have hbot : M ⊓ N ≠ ⊥ := hπ.inf_ne_bot hM hN
  have h1 : plimsup π (S + T) ≤ upper (S + T) (M ⊓ N) := plimsup_le_upper hπ hmem
  have h2 : upper (S + T) (M ⊓ N) ≤ upper S (M ⊓ N) + upper T (M ⊓ N) := upper_add_le hbot
  have h3 : upper S (M ⊓ N) ≤ upper S M := upper_mono hbot inf_le_left
  have h4 : upper T (M ⊓ N) ≤ upper T N := upper_mono hbot inf_le_right
  linarith

theorem plimsup_le_norm [Nontrivial E] (hπ : IsPluf π) (T : E →L[ℝ] E) :
    plimsup π T ≤ ‖T‖ := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  exact le_trans (plimsup_le_upper hπ hM₀) (abs_le.mp (abs_upper_le_norm (hπ.ne_bot hM₀))).2

/-- For a positive operator `A` the pluf-limsup of `-A` is nonpositive. -/
theorem plimsup_neg_nonpos_of_pos [Nontrivial E] (hπ : IsPluf π) {A : E →L[ℝ] E}
    (hA : ∀ x, 0 ≤ inner (𝕜 := ℝ) (A x) x) : plimsup π (-A) ≤ 0 := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  refine le_trans (plimsup_le_upper hπ hM₀) ?_
  refine csSup_le (rayleighSet_nonempty (T := -A) (hπ.ne_bot hM₀)) ?_
  rintro a ⟨x, -, rfl⟩
  show inner (𝕜 := ℝ) ((-A) x) x ≤ 0
  have : inner (𝕜 := ℝ) ((-A) x) x = -inner (𝕜 := ℝ) (A x) x := by simp
  rw [this]
  linarith [hA x]

end Plimsup

/-! ### The projection calculus -/

section Projections

variable {M : Submodule ℝ E} [M.HasOrthogonalProjection]

omit [CompleteSpace E]

theorem inner_starProjection_self (x : E) :
    inner (𝕜 := ℝ) (M.starProjection x) x = ‖M.starProjection x‖ ^ 2 := by
  have hidem : M.starProjection (M.starProjection x) = M.starProjection x := by
    have h := M.isIdempotentElem_starProjection
    have h2 := congrArg (fun S : E →L[ℝ] E => S x) h
    simpa using h2
  calc inner (𝕜 := ℝ) (M.starProjection x) x
      = inner (𝕜 := ℝ) (M.starProjection (M.starProjection x)) x := by rw [hidem]
    _ = inner (𝕜 := ℝ) (M.starProjection x) (M.starProjection x) :=
        M.inner_starProjection_left_eq_right _ _
    _ = ‖M.starProjection x‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem norm_starProjection_le (x : E) : ‖M.starProjection x‖ ≤ ‖x‖ := by
  have h1 : ‖M.starProjection x‖ ^ 2 = inner (𝕜 := ℝ) (M.starProjection x) x :=
    (inner_starProjection_self x).symm
  have h2 : inner (𝕜 := ℝ) (M.starProjection x) x ≤ ‖M.starProjection x‖ * ‖x‖ :=
    real_inner_le_norm _ _
  nlinarith [norm_nonneg (M.starProjection x), norm_nonneg x]

/-- The upper Rayleigh value of a projection never exceeds `1`. -/
theorem upper_starProjection_le_one {N : Submodule ℝ E} (hN : N ≠ ⊥) :
    upper M.starProjection N ≤ 1 := by
  refine csSup_le (rayleighSet_nonempty (T := M.starProjection) hN) ?_
  rintro a ⟨x, ⟨-, hx1⟩, rfl⟩
  show inner (𝕜 := ℝ) (M.starProjection x) x ≤ 1
  rw [inner_starProjection_self]
  have := norm_starProjection_le (M := M) x
  rw [hx1] at this
  nlinarith [norm_nonneg (M.starProjection x)]

/-- Below `M` the projection onto `M` is the identity, so both Rayleigh
    values are `1`. -/
theorem rayleighSet_starProjection_of_le {N : Submodule ℝ E} (hN : N ≠ ⊥) (hNM : N ≤ M) :
    rayleighSet M.starProjection N = {1} := by
  ext a
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hxN, hx1⟩, rfl⟩
    show inner (𝕜 := ℝ) (M.starProjection x) x = 1
    rw [Submodule.starProjection_eq_self_iff.mpr (hNM hxN), real_inner_self_eq_norm_sq, hx1]
    norm_num
  · intro ha
    obtain ⟨b, x, ⟨hxN, hx1⟩, -⟩ := rayleighSet_nonempty (T := M.starProjection) hN
    refine ⟨x, ⟨hxN, hx1⟩, ?_⟩
    show inner (𝕜 := ℝ) (M.starProjection x) x = a
    rw [Submodule.starProjection_eq_self_iff.mpr (hNM hxN), real_inner_self_eq_norm_sq, hx1, ha]
    norm_num

theorem lower_starProjection_self {N : Submodule ℝ E} (hN : N ≠ ⊥) (hNM : N ≤ M) :
    lower M.starProjection N = 1 := by
  rw [lower_eq, rayleighSet_starProjection_of_le hN hNM, csInf_singleton]

theorem upper_starProjection_self {N : Submodule ℝ E} (hN : N ≠ ⊥) (hNM : N ≤ M) :
    upper M.starProjection N = 1 := by
  rw [upper_eq, rayleighSet_starProjection_of_le hN hNM, csSup_singleton]

end Projections

/-! ### The face of a pluf -/

section Face

variable {π : Set (Submodule ℝ E)}

omit [CompleteSpace E] in
/-- A functional dominated by the pluf-limsup is a state. -/
theorem isState_of_le_plimsup [Nontrivial E] (hπ : IsPluf π)
    {φ : (E →L[ℝ] E) →L[ℝ] ℝ} (h : ∀ T, φ T ≤ plimsup π T) : IsState φ := by
  constructor
  · intro A hA
    have h1 : φ (-A) ≤ plimsup π (-A) := h (-A)
    have h2 : plimsup π (-A) ≤ 0 := plimsup_neg_nonpos_of_pos hπ hA
    have h3 : φ (-A) = -φ A := by rw [map_neg]
    linarith [h3 ▸ h1]
  · have h1 : φ (ContinuousLinearMap.id ℝ E) ≤ 1 := by
      have := h (ContinuousLinearMap.id ℝ E)
      rwa [plimsup_one hπ] at this
    have h2 : φ (-(ContinuousLinearMap.id ℝ E)) ≤ -1 := by
      have := h (-(ContinuousLinearMap.id ℝ E))
      rwa [plimsup_neg, pliminf_one hπ] at this
    rw [map_neg] at h2
    linarith

/-- A functional dominated by the pluf-limsup lies in the face of `π`. -/
theorem mem_face_of_le_plimsup (hπ : IsPluf π)
    {φ : (E →L[ℝ] E) →L[ℝ] ℝ} (h : ∀ T, φ T ≤ plimsup π T) :
    ∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1 := by
  intro M hM hMc
  have hbot : M ≠ ⊥ := hπ.ne_bot hM
  have hle : φ (M.starProjection) ≤ 1 :=
    le_trans (h _) (le_trans (plimsup_le_upper hπ hM) (upper_starProjection_le_one hbot))
  have hge : φ (-(M.starProjection)) ≤ -1 := by
    refine le_trans (h _) (le_trans (plimsup_le_upper hπ hM) ?_)
    rw [upper_neg, lower_starProjection_self hbot le_rfl]
  rw [map_neg] at hge
  linarith

/-- The construction lemma behind Part E: for every `T₁` and every value
    `a` compatible with the sublinear functional along the ray through
    `T₁`, there is a state in the face of `π` taking the value `a` at
    `T₁`.  This is Hahn–Banach dominated extension. -/
theorem exists_state_with_value [Nontrivial E] (hπ : IsPluf π)
    (T₁ : E →L[ℝ] E) (a : ℝ) (ha : ∀ c : ℝ, c * a ≤ plimsup π (c • T₁)) :
    ∃ φ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ ∧
      (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1) ∧
      φ T₁ = a := by
  have hplim0 : plimsup π (0 : E →L[ℝ] E) = 0 := plimsup_zero hπ
  have H : ∀ c : ℝ, c • T₁ = 0 → c • a = 0 := by
    intro c hc
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have hT1 : T₁ = 0 := by
        have hh : c⁻¹ • (c • T₁) = c⁻¹ • (0 : E →L[ℝ] E) := by rw [hc]
        rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul, smul_zero] at hh
      subst hT1
      have h1 := ha 1
      have h2 := ha (-1)
      rw [one_smul, hplim0] at h1
      rw [neg_one_smul, neg_zero, hplim0] at h2
      have haz : a = 0 := by linarith
      simp [haz]
  have hf : ∀ x : (LinearPMap.mkSpanSingleton' T₁ a H).domain,
      (LinearPMap.mkSpanSingleton' T₁ a H) x ≤ plimsup π (x : E →L[ℝ] E) := by
    intro x
    have hxmem : (x : E →L[ℝ] E) ∈ Submodule.span ℝ ({T₁} : Set (E →L[ℝ] E)) := by
      rw [← LinearPMap.domain_mkSpanSingleton T₁ a H]
      exact x.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxmem
    have hmem' : c • T₁ ∈ (LinearPMap.mkSpanSingleton' T₁ a H).domain := by
      rw [LinearPMap.domain_mkSpanSingleton]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    have hxeq : x = ⟨c • T₁, hmem'⟩ := Subtype.ext hc.symm
    rw [hxeq, LinearPMap.mkSpanSingleton'_apply]
    simpa [smul_eq_mul] using ha c
  obtain ⟨g, hgext, hgle⟩ := exists_extension_of_le_sublinear
    (LinearPMap.mkSpanSingleton' T₁ a H) (plimsup π)
    (fun c hc T => plimsup_smul hc.le T) (fun S T => plimsup_add_le hπ S T) hf
  have hbound : ∀ T : E →L[ℝ] E, ‖g T‖ ≤ 1 * ‖T‖ := by
    intro T
    have h1 : g T ≤ ‖T‖ := le_trans (hgle T) (plimsup_le_norm hπ T)
    have h2 : g (-T) ≤ ‖T‖ := by
      have := le_trans (hgle (-T)) (plimsup_le_norm hπ (-T))
      simpa using this
    rw [map_neg] at h2
    rw [one_mul, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, h1⟩
  refine ⟨g.mkContinuous 1 hbound, ?_, ?_, ?_⟩
  · exact isState_of_le_plimsup hπ (fun T => by
      simpa [LinearMap.mkContinuous_apply] using hgle T)
  · exact mem_face_of_le_plimsup hπ (fun T => by
      simpa [LinearMap.mkContinuous_apply] using hgle T)
  · have hmem : T₁ ∈ (LinearPMap.mkSpanSingleton' T₁ a H).domain := by
      rw [LinearPMap.domain_mkSpanSingleton]
      exact Submodule.mem_span_singleton_self T₁
    have hmem1 : (1 : ℝ) • T₁ ∈ (LinearPMap.mkSpanSingleton' T₁ a H).domain := by
      rw [one_smul]; exact hmem
    have hx : (⟨T₁, hmem⟩ : (LinearPMap.mkSpanSingleton' T₁ a H).domain)
        = ⟨(1 : ℝ) • T₁, hmem1⟩ := Subtype.ext (one_smul ℝ T₁).symm
    have hfval : (LinearPMap.mkSpanSingleton' T₁ a H) ⟨T₁, hmem⟩ = a := by
      rw [hx, LinearPMap.mkSpanSingleton'_apply, one_smul]
    have hg := hgext ⟨T₁, hmem⟩
    simp only [LinearMap.mkContinuous_apply]
    rw [hg, hfval]

/-! ### E1–E4 -/

/-  E1, contract statement, preserved verbatim:

theorem face_nonempty (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    ∃ φ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ ∧
      ∀ M ∈ π, ∀ hM : IsClosed (M : Set E), φ (M.starProjection) = 1

    Over the zero space `π = ∅` is a pluf (see `isPluf_empty_zero_space`)
    and `φ (id) = 1` is impossible because `id = 0` there: no state
    exists at all.  The marked minimal repair adds `[Nontrivial E]`, as
    for A1, A5, C2 and D2. -/

/-- E1 (Proposition 3.4, nonemptiness), minimal repair: `E ≠ 0`.  The face
    is nonempty, by Hahn–Banach dominated extension against the sublinear
    functional `T ↦ ⨅_{M ∈ π} upper T M`. -/
theorem face_nonempty [Nontrivial E] (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    ∃ φ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ ∧
      ∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1 := by
  obtain ⟨φ, hφ, hface, -⟩ := exists_state_with_value hπ 0 0 (fun c => by
    rw [smul_zero, plimsup_zero hπ, mul_zero])
  exact ⟨φ, hφ, hface⟩

/-- E2 (the sandwich characterization) over a nonzero space.  A state lies
    in the face of `π` iff its value at every self-adjoint `T` is caught
    between the two pluf-limits.  (The contract form, with no hypothesis on
    `E`, follows: see `face_iff_sandwich`.) -/
theorem face_iff_sandwich' [Nontrivial E] (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : IsState φ) :
    (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1) ↔
      ∀ T : E →L[ℝ] E, IsSelfAdjoint T →
        sSup (lower T '' π) ≤ φ T ∧ φ T ≤ sInf (upper T '' π) := by
  obtain ⟨M₀, hM₀⟩ := hπ.nonempty
  constructor
  · intro hface T _hT
    -- the key estimate: `φ T ≤ upper T M` for every member `M`
    have key : ∀ (S : E →L[ℝ] E), ∀ M ∈ π, φ S ≤ upper S M := by
      intro S M hM
      haveI hMc : IsClosed (M : Set E) := hπ.mem_closed M hM
      have hP1 : φ (M.starProjection) = 1 := hface M hM hMc
      have hcomp : φ (M.starProjection ∘L S ∘L M.starProjection) = φ S :=
        hφ.compress hP1 S
      have hmono : φ (M.starProjection ∘L S ∘L M.starProjection)
          ≤ φ ((upper S M) • M.starProjection) := by
        refine hφ.mono (fun x => ?_)
        have hL : inner (𝕜 := ℝ) ((M.starProjection ∘L S ∘L M.starProjection) x) x
            = inner (𝕜 := ℝ) (S (M.starProjection x)) (M.starProjection x) := by
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
          exact M.inner_starProjection_left_eq_right _ _
        have hR : inner (𝕜 := ℝ) (((upper S M) • M.starProjection : E →L[ℝ] E) x) x
            = upper S M * ‖M.starProjection x‖ ^ 2 := by
          simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left]
          rw [inner_starProjection_self]
        rw [hL, hR]
        exact inner_le_upper_mul M (M.starProjection_apply_mem x)
      have hval : φ ((upper S M) • M.starProjection) = upper S M := by
        rw [map_smul, smul_eq_mul, hP1, mul_one]
      rw [hcomp, hval] at hmono
      exact hmono
    constructor
    · refine csSup_le ⟨lower T M₀, M₀, hM₀, rfl⟩ ?_
      rintro a ⟨M, hM, rfl⟩
      have h := key (-T) M hM
      rw [upper_neg, map_neg] at h
      linarith
    · refine le_csInf ⟨upper T M₀, M₀, hM₀, rfl⟩ ?_
      rintro b ⟨M, hM, rfl⟩
      exact key T M hM
  · intro hsand M hM hMc
    have hbot : M ≠ ⊥ := hπ.ne_bot hM
    obtain ⟨h1, h2⟩ := hsand (M.starProjection) (isSelfAdjoint_starProjection M)
    have hge : (1 : ℝ) ≤ φ (M.starProjection) := by
      refine le_trans ?_ h1
      refine le_csSup (lower_image_bddAbove hπ _) ?_
      exact ⟨M, hM, lower_starProjection_self hbot le_rfl⟩
    have hle : φ (M.starProjection) ≤ 1 := by
      refine le_trans h2 ?_
      refine le_trans (csInf_le (upper_image_bddBelow hπ _) ⟨M, hM, rfl⟩) ?_
      exact upper_starProjection_le_one hbot
    linarith

/-- E2 (the sandwich characterization), exactly as contracted: no
    hypothesis on `E` is needed.  Over the zero space the statement is
    vacuous, there being no state at all (`id = 0` there, so no functional
    is normalized). -/
theorem face_iff_sandwich (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (φ : (E →L[ℝ] E) →L[ℝ] ℝ) (hφ : IsState φ) :
    (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1) ↔
      ∀ T : E →L[ℝ] E, IsSelfAdjoint T →
        sSup (lower T '' π) ≤ φ T ∧ φ T ≤ sInf (upper T '' π) := by
  rcases subsingleton_or_nontrivial E with _ | hnt
  · exfalso
    have hid : (ContinuousLinearMap.id ℝ E) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have := hφ.norm_one
    rw [hid, map_zero] at this
    exact zero_ne_one this
  · exact face_iff_sandwich' π hπ φ hφ

omit [CompleteSpace E] in
/-- Every state is at most `1` on a projection. -/
theorem IsState.starProjection_le_one {φ : (E →L[ℝ] E) →L[ℝ] ℝ} (hφ : IsState φ)
    (M : Submodule ℝ E) [M.HasOrthogonalProjection] : φ (M.starProjection) ≤ 1 := by
  have hpos : 0 ≤ φ (ContinuousLinearMap.id ℝ E - M.starProjection) := by
    refine hφ.pos _ (fun x => ?_)
    have hx : inner (𝕜 := ℝ) ((ContinuousLinearMap.id ℝ E - M.starProjection) x) x
        = ‖x‖ ^ 2 - ‖M.starProjection x‖ ^ 2 := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_sub_left]
      rw [real_inner_self_eq_norm_sq, inner_starProjection_self]
    rw [hx]
    have := norm_starProjection_le (M := M) x
    nlinarith [norm_nonneg (M.starProjection x), norm_nonneg x]
  rw [map_sub, hφ.norm_one] at hpos
  linarith

/-- E3 (the face property).  If a proper convex combination of two states
    is `1` at every projection from `π`, both summands are.

    The contracted hypothesis `hπ : IsPluf π` is kept as contracted, but
    the proof does not use it: the face property holds for the set of
    states taking the value `1` on any family of projections. -/
theorem face_isFace (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    ∀ φ ψ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ → IsState ψ →
      ∀ t : ℝ, 0 < t → t < 1 →
      (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E),
        (t • φ + (1 - t) • ψ) (M.starProjection) = 1) →
      (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1) ∧
      (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), ψ (M.starProjection) = 1) := by
  intro φ ψ hφ hψ t ht0 ht1 hcomb
  have key : ∀ M ∈ π, ∀ _hM : IsClosed (M : Set E),
      φ (M.starProjection) = 1 ∧ ψ (M.starProjection) = 1 := by
    intro M hM hMc
    have h := hcomb M hM hMc
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul] at h
    have h1 := hφ.starProjection_le_one M
    have h2 := hψ.starProjection_le_one M
    constructor <;> nlinarith
  exact ⟨fun M hM hMc => (key M hM hMc).1, fun M hM hMc => (key M hM hMc).2⟩

/-- A state is determined by its values on self-adjoint operators. -/
theorem IsState.ext_of_selfAdjoint {φ ψ : (E →L[ℝ] E) →L[ℝ] ℝ}
    (hφ : IsState φ) (hψ : IsState ψ)
    (h : ∀ T : E →L[ℝ] E, IsSelfAdjoint T → φ T = ψ T) : φ = ψ := by
  ext A
  set S : E →L[ℝ] E := (2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A) with hS
  have hSsa : IsSelfAdjoint S := by
    rw [IsSelfAdjoint, hS]
    show ContinuousLinearMap.adjoint ((2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A))
      = (2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A)
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ, map_add,
      ContinuousLinearMap.adjoint_adjoint]
    simp [add_comm]
  have hval : ∀ χ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState χ → χ S = χ A := by
    intro χ hχ
    rw [hS, map_smul, map_add, hχ.adjoint A, smul_eq_mul]
    ring
  rw [← hval φ hφ, ← hval ψ hψ]
  exact h S hSsa

/-- E4 (RSP for all self-adjoint operators ⟺ the face is a singleton),
    minimal repair: `E ≠ 0`. -/
theorem rsp_all_iff_face_subsingleton [Nontrivial E] (π : Set (Submodule ℝ E))
    (hπ : IsPluf π) :
    (∀ T : E →L[ℝ] E, IsSelfAdjoint T → RSP π T) ↔
      ∀ φ ψ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ → IsState ψ →
        (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1) →
        (∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), ψ (M.starProjection) = 1) →
        φ = ψ := by
  constructor
  · intro hall φ ψ hφ hψ hfφ hfψ
    refine hφ.ext_of_selfAdjoint hψ (fun T hT => ?_)
    have heq : sSup (lower T '' π) = sInf (upper T '' π) :=
      (rsp_iff_sup_eq_inf' T π hπ).mp (hall T hT)
    obtain ⟨hφ1, hφ2⟩ := (face_iff_sandwich π hπ φ hφ).mp hfφ T hT
    obtain ⟨hψ1, hψ2⟩ := (face_iff_sandwich π hπ ψ hψ).mp hfψ T hT
    rw [heq] at hφ1 hψ1
    linarith
  · intro huniq
    by_contra hcon
    push_neg at hcon
    obtain ⟨T₀, hT₀sa, hT₀⟩ := hcon
    have hne : pliminf π T₀ ≠ plimsup π T₀ := by
      intro h
      exact hT₀ ((rsp_iff_sup_eq_inf' T₀ π hπ).mpr h)
    have hlt : pliminf π T₀ < plimsup π T₀ :=
      lt_of_le_of_ne (pliminf_le_plimsup hπ T₀) hne
    -- a state attaining the upper value
    obtain ⟨φ, hφ, hfφ, hφval⟩ := exists_state_with_value hπ T₀ (plimsup π T₀) (fun c => by
      rcases le_or_gt 0 c with hc | hc
      · rw [plimsup_smul hc]
      · have hcneg : (0:ℝ) ≤ -c := by linarith
        have hrw : c • T₀ = (-c) • (-T₀) := by
          rw [smul_neg, neg_smul, neg_neg]
        rw [hrw, plimsup_smul hcneg, plimsup_neg]
        nlinarith [pliminf_le_plimsup hπ T₀])
    -- a state attaining the lower value
    obtain ⟨ψ, hψ, hfψ, hψval⟩ := exists_state_with_value hπ T₀ (pliminf π T₀) (fun c => by
      rcases le_or_gt 0 c with hc | hc
      · rw [plimsup_smul hc]
        nlinarith [pliminf_le_plimsup hπ T₀]
      · have hcneg : (0:ℝ) ≤ -c := by linarith
        have hrw : c • T₀ = (-c) • (-T₀) := by
          rw [smul_neg, neg_smul, neg_neg]
        rw [hrw, plimsup_smul hcneg, plimsup_neg]
        ring_nf
        nlinarith [pliminf_le_plimsup hπ T₀])
    have := huniq φ ψ hφ hψ hfφ hfψ
    rw [this] at hφval
    rw [hφval] at hψval
    exact absurd hψval.symm (ne_of_lt hlt)

end Face

end PlufWO6
