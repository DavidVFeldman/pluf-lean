/-
  PlufWO4/EPP.lean — Work Order 4, Part C: the exact-paving property, its
  proof for the Fubini product (the centerpiece, Paper IV Theorem 4.1), and
  the transfer of the WO-2/WO-3 theory to EPP hypotheses.

  REFACTORING DECISION (C4–C6, reported): option (ii) of the licence — the
  EPP versions are proved fresh in this namespace, reusing the WO-2/WO-3
  auxiliary lemmas (`PlufWO2.inner_eq_coord_mul`, `PlufWO2.hasSum_coord_smul`,
  `PlufWO2.block_le_of_evec_mem`, `PlufWO2.block_mono`, …) as they stand and
  replacing only the paving input.  The WO-2/WO-3 files are untouched, so all
  39 prior theorems stay green verbatim.
-/
import RequestProject.PlufWO4.Fubini

open Set PlufWO2 PlufWO3

namespace PlufWO4

/-! ### Part C: the exact-paving property and the transfer -/

section EPPDef

variable {X : Type*}

/-- The exact-paving property (Paper IV, Definition 5.1). -/
def EPP (U : Ultrafilter X) : Prop :=
  ∀ c : X → Set X, (∀ x, (c x).Countable) →
    ∃ S ∈ U, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → y ∉ c x

/-- C1 (EPP ⇒ σ-Q; Paper IV, Section 5). Apply EPP to
    `c x = (piece of x) \ {x}`. -/
theorem sigmaQ_of_EPP (U : Ultrafilter X) (hEPP : EPP U) :
    PlufWO1.SigmaQPoint U := by
  intro g hg
  obtain ⟨S, hS, hmut⟩ := hEPP (fun x => g ⁻¹' {g x} \ {x})
    (fun x => ((hg (g x)).mono (fun y hy => hy)).mono (fun y hy => hy.1))
  refine ⟨S, hS, ?_⟩
  intro a ha b hb hab
  by_contra hne
  exact hmut a ha b hb hne ⟨by simpa using hab.symm, by simpa using (Ne.symm hne)⟩

end EPPDef

section Product

variable {κ : Type*} [LinearOrder κ]

/-- C2 (Exact paving for the product; Paper IV, Theorem 4.1 — the
    centerpiece). Under the Part A hypotheses on `D`, the self-product has
    EPP.

    The membership-pattern analysis is `exists_avoiding_homog`
    (`PlufWO4/Homog.lean`): the twelve ordered placement patterns of a pair
    of distinct increasing pairs — six on a three-element set and six on a
    four-element set — are homogenized separately, and each "yes" colour is
    refuted by freezing `x` and freeing a coordinate of `y`, upward along a
    tail (`htail`) or below an uncountable pivot (`UncountablePivots`).

    PATTERN-ANALYSIS FINDING (reported).  The paper's Section 4 enumerates
    the placement patterns as *unordered* pairs of positions, then treats
    "x on top" and "y on top" as the two regimes.  Mechanization requires
    the ordered enumeration: for each of the three ways of splitting a
    four-element set into two disjoint pairs, and each of the three pairs
    from a three-element set, *both* assignments of the roles `x` and `y`
    must be refuted, twelve patterns in all.  All twelve are refutable, so
    the theorem stands as claimed; but two of them (the patterns
    `x = (h₁,h₃), y = (h₁,h₂)` and `x = (h₃,h₄), y = (h₁,h₂)`, where the
    free coordinate of `y` must be found *between* two coordinates of `x`)
    are not covered by either of the paper's two regimes as literally
    stated: freeing a coordinate below a pivot is not enough, since the
    pivot must be taken *above* an already-fixed coordinate of `x`.  The
    fix is small and is the lemma `exists_mid`: apply `UncountablePivots`
    to the tail `H ∩ (γ, →)` rather than to `H`, which yields uncountably
    many points of `H` strictly between `γ` and the pivot. -/
theorem EPP_fubini (D : Ultrafilter κ)
    (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
    (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D) :
    EPP (fubini D D) := by
  intro c hc
  obtain ⟨H, hH, havoid⟩ := exists_avoiding_homog h3 h4 hpiv htail
    (fun a b => c (a, b)) (fun a b => hc (a, b))
  refine ⟨{p : κ × κ | p.1 ∈ H ∧ p.2 ∈ H ∧ p.1 < p.2}, triangle_mem_fubini D htail hH, ?_⟩
  rintro ⟨a, b⟩ ⟨haH, hbH, hab⟩ ⟨a', b'⟩ ⟨ha'H, hb'H, ha'b'⟩ hne
  exact havoid a haH b hbH a' ha'H b' hb'H hab ha'b' hne

end Product

section Transfer

variable {X : Type*} [LinearOrder X]

/-- C3 (exact paving of operators from EPP). The conclusion of
    `PlufWO2.exact_paving`, with `DiagInt` replaced by EPP; the countable
    avoidance sets are the supports of `T (evec x)` (`countable_supp`).

    Route report: the adjoint of `T` is not needed here.  WO-2's diagonal
    intersection was one-sided, so the `α < β` half of the argument had to
    be complemented by the adjoint; EPP is symmetric in `x` and `y`, so a
    single family of supports serves both halves. -/
theorem exact_paving_of_EPP (U : Ultrafilter X) (hEPP : EPP U)
    (T : Hk X →L[ℝ] Hk X) :
    ∃ S ∈ U, ∀ α ∈ S, ∀ β ∈ S, α ≠ β →
      inner (𝕜 := ℝ) (T (evec α)) (evec β) = 0 := by
  obtain ⟨S, hS, hmut⟩ := hEPP (fun α => supp (T (evec α))) (fun α => countable_supp _)
  refine ⟨S, hS, ?_⟩
  intro α hα β hβ hne
  rw [inner_evec_right]
  by_contra hcoord
  exact hmut α hα β hβ hne hcoord

/-- C4 (the exact dichotomy from EPP; Paper IV, Theorem 5.2).

    Note: the smallness hypothesis `hsmall` of the contract is retained as
    stated, but it is not needed once paving is available — in WO-2 it was
    consumed only by `exact_paving`. -/
theorem exact_dichotomy_of_EPP (U : Ultrafilter X) (hEPP : EPP U)
    (hsmall : ∀ s : Set X, s.Countable → sᶜ ∈ U)
    (W : Submodule ℝ (Hk X)) (hW : IsClosed (W : Set (Hk X))) :
    ∃ S ∈ U, block S ≤ W ∨ W ⊓ block S = ⊥ := by
  classical
  haveI : CompleteSpace W := hW.completeSpace_coe
  set P : Hk X →L[ℝ] Hk X := (Wᗮ).starProjection with hP
  obtain ⟨S₀, hS₀U, hoff⟩ := exact_paving_of_EPP U hEPP P
  set S₁ : Set X := {α ∈ S₀ | evec α ∈ W}
  by_cases h1 : S₁ ∈ U
  · exact ⟨S₁, h1, Or.inl (block_le_of_evec_mem W hW S₁ (fun _ hα => hα.2))⟩
  · have h2 : S₀ \ S₁ ∈ U := by
      have hc : S₁ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr h1
      have hi : S₀ ∩ S₁ᶜ ∈ U := Filter.inter_mem hS₀U hc
      rwa [← Set.diff_eq] at hi
    refine ⟨S₀ \ S₁, h2, Or.inr ?_⟩
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxB⟩
    have hxB0 : x ∈ block S₀ := block_mono Set.diff_subset hxB
    have hall : ∀ α : X, (x : ∀ _ : X, ℝ) α = 0 := by
      intro α
      by_cases hα : α ∈ S₀ \ S₁
      · have hnW : evec α ∉ W := fun hm => hα.2 ⟨hα.1, hm⟩
        have key := inner_eq_coord_mul S₀ P hoff hxB0 hα.1
        -- the left-hand side vanishes: `P (evec α) ∈ Wᗮ` and `x ∈ W`
        have hleft : inner (𝕜 := ℝ) (P (evec α)) x = 0 := by
          have hmemo : P (evec α) ∈ Wᗮ := Submodule.starProjection_apply_mem _ _
          have := (Submodule.mem_orthogonal W (P (evec α))).mp hmemo x hxW
          rw [real_inner_comm]
          exact this
        -- the diagonal entry is `‖P (evec α)‖² ≠ 0`
        have hdiagv : inner (𝕜 := ℝ) (P (evec α)) (evec α)
            = inner (𝕜 := ℝ) (P (evec α)) (P (evec α)) := by
          have hsub : evec α - P (evec α) ∈ (Wᗮ)ᗮ :=
            Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) (evec α)
          have hz : inner (𝕜 := ℝ) (P (evec α)) (evec α - P (evec α)) = 0 :=
            (Submodule.mem_orthogonal (Wᗮ) _).mp hsub _ (Submodule.starProjection_apply_mem _ _)
          rw [inner_sub_right] at hz
          linarith
        have hPne : P (evec α) ≠ 0 := by
          intro h0
          rw [hP, Submodule.starProjection_apply_eq_zero_iff,
            Submodule.orthogonal_orthogonal] at h0
          exact hnW h0
        have hpos : inner (𝕜 := ℝ) (P (evec α)) (P (evec α)) ≠ 0 := by
          simpa [inner_self_eq_zero] using hPne
        rw [hleft, hdiagv] at key
        exact (mul_eq_zero.mp key.symm).resolve_right hpos
      · exact (mem_block_iff _ x).mp hxB α hα
    have hx0 : x = 0 := lp.ext (funext hall)
    simpa using hx0

/-- C5 (the diagonal flattening from EPP; Paper IV, Theorem 5.2).  The
    WO-3 proof of `PlufWO3.quadratic_flat` consumed normality only through
    the paving conclusion; the argument below is that proof with
    `exact_paving_of_EPP` in place of `PlufWO2.exact_paving`. -/
theorem quadratic_flat_of_EPP (U : Ultrafilter X) (hEPP : EPP U)
    (T : Hk X →L[ℝ] Hk X) (L : ℝ)
    (hL : ∀ ε > 0, {α | |inner (𝕜 := ℝ) (T (evec α)) (evec α) - L| ≤ ε} ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S ∈ U, ∀ x ∈ block S,
      |inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2 := by
  classical
  obtain ⟨S₀, hS₀U, hoff⟩ := exact_paving_of_EPP U hEPP T
  set d : X → ℝ := fun α => inner (𝕜 := ℝ) (T (evec α)) (evec α) with hd
  have hAU : {α : X | |d α - L| ≤ ε} ∈ U := hL ε hε
  refine ⟨S₀ ∩ {α : X | |d α - L| ≤ ε}, Filter.inter_mem hS₀U hAU, ?_⟩
  intro x hx
  have hxS₀ : x ∈ block S₀ := block_mono Set.inter_subset_left hx
  -- the ℓ²-expansion of the quadratic form along the standard basis
  have hexp := hasSum_coord_smul ((innerSL ℝ x).comp T) x
  have hfx : ((innerSL ℝ x).comp T) x = inner (𝕜 := ℝ) (T x) x := by
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply]
    exact real_inner_comm (T x) x
  have hterm : ∀ β : X, (x : ∀ _ : X, ℝ) β * ((innerSL ℝ x).comp T) (evec β)
      = ((x : ∀ _ : X, ℝ) β) ^ 2 * d β := by
    intro β
    by_cases hβ : β ∈ S₀
    · have hcoord := inner_eq_coord_mul S₀ T hoff hxS₀ hβ
      have hval : ((innerSL ℝ x).comp T) (evec β) = inner (𝕜 := ℝ) (T (evec β)) x := by
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply]
        exact real_inner_comm (T (evec β)) x
      rw [hval, hcoord, hd]
      ring
    · have hxβ : (x : ∀ _ : X, ℝ) β = 0 :=
        (mem_block_iff _ x).mp hx β (fun hm => hβ hm.1)
      rw [hxβ]
      ring
  rw [funext hterm, hfx] at hexp
  -- the ℓ²-expansion of the norm
  have hnorm : HasSum (fun β : X => ((x : ∀ _ : X, ℝ) β) ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : X => ℝ) (p := 2) (by norm_num) x
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    rw [h2] at h
    have hcast : ∀ y : ℝ, 0 ≤ y → y ^ (2:ℝ) = y ^ (2:ℕ) := by
      intro y _
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hcast ‖x‖ (norm_nonneg _)] at h
    refine h.congr_fun (fun β => ?_)
    rw [hcast _ (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  -- termwise comparison
  have hbound : ∀ β : X,
      |((x : ∀ _ : X, ℝ) β) ^ 2 * d β - L * ((x : ∀ _ : X, ℝ) β) ^ 2|
        ≤ ε * ((x : ∀ _ : X, ℝ) β) ^ 2 := by
    intro β
    by_cases hxβ : (x : ∀ _ : X, ℝ) β = 0
    · simp [hxβ]
    · have hβmem : β ∈ S₀ ∩ {α : X | |d α - L| ≤ ε} := by
        by_contra hmem
        exact hxβ ((mem_block_iff _ x).mp hx β hmem)
      have hdA : |d β - L| ≤ ε := hβmem.2
      have hrw : ((x : ∀ _ : X, ℝ) β) ^ 2 * d β - L * ((x : ∀ _ : X, ℝ) β) ^ 2
          = ((x : ∀ _ : X, ℝ) β) ^ 2 * (d β - L) := by ring
      rw [hrw, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm ε]
      exact mul_le_mul_of_nonneg_left hdA (sq_nonneg _)
  have hdiff : HasSum
      (fun β : X => ((x : ∀ _ : X, ℝ) β) ^ 2 * d β - L * ((x : ∀ _ : X, ℝ) β) ^ 2)
      (inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2) := hexp.sub (hnorm.mul_left L)
  have hscaled : HasSum (fun β : X => ε * ((x : ∀ _ : X, ℝ) β) ^ 2) (ε * ‖x‖ ^ 2) :=
    hnorm.mul_left ε
  have hub : inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2 ≤ ε * ‖x‖ ^ 2 :=
    hasSum_le (fun β => (abs_le.mp (hbound β)).2) hdiff hscaled
  have hlb : -(ε * ‖x‖ ^ 2) ≤ inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2 :=
    hasSum_le (fun β => (abs_le.mp (hbound β)).1) hscaled.neg hdiff
  exact abs_le.mpr ⟨hlb, hub⟩

/-! ### Part H: the block filter Φ(U), as a filter -/

/-- C6 (the decision property of `PhiU` from EPP; Paper IV, Theorem 5.2).

    Note: as in C4, `hsmall` is retained from the contract but not needed. -/
theorem PhiU_decides_of_EPP (U : Ultrafilter X) (hEPP : EPP U)
    (hsmall : ∀ s : Set X, s.Countable → sᶜ ∈ U)
    (W : Submodule ℝ (Hk X)) (hW : IsClosed (W : Set (Hk X))) :
    W ∈ PhiU U ∨ ∃ M ∈ PhiU U, W ⊓ M = ⊥ := by
  rcases exact_dichotomy_of_EPP U hEPP hsmall W hW with ⟨S, hSU, hS | hS⟩
  · exact Or.inl ⟨S, hSU, hS⟩
  · exact Or.inr ⟨block S, ⟨S, hSU, le_rfl⟩, hS⟩

end Transfer

section Headline

variable {κ : Type*} [LinearOrder κ]

/-- C7 (the headline instantiation; Paper IV, Theorem 5.2 at the product).
    Under the Part A/B hypotheses on `D`, the block filter of the
    self-product decides every closed subspace: together with WO-3's filter
    axioms (which apply verbatim, being generic in the ultrafilter) and
    `PlufWO3.PhiU_nonprincipal`, this exhibits a maximal projection filter
    from an ultrafilter that is isomorphic to no Fodor ultrafilter (B7).

    Instance note: `PlufWO2.evec` carries the `LinearOrder` of its index
    type, so the transfer theorems C3–C6 are stated over a linearly ordered
    index set; at `X = κ × κ` any linear order will do (nothing in the
    statement depends on it), and the lexicographic one is used here. -/
theorem product_decides (D : Ultrafilter κ)
    (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
    (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D)
    (hcs : ∀ s : Set κ, s.Countable → sᶜ ∈ D)
    (W : Submodule ℝ (Hk (κ × κ))) (hW : IsClosed (W : Set (Hk (κ × κ)))) :
    W ∈ PhiU (fubini D D) ∨ ∃ M ∈ PhiU (fubini D D), W ⊓ M = ⊥ := by
  letI : LinearOrder (κ × κ) :=
    LinearOrder.lift' (β := κ ×ₗ κ) toLex (Equiv.injective (toLex (α := κ × κ)))
  exact PhiU_decides_of_EPP (fubini D D) (EPP_fubini D h3 h4 hpiv htail)
    (countableSmall_fubini D hcs) W hW

end Headline

end PlufWO4
