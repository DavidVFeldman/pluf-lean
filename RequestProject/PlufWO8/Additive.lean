/-
  PlufWO8/Additive.lean — Work Order 8, Part C: countable additivity of
  the limit state (Paper III, Theorem 4.1).

  The engine is `diag_eq_zero_mem_of_phiLim_eq_zero`: for a positive
  operator the vanishing of the `U`-limit of the diagonal already forces
  the diagonal to vanish *identically* on a member of `U`, because the
  countably many sets `{α | d α ≤ 1/(n+1)}` all belong to `U` and `U` is
  countably complete. This replaces the paper's `ε 2⁻ⁿ` bookkeeping in the
  null case (C1, C3); the `ε 2⁻ⁿ` argument is still what proves the
  general `tsum` form (C2).
-/
import RequestProject.PlufWO8.Singular

open Set PlufWO2 PlufWO3 PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {κ : Type*} [LinearOrder κ] {U : Ultrafilter κ}
  {hcc : PlufWO3.CountablyComplete U}

/-- For an operator with nonnegative diagonal, a vanishing `U`-limit means
    the diagonal vanishes identically on a member of `U`. -/
theorem diag_eq_zero_mem_of_phiLim_eq_zero {T : Hk κ →L[ℝ] Hk κ}
    (hpos : ∀ α, 0 ≤ diag T α) (h : phiLim U hcc T = 0) :
    {α : κ | diag T α = 0} ∈ U := by
  have hset : {α : κ | diag T α = 0}
      = ⋂ n : ℕ, {α : κ | |diag T α - phiLim U hcc T| ≤ 1 / (n + 1)} := by
    ext α
    simp only [Set.mem_iInter, Set.mem_setOf_eq, h, sub_zero]
    constructor
    · intro hα n
      rw [hα]
      simp only [abs_zero]
      positivity
    · intro hα
      by_contra hne
      have hposα : 0 < diag T α := lt_of_le_of_ne (hpos α) (Ne.symm hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hposα
      have hle := hα n
      rw [abs_of_nonneg (hpos α)] at hle
      linarith
  rw [hset]
  exact hcc _ (fun n => uLim_phiLim (hcc := hcc) T (1 / (n + 1)) (by positivity))

/-- C1 (Paper III, Theorem 4.1). A countable orthogonal-type expansion of
    a projection into null projections is null. -/
theorem phiLim_starProjection_eq_zero_of_hasSum
    (q : ℕ → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    [∀ n, (q n).HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hq0 : ∀ n, phiLim U hcc (q n).starProjection = 0)
    (hexp : ∀ x : Hk κ, HasSum (fun n => inner (𝕜 := ℝ) ((q n).starProjection x) x)
      (inner (𝕜 := ℝ) (Q.starProjection x) x)) :
    phiLim U hcc Q.starProjection = 0 := by
  have hZ : ∀ n : ℕ, {α : κ | diag ((q n).starProjection) α = 0} ∈ U := fun n =>
    diag_eq_zero_mem_of_phiLim_eq_zero
      (fun α => inner_starProjection_nonneg (q n) (evec α)) (hq0 n)
  refine phiLim_eq_zero_of_diag_eq_zero_on (hcc := hcc) (hcc _ hZ) ?_
  intro α hα
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hα
  have hd : HasSum (fun n => diag ((q n).starProjection) α) (diag Q.starProjection α) :=
    hexp (evec α)
  have hzero : HasSum (fun n : ℕ => diag ((q n).starProjection) α) 0 := by
    have hfun : (fun n : ℕ => diag ((q n).starProjection) α) = fun _ => (0:ℝ) :=
      funext (fun n => hα n)
    rw [hfun]
    exact hasSum_zero
  exact hd.unique hzero

/-- C3 (the `<κ`-additive form, generic index). -/
theorem phiLim_starProjection_eq_zero_generic {ι : Type*}
    (hU : ∀ s : ι → Set κ, (∀ i, s i ∈ U) → (⋂ i, s i) ∈ U)
    (q : ι → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    [∀ i, (q i).HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hq0 : ∀ i, phiLim U hcc (q i).starProjection = 0)
    (hexp : ∀ x : Hk κ, ∀ ε > 0, ∃ F : Finset ι,
      inner (𝕜 := ℝ) (Q.starProjection x) x
        ≤ (∑ i ∈ F, inner (𝕜 := ℝ) ((q i).starProjection x) x) + ε) :
    phiLim U hcc Q.starProjection = 0 := by
  have hZ : ∀ i : ι, {α : κ | diag ((q i).starProjection) α = 0} ∈ U := fun i =>
    diag_eq_zero_mem_of_phiLim_eq_zero
      (fun α => inner_starProjection_nonneg (q i) (evec α)) (hq0 i)
  refine phiLim_eq_zero_of_diag_eq_zero_on (hcc := hcc) (hU _ hZ) ?_
  intro α hα
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hα
  have hle : ∀ ε > 0, diag Q.starProjection α ≤ ε := by
    intro ε hε
    obtain ⟨F, hF⟩ := hexp (evec α) ε hε
    have hsum : (∑ i ∈ F, inner (𝕜 := ℝ) ((q i).starProjection (evec α)) (evec α)) = 0 :=
      Finset.sum_eq_zero (fun i _ => hα i)
    rw [hsum, zero_add] at hF
    exact hF
  have hge : 0 ≤ diag Q.starProjection α := inner_starProjection_nonneg Q (evec α)
  refine le_antisymm ?_ hge
  by_contra hpos
  push_neg at hpos
  exact absurd (hle (diag Q.starProjection α / 2) (by linarith)) (by linarith)

/-- C2 (countable additivity, general form). -/
theorem phiLim_starProjection_tsum
    (q : ℕ → Submodule ℝ (Hk κ)) (Q : Submodule ℝ (Hk κ))
    [∀ n, (q n).HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hexp : ∀ x : Hk κ, HasSum (fun n => inner (𝕜 := ℝ) ((q n).starProjection x) x)
      (inner (𝕜 := ℝ) (Q.starProjection x) x)) :
    phiLim U hcc Q.starProjection = ∑' n, phiLim U hcc (q n).starProjection := by
  set a : ℕ → ℝ := fun n => phiLim U hcc (q n).starProjection with ha
  have hanneg : ∀ n, 0 ≤ a n := fun n =>
    phiLim_nonneg (hcc := hcc) (fun x => inner_starProjection_nonneg (q n) x)
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n ≤ phiLim U hcc Q.starProjection := by
    intro N
    have hmapsum : phiLim U hcc (∑ n ∈ Finset.range N, (q n).starProjection)
        = ∑ n ∈ Finset.range N, a n := by
      have h := map_sum (phiLimCLM U hcc) (fun n => (q n).starProjection) (Finset.range N)
      simp only [phiLimCLM_apply] at h
      exact h
    rw [← hmapsum]
    refine phiLim_mono (hcc := hcc) (fun x => ?_)
    have h1 : inner (𝕜 := ℝ) ((∑ n ∈ Finset.range N, (q n).starProjection) x) x
        = ∑ n ∈ Finset.range N, inner (𝕜 := ℝ) ((q n).starProjection x) x := by
      rw [ContinuousLinearMap.sum_apply, sum_inner]
    rw [h1]
    exact sum_le_hasSum _ (fun i _ => inner_starProjection_nonneg (q i) x) (hexp x)
  have hsummable : Summable a := summable_of_sum_range_le hanneg hpartial
  have hS : HasSum a (∑' n, a n) := hsummable.hasSum
  refine phiLim_eq (hcc := hcc) ?_
  intro ε hε
  have hA : ∀ n : ℕ,
      {α : κ | |diag ((q n).starProjection) α - a n| ≤ ε / 2 / 2 ^ n} ∈ U := fun n =>
    uLim_phiLim (hcc := hcc) ((q n).starProjection) (ε / 2 / 2 ^ n) (by positivity)
  refine Filter.mem_of_superset (hcc _ hA) ?_
  intro α hα
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hα ⊢
  have hgeo : HasSum (fun n => ε / 2 / 2 ^ n) ε := hasSum_geometric_two' ε
  have hd : HasSum (fun n => diag ((q n).starProjection) α) (diag Q.starProjection α) :=
    hexp (evec α)
  have hub : diag Q.starProjection α ≤ (∑' n, a n) + ε :=
    hasSum_le (fun n => by have := (abs_le.mp (hα n)).2; linarith) hd (hS.add hgeo)
  have hlb : (∑' n, a n) - ε ≤ diag Q.starProjection α :=
    hasSum_le (fun n => by have := (abs_le.mp (hα n)).1; linarith) (hS.sub hgeo) hd
  rw [abs_le]
  constructor <;> linarith

end PlufWO8
