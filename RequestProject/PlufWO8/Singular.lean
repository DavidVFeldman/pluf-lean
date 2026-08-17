/-
  PlufWO8/Singular.lean — Work Order 8, Part B: singularity of the limit
  state.

  The mechanism is the countable-support argument of Paper III: if a
  subspace is spanned by countably many vectors, then all but countably
  many basis vectors are orthogonal to it, so the diagonal of its
  projection vanishes on a `U`-set (`CountableSmall`), and the `U`-limit
  is `0`. Both the rank-one form (B1) and the finite-rank form (B2) are
  instances.
-/
import RequestProject.PlufWO8.Proj

open Set PlufWO2 PlufWO3 PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {κ : Type*} [LinearOrder κ] {U : Ultrafilter κ}
  {hcc : PlufWO3.CountablyComplete U}

/-- If the diagonal of `T` vanishes on a member of `U`, the limit is `0`. -/
theorem phiLim_eq_zero_of_diag_eq_zero_on {T : Hk κ →L[ℝ] Hk κ} {s : Set κ}
    (hs : s ∈ U) (h : ∀ α ∈ s, diag T α = 0) : phiLim U hcc T = 0 :=
  phiLim_eq (ULim.zero_of_eq_zero_on hs h)

/-- The key countability step: if `M` sits inside the span of a countable
    set of vectors, all but countably many basis vectors are orthogonal to
    `M`. -/
theorem countable_evec_not_orthogonal {M : Submodule ℝ (Hk κ)} {S : Set (Hk κ)}
    (hS : S.Countable) (hM : M ≤ Submodule.span ℝ S) :
    {α : κ | evec α ∉ Mᗮ}.Countable := by
  have hsub : {α : κ | evec α ∉ Mᗮ} ⊆ ⋃ v ∈ S, supp v := by
    intro α hα
    by_contra hmem
    refine hα ?_
    simp only [Set.mem_iUnion, exists_prop, not_exists, not_and] at hmem
    have horth : evec α ∈ (Submodule.span ℝ S)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
          have hv0 : (v : ∀ _ : κ, ℝ) α = 0 := by
            by_contra hne
            exact (hmem v hv) (by simpa [supp] using hne)
          rw [inner_evec_right]
          exact hv0
      | zero => simp
      | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
      | smul c a _ ha => simp [inner_smul_left, ha]
    exact Submodule.orthogonal_le hM horth
  refine Set.Countable.mono hsub ?_
  exact hS.biUnion (fun v _ => countable_supp v)

/-- The core of Part B: the limit state annihilates the projection onto
    any subspace contained in the span of countably many vectors. -/
theorem phiLim_starProjection_eq_zero_of_countable_span
    (hsmall : PlufWO2.CountableSmall U) {M : Submodule ℝ (Hk κ)}
    [M.HasOrthogonalProjection] {S : Set (Hk κ)} (hS : S.Countable)
    (hM : M ≤ Submodule.span ℝ S) :
    phiLim U hcc M.starProjection = 0 := by
  have hc : {α : κ | evec α ∉ Mᗮ}.Countable := countable_evec_not_orthogonal hS hM
  refine phiLim_eq_zero_of_diag_eq_zero_on (hsmall _ hc) ?_
  intro α hα
  have hmem : evec α ∈ Mᗮ := by
    by_contra h
    exact hα h
  have h0 : M.starProjection (evec α) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff M).mpr hmem
  simp [diag, h0]

/-- B1. The limit state annihilates every rank-one projection. -/
theorem phiLim_starProjection_singleton_eq_zero
    (hsmall : PlufWO2.CountableSmall U) (v : Hk κ) :
    phiLim U hcc ((ℝ ∙ v).starProjection) = 0 :=
  phiLim_starProjection_eq_zero_of_countable_span (hcc := hcc) hsmall
    (S := {v}) (Set.countable_singleton v) le_rfl

/-- B2. The limit state annihilates every finite-rank projection. -/
theorem phiLim_starProjection_finite_eq_zero
    (hsmall : PlufWO2.CountableSmall U) (M : Submodule ℝ (Hk κ))
    (hM : Module.Finite ℝ ↥M) [M.HasOrthogonalProjection] :
    phiLim U hcc M.starProjection = 0 := by
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp hM)
  exact phiLim_starProjection_eq_zero_of_countable_span (hcc := hcc) hsmall
    hSfin.countable (le_of_eq hSspan.symm)

end PlufWO8
