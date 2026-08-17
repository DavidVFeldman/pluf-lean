/-
  PlufWO8/Compacts.lean — Work Order 8, the compact-operator form of
  Part B, delivered in addition to the contracted finite-rank form.

  Paper III says the limit state "annihilates the compacts". The
  finite-rank statement is B2; this file upgrades it, first to operators
  with finite-dimensional range (Cauchy–Schwarz for the form
  `(A, B) ↦ φ(A* B)` at a null projection), then to all compact
  operators.

  The approximation step does not use any Hilbert basis: total
  boundedness of the image of the unit ball gives a finite `ε/2`-net, and
  the orthogonal projection onto its span is within `ε` of the operator
  in norm, because the projection minimizes distance to the subspace.
-/
import RequestProject.PlufWO8.Singular

open Set PlufWO2 PlufWO3 PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The orthogonal projection minimizes the distance to the subspace. -/
theorem norm_sub_starProjection_le_of_mem {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    (z : E) {m : E} (hm : m ∈ M) : ‖z - M.starProjection z‖ ≤ ‖z - m‖ := by
  have horth : inner (𝕜 := ℝ) (z - M.starProjection z) (M.starProjection z - m) = 0 := by
    have h := (Submodule.mem_orthogonal M (z - M.starProjection z)).mp
      (Submodule.sub_starProjection_mem_orthogonal (K := M) z)
    have h2 := h (M.starProjection z - m) (M.sub_mem (M.starProjection_apply_mem z) hm)
    rw [real_inner_comm] at h2
    exact h2
  have hsplit : z - m = (z - M.starProjection z) + (M.starProjection z - m) := by abel
  have hpyth := norm_add_sq_real (z - M.starProjection z) (M.starProjection z - m)
  rw [horth] at hpyth
  rw [hsplit]
  nlinarith [norm_nonneg (z - M.starProjection z),
    norm_nonneg ((z - M.starProjection z) + (M.starProjection z - m)),
    sq_nonneg ‖M.starProjection z - m‖]

/-- Finite-rank approximation of a compact operator, without bases: the
    projection onto the span of a finite `ε/2`-net of the image of the
    unit ball is within `ε` of the operator. -/
theorem exists_finiteDimensional_approx (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : Submodule ℝ E) (_hfin : Module.Finite ℝ ↥M),
      ‖T - M.starProjection ∘L T‖ ≤ ε := by
  have htb : TotallyBounded (T '' Metric.closedBall (0:E) 1) := by
    have hcomp := hT.isCompact_closure_image_closedBall (f := (T : E →ₗ[ℝ] E)) 1
    exact hcomp.totallyBounded.subset subset_closure
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (by linarith)
  refine ⟨Submodule.span ℝ t, Module.Finite.span_of_finite ℝ htfin, ?_⟩
  haveI : FiniteDimensional ℝ ↥(Submodule.span ℝ t) := FiniteDimensional.span_of_finite ℝ htfin
  set M : Submodule ℝ E := Submodule.span ℝ t with hM
  have hball : ∀ y : E, ‖y‖ ≤ 1 → ‖(T - M.starProjection ∘L T) y‖ ≤ ε := by
    intro y hy
    have hmem : T y ∈ T '' Metric.closedBall (0:E) 1 :=
      ⟨y, by simpa [Metric.mem_closedBall, dist_zero_right] using hy, rfl⟩
    obtain ⟨c, hct, hdist⟩ := by
      have := hcover hmem
      simpa only [Set.mem_iUnion, exists_prop, Metric.mem_ball] using this
    have hcM : c ∈ M := Submodule.subset_span hct
    have hle : ‖T y - M.starProjection (T y)‖ ≤ ‖T y - c‖ :=
      norm_sub_starProjection_le_of_mem (T y) hcM
    have hlt : ‖T y - c‖ < ε / 2 := by
      rwa [dist_eq_norm] at hdist
    have hval : (T - M.starProjection ∘L T) y = T y - M.starProjection (T y) := by
      simp
    rw [hval]
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (le_of_lt hε) (fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set y : E := ‖x‖⁻¹ • x with hy
    have hny : ‖y‖ ≤ 1 := by
      rw [hy, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hxpos)]
    have hscale : (T - M.starProjection ∘L T) x = ‖x‖ • (T - M.starProjection ∘L T) y := by
      rw [hy, map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hxpos, mul_comm]
    exact mul_le_mul_of_nonneg_right (hball y hny) (le_of_lt hxpos)

end Approx

variable {κ : Type*} [LinearOrder κ] {U : Ultrafilter κ}
  {hcc : PlufWO3.CountablyComplete U}

/-- The limit state annihilates every operator with finite-dimensional
    range. -/
theorem phiLim_eq_zero_of_range_le (hsmall : PlufWO2.CountableSmall U)
    {M : Submodule ℝ (Hk κ)} (hMfin : Module.Finite ℝ ↥M) [M.HasOrthogonalProjection]
    {T : Hk κ →L[ℝ] Hk κ} (hrange : ∀ x, T x ∈ M) :
    phiLim U hcc T = 0 := by
  have hstate : PlufWO6.IsState (phiLimCLM U hcc) := isState_phiLimCLM
  have hP0 : phiLimCLM U hcc M.starProjection = 0 := by
    simpa using phiLim_starProjection_finite_eq_zero (hcc := hcc) hsmall M hMfin
  have hsa : ContinuousLinearMap.adjoint M.starProjection = M.starProjection :=
    isSelfAdjoint_starProjection M
  have hidem : M.starProjection ∘L M.starProjection = M.starProjection :=
    M.isIdempotentElem_starProjection
  have hPP : phiLimCLM U hcc
      (ContinuousLinearMap.adjoint M.starProjection ∘L M.starProjection) = 0 := by
    rw [hsa, hidem]; exact hP0
  have h1 : phiLimCLM U hcc (ContinuousLinearMap.adjoint T ∘L M.starProjection) = 0 :=
    hstate.eq_zero_of_adjoint_comp_eq_zero hPP T
  have hadj : ContinuousLinearMap.adjoint
      (ContinuousLinearMap.adjoint T ∘L M.starProjection)
      = M.starProjection ∘L T := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hsa]
  have h2 : phiLimCLM U hcc (M.starProjection ∘L T) = 0 := by
    rw [← hadj, hstate.adjoint]
    exact h1
  have hTfact : T = M.starProjection ∘L T :=
    ContinuousLinearMap.ext
      (fun x => (Submodule.starProjection_eq_self_iff.mpr (hrange x)).symm)
  have := h2
  rw [← hTfact] at this
  simpa using this

/-- The limit state annihilates every compact operator (Paper III's
    "vanishes on the compacts"). -/
theorem phiLim_compactOperator_eq_zero (hsmall : PlufWO2.CountableSmall U)
    (T : Hk κ →L[ℝ] Hk κ) (hT : IsCompactOperator T) :
    phiLim U hcc T = 0 := by
  have key : ∀ ε > 0, |phiLim U hcc T| ≤ ε := by
    intro ε hε
    obtain ⟨M, hMfin, hle⟩ := exists_finiteDimensional_approx T hT hε
    haveI : FiniteDimensional ℝ ↥M := hMfin
    have h0 : phiLim U hcc (M.starProjection ∘L T) = 0 :=
      phiLim_eq_zero_of_range_le (hcc := hcc) hsmall hMfin
        (fun x => M.starProjection_apply_mem (T x))
    have hsplit : T = (T - M.starProjection ∘L T) + M.starProjection ∘L T := by abel
    have hadd : phiLim U hcc T
        = phiLim U hcc (T - M.starProjection ∘L T) + phiLim U hcc (M.starProjection ∘L T) := by
      conv_lhs => rw [hsplit]
      exact phiLim_add (hcc := hcc) _ _
    rw [h0, add_zero] at hadd
    rw [hadd]
    exact le_trans (abs_phiLim_le (hcc := hcc) _) hle
  by_contra hne
  have hpos : 0 < |phiLim U hcc T| := abs_pos.mpr hne
  have := key (|phiLim U hcc T| / 2) (by linarith)
  linarith

end PlufWO8
