/-
  PlufWO6/PartECompact.lean — Work Order 6, Part E, the remaining clauses
  of the paper's Proposition 3.3: the face `S_π` is convex and weak-*
  compact.

  The contract's E1–E4 ask for nonemptiness, the sandwich characterization,
  the face property and the RSP dichotomy; the paper's proposition also
  records that `S_π` is convex and weak-* compact.  That is not contracted,
  but the Part E census found Banach–Alaoglu available in Mathlib
  (`WeakDual.isCompact_closedBall`), so the clause is delivered here for
  completeness: states have dual norm at most one, the face is cut out by
  conditions each of which is closed for the topology of pointwise
  convergence, and Alaoglu finishes.
-/
import RequestProject.PlufWO6.PartE

open Set
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The face of the state space cut out by a family of subspaces:
    `S_π = {φ a state : φ (P_M) = 1 for all M ∈ π}`. -/
def stateFace (π : Set (Submodule ℝ E)) : Set ((E →L[ℝ] E) →L[ℝ] ℝ) :=
  {φ | IsState φ ∧ ∀ M ∈ π, ∀ _hM : IsClosed (M : Set E), φ (M.starProjection) = 1}

omit [CompleteSpace E] in
/-- A state has dual norm at most one. -/
theorem IsState.norm_le_one {φ : (E →L[ℝ] E) →L[ℝ] ℝ} (hφ : IsState φ) : ‖φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound φ zero_le_one (fun A => ?_)
  have key : ∀ B : E →L[ℝ] E, φ B ≤ ‖B‖ := by
    intro B
    have hmono : φ B ≤ φ ((‖B‖ : ℝ) • ContinuousLinearMap.id ℝ E) := by
      refine hφ.mono (fun x => ?_)
      have h1 : inner (𝕜 := ℝ) (B x) x ≤ ‖B‖ * ‖x‖ ^ 2 := by
        calc inner (𝕜 := ℝ) (B x) x ≤ |inner (𝕜 := ℝ) (B x) x| := le_abs_self _
          _ ≤ ‖B x‖ * ‖x‖ := abs_real_inner_le_norm _ _
          _ ≤ (‖B‖ * ‖x‖) * ‖x‖ :=
              mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x)
          _ = ‖B‖ * ‖x‖ ^ 2 := by ring
      have h2 : inner (𝕜 := ℝ) (((‖B‖ : ℝ) • ContinuousLinearMap.id ℝ E) x) x
          = ‖B‖ * ‖x‖ ^ 2 := by
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
          real_inner_smul_left]
        rw [real_inner_self_eq_norm_sq]
      rw [h2]
      exact h1
    rwa [map_smul, smul_eq_mul, hφ.norm_one, mul_one] at hmono
  have h1 : φ A ≤ ‖A‖ := key A
  have h2 : -φ A ≤ ‖A‖ := by
    have := key (-A)
    rwa [map_neg, norm_neg] at this
  rw [Real.norm_eq_abs, one_mul]
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- The face is convex. -/
theorem convex_stateFace (π : Set (Submodule ℝ E)) : Convex ℝ (stateFace π) := by
  rintro φ ⟨hφ, hfφ⟩ ψ ⟨hψ, hfψ⟩ s t hs ht hst
  refine ⟨⟨fun A hA => ?_, ?_⟩, fun M hM hMc => ?_⟩
  · have h1 := hφ.pos A hA
    have h2 := hψ.pos A hA
    have : (s • φ + t • ψ) A = s * φ A + t * ψ A := by simp
    rw [this]
    positivity
  · have : (s • φ + t • ψ) (ContinuousLinearMap.id ℝ E)
        = s * φ (ContinuousLinearMap.id ℝ E) + t * ψ (ContinuousLinearMap.id ℝ E) := by simp
    rw [this, hφ.norm_one, hψ.norm_one, mul_one, mul_one, hst]
  · have : (s • φ + t • ψ) (M.starProjection)
        = s * φ (M.starProjection) + t * ψ (M.starProjection) := by simp
    rw [this, hfφ M hM hMc, hfψ M hM hMc, mul_one, mul_one, hst]

/-- The projections appearing in the face condition. -/
def projSet (π : Set (Submodule ℝ E)) : Set (E →L[ℝ] E) :=
  {P | ∃ M ∈ π, ∃ _hM : IsClosed (M : Set E), P = M.starProjection}

/-- The face is closed for the weak-* topology. -/
theorem isClosed_stateFace (π : Set (Submodule ℝ E)) :
    IsClosed {φ : WeakDual ℝ (E →L[ℝ] E) | φ ∈ stateFace π} := by
  have hset : {φ : WeakDual ℝ (E →L[ℝ] E) | φ ∈ stateFace π}
      = (⋂ A ∈ {A : E →L[ℝ] E | ∀ x, 0 ≤ inner (𝕜 := ℝ) (A x) x},
            {φ : WeakDual ℝ (E →L[ℝ] E) | 0 ≤ φ A})
        ∩ {φ : WeakDual ℝ (E →L[ℝ] E) | φ (ContinuousLinearMap.id ℝ E) = 1}
        ∩ (⋂ P ∈ projSet π, {φ : WeakDual ℝ (E →L[ℝ] E) | φ P = 1}) := by
    ext φ
    simp only [stateFace, projSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hφ, hface⟩
      refine ⟨⟨fun A hA => hφ.pos A hA, hφ.norm_one⟩, ?_⟩
      rintro P ⟨M, hM, hMc, rfl⟩
      exact hface M hM hMc
    · rintro ⟨⟨hpos, hone⟩, hface⟩
      exact ⟨⟨fun A hA => hpos A hA, hone⟩,
        fun M hM hMc => hface (M.starProjection) ⟨M, hM, hMc, rfl⟩⟩
  rw [hset]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_biInter (fun A _ => isClosed_le continuous_const (WeakDual.eval_continuous A))
  · exact isClosed_eq (WeakDual.eval_continuous _) continuous_const
  · exact isClosed_biInter (fun P _ =>
      isClosed_eq (WeakDual.eval_continuous P) continuous_const)

/-- Proposition 3.3, compactness: the face is weak-* compact.  (Together
    with `convex_stateFace` and `face_isFace` this is the paper's "`S_π`
    is a nonempty weak-* compact face of the state space", the
    nonemptiness being E1.) -/
theorem isCompact_stateFace (π : Set (Submodule ℝ E)) :
    IsCompact {φ : WeakDual ℝ (E →L[ℝ] E) | φ ∈ stateFace π} := by
  have hball : IsCompact (⇑(WeakDual.toStrongDual (𝕜 := ℝ) (E := E →L[ℝ] E)) ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ (E →L[ℝ] E)) 1) :=
    WeakDual.isCompact_closedBall ℝ 0 1
  refine hball.of_isClosed_subset (isClosed_stateFace π) (fun φ hφ => ?_)
  have hnorm : @norm (StrongDual ℝ (E →L[ℝ] E)) SeminormedAddGroup.toNorm
      (WeakDual.toStrongDual φ) ≤ 1 := hφ.1.norm_le_one
  exact mem_closedBall_zero_iff.mpr hnorm

end PlufWO6
