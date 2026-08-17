/-
  PlufWO8/Proj.lean — Work Order 8, shared projection calculus.

  Two facts about orthogonal projections used repeatedly below: a closed
  subspace of a complete space has an orthogonal projection, and the
  quadratic form of the projection is monotone in the subspace.
-/
import RequestProject.PlufWO8.Limits

open Set PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A closed subspace of a complete inner product space has an orthogonal
    projection. -/
theorem hasOrthogonalProjection_of_isClosed {M : Submodule ℝ E}
    (hM : IsClosed (M : Set E)) : M.HasOrthogonalProjection := by
  haveI : CompleteSpace ↥M := hM.completeSpace_coe
  infer_instance

omit [CompleteSpace E] in
/-- Monotonicity of projections in norm: `‖P_M x‖ ≤ ‖P_N x‖` for `M ≤ N`. -/
theorem norm_starProjection_le_of_le {M N : Submodule ℝ E} [M.HasOrthogonalProjection]
    [N.HasOrthogonalProjection] (h : M ≤ N) (x : E) :
    ‖M.starProjection x‖ ≤ ‖N.starProjection x‖ := by
  have hzero : inner (𝕜 := ℝ) (M.starProjection x) (x - N.starProjection x) = 0 :=
    (Submodule.mem_orthogonal N _).mp
      (Submodule.sub_starProjection_mem_orthogonal (K := N) x)
      _ (h (M.starProjection_apply_mem x))
  have hsq : ‖M.starProjection x‖ ^ 2 = inner (𝕜 := ℝ) (M.starProjection x) x :=
    (inner_starProjection_self x).symm
  have hsplit : inner (𝕜 := ℝ) (M.starProjection x) x
      = inner (𝕜 := ℝ) (M.starProjection x) (N.starProjection x) := by
    have := inner_sub_right (𝕜 := ℝ) (M.starProjection x) x (N.starProjection x)
    rw [hzero] at this
    linarith
  have hcs : inner (𝕜 := ℝ) (M.starProjection x) (N.starProjection x)
      ≤ ‖M.starProjection x‖ * ‖N.starProjection x‖ := real_inner_le_norm _ _
  nlinarith [norm_nonneg (M.starProjection x), norm_nonneg (N.starProjection x)]

omit [CompleteSpace E] in
/-- Monotonicity of projections for the quadratic-form order. -/
theorem inner_starProjection_le_of_le {M N : Submodule ℝ E} [M.HasOrthogonalProjection]
    [N.HasOrthogonalProjection] (h : M ≤ N) (x : E) :
    inner (𝕜 := ℝ) (M.starProjection x) x ≤ inner (𝕜 := ℝ) (N.starProjection x) x := by
  rw [inner_starProjection_self, inner_starProjection_self]
  have := norm_starProjection_le_of_le h x
  nlinarith [norm_nonneg (M.starProjection x), norm_nonneg (N.starProjection x)]

omit [CompleteSpace E] in
/-- The quadratic form of a projection is nonnegative. -/
theorem inner_starProjection_nonneg (M : Submodule ℝ E) [M.HasOrthogonalProjection] (x : E) :
    0 ≤ inner (𝕜 := ℝ) (M.starProjection x) x := by
  rw [inner_starProjection_self]
  positivity

omit [CompleteSpace E] in
/-- A state is monotone along inclusions of subspaces. -/
theorem state_starProjection_mono {φ : (E →L[ℝ] E) →L[ℝ] ℝ} (hφ : IsState φ)
    {M N : Submodule ℝ E} [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    (h : M ≤ N) : φ M.starProjection ≤ φ N.starProjection :=
  hφ.mono (fun x => inner_starProjection_le_of_le h x)

end PlufWO8
