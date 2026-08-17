/-
  PlufWO6/States.lean — Work Order 6, Part E infrastructure: states on
  `B(E)` in the contracted rendering, and the standard consequences of
  positivity: monotonicity for the quadratic order, invariance under the
  adjoint, the Cauchy–Schwarz inequality for the form `(A, B) ↦ φ(A*B)`,
  and the compression identity `φ(A) = φ(P A P)` at a projection of
  value 1.
-/
import RequestProject.PlufWO6.PartD

open Set
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A state on the bounded operators: positive, normalized, linear,
    continuous. (Rendering to be adjusted per census — this is a
    placeholder shape, not a contract to be honored literally if Mathlib
    offers a better one. REPORT the rendering used.) -/
structure IsState (φ : (E →L[ℝ] E) →L[ℝ] ℝ) : Prop where
  pos : ∀ A : E →L[ℝ] E, (∀ x, 0 ≤ inner (𝕜 := ℝ) (A x) x) → 0 ≤ φ A
  norm_one : φ (ContinuousLinearMap.id ℝ E) = 1

namespace IsState

variable {φ : (E →L[ℝ] E) →L[ℝ] ℝ}

omit [CompleteSpace E] in
/-- A state is monotone for the quadratic-form order. -/
theorem mono (hφ : IsState φ) {A B : E →L[ℝ] E}
    (h : ∀ x, inner (𝕜 := ℝ) (A x) x ≤ inner (𝕜 := ℝ) (B x) x) : φ A ≤ φ B := by
  have hpos : 0 ≤ φ (B - A) := by
    refine hφ.pos _ (fun x => ?_)
    have : inner (𝕜 := ℝ) ((B - A) x) x
        = inner (𝕜 := ℝ) (B x) x - inner (𝕜 := ℝ) (A x) x := by
      simp [inner_sub_left]
    rw [this]
    linarith [h x]
  rw [map_sub] at hpos
  linarith

omit [CompleteSpace E] in
/-- A state annihilates operators with vanishing quadratic form; in
    particular it annihilates antisymmetric operators. -/
theorem eq_zero_of_form_zero (hφ : IsState φ) {A : E →L[ℝ] E}
    (h : ∀ x, inner (𝕜 := ℝ) (A x) x = 0) : φ A = 0 := by
  have h1 : φ A ≤ φ 0 := hφ.mono (fun x => by simp [h x])
  have h2 : φ 0 ≤ φ A := hφ.mono (fun x => by simp [h x])
  have h0 : φ 0 = 0 := map_zero φ
  linarith [h0 ▸ h1, h0 ▸ h2]

/-- A state does not see the adjoint. -/
theorem adjoint (hφ : IsState φ) (A : E →L[ℝ] E) :
    φ (ContinuousLinearMap.adjoint A) = φ A := by
  have h : φ (ContinuousLinearMap.adjoint A - A) = 0 := by
    refine hφ.eq_zero_of_form_zero (fun x => ?_)
    have h1 : inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint A) x) x
        = inner (𝕜 := ℝ) (A x) x := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact real_inner_comm _ _
    simp [inner_sub_left, h1]
  rw [map_sub] at h
  linarith

/-- `φ (A* A) ≥ 0`. -/
theorem nonneg_adjoint_comp (hφ : IsState φ) (A : E →L[ℝ] E) :
    0 ≤ φ (ContinuousLinearMap.adjoint A ∘L A) := by
  refine hφ.pos _ (fun x => ?_)
  have : inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint A ∘L A) x) x
      = inner (𝕜 := ℝ) (A x) (A x) := by
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [this]
  exact real_inner_self_nonneg

/-- The form `(A, B) ↦ φ(A* B)` is symmetric. -/
theorem adjoint_comp_comm (hφ : IsState φ) (A B : E →L[ℝ] E) :
    φ (ContinuousLinearMap.adjoint A ∘L B) = φ (ContinuousLinearMap.adjoint B ∘L A) := by
  have h := hφ.adjoint (ContinuousLinearMap.adjoint A ∘L B)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at h
  exact h.symm

/-- Cauchy–Schwarz for the positive semidefinite form `(A, B) ↦ φ(A* B)`. -/
theorem cauchy_schwarz (hφ : IsState φ) (A B : E →L[ℝ] E) :
    (φ (ContinuousLinearMap.adjoint A ∘L B)) ^ 2 ≤
      φ (ContinuousLinearMap.adjoint A ∘L A) * φ (ContinuousLinearMap.adjoint B ∘L B) := by
  set a : ℝ := φ (ContinuousLinearMap.adjoint B ∘L B) with ha
  set b : ℝ := φ (ContinuousLinearMap.adjoint A ∘L B) with hb
  set c : ℝ := φ (ContinuousLinearMap.adjoint A ∘L A) with hc
  have hquad : ∀ t : ℝ, 0 ≤ a * (t * t) + (2 * b) * t + c := by
    intro t
    have hexp : φ (ContinuousLinearMap.adjoint (A + t • B) ∘L (A + t • B))
        = a * (t * t) + (2 * b) * t + c := by
      have hadj : ContinuousLinearMap.adjoint (A + t • B)
          = ContinuousLinearMap.adjoint A + t • ContinuousLinearMap.adjoint B := by
        rw [map_add]
        congr 1
        rw [ContinuousLinearMap.adjoint.map_smulₛₗ]
        simp
      rw [hadj]
      have hcomm : φ (ContinuousLinearMap.adjoint B ∘L A) = b :=
        (hφ.adjoint_comp_comm A B).symm
      simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, map_add, map_smul,
        smul_eq_mul]
      rw [← ha, ← hb, ← hc, hcomm]
      ring
    rw [← hexp]
    exact hφ.nonneg_adjoint_comp _
  have hdis := discrim_le_zero hquad
  rw [discrim] at hdis
  nlinarith [hdis]

/-- If `φ(B* B) = 0` then `φ(A* B) = 0`. -/
theorem eq_zero_of_adjoint_comp_eq_zero (hφ : IsState φ) {B : E →L[ℝ] E}
    (hB : φ (ContinuousLinearMap.adjoint B ∘L B) = 0) (A : E →L[ℝ] E) :
    φ (ContinuousLinearMap.adjoint A ∘L B) = 0 := by
  have h := hφ.cauchy_schwarz A B
  rw [hB, mul_zero] at h
  nlinarith [sq_nonneg (φ (ContinuousLinearMap.adjoint A ∘L B))]

/-- The compression identity: if `φ` takes the value `1` at the projection
    onto `M`, then `φ(A) = φ(P A P)` for every `A`. -/
theorem compress (hφ : IsState φ) {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    (hP : φ M.starProjection = 1) (A : E →L[ℝ] E) :
    φ (M.starProjection ∘L A ∘L M.starProjection) = φ A := by
  set P : E →L[ℝ] E := M.starProjection with hPdef
  set Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P with hQdef
  have hPsa : ContinuousLinearMap.adjoint P = P := isSelfAdjoint_starProjection M
  have hPP : P ∘L P = P := M.isIdempotentElem_starProjection
  have hQsa : ContinuousLinearMap.adjoint Q = Q := by
    rw [hQdef, map_sub, hPsa, ContinuousLinearMap.adjoint_id]
  have hQQ : Q ∘L Q = Q := by
    rw [hQdef]
    ext x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
    have : P (P x) = P x := by
      have := congrArg (fun (S : E →L[ℝ] E) => S x) hPP
      simpa using this
    rw [this]
    abel
  have hQzero : φ Q = 0 := by
    rw [hQdef, map_sub, hφ.norm_one, hP, sub_self]
  have hQQzero : φ (ContinuousLinearMap.adjoint Q ∘L Q) = 0 := by
    rw [hQsa, hQQ, hQzero]
  have h1 : φ (Q ∘L (A ∘L P)) = 0 := by
    have := hφ.eq_zero_of_adjoint_comp_eq_zero hQQzero (A ∘L P)
    rwa [hφ.adjoint_comp_comm (A ∘L P) Q, hQsa] at this
  have h2 : φ (Q ∘L (A ∘L Q)) = 0 := by
    have := hφ.eq_zero_of_adjoint_comp_eq_zero hQQzero (A ∘L Q)
    rwa [hφ.adjoint_comp_comm (A ∘L Q) Q, hQsa] at this
  have h3 : φ (P ∘L (A ∘L Q)) = 0 := by
    have := hφ.eq_zero_of_adjoint_comp_eq_zero hQQzero
      (ContinuousLinearMap.adjoint (P ∘L A))
    rwa [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc] at this
  have hsplit : A = P ∘L (A ∘L P) + P ∘L (A ∘L Q) + Q ∘L (A ∘L P) + Q ∘L (A ∘L Q) := by
    have hPQ : P + Q = ContinuousLinearMap.id ℝ E := by rw [hQdef]; abel
    ext x
    have hx : P x + Q x = x := by
      have := congrArg (fun (S : E →L[ℝ] E) => S x) hPQ
      simpa using this
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    calc A x = A (P x + Q x) := by rw [hx]
      _ = A (P x) + A (Q x) := by rw [map_add]
      _ = P (A (P x)) + Q (A (P x)) + (P (A (Q x)) + Q (A (Q x))) := by
          rw [show P (A (P x)) + Q (A (P x)) = A (P x) from by
                have := congrArg (fun (S : E →L[ℝ] E) => S (A (P x))) hPQ
                simpa using this,
            show P (A (Q x)) + Q (A (Q x)) = A (Q x) from by
                have := congrArg (fun (S : E →L[ℝ] E) => S (A (Q x))) hPQ
                simpa using this]
      _ = P (A (P x)) + P (A (Q x)) + Q (A (P x)) + Q (A (Q x)) := by abel
  calc φ (P ∘L A ∘L P) = φ (P ∘L (A ∘L P)) := rfl
    _ = φ (P ∘L (A ∘L P)) + φ (P ∘L (A ∘L Q)) + φ (Q ∘L (A ∘L P)) + φ (Q ∘L (A ∘L Q)) := by
        rw [h1, h2, h3]; ring
    _ = φ A := by
        rw [← map_add, ← map_add, ← map_add, ← hsplit]

end IsState

end PlufWO6
