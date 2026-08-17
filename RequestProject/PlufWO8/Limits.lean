/-
  PlufWO8/Limits.lean — Work Order 8, Part A infrastructure.

  Ultrafilter limits of bounded real functions, packaged as the predicate
  `ULim`, with the calculus used throughout WO-8 (uniqueness, linearity,
  monotonicity, congruence along a `U`-set), and the limit state `phiLim`
  of the diagonal of a bounded operator on ℓ²(κ), together with its
  bundling as a continuous linear functional and the verification of
  `PlufWO6.IsState`.
-/
import RequestProject.PlufWO6

open Set PlufWO2 PlufWO3 PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {κ : Type*} [LinearOrder κ]

/-! ### Ultrafilter limits -/

omit [LinearOrder κ] in
/-- `L` is the `U`-limit of `f`: every `ε`-neighbourhood of `L` is reached
    on a member of `U`. -/
def ULim (U : Ultrafilter κ) (f : κ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, {α | |f α - L| ≤ ε} ∈ U

namespace ULim

variable {U : Ultrafilter κ} {f g : κ → ℝ} {L M : ℝ}

omit [LinearOrder κ]

/-- `U`-limits are unique. -/
theorem unique (hf : ULim U f L) (hg : ULim U f M) : L = M := by
  by_contra hne
  have habs : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set ε : ℝ := |L - M| / 3 with hε
  have hpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨α, hα1, hα2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (hf ε hpos) (hg ε hpos))
  simp only [Set.mem_setOf_eq] at hα1 hα2
  have hkey : |L - M| ≤ 2 * ε := by
    calc |L - M| = |(f α - M) - (f α - L)| := by ring_nf
      _ ≤ |f α - M| + |f α - L| := abs_sub _ _
      _ ≤ ε + ε := add_le_add hα2 hα1
      _ = 2 * ε := by ring
  rw [hε] at hkey
  linarith

/-- The constant function. -/
theorem const (c : ℝ) : ULim U (fun _ => c) c := by
  intro ε hε
  have h : {α : κ | |(fun _ : κ => c) α - c| ≤ ε} = Set.univ := by
    ext α; simp [le_of_lt hε]
  rw [h]
  exact Filter.univ_mem

/-- A function agreeing with `f` on a member of `U` has the same limit. -/
theorem congr_of_mem (hf : ULim U f L) {s : Set κ} (hs : s ∈ U)
    (h : ∀ α ∈ s, g α = f α) : ULim U g L := by
  intro ε hε
  refine Filter.mem_of_superset (Filter.inter_mem (hf ε hε) hs) ?_
  rintro α ⟨hα1, hα2⟩
  simp only [Set.mem_setOf_eq] at hα1 ⊢
  rw [h α hα2]
  exact hα1

/-- A function which vanishes on a member of `U` has limit `0`. -/
theorem zero_of_eq_zero_on {s : Set κ} (hs : s ∈ U) (h : ∀ α ∈ s, f α = 0) :
    ULim U f 0 :=
  (const (U := U) (0 : ℝ)).congr_of_mem hs (fun α hα => by simp [h α hα])

theorem add (hf : ULim U f L) (hg : ULim U g M) : ULim U (fun α => f α + g α) (L + M) := by
  intro ε hε
  refine Filter.mem_of_superset (Filter.inter_mem (hf (ε/2) (by linarith))
    (hg (ε/2) (by linarith))) ?_
  rintro α ⟨hα1, hα2⟩
  simp only [Set.mem_setOf_eq] at hα1 hα2 ⊢
  calc |f α + g α - (L + M)| = |(f α - L) + (g α - M)| := by ring_nf
    _ ≤ |f α - L| + |g α - M| := abs_add_le _ _
    _ ≤ ε/2 + ε/2 := add_le_add hα1 hα2
    _ = ε := by ring

theorem smul (c : ℝ) (hf : ULim U f L) : ULim U (fun α => c * f α) (c * L) := by
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using (const (U := U) (0:ℝ)) ε hε
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    refine Filter.mem_of_superset (hf (ε / |c|) (by positivity)) ?_
    intro α hα
    simp only [Set.mem_setOf_eq] at hα ⊢
    have habs : |c * f α - c * L| = |c| * |f α - L| := by
      rw [← abs_mul]; ring_nf
    rw [habs]
    calc |c| * |f α - L| ≤ |c| * (ε / |c|) :=
          mul_le_mul_of_nonneg_left hα (le_of_lt hcpos)
      _ = ε := by field_simp

/-- Monotonicity of the `U`-limit. -/
theorem le_of_le (h : ∀ α, f α ≤ g α) (hf : ULim U f L) (hg : ULim U g M) : L ≤ M := by
  by_contra hlt
  push_neg at hlt
  set ε : ℝ := (L - M) / 3 with hε
  have hpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨α, hα1, hα2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (hf ε hpos) (hg ε hpos))
  simp only [Set.mem_setOf_eq] at hα1 hα2
  have h1 : L - ε ≤ f α := by have := (abs_le.mp hα1).1; linarith
  have h2 : g α ≤ M + ε := by have := (abs_le.mp hα2).2; linarith
  have h3 := h α
  rw [hε] at h1 h2
  linarith

end ULim

/-! ### The diagonal of an operator -/

/-- The diagonal function of a bounded operator on ℓ²(κ). -/
noncomputable def diag (T : Hk κ →L[ℝ] Hk κ) (α : κ) : ℝ :=
  inner (𝕜 := ℝ) (T (evec α)) (evec α)

theorem norm_evec (α : κ) : ‖evec (κ := κ) α‖ = 1 := by
  have h := lp.norm_single (E := fun _ : κ => ℝ) (p := 2) (by norm_num) α (1 : ℝ)
  simp [evec, h]

theorem abs_diag_le (T : Hk κ →L[ℝ] Hk κ) (α : κ) : |diag T α| ≤ ‖T‖ := by
  have h1 : |diag T α| ≤ ‖T (evec α)‖ * ‖evec (κ := κ) α‖ :=
    abs_real_inner_le_norm _ _
  have h2 : ‖T (evec (κ := κ) α)‖ ≤ ‖T‖ * ‖evec (κ := κ) α‖ := T.le_opNorm _
  rw [norm_evec] at h1 h2
  linarith

@[simp] theorem diag_add (T S : Hk κ →L[ℝ] Hk κ) (α : κ) :
    diag (T + S) α = diag T α + diag S α := by
  simp [diag, inner_add_left]

@[simp] theorem diag_smul (c : ℝ) (T : Hk κ →L[ℝ] Hk κ) (α : κ) :
    diag (c • T) α = c * diag T α := by
  simp [diag, real_inner_smul_left]

@[simp] theorem diag_id (α : κ) : diag (ContinuousLinearMap.id ℝ (Hk κ)) α = 1 := by
  simp [diag, norm_evec]

theorem diag_nonneg {T : Hk κ →L[ℝ] Hk κ} (hT : ∀ x, 0 ≤ inner (𝕜 := ℝ) (T x) x) (α : κ) :
    0 ≤ diag T α := hT _

theorem diag_mono {T S : Hk κ →L[ℝ] Hk κ}
    (h : ∀ x, inner (𝕜 := ℝ) (T x) x ≤ inner (𝕜 := ℝ) (S x) x) (α : κ) :
    diag T α ≤ diag S α := h _

/-! ### The limit state -/

/-- A1. The `U`-limit of the diagonal of `T`, for a countably complete
    ultrafilter `U`. (Existence is WO-3's `exists_ulim`, with the bound
    `|⟪T e_α, e_α⟫| ≤ ‖T‖`; `hcc` is carried because the contract asks
    for it.) -/
noncomputable def phiLim (U : Ultrafilter κ) (hcc : PlufWO3.CountablyComplete U)
    (T : Hk κ →L[ℝ] Hk κ) : ℝ :=
  (PlufWO3.exists_ulim U hcc (diag T) ‖T‖ (abs_diag_le T)).choose

variable {U : Ultrafilter κ} {hcc : PlufWO3.CountablyComplete U}

/-- The defining property of `phiLim`. -/
theorem uLim_phiLim (T : Hk κ →L[ℝ] Hk κ) : ULim U (diag T) (phiLim U hcc T) :=
  (PlufWO3.exists_ulim U hcc (diag T) ‖T‖ (abs_diag_le T)).choose_spec

/-- `phiLim` is characterized by being *the* `U`-limit of the diagonal. -/
theorem phiLim_eq {T : Hk κ →L[ℝ] Hk κ} {L : ℝ} (h : ULim U (diag T) L) :
    phiLim U hcc T = L :=
  ULim.unique (uLim_phiLim (hcc := hcc) T) h

theorem phiLim_add (T S : Hk κ →L[ℝ] Hk κ) :
    phiLim U hcc (T + S) = phiLim U hcc T + phiLim U hcc S := by
  refine phiLim_eq ?_
  have h := (uLim_phiLim (hcc := hcc) T).add (uLim_phiLim (hcc := hcc) S)
  have hfun : diag (T + S) = fun α => diag T α + diag S α := funext (diag_add T S)
  rw [hfun]
  exact h

theorem phiLim_smul (c : ℝ) (T : Hk κ →L[ℝ] Hk κ) :
    phiLim U hcc (c • T) = c * phiLim U hcc T := by
  refine phiLim_eq ?_
  have h := (uLim_phiLim (hcc := hcc) T).smul c
  have hfun : diag (c • T) = fun α => c * diag T α := funext (diag_smul c T)
  rw [hfun]
  exact h

theorem phiLim_id : phiLim U hcc (ContinuousLinearMap.id ℝ (Hk κ)) = 1 := by
  refine phiLim_eq ?_
  have hfun : diag (ContinuousLinearMap.id ℝ (Hk κ)) = fun _ : κ => (1:ℝ) := funext diag_id
  rw [hfun]
  exact ULim.const (U := U) (1 : ℝ)

theorem abs_phiLim_le (T : Hk κ →L[ℝ] Hk κ) : |phiLim U hcc T| ≤ ‖T‖ := by
  have h1 : phiLim U hcc T ≤ ‖T‖ := by
    refine ULim.le_of_le (f := diag T) (g := fun _ => ‖T‖) (fun α => ?_)
      (uLim_phiLim (hcc := hcc) T) (ULim.const _)
    exact le_trans (le_abs_self _) (abs_diag_le T α)
  have h2 : -‖T‖ ≤ phiLim U hcc T := by
    refine ULim.le_of_le (f := fun _ => -‖T‖) (g := diag T) (fun α => ?_)
      (ULim.const _) (uLim_phiLim (hcc := hcc) T)
    have h := (abs_le.mp (abs_diag_le T α)).1
    linarith
  exact abs_le.mpr ⟨h2, h1⟩

theorem phiLim_nonneg {T : Hk κ →L[ℝ] Hk κ} (hT : ∀ x, 0 ≤ inner (𝕜 := ℝ) (T x) x) :
    0 ≤ phiLim U hcc T :=
  ULim.le_of_le (f := fun _ => (0:ℝ)) (g := diag T) (fun α => diag_nonneg hT α)
    (ULim.const _) (uLim_phiLim (hcc := hcc) T)

theorem phiLim_mono {T S : Hk κ →L[ℝ] Hk κ}
    (h : ∀ x, inner (𝕜 := ℝ) (T x) x ≤ inner (𝕜 := ℝ) (S x) x) :
    phiLim U hcc T ≤ phiLim U hcc S :=
  ULim.le_of_le (fun α => diag_mono h α) (uLim_phiLim (hcc := hcc) T)
    (uLim_phiLim (hcc := hcc) S)

/-- A2. `phiLim` bundled as a continuous linear functional, with the bound
    `|φ T| ≤ ‖T‖`. -/
noncomputable def phiLimCLM (U : Ultrafilter κ) (hcc : PlufWO3.CountablyComplete U) :
    (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    ({ toFun := phiLim U hcc
       map_add' := fun T S => phiLim_add (hcc := hcc) T S
       map_smul' := fun c T => by simpa using phiLim_smul (hcc := hcc) c T } :
      (Hk κ →L[ℝ] Hk κ) →ₗ[ℝ] ℝ)
    1 (fun T => by
      rw [Real.norm_eq_abs, one_mul]
      exact abs_phiLim_le (hcc := hcc) T)

@[simp] theorem phiLimCLM_apply (T : Hk κ →L[ℝ] Hk κ) :
    phiLimCLM U hcc T = phiLim U hcc T := rfl

theorem isState_phiLimCLM : PlufWO6.IsState (phiLimCLM U hcc) := by
  constructor
  · intro A hA
    simpa using phiLim_nonneg (hcc := hcc) hA
  · simpa using phiLim_id (hcc := hcc)

end PlufWO8
