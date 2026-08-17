/-
  PlufWO8/Face.lean — Work Order 8, Parts D and F.

  The limit state lies in the face of `Φ(U)` (D1), and in fact *every*
  state in that face is `phiLim` (the purity statement D2): the route is
  WO-3's diagonal flattening `quadratic_flat` at `L = phiLim T`, combined
  with the compression identity `PlufWO6.IsState.compress` at a block
  projection of value one.

  The same flattening, applied at `L = 1` along a countable family of
  tolerances, identifies the 1-set of `phiLim` with the block filter
  `Φ(U)` (F1).
-/
import RequestProject.PlufWO8.Additive

open Set PlufWO2 PlufWO3 PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {κ : Type*} [LinearOrder κ] {U : Ultrafilter κ}
  {hcc : PlufWO3.CountablyComplete U}

/-- If the diagonal of `T` is constantly `c` on a member of `U`, the limit
    is `c`. -/
theorem phiLim_eq_of_diag_eq_on {T : Hk κ →L[ℝ] Hk κ} {s : Set κ} {c : ℝ}
    (hs : s ∈ U) (h : ∀ α ∈ s, diag T α = c) : phiLim U hcc T = c :=
  phiLim_eq (ULim.congr_of_mem (ULim.const c) hs h)

/-- The diagonal of a block projection is the indicator of the block. -/
theorem diag_starProjection_block {S : Set κ} {α : κ} (hα : α ∈ S)
    [(block S).HasOrthogonalProjection] :
    diag ((block S).starProjection) α = 1 := by
  have hmem : evec α ∈ block S := evec_mem_block hα
  have hfix : (block S).starProjection (evec α) = evec α :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  simp [diag, hfix, norm_evec]

/-- The limit state is `1` at every block projection of a `U`-set. -/
theorem phiLim_starProjection_block_eq_one {S : Set κ} (hS : S ∈ U)
    [(block S).HasOrthogonalProjection] :
    phiLim U hcc ((block S).starProjection) = 1 :=
  phiLim_eq_of_diag_eq_on (hcc := hcc) hS (fun _ hα => diag_starProjection_block hα)

/-- D1 (core). A state agreeing with `phiLim` is `1` at every closed
    member of `Φ(U)`. -/
theorem eq_one_of_mem_PhiU (φ : (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hval : ∀ T, φ T = phiLim U hcc T) (M : Submodule ℝ (Hk κ)) (hM : M ∈ PhiU U)
    [M.HasOrthogonalProjection] :
    φ M.starProjection = 1 := by
  obtain ⟨S, hSU, hSM⟩ := hM
  haveI : (block S).HasOrthogonalProjection :=
    hasOrthogonalProjection_of_isClosed (isClosed_block S)
  have hge : φ ((block S).starProjection) ≤ φ M.starProjection :=
    state_starProjection_mono hφ hSM
  have hb : φ ((block S).starProjection) = 1 := by
    rw [hval, phiLim_starProjection_block_eq_one (hcc := hcc) hSU]
  have hle : φ M.starProjection ≤ 1 := hφ.starProjection_le_one M
  rw [hb] at hge
  linarith

/-- D2 (core; the purity computation). Every state which is `1` at the
    closed members of `Φ(U)` agrees with `phiLim`: flattening (WO-3's
    `quadratic_flat`) squeezes the compression of `T` to a block between
    `(L ± ε) P`. -/
theorem eq_phiLim_of_mem_face (hdiag : PlufWO2.DiagInt U) (hsmall : PlufWO2.CountableSmall U)
    (φ : (Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hf : ∀ M ∈ PhiU U, ∀ _hM : IsClosed (M : Set (Hk κ)), φ M.starProjection = 1)
    (T : Hk κ →L[ℝ] Hk κ) : φ T = phiLim U hcc T := by
  set L : ℝ := phiLim U hcc T with hL
  have key : ∀ ε > 0, |φ T - L| ≤ ε := by
    intro ε hε
    obtain ⟨S, hSU, hS⟩ :=
      PlufWO3.quadratic_flat U hdiag hsmall T L (uLim_phiLim (hcc := hcc) T) hε
    haveI hinst : (block S).HasOrthogonalProjection :=
      hasOrthogonalProjection_of_isClosed (isClosed_block S)
    set P : Hk κ →L[ℝ] Hk κ := (block S).starProjection with hP
    have hP1 : φ P = 1 := hf (block S) ⟨S, hSU, le_rfl⟩ (isClosed_block S)
    have hcomp : φ (P ∘L T ∘L P) = φ T := hφ.compress hP1 T
    have hform : ∀ x : Hk κ, inner (𝕜 := ℝ) ((P ∘L T ∘L P) x) x
        = inner (𝕜 := ℝ) (T (P x)) (P x) := by
      intro x
      simp only [hP, ContinuousLinearMap.coe_comp', Function.comp_apply]
      exact (block S).inner_starProjection_left_eq_right _ _
    have hsmulform : ∀ (c : ℝ) (x : Hk κ),
        inner (𝕜 := ℝ) ((c • P : Hk κ →L[ℝ] Hk κ) x) x = c * ‖P x‖ ^ 2 := by
      intro c x
      simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left, hP]
      rw [inner_starProjection_self]
    have hupper : φ (P ∘L T ∘L P) ≤ L + ε := by
      have hmono : φ (P ∘L T ∘L P) ≤ φ ((L + ε) • P) := by
        refine hφ.mono (fun x => ?_)
        have hx : P x ∈ block S := Submodule.starProjection_apply_mem _ _
        have hflat := hS (P x) hx
        rw [hform x, hsmulform (L + ε) x]
        have := (abs_le.mp hflat).2
        nlinarith [sq_nonneg ‖P x‖]
      rwa [map_smul, smul_eq_mul, hP1, mul_one] at hmono
    have hlower : L - ε ≤ φ (P ∘L T ∘L P) := by
      have hmono : φ ((L - ε) • P) ≤ φ (P ∘L T ∘L P) := by
        refine hφ.mono (fun x => ?_)
        have hx : P x ∈ block S := Submodule.starProjection_apply_mem _ _
        have hflat := hS (P x) hx
        rw [hform x, hsmulform (L - ε) x]
        have := (abs_le.mp hflat).1
        nlinarith [sq_nonneg ‖P x‖]
      rwa [map_smul, smul_eq_mul, hP1, mul_one] at hmono
    rw [hcomp] at hupper hlower
    rw [abs_le]
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |φ T - L| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have := key (|φ T - L| / 2) (by linarith)
  linarith

/-- F1 (the hard inclusion). If the limit state is `1` at the projection
    onto a closed subspace `M`, then `M` contains a block of a `U`-set,
    i.e. `M ∈ Φ(U)`. Flattening at `L = 1` and tolerance `1/(n+1)`, the
    countable intersection of the flattening sets is a member of `U` on
    whose block the projection acts as the identity. -/
theorem mem_PhiU_of_phiLim_starProjection_eq_one (hdiag : PlufWO2.DiagInt U)
    (hsmall : PlufWO2.CountableSmall U) (M : Submodule ℝ (Hk κ))
    [M.HasOrthogonalProjection] (h1 : phiLim U hcc M.starProjection = 1) :
    M ∈ PhiU U := by
  have hlim : ULim U (diag M.starProjection) 1 := by
    have := uLim_phiLim (hcc := hcc) M.starProjection
    rwa [h1] at this
  have hflat : ∀ n : ℕ, ∃ S ∈ U, ∀ x ∈ block S,
      |inner (𝕜 := ℝ) (M.starProjection x) x - 1 * ‖x‖ ^ 2| ≤ (1 / (n + 1)) * ‖x‖ ^ 2 := by
    intro n
    exact PlufWO3.quadratic_flat U hdiag hsmall M.starProjection 1 hlim (by positivity)
  choose S hSU hS using hflat
  refine ⟨⋂ n, S n, hcc _ hSU, ?_⟩
  intro x hx
  have hxn : ∀ n : ℕ, x ∈ block (S n) := fun n =>
    block_mono (Set.iInter_subset S n) hx
  have hkey : ∀ n : ℕ, ‖x‖ ^ 2 - ‖M.starProjection x‖ ^ 2 ≤ (1 / (n + 1)) * ‖x‖ ^ 2 := by
    intro n
    have h := (abs_le.mp (hS n x (hxn n))).1
    rw [inner_starProjection_self] at h
    linarith
  have hge : ‖x‖ ^ 2 ≤ ‖M.starProjection x‖ ^ 2 := by
    by_contra hlt
    push_neg at hlt
    set c : ℝ := ‖x‖ ^ 2 - ‖M.starProjection x‖ ^ 2 with hc
    have hcpos : 0 < c := by rw [hc]; linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < c / (‖x‖ ^ 2 + 1) by positivity)
    have hkn := hkey n
    have hx2 : (0:ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have hmul : (1 / ((n:ℝ) + 1)) * ‖x‖ ^ 2 < (c / (‖x‖ ^ 2 + 1)) * ‖x‖ ^ 2 := by
      rcases eq_or_lt_of_le hx2 with heq | hlt2
      · exfalso
        rw [hc] at hcpos
        nlinarith [sq_nonneg ‖M.starProjection x‖]
      · exact (mul_lt_mul_of_pos_right hn hlt2)
    have hfrac : (c / (‖x‖ ^ 2 + 1)) * ‖x‖ ^ 2 < c := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hfix : x = M.starProjection x := by
    have hnormsq : ‖x - M.starProjection x‖ ^ 2 = ‖x‖ ^ 2 - ‖M.starProjection x‖ ^ 2 := by
      have hinner : inner (𝕜 := ℝ) (M.starProjection x) x = ‖M.starProjection x‖ ^ 2 :=
        inner_starProjection_self x
      have hexp : ‖x - M.starProjection x‖ ^ 2
          = ‖x‖ ^ 2 - 2 * inner (𝕜 := ℝ) (M.starProjection x) x
            + ‖M.starProjection x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          ← real_inner_self_eq_norm_sq]
        rw [inner_sub_sub_self]
        have hsymm : inner (𝕜 := ℝ) x (M.starProjection x)
            = inner (𝕜 := ℝ) (M.starProjection x) x := real_inner_comm _ _
        rw [hsymm]
        ring
      rw [hexp, hinner]
      ring
    have hzero : ‖x - M.starProjection x‖ ^ 2 ≤ 0 := by rw [hnormsq]; linarith
    have hn0 : ‖x - M.starProjection x‖ = 0 := by
      nlinarith [norm_nonneg (x - M.starProjection x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn0)
  rw [hfix]
  exact M.starProjection_apply_mem x

end PlufWO8
