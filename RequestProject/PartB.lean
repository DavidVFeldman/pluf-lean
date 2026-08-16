/-
  PartB.lean — Part B of Work Order 1 for the pluf project (Feldman–Wilce):
  the witness subspace in ℓ²(ℕ) and the thinness lemma.
-/
import RequestProject.PartA

open Set
open scoped ENNReal

namespace PlufWO1

/-! ### Part B: the witness subspace in ℓ²(ℕ) and the thinness lemma -/

section Hilbert

noncomputable section

/-- The ambient Hilbert space ℓ²(ℕ; ℝ). -/
abbrev H : Type := lp (fun _ : ℕ => ℝ) 2

/-- Evaluation at a coordinate, as a linear map on `H`. -/
def coordL (n : ℕ) : H →ₗ[ℝ] ℝ where
  toFun x := (x : ∀ _ : ℕ, ℝ) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordL_apply (n : ℕ) (x : H) : coordL n x = (x : ∀ _ : ℕ, ℝ) n := rfl

/-- Evaluation at a coordinate, as a continuous linear map on `H`. -/
def coordCLM (n : ℕ) : H →L[ℝ] ℝ :=
  (coordL n).mkContinuous 1 (by
    intro x
    simpa using lp.norm_apply_le_norm (p := 2) (by norm_num) x n)

@[simp] theorem coordCLM_apply (n : ℕ) (x : H) : coordCLM n x = (x : ∀ _ : ℕ, ℝ) n := rfl

/-- B1a (square-summability). The weight sequence `2^{-(n+1)}` restricted to a
    set `A ⊆ ℕ` is square-summable. -/
theorem memlp_constraint (A : Set ℕ) :
    Memℓp (fun n : ℕ => Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2]
  have hconv : ∀ n : ℕ, ‖Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n‖ ^ (2:ℝ)
      = ‖Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n‖ ^ (2:ℕ) := by
    intro n; rw [← Real.rpow_natCast _ 2]; norm_num
  simp only [hconv]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num))
  have hb : ‖Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n‖ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
    rcases Classical.em (n ∈ A) with h | h
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · rw [Set.indicator_of_notMem h]
      simp only [norm_zero]
      positivity
  calc ‖Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n‖ ^ (2:ℕ)
      ≤ (((2:ℝ)^(n+1))⁻¹)^(2:ℕ) := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (1/4:ℝ)^(n+1) := by
        rw [show ((2:ℝ)^(n+1))⁻¹ = (1/2:ℝ)^(n+1) by rw [one_div, inv_pow], ← pow_mul,
          mul_comm (n+1) 2, pow_mul]
        norm_num
    _ ≤ (1/4:ℝ)^n := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) n]

/-- B1a. The weight sequence restricted to a set `A ⊆ ℕ`, as an element of `H`:
    coordinates `2^{-(n+1)}` on `A`, zero off `A`. -/
def constraintVec (A : Set ℕ) : H :=
  ⟨fun n => Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n, memlp_constraint A⟩

open Classical in
theorem constraintVec_apply (A : Set ℕ) (n : ℕ) :
    (constraintVec A : ∀ _ : ℕ, ℝ) n =
      if n ∈ A then ((2 : ℝ) ^ (n + 1))⁻¹ else 0 := by
  show Set.indicator A (fun n => ((2 : ℝ) ^ (n + 1))⁻¹) n = _
  rw [Set.indicator_apply]

theorem constraintVec_ne_zero {A : Set ℕ} (hA : A.Nonempty) :
    constraintVec A ≠ 0 := by
  obtain ⟨n, hn⟩ := hA
  intro h
  have : (constraintVec A : ∀ _ : ℕ, ℝ) n = 0 := by rw [h]; rfl
  rw [constraintVec_apply, if_pos hn] at this
  have : ((2:ℝ) ^ (n+1))⁻¹ ≠ 0 := by positivity
  exact this ‹((2:ℝ) ^ (n+1))⁻¹ = 0›

/-- B1b. The block of a set `S ⊆ ℕ`: the closed subspace of vectors
    supported in `S`, presented as an intersection of kernels of coordinate
    functionals. -/
def block (S : Set ℕ) : Submodule ℝ H :=
  ⨅ n ∈ Sᶜ, LinearMap.ker (coordL n)

theorem mem_block_iff (S : Set ℕ) (x : H) :
    x ∈ block S ↔ ∀ n ∉ S, (x : ∀ _ : ℕ, ℝ) n = 0 := by
  simp [block, Submodule.mem_iInf, LinearMap.mem_ker]

/-- B1c. Blocks are closed. -/
theorem isClosed_block (S : Set ℕ) : IsClosed (block S : Set H) := by
  have h : (block S : Set H) = ⋂ n ∈ Sᶜ, {x : H | coordCLM n x = 0} := by
    ext x
    simp [mem_block_iff]
  rw [h]
  exact isClosed_biInter fun n _ => isClosed_eq (coordCLM n).continuous continuous_const

/-- B1d. Inner product against a constraint vector sees only the
    coordinates in its support: if `x` is supported in a set disjoint from
    `A`, then `⟪x, constraintVec A⟫ = 0`. -/
theorem inner_constraintVec_eq_zero_of_disjoint {A S : Set ℕ}
    (hdisj : Disjoint A S) {x : H} (hx : x ∈ block S) :
    inner (𝕜 := ℝ) x (constraintVec A) = 0 := by
  rw [lp.inner_eq_tsum]
  have : ∀ n : ℕ, inner (𝕜 := ℝ) ((x : ∀ _ : ℕ, ℝ) n) ((constraintVec A : ∀ _ : ℕ, ℝ) n) = 0 := by
    intro n
    rcases Classical.em (n ∈ A) with h | h
    · have hnS : n ∉ S := fun hS => (Set.disjoint_left.mp hdisj h) hS
      rw [(mem_block_iff S x).mp hx n hnS]
      simp
    · rw [constraintVec_apply, if_neg h]
      simp
  rw [tsum_congr this, tsum_zero]

/-- The witness subspace of a partition `A : ℕ → Set ℕ`:
    everything orthogonal to every constraint vector. -/
def W (A : ℕ → Set ℕ) : Submodule ℝ H :=
  ⨅ k, LinearMap.ker
    ((innerSL ℝ (constraintVec (A k)) : H →L[ℝ] ℝ) : H →ₗ[ℝ] ℝ)

theorem mem_W_iff (A : ℕ → Set ℕ) (x : H) :
    x ∈ W A ↔ ∀ k, inner (𝕜 := ℝ) x (constraintVec (A k)) = 0 := by
  simp only [W, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h k
    have := h k
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply] at this
    rw [real_inner_comm]
    exact this
  · intro h k
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [real_inner_comm]
    exact h k

/-- B2 (Thinness Lemma; Paper II, Lemma 3.6). Let `A` be a partition of ℕ
    into pairwise disjoint nonempty pieces. If a submodule `R` meets `W A`
    trivially, then `R` meets each piece-block in rank at most one. -/
theorem thin (A : ℕ → Set ℕ)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (R : Submodule ℝ H) (hRW : R ⊓ W A = ⊥) (k : ℕ) :
    Module.rank ℝ ↥(R ⊓ block (A k)) ≤ 1 := by
  -- the functional `x ↦ ⟪x, constraintVec (A k)⟫` restricted to `R ⊓ block (A k)`
  set f : ↥(R ⊓ block (A k)) →ₗ[ℝ] ℝ :=
    (innerSL ℝ (constraintVec (A k)) : H →L[ℝ] ℝ).toLinearMap.comp
      (Submodule.subtype (R ⊓ block (A k))) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    rintro ⟨x, hxR, hxB⟩ hker
    have hx0 : inner (𝕜 := ℝ) (constraintVec (A k)) x = 0 := by
      simpa [hf] using hker
    have hxW : x ∈ W A := by
      rw [mem_W_iff]
      intro j
      rcases eq_or_ne j k with rfl | hjk
      · rw [real_inner_comm]; exact hx0
      · exact inner_constraintVec_eq_zero_of_disjoint (hdisj hjk) hxB
    have : x ∈ R ⊓ W A := ⟨hxR, hxW⟩
    rw [hRW] at this
    exact Subtype.ext (by simpa using this)
  have := LinearMap.rank_le_of_injective f hinj
  simpa using this

end

end Hilbert

end PlufWO1
