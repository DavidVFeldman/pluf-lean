/-
  PlufWO5/PartD.lean — Work Order 5, Part D: Gowers's intimate subspace
  (Paper II, Theorem 4.1/4.2): intimacy, the dimension bound, and the
  no-cofinite corollary.
-/
import RequestProject.PlufWO5.PartA

open Set

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO5

open PlufWO1

noncomputable section

section Gowers

/-- The auxiliary vectors: `u n = e n − ((n+2)/(n+1)) • e (n+1)` in
    0-indexing, orthogonal to the weight vector `w = (1/(n+1))_n`. -/
def gowersU (n : ℕ) : H :=
  evec n - (((n : ℝ) + 2) / ((n : ℝ) + 1)) • evec (n + 1)

/-- The duplicated constraints: `v n` has coordinates
    `(v n) (2i) = (v n) (2i+1) = (u n) i`. -/
def gowersV (n : ℕ) : H :=
  (evec (2 * n) + evec (2 * n + 1))
    - (((n : ℝ) + 2) / ((n : ℝ) + 1)) • (evec (2 * n + 2) + evec (2 * n + 3))

/-- The duplication property defining `gowersV` from `gowersU`. -/
theorem gowersV_apply_two_mul (n i : ℕ) :
    (gowersV n : ∀ _ : ℕ, ℝ) (2 * i) = (gowersU n : ∀ _ : ℕ, ℝ) i ∧
      (gowersV n : ∀ _ : ℕ, ℝ) (2 * i + 1) = (gowersU n : ∀ _ : ℕ, ℝ) i := by
  constructor <;>
  · simp only [gowersV, gowersU, lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, evec_apply]
    split_ifs <;> first | (exfalso; omega) | ring1

/-- Gowers's subspace: the joint kernel of the duplicated constraints. -/
def gowersX : Submodule ℝ H :=
  ⨅ n, LinearMap.ker
    ((innerSL ℝ (gowersV n) : H →L[ℝ] ℝ) : H →ₗ[ℝ] ℝ)

theorem inner_gowersV (n : ℕ) (x : H) :
    inner (𝕜 := ℝ) (gowersV n) x
      = ((x : ∀ _ : ℕ, ℝ) (2 * n) + (x : ∀ _ : ℕ, ℝ) (2 * n + 1))
        - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
          ((x : ∀ _ : ℕ, ℝ) (2 * n + 2) + (x : ∀ _ : ℕ, ℝ) (2 * n + 3)) := by
  rw [gowersV, inner_sub_left, inner_add_left, real_inner_smul_left, inner_add_left,
    inner_evec_left, inner_evec_left, inner_evec_left, inner_evec_left]

/-- Membership in Gowers's subspace, in coordinates: the pair sums
    `s n = x (2n) + x (2n+1)` satisfy `s n = ((n+2)/(n+1)) * s (n+1)`. -/
theorem mem_gowersX_iff (x : H) :
    x ∈ gowersX ↔ ∀ n : ℕ,
      ((x : ∀ _ : ℕ, ℝ) (2 * n) + (x : ∀ _ : ℕ, ℝ) (2 * n + 1))
        = (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
          ((x : ∀ _ : ℕ, ℝ) (2 * n + 2) + (x : ∀ _ : ℕ, ℝ) (2 * n + 3)) := by
  simp only [gowersX, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply]
  constructor
  · intro h n
    have := h n
    rw [inner_gowersV] at this
    linarith
  · intro h n
    rw [inner_gowersV, h n]
    ring

theorem isClosed_gowersX : IsClosed (gowersX : Set H) := by
  have h : ((gowersX : Submodule ℝ H) : Set H)
      = ⋂ n, {x : H | innerSL ℝ (gowersV n) x = 0} := by
    ext x
    simp only [SetLike.mem_coe, gowersX, Submodule.mem_iInf, LinearMap.mem_ker, mem_iInter,
      mem_setOf_eq, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
  rw [h]
  exact isClosed_iInter fun n =>
    isClosed_eq (innerSL ℝ (gowersV n)).continuous continuous_const

/-! ### The two families of witnesses -/

/-- The difference of a pair of basis vectors lies in `X`. -/
theorem pairDiff_mem_gowersX (i : ℕ) : evec (2 * i) - evec (2 * i + 1) ∈ gowersX := by
  rw [mem_gowersX_iff]
  intro n
  simp only [lp.coeFn_sub, Pi.sub_apply, evec_apply]
  rw [if_neg (by omega : ¬ (2 * n = 2 * i + 1)), if_neg (by omega : ¬ (2 * n + 1 = 2 * i)),
    if_neg (by omega : ¬ (2 * n + 2 = 2 * i + 1)), if_neg (by omega : ¬ (2 * n + 3 = 2 * i))]
  by_cases h : n = i
  · subst h
    rw [if_pos rfl, if_pos rfl, if_neg (by omega : ¬ (2 * n + 2 = 2 * n)),
      if_neg (by omega : ¬ (2 * n + 3 = 2 * n + 1))]
    ring
  · rw [if_neg (by omega : ¬ (2 * n = 2 * i)), if_neg (by omega : ¬ (2 * n + 1 = 2 * i + 1))]
    by_cases h2 : n + 1 = i
    · subst h2
      rw [if_pos (by omega), if_pos (by omega)]
      ring
    · rw [if_neg (by omega : ¬ (2 * n + 2 = 2 * i)),
        if_neg (by omega : ¬ (2 * n + 3 = 2 * i + 1))]
      ring

theorem pairDiff_ne_zero (i : ℕ) : evec (2 * i) - evec (2 * i + 1) ≠ 0 := by
  intro h
  have : ((evec (2 * i) - evec (2 * i + 1) : H) : ∀ _ : ℕ, ℝ) (2 * i) = 0 := by
    rw [h]; rfl
  simp only [lp.coeFn_sub, Pi.sub_apply, evec_apply,
    if_neg (by omega : ¬ (2 * i = 2 * i + 1))] at this
  norm_num at this

theorem pairDiff_mem_block {A : Set ℕ} {i : ℕ} (h1 : 2 * i ∈ A) (h2 : 2 * i + 1 ∈ A) :
    evec (2 * i) - evec (2 * i + 1) ∈ block A :=
  Submodule.sub_mem _ (evec_mem_block h1) (evec_mem_block h2)

/-- Square summability of the harmonic weights used by the transversal
    witness. -/
theorem summable_inv_succ_sq : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

/-- The transversal witness: a vector of weight `1/(i+1)` on the chosen
    representative `a i` of the pair `{2i, 2i+1}`. -/
def transversalVec (a : ℕ → ℕ) : H :=
  ⟨fun m => if a (m / 2) = m then 1 / ((m / 2 : ℕ) + 1 : ℝ) else 0, by
    apply memℓp_gen
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    rw [h2]
    have hpow : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := fun y => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hpow]
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (Summable.mul_left 4 summable_inv_succ_sq)
    have hpos : (0 : ℝ) < ((m / 2 : ℕ) : ℝ) + 1 := by positivity
    have hle : ((m : ℝ) + 1) ≤ 2 * (((m / 2 : ℕ) : ℝ) + 1) := by
      have : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
        have hnat : m ≤ 2 * (m / 2) + 1 := by omega
        exact_mod_cast hnat
      linarith
    have hbound : ‖(if a (m / 2) = m then 1 / ((m / 2 : ℕ) + 1 : ℝ) else 0)‖
        ≤ 1 / (((m / 2 : ℕ) : ℝ) + 1) := by
      by_cases h : a (m / 2) = m
      · rw [if_pos h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [if_neg h]
        simp only [norm_zero]
        positivity
    calc ‖(if a (m / 2) = m then 1 / ((m / 2 : ℕ) + 1 : ℝ) else 0)‖ ^ (2 : ℕ)
        ≤ (1 / (((m / 2 : ℕ) : ℝ) + 1)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ ≤ 4 * (1 / ((m : ℝ) + 1) ^ 2) := by
          have hY : ((m : ℝ) + 1) ^ 2 ≤ 4 * (((m / 2 : ℕ) : ℝ) + 1) ^ 2 := by
            nlinarith [hpos, hle]
          rw [div_pow, one_pow, show (4 : ℝ) * (1 / ((m : ℝ) + 1) ^ 2)
            = 4 / ((m : ℝ) + 1) ^ 2 by ring,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hY]⟩

theorem transversalVec_apply (a : ℕ → ℕ) (m : ℕ) :
    (transversalVec a : ∀ _ : ℕ, ℝ) m =
      if a (m / 2) = m then 1 / ((m / 2 : ℕ) + 1 : ℝ) else 0 := rfl

/-- D1 (Theorem 4.1, intimacy). For every `A ⊆ ℕ`, Gowers's subspace
    meets `block A` or `block Aᶜ` nontrivially. -/
theorem gowersX_intimate (A : Set ℕ) :
    gowersX ⊓ block A ≠ ⊥ ∨ gowersX ⊓ block Aᶜ ≠ ⊥ := by
  classical
  by_cases hpair : ∃ i : ℕ, 2 * i ∈ A ∧ 2 * i + 1 ∈ A
  · obtain ⟨i, h1, h2⟩ := hpair
    refine Or.inl (fun hbot => pairDiff_ne_zero i ?_)
    have : (evec (2 * i) - evec (2 * i + 1) : H) ∈ gowersX ⊓ block A :=
      ⟨pairDiff_mem_gowersX i, pairDiff_mem_block h1 h2⟩
    rw [hbot] at this
    simpa using this
  by_cases hpair' : ∃ i : ℕ, 2 * i ∈ Aᶜ ∧ 2 * i + 1 ∈ Aᶜ
  · obtain ⟨i, h1, h2⟩ := hpair'
    refine Or.inr (fun hbot => pairDiff_ne_zero i ?_)
    have : (evec (2 * i) - evec (2 * i + 1) : H) ∈ gowersX ⊓ block Aᶜ :=
      ⟨pairDiff_mem_gowersX i, pairDiff_mem_block h1 h2⟩
    rw [hbot] at this
    simpa using this
  -- the split case: `A` is a transversal of the pairs
  push_neg at hpair hpair'
  set a : ℕ → ℕ := fun i => if 2 * i ∈ A then 2 * i else 2 * i + 1 with hadef
  have hamem : ∀ i, a i ∈ A := by
    intro i
    by_cases h : 2 * i ∈ A
    · rw [hadef]; simp [h]
    · have := hpair' i (by simpa using h)
      rw [hadef]
      simp only [if_neg h]
      simpa using this
  have hadiv : ∀ i, a i / 2 = i := by
    intro i
    by_cases h : 2 * i ∈ A
    · simp [hadef, h]
    · simp only [hadef, if_neg h]
      omega
  have hacases : ∀ i, a i = 2 * i ∨ a i = 2 * i + 1 := by
    intro i
    by_cases h : 2 * i ∈ A <;> simp [hadef, h]
  set x : H := transversalVec a with hxdef
  have hcoord : ∀ n : ℕ,
      (x : ∀ _ : ℕ, ℝ) (2 * n) + (x : ∀ _ : ℕ, ℝ) (2 * n + 1) = 1 / ((n : ℝ) + 1) := by
    intro n
    rw [hxdef, transversalVec_apply, transversalVec_apply]
    have hd1 : (2 * n) / 2 = n := by omega
    have hd2 : (2 * n + 1) / 2 = n := by omega
    rw [hd1, hd2]
    rcases hacases n with h | h
    · rw [if_pos h, if_neg (by omega : ¬ (a n = 2 * n + 1))]
      push_cast
      ring
    · rw [if_neg (by omega : ¬ (a n = 2 * n)), if_pos h]
      push_cast
      ring
  have hxX : x ∈ gowersX := by
    rw [mem_gowersX_iff]
    intro n
    rw [show (2 * n + 2) = 2 * (n + 1) by ring, show (2 * n + 3) = 2 * (n + 1) + 1 by ring,
      hcoord n, hcoord (n + 1)]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hxA : x ∈ block A := by
    rw [mem_block_iff]
    intro m hm
    rw [hxdef, transversalVec_apply, if_neg]
    intro h
    exact hm (h ▸ hamem (m / 2))
  have hxne : x ≠ 0 := by
    intro h0
    have := hcoord 0
    rw [h0] at this
    norm_num at this
  refine Or.inl (fun hbot => hxne ?_)
  have hmem : x ∈ gowersX ⊓ block A := ⟨hxX, hxA⟩
  rw [hbot] at hmem
  simpa using hmem

/-! ### The dimension bound -/

/-- On a finitely supported member of `X` all pair sums vanish. -/
theorem gowersX_pairSum_eq_zero {C : Set ℕ} (hC : C.Finite) {x : H}
    (hxX : x ∈ gowersX) (hxC : x ∈ block C) (n : ℕ) :
    (x : ∀ _ : ℕ, ℝ) (2 * n) + (x : ∀ _ : ℕ, ℝ) (2 * n + 1) = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ m ∈ C, m < 2 * N := by
    obtain ⟨T, hT⟩ := hC.exists_finset_coe
    refine ⟨(T.sup id) + 1, fun m hm => ?_⟩
    have : m ≤ T.sup id := Finset.le_sup (f := id) (by rw [← Finset.mem_coe, hT]; exact hm)
    omega
  have hzero : ∀ m, 2 * N ≤ m → (x : ∀ _ : ℕ, ℝ) m = 0 := by
    intro m hm
    refine (mem_block_iff C x).mp hxC m (fun hmem => ?_)
    exact absurd (hN m hmem) (by omega)
  have hrel := (mem_gowersX_iff x).mp hxX
  have hbig : ∀ k, N ≤ k → (x : ∀ _ : ℕ, ℝ) (2 * k) + (x : ∀ _ : ℕ, ℝ) (2 * k + 1) = 0 := by
    intro k hk
    rw [hzero (2 * k) (by omega), hzero (2 * k + 1) (by omega)]
    ring
  have hdown : ∀ j, (x : ∀ _ : ℕ, ℝ) (2 * (N - j)) + (x : ∀ _ : ℕ, ℝ) (2 * (N - j) + 1) = 0 := by
    intro j
    induction j with
    | zero => exact hbig N (le_refl N)
    | succ j ih =>
        by_cases hj : N ≤ j
        · have : N - (j + 1) = 0 := by omega
          rw [this]
          have h0 : N - j = 0 := by omega
          rw [h0] at ih
          exact ih
        · have hsucc : (N - (j + 1)) + 1 = N - j := by omega
          have := hrel (N - (j + 1))
          rw [show 2 * (N - (j + 1)) + 2 = 2 * ((N - (j + 1)) + 1) by ring,
            show 2 * (N - (j + 1)) + 3 = 2 * ((N - (j + 1)) + 1) + 1 by ring, hsucc] at this
          rw [this, ih]
          ring
  by_cases hn : n ≤ N
  · have := hdown (N - n)
    rwa [show N - (N - n) = n by omega] at this
  · exact hbig n (by omega)

/-- D2 (Theorem 4.1, the dimension bound). On a finite block,
    `2 · dim (X ⊓ block C) ≤ |C|`. -/
theorem gowersX_dim_bound (C : Finset ℕ) :
    2 * Module.finrank ℝ ↥(gowersX ⊓ block (C : Set ℕ)) ≤ C.card := by
  classical
  set D : Finset ℕ := C.filter (fun m => m % 2 = 0 ∧ m + 1 ∈ C) with hD
  -- the coordinate map on the full pairs is injective on `X ⊓ block C`
  set f : ↥(gowersX ⊓ block (C : Set ℕ)) →ₗ[ℝ] (↥(D : Set ℕ) → ℝ) :=
    { toFun := fun x m => ((x : H) : ∀ _ : ℕ, ℝ) (m : ℕ)
      map_add' := by intro x y; funext m; rfl
      map_smul' := by intro c x; funext m; rfl } with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxX, hxC⟩ hker
    have hval : ∀ m ∈ D, (x : ∀ _ : ℕ, ℝ) m = 0 := by
      intro m hm
      have : f ⟨x, hxX, hxC⟩ ⟨m, hm⟩ = 0 := by rw [hker]; rfl
      exact this
    have hpair := gowersX_pairSum_eq_zero C.finite_toSet hxX hxC
    have hzero : ∀ m : ℕ, (x : ∀ _ : ℕ, ℝ) m = 0 := by
      intro m
      have hkey : ∀ k : ℕ, (x : ∀ _ : ℕ, ℝ) (2 * k) = 0 ∧ (x : ∀ _ : ℕ, ℝ) (2 * k + 1) = 0 := by
        intro k
        by_cases hk : 2 * k ∈ C ∧ 2 * k + 1 ∈ C
        · have hmD : 2 * k ∈ D := by
            rw [hD, Finset.mem_filter]
            exact ⟨hk.1, by omega, hk.2⟩
          have h1 := hval _ hmD
          have h2 := hpair k
          exact ⟨h1, by linarith⟩
        · rw [not_and_or] at hk
          rcases hk with hk | hk
          · have h1 : (x : ∀ _ : ℕ, ℝ) (2 * k) = 0 :=
              (mem_block_iff _ x).mp hxC _ (by simpa using hk)
            exact ⟨h1, by have := hpair k; linarith⟩
          · have h1 : (x : ∀ _ : ℕ, ℝ) (2 * k + 1) = 0 :=
              (mem_block_iff _ x).mp hxC _ (by simpa using hk)
            exact ⟨by have := hpair k; linarith, h1⟩
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · have : m = 2 * k := by omega
        rw [this]; exact (hkey k).1
      · have : m = 2 * k + 1 := by omega
        rw [this]; exact (hkey k).2
    exact Subtype.ext (lp.ext (funext hzero))
  haveI : Fintype ↥(D : Set ℕ) := FinsetCoe.fintype D
  have hrank : Module.finrank ℝ ↥(gowersX ⊓ block (C : Set ℕ))
      ≤ Module.finrank ℝ (↥(D : Set ℕ) → ℝ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hcard : Module.finrank ℝ (↥(D : Set ℕ) → ℝ) = D.card := by
    rw [Module.finrank_pi ℝ]
    simp
  have h2D : 2 * D.card ≤ C.card := by
    have hsub : D ∪ D.image (· + 1) ⊆ C := by
      intro m hm
      rcases Finset.mem_union.mp hm with h | h
      · exact (Finset.mem_filter.mp (hD ▸ h)).1
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp (hD ▸ hj)).2.2
    have hdisj : Disjoint D (D.image (· + 1)) := by
      rw [Finset.disjoint_left]
      intro m hmD hmI
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hmI
      have h1 : m % 2 = 0 := (Finset.mem_filter.mp (hD ▸ hmD)).2.1
      have h2 : j % 2 = 0 := (Finset.mem_filter.mp (hD ▸ hj)).2.1
      omega
    have himg : (D.image (· + 1)).card = D.card :=
      Finset.card_image_of_injective _ (fun p q h => by omega)
    calc 2 * D.card = D.card + (D.image (· + 1)).card := by rw [himg]; ring
      _ = (D ∪ D.image (· + 1)).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ C.card := Finset.card_le_card hsub
  omega

set_option maxHeartbeats 2000000 in
/-- D3 (Theorem 4.1, consequence). `X` has infinite relative codimension
    in every infinite block. -/
theorem gowersX_no_finCodim {S : Set ℕ} (hS : S.Infinite) :
    ¬ FinCodimIn gowersX (block S) := by
  classical
  intro hcodim
  haveI hfin : Module.Finite ℝ (↥(block S) ⧸ (gowersX ⊓ block S).comap (block S).subtype) :=
    hcodim
  set Q := ↥(block S) ⧸ (gowersX ⊓ block S).comap (block S).subtype with hQ
  set d := Module.finrank ℝ Q with hd
  obtain ⟨C, hCS, hCcard⟩ := hS.exists_subset_card_eq (2 * d + 1)
  -- the composite `block C → block S → Q`
  have hCle : block (C : Set ℕ) ≤ block S := block_mono hCS
  set g : ↥(block (C : Set ℕ)) →ₗ[ℝ] Q :=
    ((gowersX ⊓ block S).comap (block S).subtype).mkQ.comp
      (Submodule.inclusion hCle) with hg
  haveI : Module.Finite ℝ ↥(block (C : Set ℕ)) := finite_block C.finite_toSet
  haveI : FiniteDimensional ℝ ↥(block (C : Set ℕ)) := ‹Module.Finite ℝ _›
  have hker : LinearMap.ker g = (gowersX ⊓ block (C : Set ℕ)).comap
      (block (C : Set ℕ)).subtype := by
    ext y
    rw [LinearMap.mem_ker, hg, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap]
    exact ⟨fun h => ⟨h.1, y.2⟩, fun h => ⟨h.1, hCle y.2⟩⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hkerfin : Module.finrank ℝ ↥(LinearMap.ker g)
      = Module.finrank ℝ ↥(gowersX ⊓ block (C : Set ℕ)) := by
    rw [hker]
    exact LinearEquiv.finrank_eq
      (Submodule.comapSubtypeEquivOfLe (inf_le_right : gowersX ⊓ block (C : Set ℕ) ≤ _))
  have hrangefin : Module.finrank ℝ ↥(LinearMap.range g) ≤ d :=
    Submodule.finrank_le _
  have hCfr : (2 * d + 1) ≤ Module.finrank ℝ ↥(block (C : Set ℕ)) := by
    have := card_le_finrank_block C
    omega
  have hbound := gowersX_dim_bound C
  rw [hCcard] at hbound
  rw [hkerfin] at hrn
  omega

end Gowers

end

end PlufWO5
