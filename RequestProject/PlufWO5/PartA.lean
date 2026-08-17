/-
  PlufWO5/PartA.lean — Work Order 5, Part A: the zero–cofinite dichotomy
  (Paper II, Theorem 2.1, Corollary 2.2/2.3 and Proposition 4.2).

  The gliding-hump recursion is run *relatively*, inside an arbitrary
  block `block S₀`; the absolute statement (A1) is the case `S₀ = univ`
  and the relativization (A2) is the bridge between the contract's
  quotient rendering of relative codimension and the relative
  orthocomplement. No isometry `block S₀ ≃ H` is needed.
-/
import RequestProject.PlufWO5.Basic

open Set

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO5

open PlufWO1

noncomputable section

/-- In an infinite-dimensional subspace there is a nonzero vector vanishing
    on any prescribed initial segment of coordinates. -/
theorem exists_mem_vanishing_below (R : Submodule ℝ H) (hR : ¬ Module.Finite ℝ ↥R) (N : ℕ) :
    ∃ u ∈ R, u ≠ 0 ∧ ∀ m ≤ N, (u : ∀ _ : ℕ, ℝ) m = 0 := by
  classical
  set f : ↥R →ₗ[ℝ] (Fin (N+1) → ℝ) :=
    LinearMap.pi (fun i : Fin (N+1) => (coordL (i : ℕ)).comp R.subtype) with hf
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    exact hR (Module.Finite.of_injective f (LinearMap.ker_eq_bot.mp h))
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(u : H), u.2, fun h => hu0 (Subtype.ext h), fun m hm => ?_⟩
  have hfu : f u = 0 := hu
  have := congrFun hfu ⟨m, by omega⟩
  simpa [hf, coordL] using this

/-- One step of the gliding-hump recursion: a vector of `R` vanishing below
    `N`, a coordinate `n > N` where it does not vanish, and a threshold
    `N' > n` beyond which its tail is `ε`-small relative to that
    coordinate. -/
theorem gliding_step (R : Submodule ℝ H) (hR : ¬ Module.Finite ℝ ↥R) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : H) (n N' : ℕ), u ∈ R ∧ (∀ m ≤ N, (u : ∀ _ : ℕ, ℝ) m = 0) ∧
      N < n ∧ (u : ∀ _ : ℕ, ℝ) n ≠ 0 ∧ n < N' ∧
      ∀ y : H, (∀ m ≤ N', (y : ∀ _ : ℕ, ℝ) m = 0) →
        |inner (𝕜 := ℝ) y u| ≤ (ε * |(u : ∀ _ : ℕ, ℝ) n|) * ‖y‖ := by
  obtain ⟨u, huR, hune, hvan⟩ := exists_mem_vanishing_below R hR N
  have hex : ∃ n, (u : ∀ _ : ℕ, ℝ) n ≠ 0 := by
    by_contra h
    push_neg at h
    exact hune (lp.ext (funext h))
  obtain ⟨n, hn⟩ := hex
  have hnN : N < n := by
    by_contra h
    exact hn (hvan n (by omega))
  have hδ : 0 < |(u : ∀ _ : ℕ, ℝ) n| := abs_pos.mpr hn
  obtain ⟨N', hN'gt, htail⟩ :=
    exists_tail_norm_le u (by positivity : (0:ℝ) < ε * |(u : ∀ _ : ℕ, ℝ) n|) n
  refine ⟨u, n, N', huR, hvan, hnN, hn, hN'gt, fun y hy => ?_⟩
  have h1 : inner (𝕜 := ℝ) y u = inner (𝕜 := ℝ) y (restr {m | N' < m} u) := by
    refine inner_eq_inner_restr (fun m hm => hy m ?_) u
    simp only [mem_setOf_eq, not_lt] at hm
    exact hm
  rw [h1]
  calc |inner (𝕜 := ℝ) y (restr {m | N' < m} u)| ≤ ‖y‖ * ‖restr {m | N' < m} u‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (ε * |(u : ∀ _ : ℕ, ℝ) n|) := mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = (ε * |(u : ∀ _ : ℕ, ℝ) n|) * ‖y‖ := by ring

/-- The gliding-hump recursion, packaged: unit-free vectors `u j` of `R`,
    coordinates `n j` and thresholds `M j` with
    `M j < n j < M (j+1)`, `u j` vanishing below `M j`, not vanishing at
    `n j`, and with a tail bound beyond `M (j+1)` scaled by `2^{-(j+2)}`. -/
theorem gliding_sequence (R : Submodule ℝ H) (hR : ¬ Module.Finite ℝ ↥R) :
    ∃ (u : ℕ → H) (n M : ℕ → ℕ),
      (∀ j, u j ∈ R) ∧
      (∀ j, ∀ m ≤ M j, (u j : ∀ _ : ℕ, ℝ) m = 0) ∧
      (∀ j, M j < n j) ∧
      (∀ j, (u j : ∀ _ : ℕ, ℝ) (n j) ≠ 0) ∧
      (∀ j, n j < M (j + 1)) ∧
      (∀ j, ∀ y : H, (∀ m ≤ M (j+1), (y : ∀ _ : ℕ, ℝ) m = 0) →
        |inner (𝕜 := ℝ) y (u j)| ≤ (((1:ℝ)/2)^(j+2) * |(u j : ∀ _ : ℕ, ℝ) (n j)|) * ‖y‖) := by
  classical
  have step : ∀ (N j : ℕ), ∃ p : H × ℕ × ℕ, p.1 ∈ R ∧ (∀ m ≤ N, (p.1 : ∀ _ : ℕ, ℝ) m = 0) ∧
      N < p.2.1 ∧ (p.1 : ∀ _ : ℕ, ℝ) p.2.1 ≠ 0 ∧ p.2.1 < p.2.2 ∧
      ∀ y : H, (∀ m ≤ p.2.2, (y : ∀ _ : ℕ, ℝ) m = 0) →
        |inner (𝕜 := ℝ) y p.1| ≤ (((1:ℝ)/2)^(j+2) * |(p.1 : ∀ _ : ℕ, ℝ) p.2.1|) * ‖y‖ := by
    intro N j
    obtain ⟨u, n, N', h1, h2, h3, h4, h5, h6⟩ :=
      gliding_step R hR N (ε := ((1:ℝ)/2)^(j+2)) (by positivity)
    exact ⟨(u, n, N'), h1, h2, h3, h4, h5, h6⟩
  choose g hg1 hg2 hg3 hg4 hg5 hg6 using step
  set F : ℕ → H × ℕ × ℕ := fun j => Nat.rec (g 0 0) (fun i p => g p.2.2 (i+1)) j with hF
  set M : ℕ → ℕ := fun j => Nat.rec 0 (fun i _ => (F i).2.2) j with hM
  have hMs : ∀ j, M (j+1) = (F j).2.2 := fun j => rfl
  have hkey : ∀ j, F j = g (M j) j := by
    intro j; cases j <;> rfl
  refine ⟨fun j => (F j).1, fun j => (F j).2.1, M, fun j => ?_, fun j m hm => ?_,
    fun j => ?_, fun j => ?_, fun j => ?_, fun j y hy => ?_⟩
  · simpa only [hkey j] using hg1 (M j) j
  · simpa only [hkey j] using hg2 (M j) j m hm
  · simpa only [hkey j] using hg3 (M j) j
  · simpa only [hkey j] using hg4 (M j) j
  · rw [hMs j]
    simpa only [hkey j] using hg5 (M j) j
  · have h := hg6 (M j) j y (by intro m hm; exact hy m (by rw [hMs j, hkey j]; exact hm))
    simpa only [hkey j] using h

/-- A1 relativized: if the relative orthocomplement of `W ⊓ block S₀` in
    `block S₀` is infinite-dimensional, then some infinite `S ⊆ S₀` has
    `W ⊓ block S = ⊥`. This is the form in which the gliding-hump
    recursion is run; neither closedness of `W` nor infinitude of `S₀` is
    needed. -/
theorem gliding_hump_rel (W : Submodule ℝ H) (S₀ : Set ℕ)
    (hinf : ¬ Module.Finite ℝ ↥((W ⊓ block S₀)ᗮ ⊓ block S₀)) :
    ∃ S ⊆ S₀, S.Infinite ∧ W ⊓ block S = ⊥ := by
  classical
  obtain ⟨u, n, M, hR, hvan, hMn, hune, hnM, htail⟩ := gliding_sequence _ hinf
  have hMmono : StrictMono M := strictMono_nat_of_lt_succ (fun j => lt_trans (hMn j) (hnM j))
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ
    (fun j => lt_trans (hnM j) (hMn (j+1)))
  have hninj : Function.Injective n := hnmono.injective
  have hSsub : Set.range n ⊆ S₀ := by
    rintro m ⟨j, rfl⟩
    by_contra hm
    exact hune j ((mem_block_iff S₀ (u j)).mp (hR j).2 (n j) hm)
  refine ⟨Set.range n, hSsub, Set.infinite_range_of_injective hninj, ?_⟩
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxW, hxS⟩
  have hxS₀ : x ∈ block S₀ := block_mono hSsub hxS
  have hx0 : ∀ j, inner (𝕜 := ℝ) x (u j) = 0 := fun j =>
    (Submodule.mem_orthogonal _ _).mp (hR j).1 x ⟨hxW, hxS₀⟩
  have hxoff : ∀ m, m ∉ Set.range n → (x : ∀ _ : ℕ, ℝ) m = 0 :=
    (mem_block_iff _ x).mp hxS
  have hcoord : ∀ j, |(x : ∀ _ : ℕ, ℝ) (n j)| ≤ ((1:ℝ)/2)^(j+2) * ‖x‖ := by
    intro j
    have hMlt : M j < M (j+1) := hMmono (by omega)
    have hdecomp : restr {m | M j < m} x
        = ((x : ∀ _ : ℕ, ℝ) (n j)) • evec (n j) + restr {m | M (j+1) < m} x := by
      apply lp.ext
      funext m
      have hlhs : (restr {m | M j < m} x : ∀ _ : ℕ, ℝ) m
          = if M j < m then (x : ∀ _ : ℕ, ℝ) m else 0 := by
        by_cases h : M j < m
        · rw [if_pos h, restr_apply_of_mem (T := {m | M j < m}) x h]
        · rw [if_neg h, restr_apply_of_notMem (T := {m | M j < m}) x h]
      have hrhs : ((((x : ∀ _ : ℕ, ℝ) (n j)) • evec (n j) + restr {m | M (j+1) < m} x : H) :
            ∀ _ : ℕ, ℝ) m
          = (if m = n j then (x : ∀ _ : ℕ, ℝ) (n j) else 0)
            + (if M (j+1) < m then (x : ∀ _ : ℕ, ℝ) m else 0) := by
        have h1 : ((((x : ∀ _ : ℕ, ℝ) (n j)) • evec (n j) + restr {m | M (j+1) < m} x : H) :
              ∀ _ : ℕ, ℝ) m
            = ((x : ∀ _ : ℕ, ℝ) (n j)) * (evec (n j) : ∀ _ : ℕ, ℝ) m
              + (restr {m | M (j+1) < m} x : ∀ _ : ℕ, ℝ) m := rfl
        rw [h1, evec_apply]
        congr 1
        · by_cases h : m = n j <;> simp [h]
        · by_cases h : M (j+1) < m
          · rw [if_pos h, restr_apply_of_mem (T := {m | M (j+1) < m}) x h]
          · rw [if_neg h, restr_apply_of_notMem (T := {m | M (j+1) < m}) x h]
      rw [hlhs, hrhs]
      by_cases h3 : m = n j
      · subst h3
        rw [if_pos (hMn j), if_pos rfl, if_neg (by have := hnM j; omega)]
        ring
      · rw [if_neg h3]
        by_cases h2 : M (j+1) < m
        · rw [if_pos h2, if_pos (by omega)]
          ring
        · rw [if_neg h2]
          by_cases h1 : M j < m
          · rw [if_pos h1]
            have hxm : (x : ∀ _ : ℕ, ℝ) m = 0 := by
              by_contra hxm
              obtain ⟨i, hi⟩ : m ∈ Set.range n := by
                by_contra hmS
                exact hxm (hxoff m hmS)
              rcases lt_trichotomy i j with hij | hij | hij
              · have : n i < M j := lt_of_lt_of_le (hnM i) (hMmono.monotone (by omega))
                omega
              · exact h3 (by rw [← hi, hij])
              · have : M (j+1) < n i := lt_of_le_of_lt (hMmono.monotone (by omega)) (hMn i)
                omega
            rw [hxm]; ring
          · rw [if_neg h1]; ring
    have hvu : inner (𝕜 := ℝ) (restr {m | M j < m} x) (u j) = inner (𝕜 := ℝ) x (u j) := by
      have h := inner_eq_inner_restr (T := {m | M j < m}) (y := u j)
        (fun m hm => hvan j m (by simpa using hm)) x
      calc inner (𝕜 := ℝ) (restr {m | M j < m} x) (u j)
          = inner (𝕜 := ℝ) (u j) (restr {m | M j < m} x) := real_inner_comm _ _
        _ = inner (𝕜 := ℝ) (u j) x := h.symm
        _ = inner (𝕜 := ℝ) x (u j) := real_inner_comm _ _
    have hexpand : inner (𝕜 := ℝ) (restr {m | M j < m} x) (u j)
        = (x : ∀ _ : ℕ, ℝ) (n j) * (u j : ∀ _ : ℕ, ℝ) (n j)
          + inner (𝕜 := ℝ) (restr {m | M (j+1) < m} x) (u j) := by
      rw [hdecomp, inner_add_left, real_inner_smul_left, inner_evec_left]
    have hyb := htail j (restr {m | M (j+1) < m} x) (fun m hm =>
      restr_apply_of_notMem (T := {m | M (j+1) < m}) x (by simpa using hm))
    have hynorm : ‖restr {m | M (j+1) < m} x‖ ≤ ‖x‖ := norm_restr_le _ _
    have heq : (x : ∀ _ : ℕ, ℝ) (n j) * (u j : ∀ _ : ℕ, ℝ) (n j)
        = - inner (𝕜 := ℝ) (restr {m | M (j+1) < m} x) (u j) := by
      rw [hvu, hx0 j] at hexpand
      linarith
    have habs : |(x : ∀ _ : ℕ, ℝ) (n j)| * |(u j : ∀ _ : ℕ, ℝ) (n j)|
        ≤ (((1:ℝ)/2)^(j+2) * |(u j : ∀ _ : ℕ, ℝ) (n j)|) * ‖x‖ := by
      calc |(x : ∀ _ : ℕ, ℝ) (n j)| * |(u j : ∀ _ : ℕ, ℝ) (n j)|
          = |inner (𝕜 := ℝ) (restr {m | M (j+1) < m} x) (u j)| := by
            rw [← abs_mul, heq, abs_neg]
        _ ≤ (((1:ℝ)/2)^(j+2) * |(u j : ∀ _ : ℕ, ℝ) (n j)|)
              * ‖restr {m | M (j+1) < m} x‖ := hyb
        _ ≤ (((1:ℝ)/2)^(j+2) * |(u j : ∀ _ : ℕ, ℝ) (n j)|) * ‖x‖ :=
            mul_le_mul_of_nonneg_left hynorm (by positivity)
    have hpos : 0 < |(u j : ∀ _ : ℕ, ℝ) (n j)| := abs_pos.mpr (hune j)
    nlinarith [habs, hpos]
  have hsq : ∀ j, ((x : ∀ _ : ℕ, ℝ) (n j))^2 ≤ ((1:ℝ)/4)^(j+2) * ‖x‖^2 := by
    intro j
    have hpow : (((1:ℝ)/2)^(j+2) * ‖x‖)^2 = ((1:ℝ)/4)^(j+2) * ‖x‖^2 := by
      rw [mul_pow, ← pow_mul, mul_comm (j+2) 2, pow_mul]
      norm_num
    calc ((x : ∀ _ : ℕ, ℝ) (n j))^2 = |(x : ∀ _ : ℕ, ℝ) (n j)|^2 := (sq_abs _).symm
      _ ≤ (((1:ℝ)/2)^(j+2) * ‖x‖)^2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
      _ = ((1:ℝ)/4)^(j+2) * ‖x‖^2 := hpow
  have hsummable : Summable (fun j => ((x : ∀ _ : ℕ, ℝ) (n j))^2) := by
    have h := (summable_sq x).comp_injective hninj
    exact h
  have hsummable2 : Summable (fun j : ℕ => ((1:ℝ)/4)^(j+2) * ‖x‖^2) := by
    have hg : Summable (fun j : ℕ => ((1:ℝ)/4)^j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine ((hg.mul_left ((1:ℝ)/16)).mul_right (‖x‖^2)).congr (fun j => ?_)
    rw [pow_add]; ring
  have hreindex : ∑' j, ((x : ∀ _ : ℕ, ℝ) (n j))^2 = ∑' m, ((x : ∀ _ : ℕ, ℝ) m)^2 := by
    refine hninj.tsum_eq (f := fun m => ((x : ∀ _ : ℕ, ℝ) m)^2) (fun m hm => ?_)
    by_contra hmS
    exact hm (by show ((x : ∀ _ : ℕ, ℝ) m) ^ 2 = 0; rw [hxoff m hmS]; ring)
  have hgeom : ∑' j : ℕ, ((1:ℝ)/4)^(j+2) * ‖x‖^2 = (1/12) * ‖x‖^2 := by
    rw [tsum_mul_right]
    congr 1
    have hc : ∀ j : ℕ, ((1:ℝ)/4)^(j+2) = (1/16) * (1/4)^j := by
      intro j; rw [pow_add]; ring
    rw [tsum_congr hc, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hfinal : ‖x‖^2 ≤ (1/12) * ‖x‖^2 :=
    calc ‖x‖^2 = ∑' m, ((x : ∀ _ : ℕ, ℝ) m)^2 := norm_sq_eq_tsum x
      _ = ∑' j, ((x : ∀ _ : ℕ, ℝ) (n j))^2 := hreindex.symm
      _ ≤ ∑' j : ℕ, ((1:ℝ)/4)^(j+2) * ‖x‖^2 := hsummable.tsum_mono hsummable2 hsq
      _ = (1/12) * ‖x‖^2 := hgeom
  have hx : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hx

/-- A1 (Theorem 2.1; Galvin's question, completing a sketch of Gowers).
    A closed subspace of infinite codimension misses some infinite block
    entirely.

    Note: the proof is the relative recursion `gliding_hump_rel` at
    `S₀ = univ`; closedness of `W` is not consumed (the contract
    hypothesis `hW` is retained as stated). -/
theorem gliding_hump (W : Submodule ℝ H) (hW : IsClosed (W : Set H))
    (hcodim : ¬ Module.Finite ℝ ↥Wᗮ) :
    ∃ S : Set ℕ, S.Infinite ∧ W ⊓ block S = ⊥ := by
  have hrw : (W ⊓ block (univ : Set ℕ))ᗮ ⊓ block (univ : Set ℕ) = Wᗮ := by
    rw [block_univ, inf_top_eq, inf_top_eq]
  obtain ⟨S, -, hSinf, hbot⟩ := gliding_hump_rel W univ (by rw [hrw]; exact hcodim)
  exact ⟨S, hSinf, hbot⟩

/-- A2 (Corollary 2.2; the relativized dichotomy). Inside any infinite
    block, a closed subspace either has finite relative codimension or
    misses an infinite sub-block entirely.

    Transport route (reported): no isometry `block S₀ ≃ H` is built; the
    gliding-hump recursion of A1 is run directly inside `block S₀`
    (`gliding_hump_rel`), and the contract's quotient rendering of
    relative codimension is converted to the relative orthocomplement by
    `finCodimIn_iff_finite_orthocomplement`.

    Note: `hS₀` is retained as stated but not consumed. -/
theorem relativized_dichotomy (W : Submodule ℝ H) (hW : IsClosed (W : Set H))
    {S₀ : Set ℕ} (hS₀ : S₀.Infinite) :
    FinCodimIn W (block S₀) ∨
      ∃ S ⊆ S₀, S.Infinite ∧ W ⊓ block S = ⊥ := by
  by_cases hfin : Module.Finite ℝ ↥((W ⊓ block S₀)ᗮ ⊓ block S₀)
  · left
    rw [finCodimIn_iff_finite_orthocomplement W (block S₀)
      (isClosed_inf hW (isClosed_block S₀))]
    exact hfin
  · exact Or.inr (gliding_hump_rel W S₀ hfin)

/-- A3 (Proposition 4.2, second clause). If `W` has infinite relative
    codimension in every infinite block, then its zero-set is dense:
    every infinite set contains an infinite subset whose block misses
    `W`. Immediate from A2. -/
theorem dense_zero_set (W : Submodule ℝ H) (hW : IsClosed (W : Set H))
    (h : ∀ S : Set ℕ, S.Infinite → ¬ FinCodimIn W (block S))
    {S₀ : Set ℕ} (hS₀ : S₀.Infinite) :
    ∃ S ⊆ S₀, S.Infinite ∧ W ⊓ block S = ⊥ :=
  (relativized_dichotomy W hW hS₀).resolve_left (h S₀ hS₀)

end

end PlufWO5
