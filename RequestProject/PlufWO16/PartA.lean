/-
  PlufWO16/PartA.lean — Work Order 16, Part A: support families and unions
  (Paper V, Lemma 2.1, Proposition 2.2, Corollary 2.3, Proposition 3.2).

  The counting step (A1) is `exists_pos_lt_notMem`: a countable set of reals
  misses some point of every interval `(0, ε)`.

  A2 is the recursion with frozen minima. REPORT (recursion shape): the stage
  predicate `stepPred` below refers to the accumulated partial sums through
  `psum` and `freeze`, both of which are *functions of the coefficient
  history*; since the partial sum at stage `n` involves only the coefficients
  strictly below `n`, the whole constraint is a predicate of `n`, of the
  history below `n`, and of the new coefficient. It therefore fits
  `PlufWO14.exists_seq_of_step` exactly as it stands, with `α = ℝ`. What has
  to be arranged, and what the paper's phrasing hides, is that the stage
  predicate must be satisfiable for an *arbitrary* history; so the surviving
  clause of the recursion is only that the new coefficient does not kill a
  coordinate at which the new vector is nonzero (clause `nonvanishing`
  below), and the statement that all previously caught coordinates stay alive
  is then a separate induction (`psum_ne_zero`) over the chosen sequence.
-/
import RequestProject.PlufWO16.Basic

open Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PlufWO16

/-! ### The counting step -/

/-- A countable set of reals misses some point of every interval `(0, ε)`. -/
theorem exists_pos_lt_notMem {ε : ℝ} (hε : 0 < ε) {s : Set ℝ} (hs : s.Countable) :
    ∃ c : ℝ, 0 < c ∧ c < ε ∧ c ∉ s := by
  by_contra hcon
  push_neg at hcon
  have hsub : Set.Ioo (0 : ℝ) ε ⊆ s := fun c hc => hcon c hc.1 hc.2
  have hc : (Set.Ioo (0 : ℝ) ε).Countable := hs.mono hsub
  rw [Cardinal.Real.Ioo_countable_iff] at hc
  linarith

/-! ### A1 -/

/-- A1 (Paper V, Lemma 2.1). -/
theorem exists_supp_union (M : Submodule ℝ H) (x y : H) (hx : x ∈ M) (hy : y ∈ M) :
    ∃ z ∈ M, supp z = supp x ∪ supp y := by
  have hbad : (Set.range (fun n : ℕ =>
      -((x : ∀ _ : ℕ, ℝ) n) / ((y : ∀ _ : ℕ, ℝ) n))).Countable := countable_range _
  obtain ⟨c, hc0, -, hcbad⟩ := exists_pos_lt_notMem (ε := 1) one_pos hbad
  refine ⟨x + c • y, M.add_mem hx (M.smul_mem c hy), ?_⟩
  have hcoord : ∀ n : ℕ, ((x + c • y : H) : ∀ _ : ℕ, ℝ) n
      = (x : ∀ _ : ℕ, ℝ) n + c * (y : ∀ _ : ℕ, ℝ) n := by
    intro n
    simp [lp.coeFn_smul]
  ext n
  simp only [mem_supp_iff, mem_union, hcoord n]
  by_cases hyn : (y : ∀ _ : ℕ, ℝ) n = 0
  · simp [hyn]
  · constructor
    · intro _; exact Or.inr hyn
    · intro _ hzero
      apply hcbad
      refine ⟨n, ?_⟩
      field_simp
      linarith

/-! ### A2: the recursion with frozen minima -/

section Recursion

variable (y : ℕ → H)

/-- The `k`-th coordinate of the partial sum `∑_{i < n} u i • y i`. -/
def psum (u : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, u i * (y i : ∀ _ : ℕ, ℝ) k

/-- The frozen minimum at stage `m`: the least nonzero modulus among the
    coordinates `k ≤ m` of the partial sum `∑_{i ≤ m} u i • y i` (and `1` if
    there is none). -/
noncomputable def freeze (u : ℕ → ℝ) (m : ℕ) : ℝ :=
  (Finset.range (m + 1)).inf' (Finset.nonempty_range_add_one)
    (fun k => if psum y u (m + 1) k = 0 then 1 else |psum y u (m + 1) k|)

theorem freeze_pos (u : ℕ → ℝ) (m : ℕ) : 0 < freeze y u m := by
  rw [freeze, Finset.lt_inf'_iff]
  intro k _
  by_cases h : psum y u (m + 1) k = 0
  · simp [h]
  · simp only [h, if_false]
    exact abs_pos.mpr h

theorem freeze_le (u : ℕ → ℝ) {m k : ℕ} (hk : k ≤ m) (h : psum y u (m + 1) k ≠ 0) :
    freeze y u m ≤ |psum y u (m + 1) k| := by
  have hmem : k ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.inf'_le (f := fun k =>
    if psum y u (m + 1) k = 0 then 1 else |psum y u (m + 1) k|) hmem
  simpa [freeze, h] using this

/-- The stage predicate of the recursion. -/
def stepPred (n : ℕ) (u : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ c ≤ (1 / 2 : ℝ) ^ n ∧
    (∀ m, m < n → c ≤ (1 / 2 : ℝ) ^ (n - m + 1) * freeze y u m) ∧
    (∀ k, (y n : ∀ _ : ℕ, ℝ) k ≠ 0 → psum y u n k + c * (y n : ∀ _ : ℕ, ℝ) k ≠ 0)

theorem psum_congr {u v : ℕ → ℝ} {n : ℕ} (h : ∀ j, j < n → u j = v j) (k : ℕ) :
    psum y u n k = psum y v n k := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_range.mp hi)]

theorem freeze_congr {u v : ℕ → ℝ} {n m : ℕ} (h : ∀ j, j < n → u j = v j) (hm : m < n) :
    freeze y u m = freeze y v m := by
  have hps : ∀ k, psum y u (m + 1) k = psum y v (m + 1) k := fun k =>
    psum_congr y (fun j hj => h j (by omega)) k
  simp only [freeze, hps]

theorem stepPred_dep (n : ℕ) (u v : ℕ → ℝ) (c : ℝ) (h : ∀ j, j < n → u j = v j)
    (hP : stepPred y n u c) : stepPred y n v c := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨h1, h2, fun m hm => ?_, fun k hk => ?_⟩
  · rw [← freeze_congr y h hm]; exact h3 m hm
  · rw [← psum_congr y h k]; exact h4 k hk

theorem exists_step (n : ℕ) (u : ℕ → ℝ) : ∃ c, stepPred y n u c := by
  classical
  set g : ℕ → ℝ := fun m =>
    if m < n then (1 / 2 : ℝ) ^ (n - m + 1) * freeze y u m else (1 / 2 : ℝ) ^ n with hg
  set ε : ℝ := (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one g with hε
  have hεpos : 0 < ε := by
    rw [hε, Finset.lt_inf'_iff]
    intro m _
    by_cases hm : m < n
    · simp only [hg, if_pos hm]
      have := freeze_pos y u m
      positivity
    · simp only [hg, if_neg hm]
      positivity
  have hεn : ε ≤ (1 / 2 : ℝ) ^ n := by
    have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h := Finset.inf'_le (s := Finset.range (n + 1)) g hmem
    have hgn : g n = (1 / 2 : ℝ) ^ n := by simp only [hg, if_neg (lt_irrefl n)]
    rw [hε, ← hgn]
    exact h
  have hεm : ∀ m, m < n → ε ≤ (1 / 2 : ℝ) ^ (n - m + 1) * freeze y u m := by
    intro m hm
    have hmem : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h := Finset.inf'_le (s := Finset.range (n + 1)) g hmem
    have hgm : g m = (1 / 2 : ℝ) ^ (n - m + 1) * freeze y u m := by
      simp only [hg, if_pos hm]
    rw [hε, ← hgm]
    exact h
  have hbad : (Set.range (fun k : ℕ =>
      -(psum y u n k) / (y n : ∀ _ : ℕ, ℝ) k)).Countable := countable_range _
  obtain ⟨c, hc0, hcε, hcbad⟩ := exists_pos_lt_notMem hεpos hbad
  refine ⟨c, hc0, le_trans hcε.le hεn, fun m hm => le_trans hcε.le (hεm m hm), ?_⟩
  intro k hk hzero
  apply hcbad
  refine ⟨k, ?_⟩
  field_simp
  linarith

theorem exists_coeffs : ∃ c : ℕ → ℝ, ∀ n, stepPred y n c (c n) :=
  PlufWO14.exists_seq_of_step (stepPred y) (stepPred_dep y) (exists_step y)

/-- Under the recursion, every coordinate caught by one of the first `n + 1`
    vectors is alive in the partial sum `∑_{i ≤ n} c i • y i`. -/
theorem psum_ne_zero {c : ℕ → ℝ} (hc : ∀ n, stepPred y n c (c n)) (n k : ℕ)
    (h : ∃ i ≤ n, (y i : ∀ _ : ℕ, ℝ) k ≠ 0) : psum y c (n + 1) k ≠ 0 := by
  induction n with
  | zero =>
      obtain ⟨i, hi, hik⟩ := h
      have hi0 : i = 0 := by omega
      subst hi0
      have := (hc 0).2.2.2 k hik
      simpa [psum, Finset.sum_range_succ] using this
  | succ n ih =>
      have hsplit : psum y c (n + 2) k
          = psum y c (n + 1) k + c (n + 1) * (y (n + 1) : ∀ _ : ℕ, ℝ) k := by
        simp [psum, Finset.sum_range_succ]
      obtain ⟨i, hi, hik⟩ := h
      by_cases hlast : (y (n + 1) : ∀ _ : ℕ, ℝ) k ≠ 0
      · rw [hsplit]
        exact (hc (n + 1)).2.2.2 k hlast
      · push_neg at hlast
        have hi' : i ≤ n := by
          rcases Nat.lt_or_ge i (n + 1) with h' | h'
          · omega
          · exfalso
            have : i = n + 1 := by omega
            exact hik (this ▸ hlast)
        rw [hsplit, hlast, mul_zero, add_zero]
        exact ih ⟨i, hi', hik⟩

end Recursion

/-- A2, for a normalized sequence. -/
theorem exists_supp_iUnion_of_norm_le (M : Submodule ℝ H) (hM : IsClosed (M : Set H))
    (y : ℕ → H) (hy : ∀ i, y i ∈ M) (hnorm : ∀ i, ‖y i‖ ≤ 1) :
    ∃ z ∈ M, supp z = ⋃ i, supp (y i) := by
  classical
  obtain ⟨c, hc⟩ := exists_coeffs y
  have hcpos : ∀ i, 0 < c i := fun i => (hc i).1
  have hcle : ∀ i, c i ≤ (1 / 2 : ℝ) ^ i := fun i => (hc i).2.1
  have hcoordle : ∀ i k, |(y i : ∀ _ : ℕ, ℝ) k| ≤ 1 := by
    intro i k
    have h1 : ‖(y i : ∀ _ : ℕ, ℝ) k‖ ≤ ‖y i‖ :=
      lp.norm_apply_le_norm (p := 2) (by norm_num) (y i) k
    have := hnorm i
    rw [Real.norm_eq_abs] at h1
    linarith
  -- the series
  have hnormterm : ∀ i, ‖c i • y i‖ ≤ (1 / 2 : ℝ) ^ i := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos i)]
    calc c i * ‖y i‖ ≤ c i * 1 := by nlinarith [hnorm i, (hcpos i).le, norm_nonneg (y i)]
      _ = c i := by ring
      _ ≤ (1 / 2 : ℝ) ^ i := hcle i
  have hgeom : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsummable : Summable (fun i => c i • y i) := by
    refine Summable.of_norm ?_
    exact hgeom.of_nonneg_of_le (fun i => norm_nonneg _) hnormterm
  set z : H := ∑' i, c i • y i with hz
  have hzM : z ∈ M := by
    refine hM.mem_of_tendsto hsummable.hasSum ?_
    filter_upwards with s
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hy i)
  -- coordinates of the sum
  have hcoordsum : ∀ k : ℕ,
      HasSum (fun i => c i * (y i : ∀ _ : ℕ, ℝ) k) ((z : ∀ _ : ℕ, ℝ) k) := by
    intro k
    have := (PlufWO1.coordCLM k).hasSum hsummable.hasSum
    simpa [PlufWO1.coordCLM_apply, lp.coeFn_smul] using this
  refine ⟨z, hzM, ?_⟩
  ext k
  simp only [mem_supp_iff, mem_iUnion]
  constructor
  · intro hzk
    by_contra hno
    push_neg at hno
    have hzero : ∀ i, c i * (y i : ∀ _ : ℕ, ℝ) k = 0 := by
      intro i
      rw [hno i, mul_zero]
    exact hzk ((hcoordsum k).unique (by simp [hzero]))
  · rintro ⟨m, hm⟩
    -- freeze at stage `N = max m k`
    set N := max m k with hN
    have hps : psum y c (N + 1) k ≠ 0 := psum_ne_zero y hc N k ⟨m, le_max_left _ _, hm⟩
    have hfr : freeze y c N ≤ |psum y c (N + 1) k| :=
      freeze_le y c (le_max_right m k) hps
    -- the tail is at most half the frozen value
    have hsumk : Summable (fun i => c i * (y i : ∀ _ : ℕ, ℝ) k) := (hcoordsum k).summable
    have hsplit := (hsumk.sum_add_tsum_nat_add (N + 1))
    have hzeq : (z : ∀ _ : ℕ, ℝ) k = psum y c (N + 1) k
        + ∑' j : ℕ, c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k := by
      rw [← (hcoordsum k).tsum_eq, ← hsplit]
      rfl
    have htailbound : ∀ j : ℕ,
        |c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k|
          ≤ (1 / 2 : ℝ) ^ (j + 2) * freeze y c N := by
      intro j
      have h1 : c (j + (N + 1)) ≤ (1 / 2 : ℝ) ^ ((j + (N + 1)) - N + 1) * freeze y c N :=
        (hc (j + (N + 1))).2.2.1 N (by omega)
      have h2 : (j + (N + 1)) - N + 1 = j + 2 := by omega
      rw [h2] at h1
      rw [abs_mul, abs_of_pos (hcpos _)]
      calc c (j + (N + 1)) * |(y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k|
          ≤ c (j + (N + 1)) * 1 := by
            have := hcoordle (j + (N + 1)) k
            nlinarith [(hcpos (j + (N + 1))).le, abs_nonneg ((y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k)]
        _ = c (j + (N + 1)) := by ring
        _ ≤ (1 / 2 : ℝ) ^ (j + 2) * freeze y c N := h1
    have hgeom2 : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 2) * freeze y c N) := by
      refine Summable.congr (hgeom.mul_right ((1 / 2 : ℝ) ^ 2 * freeze y c N)) fun j => ?_
      rw [pow_add]; ring
    have htailsum : Summable (fun j : ℕ => c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k) :=
      (summable_nat_add_iff (f := fun i => c i * (y i : ∀ _ : ℕ, ℝ) k) (N + 1)).mpr hsumk
    have habssum : Summable (fun j : ℕ => ‖c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k‖) := by
      simpa only [Real.norm_eq_abs] using htailsum.abs
    have habs : |∑' j : ℕ, c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k|
        ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 2) * freeze y c N := by
      have h1 := norm_tsum_le_tsum_norm habssum
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 ?_
      have h2 : ∑' j : ℕ, ‖c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k‖
          = ∑' j : ℕ, |c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k| := by
        simp only [Real.norm_eq_abs]
      rw [h2]
      exact htailsum.abs.tsum_le_tsum htailbound hgeom2
    have hgeomval : ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 2) * freeze y c N
        = freeze y c N / 2 := by
      have h0 : ∑' j : ℕ, (1 / 2 : ℝ) ^ j = 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
      calc ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 2) * freeze y c N
          = ∑' j : ℕ, ((1 / 2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ 2 * freeze y c N)) := by
            refine tsum_congr fun j => ?_
            rw [pow_add]; ring
        _ = (∑' j : ℕ, (1 / 2 : ℝ) ^ j) * ((1 / 2 : ℝ) ^ 2 * freeze y c N) :=
            tsum_mul_right
        _ = freeze y c N / 2 := by rw [h0]; ring
    rw [hgeomval] at habs
    have hfrpos := freeze_pos y c N
    intro hzk
    rw [hzeq] at hzk
    have : |psum y c (N + 1) k| ≤ freeze y c N / 2 := by
      have heq : psum y c (N + 1) k
          = -(∑' j : ℕ, c (j + (N + 1)) * (y (j + (N + 1)) : ∀ _ : ℕ, ℝ) k) := by
        linarith [hzk]
      rw [heq, abs_neg]
      exact habs
    linarith

/-- A2 (Paper V, Proposition 2.2). -/
theorem exists_supp_iUnion (M : Submodule ℝ H) (hM : IsClosed (M : Set H))
    (x : ℕ → H) (hx : ∀ i, x i ∈ M) :
    ∃ z ∈ M, supp z = ⋃ i, supp (x i) := by
  classical
  set b : ℕ → ℝ := fun i => if ‖x i‖ = 0 then 1 else ‖x i‖⁻¹ with hb
  have hbpos : ∀ i, 0 < b i := by
    intro i
    by_cases h : ‖x i‖ = 0 <;> simp only [hb, h, if_true, if_false]
    · norm_num
    · exact inv_pos.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
  set y : ℕ → H := fun i => b i • x i with hy
  have hyM : ∀ i, y i ∈ M := fun i => M.smul_mem _ (hx i)
  have hynorm : ∀ i, ‖y i‖ ≤ 1 := by
    intro i
    rw [hy]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (hbpos i)]
    by_cases h : ‖x i‖ = 0
    · simp [hb, h]
    · rw [hb]
      simp only [h, if_false]
      rw [inv_mul_cancel₀ h]
  have hsupp : ∀ i, supp (y i) = supp (x i) := by
    intro i
    ext k
    simp only [mem_supp_iff, hy, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ne_eq,
      mul_eq_zero, not_or]
    constructor
    · rintro h; exact h.2
    · intro h; exact ⟨(hbpos i).ne', h⟩
  obtain ⟨z, hzM, hz⟩ := exists_supp_iUnion_of_norm_le M hM y hyM hynorm
  refine ⟨z, hzM, ?_⟩
  rw [hz]
  exact iUnion_congr hsupp

/-! ### A3 -/

/-- A3 (Paper V, Corollary 2.3). -/
theorem exists_supp_sUnion (M : Submodule ℝ H) (hM : IsClosed (M : Set H))
    (F : Set H) (hF : ∀ x ∈ F, x ∈ M) :
    ∃ z ∈ M, supp z = ⋃ x ∈ F, supp x := by
  classical
  set T : Set ℕ := ⋃ x ∈ F, supp x with hT
  have hchoice : ∀ n : ℕ, ∃ v : H, v ∈ M ∧ supp v ⊆ T ∧ (n ∈ T → n ∈ supp v) := by
    intro n
    by_cases hn : n ∈ T
    · rw [hT] at hn
      simp only [mem_iUnion, exists_prop] at hn
      obtain ⟨v, hvF, hvn⟩ := hn
      refine ⟨v, hF v hvF, ?_, fun _ => hvn⟩
      intro k hk
      rw [hT]
      simp only [mem_iUnion, exists_prop]
      exact ⟨v, hvF, hk⟩
    · exact ⟨0, M.zero_mem, by simp, fun h => absurd h hn⟩
  choose g hgM hgT hgn using hchoice
  obtain ⟨z, hzM, hz⟩ := exists_supp_iUnion M hM g hgM
  refine ⟨z, hzM, ?_⟩
  rw [hz]
  apply Subset.antisymm
  · exact iUnion_subset hgT
  · intro n hn
    exact mem_iUnion.mpr ⟨n, hgn n hn⟩

/-! ### A4 -/

/-- A4 (Paper V, Proposition 3.2; elimination).

    REPORT: the minimality hypotheses `hminx` and `hminy` of the contract are
    not needed — the eliminated vector is nonzero as soon as `supp x ≠ supp y`,
    since vanishing would make `x` and `y` proportional. They are retained
    verbatim, as contracted. -/
theorem exists_supp_elimination (M : Submodule ℝ H) (x y : H)
    (hx : x ∈ M) (hy : y ∈ M)
    (hminx : ∀ z ∈ M, supp z ≠ ∅ → supp z ⊆ supp x → supp z = supp x)
    (hminy : ∀ z ∈ M, supp z ≠ ∅ → supp z ⊆ supp y → supp z = supp y)
    (hne : supp x ≠ supp y) {p : ℕ} (hp : p ∈ supp x ∩ supp y) :
    ∃ z ∈ M, z ≠ 0 ∧ supp z ⊆ (supp x ∪ supp y) \ {p} := by
  obtain ⟨hpx, hpy⟩ := hp
  set a : ℝ := (y : ∀ _ : ℕ, ℝ) p with ha
  set b : ℝ := (x : ∀ _ : ℕ, ℝ) p with hbdef
  have ha0 : a ≠ 0 := hpy
  have hb0 : b ≠ 0 := hpx
  refine ⟨a • x - b • y, M.sub_mem (M.smul_mem _ hx) (M.smul_mem _ hy), ?_, ?_⟩
  · -- nonzero: otherwise `x` and `y` are proportional
    intro h0
    apply hne
    have hxy : a • x = b • y := by
      have := sub_eq_zero.mp h0
      exact this
    have hyx : y = (b⁻¹ * a) • x := by
      rw [mul_smul, hxy, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    have hab : b⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hb0) ha0
    ext k
    simp only [mem_supp_iff, hyx, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ne_eq,
      mul_eq_zero, not_or]
    exact ⟨fun h => ⟨⟨inv_ne_zero hb0, ha0⟩, h⟩, fun h => h.2⟩
  · intro k hk
    have hcoord : ((a • x - b • y : H) : ∀ _ : ℕ, ℝ) k
        = a * (x : ∀ _ : ℕ, ℝ) k - b * (y : ∀ _ : ℕ, ℝ) k := by
      simp [lp.coeFn_smul]
    simp only [mem_supp_iff, hcoord] at hk
    refine ⟨?_, ?_⟩
    · by_contra hno
      simp only [mem_union, mem_supp_iff, not_or, not_not] at hno
      rw [hno.1, hno.2] at hk
      simp at hk
    · simp only [mem_singleton_iff]
      rintro rfl
      exact hk (by rw [ha, hbdef]; ring)

end PlufWO16
