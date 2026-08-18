/-
  PlufWO16/PartC.lean — Work Order 16, Part C: the transfers to the series
  (Paper V, Section 8).

  C1 intimacy is the covering condition at level three;
  C2 the collapse on plufs with ultrafilter trace;
  C3 the three-way equivalence for nonprincipal plufs;
  C4a the general pair-sum recursion of Gowers's subspace, C4b its
      independent sets, and C4 the covering number three;
  C5 addable blockers are diagonally consistent.
-/
import RequestProject.PlufWO16.PartB

open Set

namespace PlufWO16

/-! ### C1: intimacy as the level-three covering condition -/

/-- C1 (Paper V, Proposition 8.1). -/
theorem intimate_iff_no_two_cover (M : Submodule ℝ H) :
    PlufWO5.Intimate M ↔ ¬ ∃ S T : Set ℕ, S ∈ cI M ∧ T ∈ cI M ∧ S ∪ T = univ := by
  constructor
  · rintro hint ⟨S, T, hS, hT, hcov⟩
    have hcompl : Sᶜ ∈ cI M := by
      refine cI_downward M hT ?_
      intro n hn
      rcases (Set.eq_univ_iff_forall.mp hcov) n with h | h
      · exact absurd h hn
      · exact h
    rcases hint S with h | h
    · exact h hS
    · exact h hcompl
  · intro hno S
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact hno ⟨S, Sᶜ, h1, h2, union_compl_self S⟩

/-! ### C2 and C3: the collapse on plufs -/

/-- C2 (Paper V, Proposition 8.2). -/
theorem diagonallyConsistent_of_mem_diagonalizable
    (π : Set (Submodule ℝ H)) (hπ : PlufWO6.IsPluf π)
    (U : Ultrafilter ℕ) (hU : ∀ S : Set ℕ, S ∈ U ↔ PlufWO1.block S ∈ π)
    (M : Submodule ℝ H) (hM : M ∈ π) :
    DiagonallyConsistent M :=
  ⟨U, fun S hS => trace_subset π hπ ((hU S).1 hS) M hM⟩

/-- A diagonally consistent subspace is intimate. -/
theorem intimate_of_diagonallyConsistent {M : Submodule ℝ H}
    (h : DiagonallyConsistent M) : PlufWO5.Intimate M := by
  obtain ⟨U, hU⟩ := h
  intro A
  rcases U.mem_or_compl_mem A with hA | hA
  · exact Or.inl (hU A hA)
  · exact Or.inr (hU Aᶜ hA)

/-- C3 (Paper V, Corollary 8.3). -/
theorem diagonalizable_iff_all_diagonallyConsistent
    (π : Set (Submodule ℝ H)) (hπ : PlufWO6.IsPluf π)
    (hnp : ∀ v : H, v ≠ 0 → ∃ N ∈ π, v ∉ N) :
    (∃ U : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ U ↔ PlufWO1.block S ∈ π) ↔
      (∀ M ∈ π, DiagonallyConsistent M) := by
  constructor
  · rintro ⟨U, hU⟩ M hM
    exact diagonallyConsistent_of_mem_diagonalizable π hπ U hU M hM
  · intro hall
    refine (PlufWO6.diagonalizable_iff_intimate_pluf π hπ hnp).2 ?_
    exact fun M hM => intimate_of_diagonallyConsistent (hall M hM)

/-! ### C4: Gowers's subspace

REPORT (indexing). The development is 0-indexed: `PlufWO5.gowersX` is cut out
by the constraint vectors `PlufWO5.gowersV n`, whose pairs are
`pair k = {2k, 2k+1}` for `k ≥ 0`; the paper's pairs `P_i = {2i-1, 2i}`,
`i ≥ 1`, correspond under `i = k + 1`. Every statement below is in the
0-indexed convention. -/

/-- C4a (the membership recursion, general form; the statement is supplied
    here, the contract leaving it open). For every vector of `gowersX` the
    sequence of pair sums satisfies `s k = ((k+2)/(k+1)) * s (k+1)`; and the
    recursion characterizes membership. -/
theorem gowersX_pairSum_rec {x : H} (hx : x ∈ PlufWO5.gowersX) (k : ℕ) :
    pairSum x k = (((k : ℝ) + 2) / ((k : ℝ) + 1)) * pairSum x (k + 1) := by
  have h := (PlufWO5.mem_gowersX_iff x).1 hx k
  simpa [pairSum, show 2 * (k + 1) = 2 * k + 2 by ring,
    show 2 * (k + 1) + 1 = 2 * k + 3 by ring] using h

/-- C4a, the converse half: the recursion is exactly membership. -/
theorem mem_gowersX_iff_pairSum_rec (x : H) :
    x ∈ PlufWO5.gowersX ↔
      ∀ k : ℕ, pairSum x k = (((k : ℝ) + 2) / ((k : ℝ) + 1)) * pairSum x (k + 1) := by
  rw [PlufWO5.mem_gowersX_iff]
  refine forall_congr' fun k => ?_
  simp [pairSum, show 2 * (k + 1) = 2 * k + 2 by ring]

/-- All pair sums of a member of `gowersX` vanish as soon as one of them does. -/
theorem gowersX_pairSum_eq_zero_of_eq_zero {x : H} (hx : x ∈ PlufWO5.gowersX)
    {j : ℕ} (hj : pairSum x j = 0) (k : ℕ) : pairSum x k = 0 := by
  -- forwards from `j`
  have hup : ∀ i, j ≤ i → pairSum x i = 0 := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    clear hi
    induction d with
    | zero => simpa using hj
    | succ d ih =>
        have hrec := gowersX_pairSum_rec hx (j + d)
        have hc : (((j + d : ℕ) : ℝ) + 2) / (((j + d : ℕ) : ℝ) + 1) ≠ 0 := by
          have h1 : (0 : ℝ) < ((j + d : ℕ) : ℝ) + 2 := by positivity
          have h2 : (0 : ℝ) < ((j + d : ℕ) : ℝ) + 1 := by positivity
          positivity
        have : (((j + d : ℕ) : ℝ) + 2) / (((j + d : ℕ) : ℝ) + 1) * pairSum x (j + d + 1) = 0 := by
          rw [← hrec]; exact ih
        exact (mul_eq_zero.mp this).resolve_left hc
  -- backwards below `j`
  have hdown : ∀ d, pairSum x (j - d) = 0 := by
    intro d
    induction d with
    | zero => simpa using hj
    | succ d ih =>
        by_cases hjd : j ≤ d
        · have h0 : j - (d + 1) = 0 := by omega
          have h1 : j - d = 0 := by omega
          rw [h0, ← h1]; exact ih
        · have hsucc : (j - (d + 1)) + 1 = j - d := by omega
          have hrec := gowersX_pairSum_rec hx (j - (d + 1))
          rw [hsucc, ih] at hrec
          simpa using hrec
  by_cases hk : j ≤ k
  · exact hup k hk
  · have := hdown (j - k)
    rwa [show j - (j - k) = k by omega] at this

/-- The transversal witness of `PlufWO5.transversalVec` lies in `gowersX`
    whenever `a k` is a point of the `k`-th pair. -/
theorem transversalVec_mem_gowersX {a : ℕ → ℕ} (ha : ∀ k, a k = 2 * k ∨ a k = 2 * k + 1) :
    PlufWO5.transversalVec a ∈ PlufWO5.gowersX := by
  have hcoord : ∀ n : ℕ, pairSum (PlufWO5.transversalVec a) n = 1 / ((n : ℝ) + 1) := by
    intro n
    rw [pairSum, PlufWO5.transversalVec_apply, PlufWO5.transversalVec_apply]
    rw [show (2 * n) / 2 = n by omega, show (2 * n + 1) / 2 = n by omega]
    rcases ha n with h | h
    · rw [if_pos h, if_neg (by omega : ¬ (a n = 2 * n + 1))]
      push_cast; ring
    · rw [if_neg (by omega : ¬ (a n = 2 * n)), if_pos h]
      push_cast; ring
  rw [mem_gowersX_iff_pairSum_rec]
  intro k
  rw [hcoord k, hcoord (k + 1)]
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem transversalVec_ne_zero {a : ℕ → ℕ} (ha : ∀ k, a k = 2 * k ∨ a k = 2 * k + 1) :
    PlufWO5.transversalVec a ≠ 0 := by
  intro h0
  have hcoord : pairSum (PlufWO5.transversalVec a) 0 = 1 := by
    rw [pairSum, PlufWO5.transversalVec_apply, PlufWO5.transversalVec_apply]
    rcases ha 0 with h | h <;> simp [h]
  rw [h0] at hcoord
  simp [pairSum] at hcoord

/-- C4b (Paper V, Theorem 8.4, the identification of `I(X)`). -/
theorem mem_cI_gowersX_iff (S : Set ℕ) :
    S ∈ cI PlufWO5.gowersX ↔
      (∀ k, ¬ pair k ⊆ S) ∧ (∃ j, Disjoint (pair j) S) := by
  classical
  constructor
  · intro hS
    rw [mem_cI_iff_notMem_cD, mem_cD_iff] at hS
    push_neg at hS
    constructor
    · intro k hk
      refine hS (PlufWO1.evec (2 * k) - PlufWO1.evec (2 * k + 1))
        (PlufWO5.pairDiff_mem_gowersX k) (PlufWO5.pairDiff_ne_zero k) ?_
      refine (mem_block_iff_supp_subset S _).1 ?_
      exact PlufWO5.pairDiff_mem_block (hk (by simp [pair])) (hk (by simp [pair]))
    · by_contra hno
      push_neg at hno
      -- `S` meets every pair; build the transversal witness
      have hchoice : ∀ k, ∃ m, m ∈ pair k ∧ m ∈ S := by
        intro k
        have := hno k
        rw [Set.not_disjoint_iff] at this
        exact this
      choose a ha haS using hchoice
      have hacases : ∀ k, a k = 2 * k ∨ a k = 2 * k + 1 := fun k => ha k
      refine hS (PlufWO5.transversalVec a) (transversalVec_mem_gowersX hacases)
        (transversalVec_ne_zero hacases) ?_
      intro m hm
      by_cases hma : a (m / 2) = m
      · exact hma ▸ haS (m / 2)
      · exfalso
        apply hm
        show (PlufWO5.transversalVec a : ∀ _ : ℕ, ℝ) m = 0
        rw [PlufWO5.transversalVec_apply, if_neg hma]
  · rintro ⟨hnopair, j, hj⟩
    rw [mem_cI_iff_notMem_cD, mem_cD_iff]
    push_neg
    intro x hx hx0 hxS
    apply hx0
    -- the pair sum at `j` vanishes, hence all pair sums vanish
    have hzeroj : pairSum x j = 0 := by
      have h1 : (x : ∀ _ : ℕ, ℝ) (2 * j) = 0 := by
        by_contra hne
        exact (Set.disjoint_left.mp hj (by simp [pair] : 2 * j ∈ pair j)) (hxS hne)
      have h2 : (x : ∀ _ : ℕ, ℝ) (2 * j + 1) = 0 := by
        by_contra hne
        exact (Set.disjoint_left.mp hj (by simp [pair] : 2 * j + 1 ∈ pair j)) (hxS hne)
      rw [pairSum, h1, h2]; ring
    have hall : ∀ k, pairSum x k = 0 := gowersX_pairSum_eq_zero_of_eq_zero hx hzeroj
    refine lp.ext (funext fun m => ?_)
    have hkey : ∀ k, (x : ∀ _ : ℕ, ℝ) (2 * k) = 0 ∧ (x : ∀ _ : ℕ, ℝ) (2 * k + 1) = 0 := by
      intro k
      have hsum := hall k
      rw [pairSum] at hsum
      have hnot : 2 * k ∉ S ∨ 2 * k + 1 ∉ S := by
        by_contra hcon
        push_neg at hcon
        exact hnopair k (by
          intro n hn
          rcases hn with h | h
          · exact h ▸ hcon.1
          · simp only [mem_singleton_iff] at h
            exact h ▸ hcon.2)
      rcases hnot with h | h
      · have hz : (x : ∀ _ : ℕ, ℝ) (2 * k) = 0 := by
          by_contra hne; exact h (hxS hne)
        exact ⟨hz, by linarith⟩
      · have hz : (x : ∀ _ : ℕ, ℝ) (2 * k + 1) = 0 := by
          by_contra hne; exact h (hxS hne)
        exact ⟨by linarith, hz⟩
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : m = 2 * k := by omega
      rw [this]; exact (hkey k).1
    · have : m = 2 * k + 1 := by omega
      rw [this]; exact (hkey k).2

/-! #### The three-cover -/

/-- The first class: `{0, 5} ∪ {even numbers ≥ 6}`. -/
def coverS : Set ℕ := {n | n = 0 ∨ n = 5 ∨ (6 ≤ n ∧ n % 2 = 0)}

/-- The second class: `{1, 2} ∪ {odd numbers ≥ 6}`. -/
def coverT : Set ℕ := {n | n = 1 ∨ n = 2 ∨ (6 ≤ n ∧ n % 2 = 1)}

/-- The third class: `{3, 4}`. -/
def coverV : Set ℕ := {n | n = 3 ∨ n = 4}

theorem coverS_mem_cI : coverS ∈ cI PlufWO5.gowersX := by
  rw [mem_cI_gowersX_iff]
  constructor
  · intro k hk
    have h1 : (2 * k) ∈ coverS := hk (by simp [pair])
    have h2 : (2 * k + 1) ∈ coverS := hk (by simp [pair])
    simp only [coverS, mem_setOf_eq] at h1 h2
    omega
  · refine ⟨1, ?_⟩
    rw [Set.disjoint_left]
    intro n hn
    simp only [pair, mem_insert_iff, mem_singleton_iff] at hn
    simp only [coverS, mem_setOf_eq]
    omega

theorem coverT_mem_cI : coverT ∈ cI PlufWO5.gowersX := by
  rw [mem_cI_gowersX_iff]
  constructor
  · intro k hk
    have h1 : (2 * k) ∈ coverT := hk (by simp [pair])
    have h2 : (2 * k + 1) ∈ coverT := hk (by simp [pair])
    simp only [coverT, mem_setOf_eq] at h1 h2
    omega
  · refine ⟨2, ?_⟩
    rw [Set.disjoint_left]
    intro n hn
    simp only [pair, mem_insert_iff, mem_singleton_iff] at hn
    simp only [coverT, mem_setOf_eq]
    omega

theorem coverV_mem_cI : coverV ∈ cI PlufWO5.gowersX := by
  rw [mem_cI_gowersX_iff]
  constructor
  · intro k hk
    have h1 : (2 * k) ∈ coverV := hk (by simp [pair])
    have h2 : (2 * k + 1) ∈ coverV := hk (by simp [pair])
    simp only [coverV, mem_setOf_eq] at h1 h2
    omega
  · refine ⟨0, ?_⟩
    rw [Set.disjoint_left]
    intro n hn
    simp only [pair, mem_insert_iff, mem_singleton_iff] at hn
    simp only [coverV, mem_setOf_eq]
    omega

theorem cover_union : coverS ∪ coverT ∪ coverV = univ := by
  ext n
  simp only [mem_union, coverS, coverT, coverV, mem_setOf_eq, mem_univ, iff_true]
  omega

/-- C4 (Paper V, Theorem 8.4). -/
theorem gowersX_threeCover :
    (∃ S T V : Set ℕ, S ∈ cI PlufWO5.gowersX ∧ T ∈ cI PlufWO5.gowersX ∧
      V ∈ cI PlufWO5.gowersX ∧ S ∪ T ∪ V = univ) ∧
    ¬ DiagonallyConsistent PlufWO5.gowersX := by
  classical
  refine ⟨⟨coverS, coverT, coverV, coverS_mem_cI, coverT_mem_cI, coverV_mem_cI, cover_union⟩, ?_⟩
  rw [diagonallyConsistent_iff_not_finiteCover, not_not]
  refine ⟨{coverS, coverT, coverV}, ?_, ?_⟩
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · exact coverS_mem_cI
    · exact coverT_mem_cI
    · exact coverV_mem_cI
  · rw [← cover_union]
    ext n
    simp only [mem_iUnion, Finset.mem_insert, Finset.mem_singleton, exists_prop, mem_union]
    constructor
    · rintro ⟨S, (rfl | rfl | rfl), hn⟩ <;> tauto
    · rintro ((h | h) | h)
      · exact ⟨coverS, by tauto, h⟩
      · exact ⟨coverT, by tauto, h⟩
      · exact ⟨coverV, by tauto, h⟩

/-! ### C5: addable blockers -/

/-- C5 (Paper V, Proposition 8.5). -/
theorem diagonallyConsistent_of_addableBlocker (U : Ultrafilter ℕ)
    (R : Submodule ℝ H)
    (hR : ∀ S ∈ U, ¬ Module.Finite ℝ ↥(R ⊓ PlufWO1.block S)) :
    DiagonallyConsistent R := by
  refine ⟨U, fun S hS => ?_⟩
  intro hbot
  refine hR S hS ?_
  rw [hbot]
  infer_instance

end PlufWO16
