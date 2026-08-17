/-
  PlufWO6/PartF.lean — Work Order 6, Part F: Kadison–Singer, quarantined
  (Paper I, Theorem 4.1 and Remark 4.2).

  F1 is proved from the quarantined paving hypothesis `KSHyp`. F2 is not
  returned in its contracted shape, and is discussed in `REPORT-WO6.md`:
  the round-slice property of a pluf produces *some* member with small
  Rayleigh oscillation, and nothing in the hypothesis identifies that
  member with a block of the ultrafilter, so the printed "unwinding" does
  not give the paving statement; F2 is a theorem (it is
  Marcus–Spielman–Srivastava), but not one derivable from the contracted
  hypothesis, and MSS is quarantined here. What is returned instead, as
  the marked minimal repair, is `ks_of_blockRSP`: the same implication
  with the hypothesis strengthened to block-witnessed RSP, which is the
  honest content of Remark 4.2's converse.
-/
import RequestProject.PlufWO6.PartD

open Set Filter Topology
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO6

open PlufWO1

/-! ### Ultrafilter limits of bounded sequences -/

/-- A bounded real sequence has a limit along any ultrafilter. -/
theorem exists_ultrafilter_limit (U : Ultrafilter ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hbd : ∀ n, |f n| ≤ C) : ∃ L : ℝ, ∀ ε > 0, {n | |f n - L| < ε} ∈ U := by
  have hle : (U.map f : Filter ℝ) ≤ Filter.principal (Set.Icc (-C) C) := by
    rw [Filter.le_principal_iff]
    refine Filter.mem_map.mpr (Filter.univ_mem' fun n => ?_)
    exact Set.mem_Icc.mpr ⟨(abs_le.mp (hbd n)).1, (abs_le.mp (hbd n)).2⟩
  obtain ⟨L, -, hL⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds (U.map f) hle
  refine ⟨L, fun ε hε => ?_⟩
  simpa [Filter.mem_map, Metric.mem_ball, Real.dist_eq] using hL (Metric.ball_mem_nhds L hε)

/-! ### The Kadison–Singer hypothesis -/

/-- The Kadison–Singer hypothesis for an ultrafilter `U` on ℕ, in Anderson
    paving form: every bounded operator on `PlufWO1.H` is, after passing to
    a `U`-set, within `ε` of its diagonal in the compressed norm. This is
    the theorem of Marcus–Spielman–Srivastava; it is quarantined here as a
    hypothesis, so Part F is ZFC. -/
def KSHyp (U : Ultrafilter ℕ) : Prop :=
  ∀ (T : PlufWO1.H →L[ℝ] PlufWO1.H), ∀ ε > 0, ∃ S ∈ U,
    ∀ x ∈ PlufWO1.block S, ‖x‖ = 1 →
      |inner (𝕜 := ℝ) (T x) x -
        (∑' n, (if n ∈ S then inner (𝕜 := ℝ) (T (PlufWO1.evec n)) (PlufWO1.evec n) *
          ((x : ∀ _ : ℕ, ℝ) n)^2 else 0))| < ε

/-! ### The diagonal of an operator -/

/-- The diagonal sequence of `T` in the standard basis. -/
noncomputable def diag (T : H →L[ℝ] H) (n : ℕ) : ℝ :=
  inner (𝕜 := ℝ) (T (evec n)) (evec n)

theorem norm_evec (n : ℕ) : ‖evec n‖ = 1 := PlufWO5.orthonormal_evec.1 n

theorem abs_diag_le (T : H →L[ℝ] H) (n : ℕ) : |diag T n| ≤ ‖T‖ := by
  have h := abs_real_inner_le_norm (T (evec n)) (evec n)
  calc |diag T n| ≤ ‖T (evec n)‖ * ‖evec n‖ := h
    _ ≤ (‖T‖ * ‖evec n‖) * ‖evec n‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ := by rw [norm_evec]; ring

/-- On the unit sphere of a block inside `S ∩ S'`, the diagonal sum of `T`
    over `S` is within `ε` of any value `L` that the diagonal approximates
    on `S'`. -/
theorem abs_diagSum_sub_le (T : H →L[ℝ] H) {S S' : Set ℕ} {x : H}
    (hx : x ∈ block (S ∩ S')) (hx1 : ‖x‖ = 1) {L ε : ℝ}
    (hd : ∀ n ∈ S', |diag T n - L| ≤ ε) :
    |(∑' n, (if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0)) - L| ≤ ε := by
  set c : ℕ → ℝ := fun n => if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0 with hc
  set s : ℕ → ℝ := fun n => ((x : ∀ _ : ℕ, ℝ) n)^2 with hs
  have hxzero : ∀ n ∉ S ∩ S', (x : ∀ _ : ℕ, ℝ) n = 0 := (mem_block_iff _ x).mp hx
  have hssum : Summable s := PlufWO5.summable_sq x
  have hstsum : ∑' n, s n = 1 := by
    rw [← PlufWO5.norm_sq_eq_tsum, hx1]; norm_num
  have hcsum : Summable c := by
    refine Summable.of_norm_bounded (g := fun n => ‖T‖ * s n) (hssum.mul_left ‖T‖) (fun n => ?_)
    by_cases hn : n ∈ S
    · simp only [hc, if_pos hn, Real.norm_eq_abs, abs_mul, hs]
      have h1 : |((x : ∀ _ : ℕ, ℝ) n)^2| = ((x : ∀ _ : ℕ, ℝ) n)^2 := abs_of_nonneg (by positivity)
      rw [h1]
      exact mul_le_mul_of_nonneg_right (abs_diag_le T n) (by positivity)
    · simp only [hc, if_neg hn, norm_zero]
      have : 0 ≤ s n := by simp only [hs]; positivity
      nlinarith [norm_nonneg T]
  have hgbd : ∀ n, |c n - L * s n| ≤ ε * s n := by
    intro n
    by_cases hn : n ∈ S ∩ S'
    · have hnS : n ∈ S := hn.1
      have : c n - L * s n = (diag T n - L) * s n := by
        simp only [hc, if_pos hnS, hs]; ring
      rw [this, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ s n by simp only [hs]; positivity)]
      exact mul_le_mul_of_nonneg_right (hd n hn.2) (by simp only [hs]; positivity)
    · have hx0 : (x : ∀ _ : ℕ, ℝ) n = 0 := hxzero n hn
      have hsn : s n = 0 := by simp only [hs, hx0]; ring
      have hcn : c n = 0 := by
        by_cases hnS : n ∈ S
        · simp only [hc, if_pos hnS, hx0]; ring
        · simp only [hc, if_neg hnS]
      rw [hcn, hsn]
      simp
  have hgsum : Summable (fun n => c n - L * s n) := hcsum.sub (hssum.mul_left L)
  have habs : Summable (fun n => |c n - L * s n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) hgbd (hssum.mul_left ε)
  have hkey : (∑' n, c n) - L = ∑' n, (c n - L * s n) := by
    rw [Summable.tsum_sub hcsum (hssum.mul_left L), tsum_mul_left, hstsum, mul_one]
  have hbound : |∑' n, (c n - L * s n)| ≤ ∑' n, |c n - L * s n| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun n => c n - L * s n)
        (by simpa [Real.norm_eq_abs] using habs)
  rw [hkey]
  calc |∑' n, (c n - L * s n)| ≤ ∑' n, |c n - L * s n| := hbound
    _ ≤ ∑' n, ε * s n := Summable.tsum_le_tsum hgbd habs (hssum.mul_left ε)
    _ = ε := by rw [tsum_mul_left, hstsum, mul_one]

/-- F1 (Theorem 4.1, KS-parametrized). Any pluf containing the blocks of
    `U` has RSP for every `T`, with the limit the `U`-limit of the diagonal.
    Formalize the RSP conclusion; the identification of the limit is F2.

    (The contracted hypothesis `hT : IsSelfAdjoint T` is kept as
    contracted; the argument does not use it, because the paving
    hypothesis already controls the Rayleigh quotient of `T`, which sees
    only the symmetric part of `T`.) -/
theorem rsp_of_ks (U : Ultrafilter ℕ) (hKS : KSHyp U)
    (π : Set (Submodule ℝ PlufWO1.H)) (hπ : IsPluf π)
    (hblocks : ∀ S ∈ U, PlufWO1.block S ∈ π)
    (T : PlufWO1.H →L[ℝ] PlufWO1.H) (hT : IsSelfAdjoint T) :
    RSP π T := by
  obtain ⟨L, hL⟩ := exists_ultrafilter_limit U (diag T) ‖T‖ (abs_diag_le T)
  intro ε hε
  obtain ⟨S, hSU, hS⟩ := hKS T (ε / 8) (by linarith)
  have hS'U : {n | |diag T n - L| < ε / 8} ∈ U := hL (ε / 8) (by linarith)
  set S' : Set ℕ := {n | |diag T n - L| < ε / 8} with hS'
  have hmem : S ∩ S' ∈ U := Filter.inter_mem hSU hS'U
  refine ⟨block (S ∩ S'), hblocks _ hmem, ?_⟩
  set M : Submodule ℝ H := block (S ∩ S') with hM
  have hMbot : M ≠ ⊥ := hπ.ne_bot (hblocks _ hmem)
  -- every Rayleigh value on `M` is within `ε / 4` of `L`
  have hkey : ∀ a ∈ rayleighSet T M, |a - L| ≤ ε / 4 := by
    rintro a ⟨x, ⟨hxM, hx1⟩, rfl⟩
    have hxS : x ∈ block S := PlufWO5.block_mono Set.inter_subset_left hxM
    have h1 := hS x hxS hx1
    have h2 : |(∑' n, (if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0)) - L| ≤ ε / 8 :=
      abs_diagSum_sub_le T hxM hx1 (fun n hn => le_of_lt hn)
    calc |inner (𝕜 := ℝ) (T x) x - L|
        ≤ |inner (𝕜 := ℝ) (T x) x -
            (∑' n, (if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0))| +
          |(∑' n, (if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0)) - L| :=
          abs_sub_le _ _ _
      _ ≤ ε / 8 + ε / 8 := add_le_add (le_of_lt h1) h2
      _ ≤ ε / 4 := by linarith
  have hup : upper T M ≤ L + ε / 4 := by
    rw [upper_eq]
    refine csSup_le (rayleighSet_nonempty hMbot) (fun a ha => ?_)
    have := hkey a ha
    have := abs_le.mp this
    linarith [this.2]
  have hlo : L - ε / 4 ≤ lower T M := by
    rw [lower_eq]
    refine le_csInf (rayleighSet_nonempty hMbot) (fun a ha => ?_)
    have := abs_le.mp (hkey a ha)
    linarith [this.1]
  linarith

/-! ### F2, in the marked minimal repair: block-witnessed RSP

The contracted F2 hypothesis — RSP along every pluf containing the blocks
of `U` — produces, for each `ε`, *some* member of the pluf with small
Rayleigh oscillation, and nothing identifies that member with a block of
`U`; see the discussion in `PlufWO6.lean` and `REPORT-WO6.md`. What does
follow, and is the honest content of Remark 4.2's converse direction, is
the implication from the *block-witnessed* round-slice property, in which
the witnesses are blocks of the ultrafilter. -/

/-- Block-witnessed RSP for `T` along `U`: some block of the ultrafilter
    has arbitrarily small Rayleigh oscillation. -/
def BlockRSP (U : Ultrafilter ℕ) (T : H →L[ℝ] H) : Prop :=
  ∀ ε > 0, ∃ S ∈ U, upper T (block S) - lower T (block S) < ε

/-- F2, marked minimal repair. Block-witnessed RSP for every operator
    gives the paving statement `KSHyp U`: on a block of small oscillation
    both the Rayleigh quotient of a unit vector and the diagonal sum (a
    convex combination of diagonal entries, each of which is itself a
    Rayleigh value of the block) lie within the oscillation of the lower
    Rayleigh value. -/
theorem ks_of_blockRSP (U : Ultrafilter ℕ) (h : ∀ T : H →L[ℝ] H, BlockRSP U T) :
    KSHyp U := by
  intro T ε hε
  obtain ⟨S, hSU, hosc⟩ := h T (ε / 3) (by linarith)
  refine ⟨S, hSU, ?_⟩
  intro x hxS hx1
  set L : ℝ := lower T (block S) with hL
  have hmem : ∀ y : H, y ∈ block S → ‖y‖ = 1 →
      inner (𝕜 := ℝ) (T y) y ∈ rayleighSet T (block S) := fun y hy hy1 => ⟨y, ⟨hy, hy1⟩, rfl⟩
  have hd : ∀ n ∈ S, |diag T n - L| ≤ ε / 3 := by
    intro n hn
    have hmem' : diag T n ∈ rayleighSet T (block S) :=
      hmem (evec n) (PlufWO5.evec_mem_block hn) (norm_evec n)
    have h1 : L ≤ diag T n := lower_le' hmem'
    have h2 : diag T n ≤ upper T (block S) := le_upper hmem'
    rw [abs_le]
    constructor <;> linarith
  have hxSS : x ∈ block (S ∩ S) := by simpa using hxS
  have hsum := abs_diagSum_sub_le T hxSS hx1 hd
  have hray : |inner (𝕜 := ℝ) (T x) x - L| ≤ ε / 3 := by
    have hmem' := hmem x hxS hx1
    have h1 : L ≤ inner (𝕜 := ℝ) (T x) x := lower_le' hmem'
    have h2 : inner (𝕜 := ℝ) (T x) x ≤ upper T (block S) := le_upper hmem'
    rw [abs_le]
    constructor <;> linarith
  have hgoal : (∑' n, (if n ∈ S then inner (𝕜 := ℝ) (T (evec n)) (evec n) *
        ((x : ∀ _ : ℕ, ℝ) n)^2 else 0))
      = ∑' n, (if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0) := rfl
  rw [hgoal]
  set A : ℝ := inner (𝕜 := ℝ) (T x) x with hA
  set B : ℝ := ∑' n, (if n ∈ S then diag T n * ((x : ∀ _ : ℕ, ℝ) n)^2 else 0) with hB
  have hsplit : |A - B| ≤ |A - L| + |B - L| := by
    have h := abs_sub_le A L B
    rwa [abs_sub_comm L B] at h
  linarith

end PlufWO6
