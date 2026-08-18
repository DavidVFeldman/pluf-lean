/-
  PlufWO17/PartB.lean — Work Order 17, Part B.

  B1: coordinates see the same supports (the transfer along `PlufWO16.toFun`).
  B2: support-preserving realization inside `ℓ²` by a diagonal rescaling.
  B3: Paper V, Theorem 5.2, under the quarantined hypothesis `AroKaHyp`.
-/
import RequestProject.PlufWO17.Basic

open Set

namespace PlufWO17

open PlufWO16 (supp toFun)

/-- B1 (coordinates see the same supports). The image of a finite-rank closed
    submodule of `ℓ²` under the inclusion into `ℕ → ℝ` has the same support
    family. -/
theorem suppFamily_eq_coords (M : Submodule ℝ H) :
    suppFamily M
      = {S : Set ℕ | ∃ f ∈ M.map (PlufWO16.toFun), {n | f n ≠ 0} = S} := by
  ext S
  constructor
  · rintro ⟨x, hxM, rfl⟩
    exact ⟨toFun x, Submodule.mem_map_of_mem hxM, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨x, hxM, rfl⟩ := hf
    exact ⟨x, hxM, rfl⟩

/-! ### The diagonal rescaling behind B2 -/

section Rescale

variable (t : Finset (ℕ → ℝ))

/-- The weights of the rescaling: `2⁻ⁿ` damped by the entries occurring at `n`
    among the finitely many generators. They are positive, so multiplication by
    them preserves supports. -/
noncomputable def weight (n : ℕ) : ℝ :=
  (1 / 2) ^ n / (1 + ∑ v ∈ t, |v n|)

theorem weight_pos (n : ℕ) : 0 < weight t n := by
  have hden : 0 < 1 + ∑ v ∈ t, |v n| := by
    have : 0 ≤ ∑ v ∈ t, |v n| := Finset.sum_nonneg fun v _ => abs_nonneg _
    linarith
  exact div_pos (by positivity) hden

theorem weight_ne_zero (n : ℕ) : weight t n ≠ 0 := ne_of_gt (weight_pos t n)

theorem abs_weight_mul_le {v : ℕ → ℝ} (hv : v ∈ t) (n : ℕ) :
    |weight t n * v n| ≤ (1 / 2) ^ n := by
  have hden : 0 < 1 + ∑ w ∈ t, |w n| := by
    have : 0 ≤ ∑ w ∈ t, |w n| := Finset.sum_nonneg fun w _ => abs_nonneg _
    linarith
  have hle : |v n| ≤ 1 + ∑ w ∈ t, |w n| := by
    have : |v n| ≤ ∑ w ∈ t, |w n| :=
      Finset.single_le_sum (f := fun w => |w n|) (fun w _ => abs_nonneg _) hv
    linarith
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  rw [abs_mul, abs_of_pos (weight_pos t n), weight, div_mul_eq_mul_div,
    div_le_iff₀ hden]
  nlinarith

theorem memℓp_weight_mul {v : ℕ → ℝ} (hv : v ∈ t) :
    Memℓp (fun n => weight t n * v n) 2 := by
  apply memℓp_gen
  have hsum : Summable fun n : ℕ => ((1 / 4 : ℝ)) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine hsum.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have h2' : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2', Real.rpow_natCast, Real.norm_eq_abs]
  have h := abs_weight_mul_le t hv n
  have hnn : (0 : ℝ) ≤ |weight t n * v n| := abs_nonneg _
  calc |weight t n * v n| ^ 2 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 := by nlinarith
    _ = (1 / 4 : ℝ) ^ n := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num

open scoped Classical in
/-- The rescaled generator, as a vector of `ℓ²`. -/
noncomputable def rescale (v : ℕ → ℝ) : H :=
  if h : Memℓp (fun n => weight t n * v n) 2 then ⟨_, h⟩ else 0

theorem rescale_apply {v : ℕ → ℝ} (hv : v ∈ t) (n : ℕ) :
    toFun (rescale t v) n = weight t n * v n := by
  rw [rescale, dif_pos (memℓp_weight_mul t hv)]
  rfl

theorem toFun_sum_rescale (a : (ℕ → ℝ) → ℝ) (n : ℕ) :
    toFun (∑ v ∈ t, a v • rescale t v) n = weight t n * (∑ v ∈ t, a v • v) n := by
  rw [map_sum]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [rescale_apply t hv n]
  ring

/-- The rescaled copy of `W` inside `ℓ²`: the vectors whose coordinates are the
    weighted coordinates of a member of `W`. -/
noncomputable def realization (W : Submodule ℝ (ℕ → ℝ)) : Submodule ℝ H where
  carrier := {x : H | ∃ f ∈ W, ∀ n, toFun x n = weight t n * f n}
  add_mem' := by
    rintro x y ⟨f, hf, hx⟩ ⟨g, hg, hy⟩
    refine ⟨f + g, W.add_mem hf hg, fun n => ?_⟩
    rw [map_add, Pi.add_apply, Pi.add_apply, hx n, hy n]
    ring
  zero_mem' := ⟨0, W.zero_mem, fun n => by simp⟩
  smul_mem' := by
    rintro c x ⟨f, hf, hx⟩
    refine ⟨c • f, W.smul_mem c hf, fun n => ?_⟩
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hx n]
    ring

theorem mem_realization_iff {W : Submodule ℝ (ℕ → ℝ)} {x : H} :
    x ∈ realization t W ↔ ∃ f ∈ W, ∀ n, toFun x n = weight t n * f n := Iff.rfl

end Rescale

/-- B2 (support-preserving realization; the item the WO-16 census identified as
    carrying the content). Every finite-dimensional subspace `W` of `ℕ → ℝ` is
    carried, by a diagonal rescaling with nonvanishing entries, onto a
    finite-dimensional — hence closed — subspace of `ℓ²` with the same support
    family.

    (Pick a basis `f₁, …, f_d` of `W`; choose weights `c n > 0` small enough
    that each `c • f i` is square-summable, e.g.
    `c n = 2^{-n} / (1 + max_i |f i n|)`; multiplication by a nonvanishing
    sequence preserves supports.) -/
theorem exists_realization_in_lp (W : Submodule ℝ (ℕ → ℝ))
    (hW : Module.Finite ℝ ↥W) :
    ∃ M : Submodule ℝ H, Module.Finite ℝ ↥M ∧
      suppFamily M = {S : Set ℕ | ∃ f ∈ W, {n | f n ≠ 0} = S} := by
  classical
  obtain ⟨t, ht⟩ : W.FG := Module.Finite.iff_fg.1 hW
  have htW : ∀ v ∈ t, v ∈ W := by
    intro v hv
    rw [← ht]
    exact Submodule.subset_span hv
  -- every member of `W` is a combination of the generators, so the realization
  -- of `W` is spanned by the realizations of the generators
  have hspan : realization t W = Submodule.span ℝ ↑(t.image (rescale t)) := by
    apply le_antisymm
    · rintro x ⟨f, hf, hx⟩
      rw [← ht] at hf
      obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hf
      have hxeq : x = ∑ v ∈ t, a v • rescale t v := by
        refine PlufWO16.toFun_injective (funext fun n => ?_)
        rw [toFun_sum_rescale t a n, ha, hx n]
      rw [hxeq]
      exact Submodule.sum_mem _ fun v hv =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hv))
    · rw [Submodule.span_le]
      rintro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (by simpa using hx)
      exact ⟨v, htW v hv, fun n => rescale_apply t hv n⟩
  refine ⟨realization t W, ?_, ?_⟩
  · exact Module.Finite.iff_fg.2 ⟨t.image (rescale t), hspan.symm⟩
  ext S
  constructor
  · rintro ⟨x, ⟨f, hf, hx⟩, rfl⟩
    refine ⟨f, hf, ?_⟩
    ext n
    simp only [mem_setOf_eq, PlufWO16.mem_supp_iff]
    rw [show ((x : ∀ _ : ℕ, ℝ) n) = toFun x n from rfl, hx n]
    exact (mul_ne_zero_iff.trans ⟨fun h => h.2, fun h => ⟨weight_ne_zero t n, h⟩⟩).symm
  · rintro ⟨f, hf, rfl⟩
    have hf' := hf
    rw [← ht] at hf'
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hf'
    refine ⟨∑ v ∈ t, a v • rescale t v, ⟨f, hf, fun n => ?_⟩, ?_⟩
    · rw [toFun_sum_rescale t a n, ha]
    · ext n
      simp only [mem_setOf_eq, PlufWO16.mem_supp_iff]
      rw [show ((∑ v ∈ t, a v • rescale t v : H) : ∀ _ : ℕ, ℝ) n
          = toFun (∑ v ∈ t, a v • rescale t v) n from rfl, toFun_sum_rescale t a n, ha]
      exact mul_ne_zero_iff.trans ⟨fun h => h.2, fun h => ⟨weight_ne_zero t n, h⟩⟩

/-- REPORT (work order, Part B3: "report whether Mathlib's
    finite-dimensional-implies-closed lemma applies in the form needed").
    FINDING: it does, verbatim: `Submodule.closed_of_finiteDimensional` applies
    to a submodule of `H` once `Module.Finite ℝ ↥M` is read as the
    `FiniteDimensional ℝ ↥M` instance it asks for — the two are the same
    class. -/
theorem isClosed_of_finite (M : Submodule ℝ H) (hfin : Module.Finite ℝ ↥M) :
    IsClosed (M : Set H) :=
  haveI : FiniteDimensional ℝ ↥M := hfin
  M.closed_of_finiteDimensional

/-- B3 (Paper V, Theorem 5.2). Under the quarantined hypothesis, the support
    family of a nonzero finite-rank closed submodule of `ℓ²` is a scrawl
    family, and conversely every scrawl family of the form given by a
    finite-dimensional `W ⊆ ℕ → ℝ` is realized by such a submodule.

    Assemble B1, B2 and `AroKaHyp`. Report whether the finite-dimensionality of
    a subspace of `ℓ²` is enough for closedness in the form Mathlib supplies
    (`Submodule.closed_of_finiteDimensional` or kin). -/
theorem suppFamily_isScrawlFamily (h : AroKaHyp)
    (M : Submodule ℝ H) (hM : M ≠ ⊥) (hfin : Module.Finite ℝ ↥M) :
    IsScrawlFamily (suppFamily M) := by
  rw [suppFamily_eq_coords]
  refine h (M.map toFun) ?_
    (Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hfin).map _))
  obtain ⟨x, hxM, hx0⟩ := (Submodule.ne_bot_iff M).1 hM
  refine (Submodule.ne_bot_iff _).2 ⟨toFun x, Submodule.mem_map_of_mem hxM, ?_⟩
  intro hcon
  exact hx0 (PlufWO16.toFun_injective (by simpa using hcon))

end PlufWO17
