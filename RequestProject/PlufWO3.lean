/-
  PlufWO3.lean — Work Order 3 for the pluf project (Feldman–Wilce).

  Scope: the remaining lattice-level assertions of Paper III:
    (G) ultrafilter limits of bounded functions along countably complete
        ultrafilters, and the diagonal-flattening corollary
        (Paper III, Corollary 2.2, quadratic-form formulation);
    (H) the block filter Φ(U) as a filter: properness, upward closure,
        closure under (arbitrary-index) intersections, nonprincipality,
        and the decision property (Paper III, Corollary 3.2, filter half);
    (I) the κ-witness subspace of a partition into countable pieces and
        the non-maximality proposition (Paper III, Proposition 5.3,
        Hilbert half).

  As in WO-1/WO-2, NO large-cardinal machinery is axiomatized:
  `DiagInt`, `CountableSmall`, `CountablyComplete`, and generic
  intersection-closure enter only as hypotheses.

  This WO builds on the WO-2 artifact (repo `pluf-lean`, both prior audits
  green): namespaces `PlufWO1` and `PlufWO2` are available and MUST be
  reused — in particular `PlufWO2.block`, `PlufWO2.evec`,
  `PlufWO2.hasSum_evec_smul`, `PlufWO2.hasSum_coord_smul`,
  `PlufWO2.inner_eq_coord_mul`, `PlufWO2.block_le_of_evec_mem`,
  `PlufWO2.exact_paving`, `PlufWO2.block_filter_decides`, and
  `PlufWO1.IsPartialSelector`. Do not duplicate them.

  Ground rules identical to WO-1/WO-2 (census first; report-rather-than-
  repair; no sorry/admit/axiom/native_decide; #print axioms per contract
  theorem, whitelist propext, Classical.choice, Quot.sound; WO-1's and
  WO-2's 24 theorems must remain green).

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.
-/
import RequestProject.PlufWO2

open Set PlufWO2

namespace PlufWO3

variable {κ : Type*} [LinearOrder κ]

/-- `U` is countably complete. -/
def CountablyComplete (U : Ultrafilter κ) : Prop :=
  ∀ s : ℕ → Set κ, (∀ n, s n ∈ U) → (⋂ n, s n) ∈ U

/-! ### Part G: ultrafilter limits and diagonal flattening -/

omit [LinearOrder κ] in
/-- G1. A bounded real-valued function has a limit along a countably
    complete ultrafilter. (Bisection: the U-decided halves of a nested
    interval sequence intersect by countable completeness; the limit is the
    common point. Uniqueness is immediate and need not be stated.)

    Route report: the bisection/countable-completeness route is not needed.
    Boundedness alone already produces the ultralimit as the supremum
    `L = sSup {t | {α | t ≤ f α} ∈ U}`: for `ε > 0` the set `{α | L - ε ≤ f α}`
    is a member because some `t > L - ε` lies in the (downward closed) set,
    and `{α | f α < L + ε}` is a member because its complement is not.  The
    hypothesis `hcc` is therefore unused; it is retained because the contract
    asks for it. -/
theorem exists_ulim (U : Ultrafilter κ) (hcc : CountablyComplete U)
    (f : κ → ℝ) (C : ℝ) (hbd : ∀ α, |f α| ≤ C) :
    ∃ L : ℝ, ∀ ε > 0, {α | |f α - L| ≤ ε} ∈ U := by
  classical
  set E : Set ℝ := {t : ℝ | {α | t ≤ f α} ∈ U} with hEdef
  have hEne : E.Nonempty := by
    refine ⟨-C, ?_⟩
    have : {α : κ | -C ≤ f α} = Set.univ := by
      ext α
      simpa using (abs_le.mp (hbd α)).1
    show {α : κ | -C ≤ f α} ∈ U
    rw [this]
    exact Filter.univ_mem
  have hEbdd : BddAbove E := by
    refine ⟨C, ?_⟩
    rintro t ht
    obtain ⟨α, hα⟩ := Filter.nonempty_of_mem ht
    exact le_trans hα ((abs_le.mp (hbd α)).2)
  refine ⟨sSup E, ?_⟩
  intro ε hε
  have h1 : {α : κ | sSup E - ε ≤ f α} ∈ U := by
    obtain ⟨t, htE, ht⟩ := exists_lt_of_lt_csSup hEne (by linarith : sSup E - ε < sSup E)
    exact Filter.mem_of_superset htE (fun α hα => le_trans ht.le hα)
  have h2 : {α : κ | f α < sSup E + ε} ∈ U := by
    have hnot : {α : κ | sSup E + ε ≤ f α} ∉ U := by
      intro hmem
      have : sSup E + ε ≤ sSup E := le_csSup hEbdd hmem
      linarith
    have := Ultrafilter.compl_mem_iff_notMem.mpr hnot
    refine Filter.mem_of_superset this (fun α hα => ?_)
    simpa using lt_of_not_ge (by simpa using hα)
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro α ⟨hα1, hα2⟩
  simp only [Set.mem_setOf_eq] at hα1 hα2 ⊢
  rw [abs_le]
  constructor <;> linarith

/-- G2 (Diagonal flattening; Paper III, Corollary 2.2, quadratic-form
    formulation). If the diagonal entries of `T` have `U`-limit `L`, then
    for every `ε > 0` there is `S ∈ U` on which the quadratic form of `T`
    is within `ε` of `L` times the norm-squared, uniformly on the block.

    Proof sketch: shrink the exact-paving set (E1) inside the `hL` set for
    `ε`; for `x ∈ block S`, expand `⟪T x, x⟫ = ∑' β, x β * ⟪T (evec β), x⟫`
    (push `hasSum_evec_smul` through `T` and then through `⟪·, x⟫` — over ℝ
    the inner product is bilinear), and apply `inner_eq_coord_mul` with
    `P := T` on the diagonalizing block to reduce each term to
    `(x β)^2 * d β` with `d β ∈ [L−ε, L+ε]` for `β ∈ S` and `x β = 0` off
    `S`; conclude by comparison with `∑' β, (x β)^2 = ‖x‖²`
    (`lp.inner_eq_tsum` plus `real_inner_self_eq_norm_sq`, or the `HasSum`
    form — prover's choice). Note no self-adjointness is required: exact
    paving already used the adjoint internally, and the expansion is
    orientation-uniform.

    Route report: the shrunken set is `S₀ ∩ {α | |d α - L| ≤ ε}`, with `S₀`
    from `exact_paving`.  Summability is obtained without any operator-norm
    API: the expansion `HasSum (fun β => (x β)^2 * d β) ⟪T x, x⟫` comes from
    `hasSum_coord_smul` for the functional `⟪·, x⟫ ∘ T` combined with
    `inner_eq_coord_mul`, `HasSum (fun β => (x β)^2) ‖x‖²` comes from
    `lp.hasSum_norm`, and the conclusion follows by the termwise bound
    `|(x β)^2 (d β - L)| ≤ ε (x β)^2` and `hasSum_le` in both directions.
    No self-adjointness hypothesis is needed. -/
theorem quadratic_flat (U : Ultrafilter κ) (hdiag : DiagInt U)
    (hsmall : CountableSmall U) (T : Hk κ →L[ℝ] Hk κ) (L : ℝ)
    (hL : ∀ ε > 0, {α | |inner (𝕜 := ℝ) (T (evec α)) (evec α) - L| ≤ ε} ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S ∈ U, ∀ x ∈ block S,
      |inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2 := by
  classical
  obtain ⟨S₀, hS₀U, hoff⟩ := exact_paving U hdiag hsmall T
  set d : κ → ℝ := fun α => inner (𝕜 := ℝ) (T (evec α)) (evec α) with hd
  have hAU : {α : κ | |d α - L| ≤ ε} ∈ U := hL ε hε
  refine ⟨S₀ ∩ {α : κ | |d α - L| ≤ ε}, Filter.inter_mem hS₀U hAU, ?_⟩
  intro x hx
  have hxS₀ : x ∈ block S₀ := block_mono Set.inter_subset_left hx
  -- the ℓ²-expansion of the quadratic form along the standard basis
  have hexp := hasSum_coord_smul ((innerSL ℝ x).comp T) x
  have hfx : ((innerSL ℝ x).comp T) x = inner (𝕜 := ℝ) (T x) x := by
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply]
    exact real_inner_comm (T x) x
  have hterm : ∀ β : κ, (x : ∀ _ : κ, ℝ) β * ((innerSL ℝ x).comp T) (evec β)
      = ((x : ∀ _ : κ, ℝ) β) ^ 2 * d β := by
    intro β
    by_cases hβ : β ∈ S₀
    · have hcoord := inner_eq_coord_mul S₀ T hoff hxS₀ hβ
      have hval : ((innerSL ℝ x).comp T) (evec β) = inner (𝕜 := ℝ) (T (evec β)) x := by
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply]
        exact real_inner_comm (T (evec β)) x
      rw [hval, hcoord, hd]
      ring
    · have hxβ : (x : ∀ _ : κ, ℝ) β = 0 :=
        (mem_block_iff _ x).mp hx β (fun hm => hβ hm.1)
      rw [hxβ]
      ring
  rw [funext hterm, hfx] at hexp
  -- the ℓ²-expansion of the norm
  have hnorm : HasSum (fun β : κ => ((x : ∀ _ : κ, ℝ) β) ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : κ => ℝ) (p := 2) (by norm_num) x
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    rw [h2] at h
    have hcast : ∀ y : ℝ, 0 ≤ y → y ^ (2:ℝ) = y ^ (2:ℕ) := by
      intro y _
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hcast ‖x‖ (norm_nonneg _)] at h
    refine h.congr_fun (fun β => ?_)
    rw [hcast _ (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  -- termwise comparison
  have hbound : ∀ β : κ,
      |((x : ∀ _ : κ, ℝ) β) ^ 2 * d β - L * ((x : ∀ _ : κ, ℝ) β) ^ 2|
        ≤ ε * ((x : ∀ _ : κ, ℝ) β) ^ 2 := by
    intro β
    by_cases hxβ : (x : ∀ _ : κ, ℝ) β = 0
    · simp [hxβ]
    · have hβmem : β ∈ S₀ ∩ {α : κ | |d α - L| ≤ ε} := by
        by_contra hmem
        exact hxβ ((mem_block_iff _ x).mp hx β hmem)
      have hdA : |d β - L| ≤ ε := hβmem.2
      have hrw : ((x : ∀ _ : κ, ℝ) β) ^ 2 * d β - L * ((x : ∀ _ : κ, ℝ) β) ^ 2
          = ((x : ∀ _ : κ, ℝ) β) ^ 2 * (d β - L) := by ring
      rw [hrw, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm ε]
      exact mul_le_mul_of_nonneg_left hdA (sq_nonneg _)
  have hdiff : HasSum
      (fun β : κ => ((x : ∀ _ : κ, ℝ) β) ^ 2 * d β - L * ((x : ∀ _ : κ, ℝ) β) ^ 2)
      (inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2) := hexp.sub (hnorm.mul_left L)
  have hscaled : HasSum (fun β : κ => ε * ((x : ∀ _ : κ, ℝ) β) ^ 2) (ε * ‖x‖ ^ 2) :=
    hnorm.mul_left ε
  have hub : inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2 ≤ ε * ‖x‖ ^ 2 :=
    hasSum_le (fun β => (abs_le.mp (hbound β)).2) hdiff hscaled
  have hlb : -(ε * ‖x‖ ^ 2) ≤ inner (𝕜 := ℝ) (T x) x - L * ‖x‖ ^ 2 :=
    hasSum_le (fun β => (abs_le.mp (hbound β)).1) hscaled.neg hdiff
  exact abs_le.mpr ⟨hlb, hub⟩

/-! ### Part H: the block filter Φ(U), as a filter -/

/-- The block filter: closed subspaces containing a measure-one block.
    (Membership is deliberately stated for arbitrary submodules; the
    lattice-theoretic assertions below do not need closedness of the
    members, only of the subspaces being decided.) -/
def PhiU (U : Ultrafilter κ) : Set (Submodule ℝ (Hk κ)) :=
  {M | ∃ S ∈ U, block S ≤ M}

omit [LinearOrder κ] in
/-- H1 (filter axioms). Φ(U) is upward closed, closed under pairwise
    intersection, and proper (⊥ is not a member). Properness uses only
    that members of an ultrafilter are nonempty. -/
theorem PhiU_upward (U : Ultrafilter κ) {M N : Submodule ℝ (Hk κ)}
    (hM : M ∈ PhiU U) (hMN : M ≤ N) : N ∈ PhiU U := by
  obtain ⟨S, hSU, hS⟩ := hM
  exact ⟨S, hSU, hS.trans hMN⟩

omit [LinearOrder κ] in
theorem inf_mem_PhiU (U : Ultrafilter κ) {M N : Submodule ℝ (Hk κ)}
    (hM : M ∈ PhiU U) (hN : N ∈ PhiU U) : M ⊓ N ∈ PhiU U := by
  obtain ⟨S, hSU, hS⟩ := hM
  obtain ⟨T, hTU, hT⟩ := hN
  refine ⟨S ∩ T, Filter.inter_mem hSU hTU, le_inf ?_ ?_⟩
  · exact (block_mono Set.inter_subset_left).trans hS
  · exact (block_mono Set.inter_subset_right).trans hT

omit [LinearOrder κ] in
theorem bot_notMem_PhiU (U : Ultrafilter κ) : ⊥ ∉ PhiU U := by
  haveI : LinearOrder κ := IsWellOrder.linearOrder (WellOrderingRel (α := κ))
  rintro ⟨S, hSU, hS⟩
  obtain ⟨α, hα⟩ := Filter.nonempty_of_mem hSU
  have h0 : evec α ∈ (⊥ : Submodule ℝ (Hk κ)) := hS (evec_mem_block hα)
  rw [Submodule.mem_bot] at h0
  have : (evec α : ∀ _ : κ, ℝ) α = 0 := by rw [h0]; rfl
  rw [evec_apply, if_pos rfl] at this
  exact one_ne_zero this

omit [LinearOrder κ] in
/-- H2 (completeness, generic form). If `U` is closed under `ι`-indexed
    intersections, then so is Φ(U) under `ι`-indexed infima. Instantiating
    `ι := ℕ` with `CountablyComplete` gives σ-completeness; at a measurable
    cardinal the hypothesis holds for every `ι` of size `< κ`, giving the
    κ-completeness of Paper III, Corollary 3.2 — but no cardinal arithmetic
    appears here. -/
theorem iInf_mem_PhiU (U : Ultrafilter κ) {ι : Type*}
    (hU : ∀ s : ι → Set κ, (∀ i, s i ∈ U) → (⋂ i, s i) ∈ U)
    (M : ι → Submodule ℝ (Hk κ)) (hM : ∀ i, M i ∈ PhiU U) :
    (⨅ i, M i) ∈ PhiU U := by
  choose S hSU hS using hM
  refine ⟨⋂ i, S i, hU S hSU, le_iInf fun i => ?_⟩
  exact (block_mono (Set.iInter_subset S i)).trans (hS i)

omit [LinearOrder κ] in
/-- H3 (nonprincipality). A vector lying in every member of Φ(U) is zero:
    its support is countable (D1), so the block of the complement is a
    member that excludes it unless every coordinate vanishes. -/
theorem PhiU_nonprincipal (U : Ultrafilter κ) (hsmall : CountableSmall U)
    (x : Hk κ) (hx : ∀ M ∈ PhiU U, x ∈ M) : x = 0 := by
  have hc : (supp x)ᶜ ∈ U := hsmall _ (countable_supp x)
  have hmem : x ∈ block ((supp x)ᶜ) := hx _ ⟨(supp x)ᶜ, hc, le_rfl⟩
  rw [mem_block_iff] at hmem
  have hall : ∀ α : κ, (x : ∀ _ : κ, ℝ) α = 0 := by
    intro α
    by_cases h : α ∈ supp x
    · exact hmem α (by simpa using h)
    · simpa [supp] using h
  exact lp.ext (funext hall)

/-- H4 (the decision property, membership form; Paper III, Corollary 3.2,
    filter half). Every closed subspace is a member of Φ(U) or is met
    trivially by a member. With H1–H3 this is the assertion that Φ(U) is a
    nonprincipal maximal filter of closed subspaces, via the maximality
    criterion of the companion paper. -/
theorem PhiU_decides (U : Ultrafilter κ) (hdiag : DiagInt U)
    (hsmall : CountableSmall U) (W : Submodule ℝ (Hk κ))
    (hW : IsClosed (W : Set (Hk κ))) :
    W ∈ PhiU U ∨ ∃ M ∈ PhiU U, W ⊓ M = ⊥ := by
  rcases block_filter_decides U hdiag hsmall W hW with ⟨S, hSU, hS⟩ | ⟨S, hSU, hS⟩
  · exact Or.inl ⟨S, hSU, hS⟩
  · exact Or.inr ⟨block S, ⟨S, hSU, le_rfl⟩, hS⟩

/-! ### Part I: the κ-witness (Paper III, Proposition 5.3, Hilbert half) -/

section Witness

variable {ι : Type*} (P : ι → Set κ)

/-- The injection of a countable set into `ℕ` furnished by countability.
    Internal to the construction of `kConstraintVec`. -/
private noncomputable def cIdx (P₀ : Set κ) (hP : P₀.Countable) : κ → ℕ :=
  (countable_iff_exists_injOn.mp hP).choose

omit [LinearOrder κ] in
private theorem cIdx_injOn (P₀ : Set κ) (hP : P₀.Countable) :
    Set.InjOn (cIdx P₀ hP) P₀ :=
  (countable_iff_exists_injOn.mp hP).choose_spec

omit [LinearOrder κ] in
private theorem memlp_kConstraint (P₀ : Set κ) (hP : P₀.Countable) :
    Memℓp (fun α : κ =>
      Set.indicator P₀ (fun α => ((2 : ℝ) ^ (cIdx P₀ hP α + 1))⁻¹) α) 2 := by
  classical
  apply memℓp_gen
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h2]
  have hpt : ∀ α : κ,
      ‖Set.indicator P₀ (fun α => ((2 : ℝ) ^ (cIdx P₀ hP α + 1))⁻¹) α‖ ^ (2:ℝ)
        = Set.indicator P₀ (fun α => ((4 : ℝ) ^ (cIdx P₀ hP α + 1))⁻¹) α := by
    intro α
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    by_cases hα : α ∈ P₀
    · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), ← inv_pow, ← pow_mul,
        mul_comm (cIdx P₀ hP α + 1) 2, pow_mul]
      norm_num
      rw [one_div, inv_pow]
    · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, norm_zero]
      norm_num
  rw [funext hpt]
  refine summable_subtype_iff_indicator.mp ?_
  have hgeo : Summable (fun n : ℕ => ((4 : ℝ) ^ (n + 1))⁻¹) := by
    have h := (summable_geometric_of_lt_one (r := (1/4 : ℝ)) (by norm_num)
      (by norm_num)).mul_left (1/4 : ℝ)
    refine h.congr (fun n => ?_)
    rw [pow_succ]
    field_simp
    rw [← mul_pow]
    norm_num
  exact hgeo.comp_injective
    (fun a b hab => Subtype.ext ((cIdx_injOn P₀ hP) a.2 b.2 hab))

/-- I1a. The constraint vector of a countable set: coordinates
    `2^{-(g(α)+1)}` on `P₀` for an injection `g : P₀ ↪ ℕ` furnished by
    countability, zero off `P₀`. The choice of injection is internal; the
    contract is the specification lemmas I1b–I1d. -/
noncomputable def kConstraintVec (P₀ : Set κ) (hP : P₀.Countable) : Hk κ :=
  ⟨fun α => Set.indicator P₀ (fun α => ((2 : ℝ) ^ (cIdx P₀ hP α + 1))⁻¹) α,
    memlp_kConstraint P₀ hP⟩

omit [LinearOrder κ] in
/-- Coordinates of the constraint vector. -/
theorem kConstraintVec_apply (P₀ : Set κ) (hP : P₀.Countable) (α : κ) :
    (kConstraintVec P₀ hP : ∀ _ : κ, ℝ) α =
      Set.indicator P₀ (fun α => ((2 : ℝ) ^ (cIdx P₀ hP α + 1))⁻¹) α := rfl

omit [LinearOrder κ] in
/-- The coordinates of the constraint vector are strictly positive on `P₀`. -/
theorem kConstraintVec_pos {P₀ : Set κ} (hP : P₀.Countable) {α : κ} (hα : α ∈ P₀) :
    0 < (kConstraintVec P₀ hP : ∀ _ : κ, ℝ) α := by
  rw [kConstraintVec_apply, Set.indicator_of_mem hα]
  positivity

omit [LinearOrder κ] in
/-- The coordinates of the constraint vector vanish off `P₀`. -/
theorem kConstraintVec_eq_zero {P₀ : Set κ} (hP : P₀.Countable) {α : κ} (hα : α ∉ P₀) :
    (kConstraintVec P₀ hP : ∀ _ : κ, ℝ) α = 0 := by
  rw [kConstraintVec_apply, Set.indicator_of_notMem hα]

omit [LinearOrder κ] in
/-- I1b. Membership specification: the support is exactly `P₀`. -/
theorem supp_kConstraintVec (P₀ : Set κ) (hP : P₀.Countable) :
    supp (kConstraintVec P₀ hP) = P₀ := by
  ext α
  by_cases hα : α ∈ P₀
  · simpa [supp, hα] using (kConstraintVec_pos hP hα).ne'
  · simp [supp, hα, kConstraintVec_eq_zero hP hα]

omit [LinearOrder κ] in
/-- I1c. Coordinates are nonnegative (used only to keep the two-point
    witness computation explicit; if a cleaner normalization serves,
    restate and report). -/
theorem kConstraintVec_nonneg (P₀ : Set κ) (hP : P₀.Countable) (α : κ) :
    0 ≤ (kConstraintVec P₀ hP : ∀ _ : κ, ℝ) α := by
  by_cases hα : α ∈ P₀
  · exact (kConstraintVec_pos hP hα).le
  · rw [kConstraintVec_eq_zero hP hα]

/-- The κ-witness subspace of a family of countable pieces. -/
noncomputable def Wk (h : ∀ i, (P i).Countable) : Submodule ℝ (Hk κ) :=
  ⨅ i, LinearMap.ker
    ((innerSL ℝ (kConstraintVec (P i) (h i)) : Hk κ →L[ℝ] ℝ) : Hk κ →ₗ[ℝ] ℝ)

omit [LinearOrder κ] in
/-- I1d. Membership characterization and closedness of `Wk`. -/
theorem mem_Wk_iff (h : ∀ i, (P i).Countable) (x : Hk κ) :
    x ∈ Wk P h ↔ ∀ i, inner (𝕜 := ℝ) x (kConstraintVec (P i) (h i)) = 0 := by
  simp only [Wk, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply]
  constructor
  · intro hx i
    rw [real_inner_comm]
    exact hx i
  · intro hx i
    rw [real_inner_comm]
    exact hx i

omit [LinearOrder κ] in
theorem isClosed_Wk (h : ∀ i, (P i).Countable) :
    IsClosed (Wk P h : Set (Hk κ)) := by
  have hset : (Wk P h : Set (Hk κ))
      = ⋂ i, {x : Hk κ | innerSL ℝ (kConstraintVec (P i) (h i)) x = 0} := by
    ext x
    simp only [SetLike.mem_coe, mem_Wk_iff, Set.mem_iInter, Set.mem_setOf_eq,
      innerSL_apply_apply]
    exact ⟨fun hx i => by rw [real_inner_comm]; exact hx i,
      fun hx i => by rw [real_inner_comm]; exact hx i⟩
  rw [hset]
  exact isClosed_iInter fun i =>
    isClosed_eq (innerSL ℝ (kConstraintVec (P i) (h i))).continuous continuous_const

omit [LinearOrder κ] in
/-- I2 (unadded). If the pieces cover κ, then no nonempty block sits inside
    `Wk`: a point `α` of `S` lies in some piece, and `evec α` pairs
    nontrivially with that piece's constraint vector. Consequently
    `Wk ∉ Φ(U)` for any (proper) ultrafilter. -/
theorem not_block_le_Wk (h : ∀ i, (P i).Countable)
    (hcover : (⋃ i, P i) = univ) {S : Set κ} (hS : S.Nonempty) :
    ¬ block S ≤ Wk P h := by
  haveI : LinearOrder κ := IsWellOrder.linearOrder (WellOrderingRel (α := κ))
  intro hle
  obtain ⟨α, hα⟩ := hS
  have hmem : evec α ∈ Wk P h := hle (evec_mem_block hα)
  have hcov : α ∈ ⋃ i, P i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ : ∃ i, α ∈ P i := by simpa using hcov
  have h0 := (mem_Wk_iff P h (evec α)).mp hmem i
  rw [real_inner_comm, inner_evec_right] at h0
  exact (kConstraintVec_pos (h i) hi).ne' h0

omit [LinearOrder κ] in
theorem Wk_notMem_PhiU (U : Ultrafilter κ) (h : ∀ i, (P i).Countable)
    (hcover : (⋃ i, P i) = univ) : Wk P h ∉ PhiU U := by
  rintro ⟨S, hSU, hS⟩
  exact not_block_le_Wk P h hcover (Filter.nonempty_of_mem hSU) hS

omit [LinearOrder κ] in
/-- I3, direction (⇒). If a block meets `Wk` trivially then its index set is
    a partial selector: two points `α ≠ β` of `S` inside one piece give the
    explicit two-point witness `c β • evec α − c α • evec β`, which is
    orthogonal to that piece's constraint by construction and to every other
    constraint by disjointness of the pieces — WO-1's C2 move at κ. -/
theorem selector_of_Wk_inf_block_eq_bot (h : ∀ i, (P i).Countable)
    (hdisj : Pairwise (Function.onFun Disjoint P)) {S : Set κ}
    (hbot : Wk P h ⊓ block S = ⊥) : PlufWO1.IsPartialSelector S P := by
  haveI : LinearOrder κ := IsWellOrder.linearOrder (WellOrderingRel (α := κ))
  intro i α hα β hβ
  by_contra hneαβ
  obtain ⟨hαS, hαP⟩ := hα
  obtain ⟨hβS, hβP⟩ := hβ
  set c : Hk κ := kConstraintVec (P i) (h i) with hc
  set v : Hk κ :=
    ((c : ∀ _ : κ, ℝ) β) • evec α - ((c : ∀ _ : κ, ℝ) α) • evec β with hv
  have hvapp : ∀ γ : κ, (v : ∀ _ : κ, ℝ) γ
      = ((c : ∀ _ : κ, ℝ) β) * (if γ = α then (1:ℝ) else 0)
        - ((c : ∀ _ : κ, ℝ) α) * (if γ = β then (1:ℝ) else 0) := by
    intro γ
    simp [hv, evec_apply]
  have hvblock : v ∈ block S := by
    rw [mem_block_iff]
    intro γ hγ
    rw [hvapp γ, if_neg (by rintro rfl; exact hγ hαS), if_neg (by rintro rfl; exact hγ hβS)]
    ring
  have hinner : ∀ j : ι, inner (𝕜 := ℝ) v (kConstraintVec (P j) (h j))
      = ((c : ∀ _ : κ, ℝ) β) * ((kConstraintVec (P j) (h j) : ∀ _ : κ, ℝ) α)
        - ((c : ∀ _ : κ, ℝ) α) * ((kConstraintVec (P j) (h j) : ∀ _ : κ, ℝ) β) := by
    intro j
    have e1 : inner (𝕜 := ℝ) (evec α) (kConstraintVec (P j) (h j))
        = (kConstraintVec (P j) (h j) : ∀ _ : κ, ℝ) α := by
      rw [real_inner_comm]; exact inner_evec_right _ _
    have e2 : inner (𝕜 := ℝ) (evec β) (kConstraintVec (P j) (h j))
        = (kConstraintVec (P j) (h j) : ∀ _ : κ, ℝ) β := by
      rw [real_inner_comm]; exact inner_evec_right _ _
    simp only [hv, inner_sub_left, real_inner_smul_left, e1, e2]
  have hvW : v ∈ Wk P h := by
    rw [mem_Wk_iff]
    intro j
    rw [hinner j]
    rcases eq_or_ne j i with rfl | hji
    · rw [← hc]; ring
    · have hαj : α ∉ P j := fun hm => Set.disjoint_left.mp (hdisj hji) hm hαP
      have hβj : β ∉ P j := fun hm => Set.disjoint_left.mp (hdisj hji) hm hβP
      rw [kConstraintVec_eq_zero (h j) hαj, kConstraintVec_eq_zero (h j) hβj]
      ring
  have hv0 : v = 0 := by
    have : v ∈ (⊥ : Submodule ℝ (Hk κ)) := by rw [← hbot]; exact ⟨hvW, hvblock⟩
    simpa using this
  have hcoord : (v : ∀ _ : κ, ℝ) α = 0 := by rw [hv0]; rfl
  rw [hvapp α, if_pos rfl, if_neg hneαβ] at hcoord
  have : (c : ∀ _ : κ, ℝ) β = 0 := by linarith [hcoord]
  exact (kConstraintVec_pos (h i) hβP).ne' this

omit [LinearOrder κ] in
/-- I3, direction (⇐). If the pieces cover `κ` and `S` is a partial selector,
    then the block of `S` meets `Wk` trivially: a nonzero coordinate `α` of a
    vector of the intersection lies in a piece `P i`, and the constraint of
    that piece has a single surviving term `x α * c α ≠ 0`. -/
theorem Wk_inf_block_eq_bot_of_selector (h : ∀ i, (P i).Countable)
    (hcover : (⋃ i, P i) = univ) {S : Set κ}
    (hsel : PlufWO1.IsPartialSelector S P) : Wk P h ⊓ block S = ⊥ := by
  haveI : LinearOrder κ := IsWellOrder.linearOrder (WellOrderingRel (α := κ))
  rw [eq_bot_iff]
  rintro x ⟨hxW, hxB⟩
  rw [Submodule.mem_bot]
  have hall : ∀ α : κ, (x : ∀ _ : κ, ℝ) α = 0 := by
    intro α
    by_contra hxα
    have hαS : α ∈ S := by
      by_contra hαS
      exact hxα ((mem_block_iff S x).mp hxB α hαS)
    have hcov : α ∈ ⋃ i, P i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ : ∃ i, α ∈ P i := by simpa using hcov
    set c : Hk κ := kConstraintVec (P i) (h i) with hc
    have hexp := hasSum_coord_smul (innerSL ℝ c) x
    have hterm : ∀ β : κ, (x : ∀ _ : κ, ℝ) β * (innerSL ℝ c) (evec β)
        = (x : ∀ _ : κ, ℝ) β * (c : ∀ _ : κ, ℝ) β := by
      intro β
      rw [innerSL_apply_apply, inner_evec_right]
    rw [funext hterm] at hexp
    have hzero : ∀ β : κ, β ≠ α → (x : ∀ _ : κ, ℝ) β * (c : ∀ _ : κ, ℝ) β = 0 := by
      intro β hβ
      by_cases hxβ : (x : ∀ _ : κ, ℝ) β = 0
      · rw [hxβ, zero_mul]
      by_cases hcβ : β ∈ P i
      · have hβS : β ∈ S := by
          by_contra hβS
          exact hxβ ((mem_block_iff S x).mp hxB β hβS)
        exact absurd (hsel i ⟨hβS, hcβ⟩ ⟨hαS, hi⟩) hβ
      · rw [hc, kConstraintVec_eq_zero (h i) hcβ, mul_zero]
    have hsingle := hasSum_single (f := fun β : κ => (x : ∀ _ : κ, ℝ) β * (c : ∀ _ : κ, ℝ) β)
      α hzero
    have hval := hexp.unique hsingle
    have hzeroinner : (innerSL ℝ c) x = 0 := by
      rw [innerSL_apply_apply, real_inner_comm]
      exact (mem_Wk_iff P h x).mp hxW i
    rw [hzeroinner] at hval
    exact hxα ((mul_eq_zero.mp hval.symm).resolve_right (kConstraintVec_pos (h i) hi).ne')
  exact lp.ext (funext hall)

/-  REPORT (I3).  The contract statement of I3,

      theorem Wk_inf_block_eq_bot_iff (h : ∀ i, (P i).Countable)
          (hdisj : Pairwise (Function.onFun Disjoint P))
          (hne : ∀ i, (P i).Nonempty) (S : Set κ) :
          Wk P h ⊓ block S = ⊥ ↔ PlufWO1.IsPartialSelector S P

  is FALSE as written: without the covering hypothesis the direction (⇐)
  fails.  Counterexample (formalized as `Wk_inf_block_eq_bot_iff_counterexample`
  below): `κ = ℕ`, `ι = Unit`, `P _ = {0}` (countable, nonempty, trivially
  pairwise disjoint) and `S = {1}`.  Then `S ∩ P i = ∅` is a subsingleton, so
  `S` is a partial selector, while `evec 1` is a nonzero vector lying in both
  `block S` and `Wk P h` (its only nonzero coordinate, at `1`, is off `P i`),
  so `Wk P h ⊓ block S ≠ ⊥`.

  The statement is repaired below by adding `(hcover : (⋃ i, P i) = univ)`,
  which is available at every use site (in particular in I4).  With the cover
  present, `hne` is not needed for either direction; it is kept because the
  contract asks for it.  -/
omit [LinearOrder κ] in
/-- I3 (blocking characterized; repaired statement, see the report above).
    For pairwise disjoint pieces covering `κ`, a block meets `Wk` trivially
    exactly when its index set is a partial selector.

    (⇐) On a selector, each piece contributes at most one coordinate, and
    the single surviving term of each constraint kills it.
    (⇒) Two points of `S` in one piece give the explicit two-point witness
    `c_β • evec α − c_α • evec β` (coefficients read off the constraint
    vector), orthogonal to that piece's constraint by construction and to
    every other constraint by disjoint supports — WO-1's C2 move at κ.

    The hypothesis `hne` is unused. -/
theorem Wk_inf_block_eq_bot_iff (h : ∀ i, (P i).Countable)
    (hdisj : Pairwise (Function.onFun Disjoint P))
    (hne : ∀ i, (P i).Nonempty) (hcover : (⋃ i, P i) = univ) (S : Set κ) :
    Wk P h ⊓ block S = ⊥ ↔ PlufWO1.IsPartialSelector S P :=
  ⟨fun hbot => selector_of_Wk_inf_block_eq_bot P h hdisj hbot,
    fun hsel => Wk_inf_block_eq_bot_of_selector P h hcover hsel⟩

omit [LinearOrder κ] in
/-- I4 (the κ-witness; Paper III, Proposition 5.3, Hilbert half). If no
    set of `U` is a partial selector of a partition of κ into countable
    nonempty pieces, then the witness subspace is unadded yet meets every
    member of Φ(U) nontrivially — the negation, via the maximality
    criterion, of maximality of the block filter.

    The hypothesis `hne` is unused (only disjointness and the cover enter);
    it is retained because the contract asks for it. -/
theorem kappa_witness (U : Ultrafilter κ) (h : ∀ i, (P i).Countable)
    (hdisj : Pairwise (Function.onFun Disjoint P))
    (hne : ∀ i, (P i).Nonempty) (hcover : (⋃ i, P i) = univ)
    (hsel : ∀ S ∈ U, ¬ PlufWO1.IsPartialSelector S P) :
    Wk P h ∉ PhiU U ∧ ∀ M ∈ PhiU U, Wk P h ⊓ M ≠ ⊥ := by
  refine ⟨Wk_notMem_PhiU P U h hcover, ?_⟩
  rintro M ⟨S, hSU, hSM⟩ hbot
  have hbot' : Wk P h ⊓ block S = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left (Wk P h) hSM) (le_of_eq hbot))
  exact hsel S hSU (selector_of_Wk_inf_block_eq_bot P h hdisj hbot')

end Witness

/-! ### Report: the covering hypothesis in I3 is necessary -/

/-- The contract statement of I3 without a covering hypothesis is false:
    with `κ = ℕ`, a single piece `P _ = {0}` and `S = {1}`, the set `S` is a
    partial selector while `Wk P h ⊓ block S ≠ ⊥` (it contains `evec 1`). -/
theorem Wk_inf_block_eq_bot_iff_counterexample :
    ∃ (ι : Type) (P : ι → Set ℕ) (h : ∀ i, (P i).Countable) (S : Set ℕ),
      Pairwise (Function.onFun Disjoint P) ∧ (∀ i, (P i).Nonempty) ∧
      PlufWO1.IsPartialSelector S P ∧ Wk P h ⊓ block S ≠ ⊥ := by
  classical
  refine ⟨Unit, fun _ => ({0} : Set ℕ), fun _ => Set.countable_singleton 0, ({1} : Set ℕ),
    ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · exact fun _ => Set.singleton_nonempty 0
  · intro i a ha b _
    exfalso
    have h1 : a = 1 := ha.1
    have h0 : a = 0 := ha.2
    omega
  · intro hbot
    have hmemW : evec (1 : ℕ) ∈ Wk (fun _ : Unit => ({0} : Set ℕ))
        (fun _ => Set.countable_singleton 0) := by
      rw [mem_Wk_iff]
      intro i
      rw [real_inner_comm, inner_evec_right,
        kConstraintVec_eq_zero (Set.countable_singleton 0) (by norm_num)]
    have hmemB : evec (1 : ℕ) ∈ block ({1} : Set ℕ) := evec_mem_block rfl
    have h0 : evec (1 : ℕ) ∈ (⊥ : Submodule ℝ (Hk ℕ)) := by
      rw [← hbot]; exact ⟨hmemW, hmemB⟩
    rw [Submodule.mem_bot] at h0
    have : (evec (1:ℕ) : ∀ _ : ℕ, ℝ) 1 = 0 := by rw [h0]; rfl
    rw [evec_apply, if_pos rfl] at this
    exact one_ne_zero this

/-! ### Axiom audit for the WO-3 contract theorems
(The WO-1 and WO-2 audits run via the import chain.) -/

#print axioms exists_ulim              -- G1
#print axioms quadratic_flat           -- G2
#print axioms PhiU_upward              -- H1
#print axioms inf_mem_PhiU             -- H1
#print axioms bot_notMem_PhiU          -- H1
#print axioms iInf_mem_PhiU            -- H2
#print axioms PhiU_nonprincipal        -- H3
#print axioms PhiU_decides             -- H4
#print axioms supp_kConstraintVec      -- I1
#print axioms mem_Wk_iff               -- I1
#print axioms isClosed_Wk              -- I1
#print axioms Wk_notMem_PhiU           -- I2
#print axioms Wk_inf_block_eq_bot_iff  -- I3
#print axioms kappa_witness            -- I4

-- report item: the counterexample showing the covering hypothesis of I3 is needed
#print axioms Wk_inf_block_eq_bot_iff_counterexample

end PlufWO3
