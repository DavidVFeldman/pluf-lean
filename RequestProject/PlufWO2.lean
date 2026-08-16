/-
  PlufWO2.lean — Work Order 2 for the pluf project (Feldman–Wilce).

  Scope: the measurable-cardinal core of Paper III, in axiom-free form:
    (D) infrastructure — ℓ²(κ) for an arbitrary index type, countable
        supports, blocks and coordinate functionals at κ;
    (E) exact paving along an ultrafilter closed under diagonal
        intersections (Paper III, Theorem 2.1);
    (F) the exact dichotomy (Paper III, Theorem 3.1) and the
        maximality-shaped corollary.

  As in WO-1, NO large-cardinal machinery is axiomatized: diagonal
  intersections and smallness-of-countable-sets enter only as hypotheses,
  so every theorem below is a ZFC statement about arbitrary ultrafilters
  on a well-ordered type.

  Refactoring decision (WO items D2/D3): fresh κ-versions of `coordCLM`,
  `block`, `mem_block_iff`, `isClosed_block` are defined here in namespace
  `PlufWO2`, and WO-1's Part B is left untouched, so WO-1's sixteen
  theorems remain green verbatim.

  Section-variable decision: `[WellFoundedLT κ]` is unused throughout (only
  the linear order enters, through the strict order in `DiagInt`), so it is
  omitted from the statements, as licensed by the work order; `[LinearOrder
  κ]` is likewise omitted from the order-free Part D items.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.
-/
import RequestProject.PlufWO1

open Set

namespace PlufWO2

variable {κ : Type*} [LinearOrder κ]

/-- The ambient Hilbert space ℓ²(κ; ℝ). -/
abbrev Hk (κ : Type*) : Type _ := lp (fun _ : κ => ℝ) 2

/-- Standard basis vector. -/
noncomputable def evec (α : κ) : Hk κ := lp.single 2 α (1 : ℝ)

/-- Support of a vector of ℓ²(κ). -/
def supp (x : Hk κ) : Set κ := {α | (x : ∀ _ : κ, ℝ) α ≠ 0}

/-- `U` is closed under diagonal intersections (the combinatorial content of
    normality, taken as a hypothesis). -/
def DiagInt (U : Ultrafilter κ) : Prop :=
  ∀ X : κ → Set κ, (∀ α, X α ∈ U) → {β | ∀ α < β, β ∈ X α} ∈ U

omit [LinearOrder κ] in
/-- Countable sets are `U`-small (the combinatorial content of
    κ-completeness plus nonprincipality, for the uses below). -/
def CountableSmall (U : Ultrafilter κ) : Prop :=
  ∀ s : Set κ, s.Countable → sᶜ ∈ U

/-! ### Part D: infrastructure at κ -/

omit [LinearOrder κ] in
/-- D1. Every vector of ℓ²(κ) has countable support (Paper III uses this
    silently throughout; it is the entire reason the subject softens at κ).
    Route: `Memℓp` gives summability of the squared coordinates; summable
    families over ℝ have countable support. -/
theorem countable_supp (x : Hk κ) : (supp x).Countable := by
  have hsum : Summable (fun α : κ => ‖(x : ∀ _ : κ, ℝ) α‖ ^ (2:ℝ)) := by
    have := lp.memℓp x
    rw [memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ENNReal).toReal)] at this
    simpa using this
  have hsupp : supp x = Function.support (fun α : κ => ‖(x : ∀ _ : κ, ℝ) α‖ ^ (2:ℝ)) := by
    ext α
    simp [supp, Function.mem_support]
  rw [hsupp]
  exact hsum.countable_support

omit [LinearOrder κ] in
/-- Evaluation at a coordinate, as a linear map on `Hk κ`. -/
noncomputable def coordL (α : κ) : Hk κ →ₗ[ℝ] ℝ where
  toFun x := (x : ∀ _ : κ, ℝ) α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LinearOrder κ] in
@[simp] theorem coordL_apply (α : κ) (x : Hk κ) : coordL α x = (x : ∀ _ : κ, ℝ) α := rfl

omit [LinearOrder κ] in
/-- D2. Coordinate evaluation as a continuous linear functional on ℓ²(κ)
    (the κ-generalization of WO-1's `coordCLM`). -/
noncomputable def coordCLM (α : κ) : Hk κ →L[ℝ] ℝ :=
  (coordL α).mkContinuous 1 (by
    intro x
    simpa using lp.norm_apply_le_norm (p := 2) (by norm_num) x α)

omit [LinearOrder κ] in
@[simp] theorem coordCLM_apply (α : κ) (x : Hk κ) :
    coordCLM α x = (x : ∀ _ : κ, ℝ) α := rfl

omit [LinearOrder κ] in
/-- D3. The block of a set `S ⊆ κ`: the closed subspace of vectors
    supported in `S`, with the membership characterization and closedness
    (κ-generalization of WO-1's `block`, `mem_block_iff`, `isClosed_block`). -/
noncomputable def block (S : Set κ) : Submodule ℝ (Hk κ) :=
  ⨅ α ∈ Sᶜ, LinearMap.ker (coordL α)

omit [LinearOrder κ] in
theorem mem_block_iff (S : Set κ) (x : Hk κ) :
    x ∈ block S ↔ ∀ α ∉ S, (x : ∀ _ : κ, ℝ) α = 0 := by
  simp [block, Submodule.mem_iInf, LinearMap.mem_ker]

omit [LinearOrder κ] in
theorem isClosed_block (S : Set κ) : IsClosed (block S : Set (Hk κ)) := by
  have h : (block S : Set (Hk κ)) = ⋂ α ∈ Sᶜ, {x : Hk κ | coordCLM α x = 0} := by
    ext x
    simp [mem_block_iff]
  rw [h]
  exact isClosed_biInter fun α _ => isClosed_eq (coordCLM α).continuous continuous_const

@[simp] theorem evec_apply (α β : κ) :
    (evec α : ∀ _ : κ, ℝ) β = if β = α then (1:ℝ) else 0 := by
  rw [evec, lp.single_apply]
  by_cases h : β = α
  · subst h; simp
  · simp [h]

/-- D4. Blocks of basis vectors: `evec α ∈ block S` for `α ∈ S`. -/
theorem evec_mem_block {S : Set κ} {α : κ} (hα : α ∈ S) : evec α ∈ block S := by
  rw [mem_block_iff]
  intro β hβ
  rw [evec_apply, if_neg]
  rintro rfl
  exact hβ hα

/-- Basis vectors of a block, conversely: only for `α ∈ S`. -/
theorem evec_mem_block_iff (S : Set κ) (α : κ) : evec α ∈ block S ↔ α ∈ S := by
  refine ⟨fun h => ?_, evec_mem_block⟩
  by_contra hα
  have := (mem_block_iff S _).mp h α hα
  rw [evec_apply, if_pos rfl] at this
  exact one_ne_zero this

omit [LinearOrder κ] in
theorem block_mono {S T : Set κ} (h : S ⊆ T) : block S ≤ block T := by
  intro x hx
  rw [mem_block_iff] at hx ⊢
  exact fun α hα => hx α (fun hS => hα (h hS))

/-- Inner products against basis vectors read off coordinates. -/
theorem inner_evec_right (x : Hk κ) (α : κ) :
    inner (𝕜 := ℝ) x (evec α) = (x : ∀ _ : κ, ℝ) α := by
  rw [evec, lp.inner_single_right]
  simp

/-- The ℓ²-expansion of a vector along the standard basis, pushed through a
    continuous linear functional. -/
theorem hasSum_coord_smul (f : Hk κ →L[ℝ] ℝ) (x : Hk κ) :
    HasSum (fun β : κ => (x : ∀ _ : κ, ℝ) β * f (evec β)) (f x) := by
  classical
  have h := f.hasSum (lp.hasSum_single (E := fun _ : κ => ℝ) (p := 2) (by norm_num) x)
  have hterm : ∀ β : κ, f (lp.single 2 β ((x : ∀ _ : κ, ℝ) β))
      = (x : ∀ _ : κ, ℝ) β * f (evec β) := by
    intro β
    have h1 : lp.single (E := fun _ : κ => ℝ) 2 β ((x : ∀ _ : κ, ℝ) β)
        = ((x : ∀ _ : κ, ℝ) β) • evec β := by
      rw [evec, ← lp.single_smul]
      simp
    rw [h1, map_smul, smul_eq_mul]
  simpa only [hterm] using h

/-- The ℓ²-expansion of a vector along the standard basis. -/
theorem hasSum_evec_smul (x : Hk κ) :
    HasSum (fun β : κ => ((x : ∀ _ : κ, ℝ) β) • evec β) x := by
  classical
  have h := lp.hasSum_single (E := fun _ : κ => ℝ) (p := 2) (by norm_num) x
  have hterm : ∀ β : κ, lp.single (E := fun _ : κ => ℝ) 2 β ((x : ∀ _ : κ, ℝ) β)
      = ((x : ∀ _ : κ, ℝ) β) • evec β := by
    intro β
    rw [evec, ← lp.single_smul]
    simp
  simpa only [hterm] using h

/-! ### Part E: exact paving -/

/-- E1 (Exact paving; Paper III, Theorem 2.1). Along an ultrafilter closed
    under diagonal intersections and concentrating off countable sets, every
    bounded operator compresses to an exactly diagonal operator on a
    measure-one block: there is `S ∈ U` such that all off-diagonal matrix
    entries over `S` vanish.

    Proof (paper): for each `α` the set
    `c α = supp (T (evec α)) ∪ supp (T.adjoint (evec α))` is countable (D1),
    so `(c α)ᶜ ∈ U`; the diagonal intersection `S` of these complements lies
    in `U`, and for `α < β` in `S`, membership `β ∈ (c α)ᶜ` kills
    `⟪T (evec α), evec β⟫` directly and `⟪T (evec β), evec α⟫` through the
    adjoint. -/
theorem exact_paving (U : Ultrafilter κ) (hdiag : DiagInt U)
    (hsmall : CountableSmall U) (T : Hk κ →L[ℝ] Hk κ) :
    ∃ S ∈ U, ∀ α ∈ S, ∀ β ∈ S, α ≠ β →
      inner (𝕜 := ℝ) (T (evec α)) (evec β) = 0 := by
  classical
  set c : κ → Set κ := fun α =>
    supp (T (evec α)) ∪ supp ((ContinuousLinearMap.adjoint T) (evec α))
  have hcU : ∀ α, (c α)ᶜ ∈ U := fun α =>
    hsmall _ ((countable_supp _).union (countable_supp _))
  refine ⟨{β | ∀ α < β, β ∈ (c α)ᶜ}, hdiag (fun α => (c α)ᶜ) hcU, ?_⟩
  intro α hα β hβ hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmem : β ∈ (c α)ᶜ := hβ α h
    have h0 : (T (evec α) : ∀ _ : κ, ℝ) β = 0 := by
      by_contra hb
      exact hmem (Or.inl hb)
    rw [inner_evec_right]
    exact h0
  · have hmem : α ∈ (c β)ᶜ := hα β h
    have h0 : ((ContinuousLinearMap.adjoint T) (evec β) : ∀ _ : κ, ℝ) α = 0 := by
      by_contra hb
      exact hmem (Or.inr hb)
    have hadj : inner (𝕜 := ℝ) (T (evec α)) (evec β)
        = inner (𝕜 := ℝ) (evec α) ((ContinuousLinearMap.adjoint T) (evec β)) :=
      (ContinuousLinearMap.adjoint_inner_right T (evec α) (evec β)).symm
    rw [hadj, real_inner_comm, inner_evec_right]
    exact h0

/-! ### Part F: the exact dichotomy -/

/-- F1 (coordinate rigidity on a diagonalizing block). If the operator `P`
    has vanishing off-diagonal entries over `S` and `x` is supported in `S`,
    then `⟪P (evec α), x⟫ = x α * ⟪P (evec α), evec α⟫` for `α ∈ S`.  This is
    the route taken for F2: the coordinate-rigidity functional of WO-1's C1,
    rather than a `tsum` of squared norms. -/
theorem inner_eq_coord_mul (S : Set κ) (P : Hk κ →L[ℝ] Hk κ)
    (hoff : ∀ α ∈ S, ∀ β ∈ S, α ≠ β → inner (𝕜 := ℝ) (P (evec α)) (evec β) = 0)
    {x : Hk κ} (hx : x ∈ block S) {α : κ} (hα : α ∈ S) :
    inner (𝕜 := ℝ) (P (evec α)) x
      = (x : ∀ _ : κ, ℝ) α * inner (𝕜 := ℝ) (P (evec α)) (evec α) := by
  classical
  set f : Hk κ →L[ℝ] ℝ := innerSL ℝ (P (evec α)) with hf
  have h := hasSum_coord_smul f x
  have hzero : ∀ β : κ, β ≠ α → (x : ∀ _ : κ, ℝ) β * f (evec β) = 0 := by
    intro β hβ
    by_cases hβS : β ∈ S
    · have := hoff α hα β hβS (Ne.symm hβ)
      simp only [hf, innerSL_apply_apply]
      rw [this, mul_zero]
    · rw [(mem_block_iff S x).mp hx β hβS, zero_mul]
  have hsingle := hasSum_single (f := fun β : κ => (x : ∀ _ : κ, ℝ) β * f (evec β)) α hzero
  have := h.unique hsingle
  simpa only [hf, innerSL_apply_apply] using this

/-- A block whose basis vectors lie in a closed subspace is contained in
    that subspace. -/
theorem block_le_of_evec_mem (W : Submodule ℝ (Hk κ)) (hW : IsClosed (W : Set (Hk κ)))
    (S : Set κ) (hS : ∀ α ∈ S, evec α ∈ W) : block S ≤ W := by
  classical
  intro x hx
  have h := hasSum_evec_smul x
  have hmem : ∀ β : κ, ((x : ∀ _ : κ, ℝ) β) • evec β ∈ W := by
    intro β
    by_cases hβ : β ∈ S
    · exact W.smul_mem _ (hS β hβ)
    · rw [(mem_block_iff S x).mp hx β hβ, zero_smul]
      exact W.zero_mem
  refine hW.mem_of_tendsto h ?_
  filter_upwards with s
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- F2 (Exact dichotomy; Paper III, Theorem 3.1). For every closed subspace
    `W` of ℓ²(κ) there is `S ∈ U` with `block S ≤ W` or `W ⊓ block S = ⊥`.

    Proof: apply E1 to `P = P_{Wᗮ}` to get `S₀ ∈ U` diagonalizing `P`, and
    put `S₁ = {α ∈ S₀ | evec α ∈ W}`.  If `S₁ ∈ U`, then `block S₁ ≤ W`
    because `W` is closed and contains the basis vectors indexed by `S₁`.
    Otherwise `S₀ \ S₁ ∈ U`, and for `x ∈ W` supported in `S₀ \ S₁`,
    coordinate rigidity (F1) gives `0 = ⟪P (evec α), x⟫ = x α ‖P (evec α)‖²`
    with `P (evec α) ≠ 0` (as `evec α ∉ W = Wᗮᗮ`), so `x = 0`. -/
theorem exact_dichotomy (U : Ultrafilter κ) (hdiag : DiagInt U)
    (hsmall : CountableSmall U) (W : Submodule ℝ (Hk κ))
    (hW : IsClosed (W : Set (Hk κ))) :
    ∃ S ∈ U, block S ≤ W ∨ W ⊓ block S = ⊥ := by
  classical
  haveI : CompleteSpace W := hW.completeSpace_coe
  set P : Hk κ →L[ℝ] Hk κ := (Wᗮ).starProjection with hP
  obtain ⟨S₀, hS₀U, hoff⟩ := exact_paving U hdiag hsmall P
  set S₁ : Set κ := {α ∈ S₀ | evec α ∈ W}
  by_cases h1 : S₁ ∈ U
  · exact ⟨S₁, h1, Or.inl (block_le_of_evec_mem W hW S₁ (fun _ hα => hα.2))⟩
  · have h2 : S₀ \ S₁ ∈ U := by
      have hc : S₁ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr h1
      have hi : S₀ ∩ S₁ᶜ ∈ U := Filter.inter_mem hS₀U hc
      rwa [← Set.diff_eq] at hi
    refine ⟨S₀ \ S₁, h2, Or.inr ?_⟩
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxB⟩
    have hxB0 : x ∈ block S₀ := block_mono Set.diff_subset hxB
    have hall : ∀ α : κ, (x : ∀ _ : κ, ℝ) α = 0 := by
      intro α
      by_cases hα : α ∈ S₀ \ S₁
      · have hnW : evec α ∉ W := fun hm => hα.2 ⟨hα.1, hm⟩
        have key := inner_eq_coord_mul S₀ P hoff hxB0 hα.1
        -- the left-hand side vanishes: `P (evec α) ∈ Wᗮ` and `x ∈ W`
        have hleft : inner (𝕜 := ℝ) (P (evec α)) x = 0 := by
          have hmemo : P (evec α) ∈ Wᗮ := Submodule.starProjection_apply_mem _ _
          have := (Submodule.mem_orthogonal W (P (evec α))).mp hmemo x hxW
          rw [real_inner_comm]
          exact this
        -- the diagonal entry is `‖P (evec α)‖² ≠ 0`
        have hdiagv : inner (𝕜 := ℝ) (P (evec α)) (evec α)
            = inner (𝕜 := ℝ) (P (evec α)) (P (evec α)) := by
          have hsub : evec α - P (evec α) ∈ (Wᗮ)ᗮ :=
            Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) (evec α)
          have hz : inner (𝕜 := ℝ) (P (evec α)) (evec α - P (evec α)) = 0 :=
            (Submodule.mem_orthogonal (Wᗮ) _).mp hsub _ (Submodule.starProjection_apply_mem _ _)
          rw [inner_sub_right] at hz
          linarith
        have hPne : P (evec α) ≠ 0 := by
          intro h0
          rw [hP, Submodule.starProjection_apply_eq_zero_iff,
            Submodule.orthogonal_orthogonal] at h0
          exact hnW h0
        have hpos : inner (𝕜 := ℝ) (P (evec α)) (P (evec α)) ≠ 0 := by
          simpa [inner_self_eq_zero] using hPne
        rw [hleft, hdiagv] at key
        exact (mul_eq_zero.mp key.symm).resolve_right hpos
      · exact (mem_block_iff _ x).mp hxB α hα
    have hx0 : x = 0 := lp.ext (funext hall)
    simpa using hx0

/-- F3 (maximality-shaped corollary; Paper III, Corollary 3.2, lattice
    half). Every closed subspace is decided by the block family of `U`:
    either it contains a measure-one block, or a measure-one block meets it
    trivially.  This is what \cite{FWI}, Lemma 2.1 consumes to conclude that
    the block filter is a pluf. -/
theorem block_filter_decides (U : Ultrafilter κ) (hdiag : DiagInt U)
    (hsmall : CountableSmall U) (W : Submodule ℝ (Hk κ))
    (hW : IsClosed (W : Set (Hk κ))) :
    (∃ S ∈ U, block S ≤ W) ∨ (∃ S ∈ U, W ⊓ block S = ⊥) := by
  rcases exact_dichotomy U hdiag hsmall W hW with ⟨S, hSU, h | h⟩
  · exact Or.inl ⟨S, hSU, h⟩
  · exact Or.inr ⟨S, hSU, h⟩

/-! ### Axiom audit for the WO-2 contract theorems

(The WO-1 audit is in `RequestProject.PlufWO1`, imported above, so building
this file re-runs both.) -/

#print axioms countable_supp        -- D1
#print axioms coordCLM_apply        -- D2
#print axioms mem_block_iff         -- D3
#print axioms isClosed_block        -- D3
#print axioms evec_mem_block        -- D4
#print axioms exact_paving          -- E1
#print axioms exact_dichotomy       -- F2
#print axioms block_filter_decides  -- F3

end PlufWO2
