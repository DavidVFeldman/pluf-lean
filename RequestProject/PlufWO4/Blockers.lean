/-
  PlufWO4/Blockers.lean — Work Order 4, Part D: constraints on addable
  blockers at ℕ (Paper IV, Section 6): generalized thinness, the support
  lemma, and the Baire piece-spread lemma.
-/
import RequestProject.PlufWO4.EPP

open Set
open scoped Cardinal

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO4

/-! ### Part D: constraints on blockers at ℕ (Paper IV, Section 6) -/

section Blockers

open PlufWO1

-- Ambient: the WO-1 Part B setting — `H := lp (fun _ : ℕ => ℝ) 2`, the
-- partition `A : ℕ → Set ℕ`, constraint vectors and the witness `W A`.

/-- D1 (Generalized thinness; Paper IV, Lemma 6.1). A subspace meeting
    `W A` trivially meets the block of finitely many pieces in rank at
    most the number of pieces. `F.card` functionals cut codimension at
    most `F.card`; a surviving vector is orthogonal to the remaining
    constraints by disjoint supports, hence lies in `R ⊓ W A = ⊥`.
    (WO-1's `thin` is the case of a singleton.) -/
theorem gen_thin (A : ℕ → Set ℕ)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (R : Submodule ℝ PlufWO1.H) (hRW : R ⊓ PlufWO1.W A = ⊥)
    (F : Finset ℕ) :
    Module.rank ℝ ↥(R ⊓ PlufWO1.block (⋃ k ∈ F, A k)) ≤ F.card := by
  classical
  set K : Submodule ℝ PlufWO1.H := R ⊓ PlufWO1.block (⋃ k ∈ F, A k) with hK
  set f : ↥K →ₗ[ℝ] (F → ℝ) :=
    LinearMap.pi (fun k : F =>
      ((innerSL ℝ (PlufWO1.constraintVec (A (k : ℕ))) : PlufWO1.H →L[ℝ] ℝ) :
        PlufWO1.H →ₗ[ℝ] ℝ).comp (Submodule.subtype K)) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxR, hxB⟩ hker
    have hcoord : ∀ k ∈ F, inner (𝕜 := ℝ) x (PlufWO1.constraintVec (A k)) = 0 := by
      intro k hkF
      have : f ⟨x, hxR, hxB⟩ ⟨k, hkF⟩ = 0 := by
        rw [show f ⟨x, hxR, hxB⟩ = 0 from hker]
        rfl
      simp only [hf, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply, Submodule.coe_subtype] at this
      rw [real_inner_comm]
      exact this
    have hxW : x ∈ PlufWO1.W A := by
      rw [PlufWO1.mem_W_iff]
      intro j
      by_cases hjF : j ∈ F
      · exact hcoord j hjF
      · refine PlufWO1.inner_constraintVec_eq_zero_of_disjoint ?_ hxB
        rw [Set.disjoint_right]
        intro n hn hnj
        simp only [Set.mem_iUnion, exists_prop] at hn
        obtain ⟨k, hkF, hnk⟩ := hn
        have hkj : k ≠ j := fun h => hjF (h ▸ hkF)
        exact Set.disjoint_left.mp (hdisj hkj) hnk hnj
    have hmem : x ∈ R ⊓ PlufWO1.W A := ⟨hxR, hxW⟩
    rw [hRW] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hrank := LinearMap.rank_le_of_injective f hinj
  have hfun : Module.rank ℝ (F → ℝ) = (F.card : Cardinal) := by
    rw [rank_fun']
    simp
  rw [hfun] at hrank
  exact hrank

/-- D2a (ultrafilter glue). For an ultrafilter containing the cofinite
    filter, a set meets every member in an infinite set iff it is a
    member. -/
theorem inter_infinite_iff_mem (U : Ultrafilter ℕ)
    (hcof : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U) (T : Set ℕ) :
    (∀ S ∈ U, (T ∩ S).Infinite) ↔ T ∈ U := by
  constructor
  · intro h
    by_contra hT
    have hTc : Tᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hT
    have := h Tᶜ hTc
    rw [Set.inter_compl_self] at this
    exact this.nonempty.ne_empty rfl
  · intro hT S hS
    have hTS : T ∩ S ∈ U := Filter.inter_mem hT hS
    intro hfin
    -- a finite member of `U` is impossible: its complement is a finite
    -- intersection of complements of singletons, hence in `U`
    have hcompl : (T ∩ S)ᶜ ∈ U := by
      have hrepr : (T ∩ S)ᶜ = ⋂ n ∈ hfin.toFinset, ({n}ᶜ : Set ℕ) := by
        ext m
        constructor
        · intro hm
          refine Set.mem_iInter₂.mpr ?_
          intro i hi
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          rintro rfl
          exact hm (hfin.mem_toFinset.mp hi)
        · intro hm hmTS
          exact Set.mem_iInter₂.mp hm m (hfin.mem_toFinset.mpr hmTS) rfl
      rw [hrepr]
      exact (Filter.biInter_finset_mem _).mpr (fun n _ => hcof n)
    exact U.empty_notMem (by simpa using Filter.inter_mem hTS hcompl)

/-- D2b (rank of a finite block). -/
theorem rank_le_of_le_block_finite {T : Set ℕ} (hT : T.Finite)
    (R : Submodule ℝ PlufWO1.H) (hR : R ≤ PlufWO1.block T) :
    Module.rank ℝ ↥R ≤ hT.toFinset.card := by
  classical
  set f : ↥R →ₗ[ℝ] (hT.toFinset → ℝ) :=
    LinearMap.pi (fun n : hT.toFinset =>
      (PlufWO1.coordL (n : ℕ)).comp (Submodule.subtype R)) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxR⟩ hker
    have hall : ∀ n : ℕ, (x : ∀ _ : ℕ, ℝ) n = 0 := by
      intro n
      by_cases hn : n ∈ T
      · have hmem : n ∈ hT.toFinset := hT.mem_toFinset.mpr hn
        have : f ⟨x, hxR⟩ ⟨n, hmem⟩ = 0 := by
          rw [show f ⟨x, hxR⟩ = 0 from hker]
          rfl
        simpa [hf] using this
      · exact (PlufWO1.mem_block_iff T x).mp (hR hxR) n hn
    exact Subtype.ext (lp.ext (funext hall))
  have hrank := LinearMap.rank_le_of_injective f hinj
  have hfun : Module.rank ℝ (hT.toFinset → ℝ) = (hT.toFinset.card : Cardinal) := by
    rw [rank_fun']
    simp
  rw [hfun] at hrank
  exact hrank

/-- D2 (Support lemma; Paper IV, Lemma 6.2). If every vector of `R` is
    supported in `T`, and for every `S ∈ U` the space `R ⊓ block S` has
    infinite rank, then `T ∈ U`. (Contrapositive: otherwise `Tᶜ ∈ U`, and
    `R ⊓ block Tᶜ = ⊥` has rank `0 < ℵ₀`.)

    Note: the contract hypothesis `hcof` is retained as stated, but the
    contrapositive above needs no cofiniteness — the witness `S = Tᶜ` meets
    `R` in `⊥`, not merely in a finite-dimensional space, so D2a and D2b
    (which are the contract's suggested route, and are proved separately
    above) are not consumed here. -/
theorem support_mem (U : Ultrafilter ℕ)
    (hcof : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U)
    (R : Submodule ℝ PlufWO1.H) (T : Set ℕ)
    (hsupp : ∀ x ∈ R, ∀ n ∉ T, (x : ∀ _ : ℕ, ℝ) n = 0)
    (hbig : ∀ S ∈ U, ¬ Module.rank ℝ ↥(R ⊓ PlufWO1.block S) < ℵ₀) :
    T ∈ U := by
  by_contra hT
  have hTc : Tᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hT
  have hbot : R ⊓ PlufWO1.block Tᶜ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxR, hxB⟩
    have hall : ∀ n : ℕ, (x : ∀ _ : ℕ, ℝ) n = 0 := by
      intro n
      by_cases hn : n ∈ T
      · exact (PlufWO1.mem_block_iff Tᶜ x).mp hxB n (by simpa using hn)
      · exact hsupp x hxR n hn
    exact lp.ext (funext hall)
  refine hbig Tᶜ hTc ?_
  rw [hbot]
  simpa using Cardinal.aleph0_pos

/-- D3 (Baire piece-spread; Paper IV, Lemma 6.3). If `R` is closed with
    `R ⊓ W A = ⊥` and `R ⊓ block S` has infinite rank, then it contains a
    vector whose piece-spread `{k | ∃ n ∈ A k, x n ≠ 0}` is infinite.

    Inside the complete space `R ⊓ block S`, the vectors of piece-spread
    inside a fixed finite `F` form the closed subspace cut out by
    `block (⋃ k ∈ F, A k)`, of rank at most `F.card` by D1 (`gen_thin`),
    hence proper, hence of empty interior
    (`Submodule.eq_top_of_nonempty_interior'`); the finite-spread vectors
    are the countable union over `F : Finset ℕ`, and Baire category leaves
    a vector outside. -/
theorem baire_spread (A : ℕ → Set ℕ)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : (⋃ k, A k) = univ)
    (R : Submodule ℝ PlufWO1.H) (hRcl : IsClosed (R : Set PlufWO1.H))
    (hRW : R ⊓ PlufWO1.W A = ⊥) (S : Set ℕ)
    (hbig : ¬ Module.rank ℝ ↥(R ⊓ PlufWO1.block S) < ℵ₀) :
    ∃ x ∈ R ⊓ PlufWO1.block S, {k | ∃ n ∈ A k, (x : ∀ _ : ℕ, ℝ) n ≠ 0}.Infinite := by
  classical
  by_contra hcon
  push_neg at hcon
  set K : Submodule ℝ PlufWO1.H := R ⊓ PlufWO1.block S with hK
  have hKcl : IsClosed (K : Set PlufWO1.H) := by
    rw [hK, Submodule.coe_inf]
    exact hRcl.inter (PlufWO1.isClosed_block S)
  haveI : CompleteSpace ↥K := hKcl.completeSpace_coe
  haveI : BaireSpace ↥K := BaireSpace.of_completelyPseudoMetrizable
  -- the finite-spread pieces, as closed subspaces of `K`
  set C : Finset ℕ → Submodule ℝ ↥K :=
    fun F => (PlufWO1.block (⋃ k ∈ F, A k)).comap (Submodule.subtype K) with hC
  have hCclosed : ∀ F : Finset ℕ, IsClosed ((C F : Submodule ℝ ↥K) : Set ↥K) := by
    intro F
    have : ((C F : Submodule ℝ ↥K) : Set ↥K)
        = Subtype.val ⁻¹' ((PlufWO1.block (⋃ k ∈ F, A k) : Submodule ℝ PlufWO1.H) :
            Set PlufWO1.H) := rfl
    rw [this]
    exact (PlufWO1.isClosed_block _).preimage continuous_subtype_val
  have hcov : (⋃ F : Finset ℕ, ((C F : Submodule ℝ ↥K) : Set ↥K)) = univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hfin : {k | ∃ n ∈ A k, ((x : PlufWO1.H) : ∀ _ : ℕ, ℝ) n ≠ 0}.Finite :=
      hcon (x : PlufWO1.H) x.2
    refine ⟨hfin.toFinset, ?_⟩
    show (x : PlufWO1.H) ∈ PlufWO1.block (⋃ k ∈ hfin.toFinset, A k)
    rw [PlufWO1.mem_block_iff]
    intro n hn
    by_contra hxn
    have hncov : n ∈ (⋃ k, A k) := by rw [hcover]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hncov
    have hkspread : k ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨n, hk, hxn⟩
    exact hn (Set.mem_biUnion hkspread hk)
  obtain ⟨F, hF⟩ := nonempty_interior_of_iUnion_of_closed hCclosed hcov
  have hCtop : C F = ⊤ := Submodule.eq_top_of_nonempty_interior' _ hF
  -- then `K` is contained in the block of the finitely many pieces
  have hKle : K ≤ R ⊓ PlufWO1.block (⋃ k ∈ F, A k) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have : (⟨x, hx⟩ : ↥K) ∈ C F := by rw [hCtop]; trivial
    exact this
  have hrank : Module.rank ℝ ↥K ≤ (F.card : Cardinal) :=
    le_trans (Submodule.rank_mono hKle) (gen_thin A hdisj R hRW F)
  exact hbig (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)

end Blockers

end PlufWO4
