/-
  PlufWO5/PartE.lean — Work Order 5, Part E: diagonalization
  (Paper II, Theorem 5.1/5.2 and Corollary 5.2(a)/5.3(a)), stated against
  a package of lattice facts consumed from Paper I.
-/
import RequestProject.PlufWO5.PartB

open Set

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO5

open PlufWO1

noncomputable section

section Diagonal

/-- The package of lattice facts consumed from the companion paper. -/
structure PlufPackage (π : Set (Submodule ℝ H)) : Prop where
  mem_closed : ∀ M ∈ π, IsClosed (M : Set H)
  upward : ∀ M ∈ π, ∀ N : Submodule ℝ H, IsClosed (N : Set H) → M ≤ N → N ∈ π
  inf_mem : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π
  proper : (⊥ : Submodule ℝ H) ∉ π
  finCodim_mem : ∀ M : Submodule ℝ H, IsClosed (M : Set H) →
    Module.Finite ℝ ↥Mᗮ → M ∈ π
  decides : ∀ M : Submodule ℝ H, IsClosed (M : Set H) →
    M ∈ π ∨ ∃ N ∈ π, M ⊓ N = ⊥

/-- Intimacy for the standard basis. -/
def Intimate (M : Submodule ℝ H) : Prop :=
  ∀ A : Set ℕ, M ⊓ block A ≠ ⊥ ∨ M ⊓ block Aᶜ ≠ ⊥

/-- E1 (Theorem 5.1). A package family is diagonalizable — its block
    trace is an ultrafilter — iff every member is intimate. -/
theorem diagonalizable_iff_intimate (π : Set (Submodule ℝ H))
    (hπ : PlufPackage π) :
    (∃ V : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ V ↔ block S ∈ π) ↔
      (∀ M ∈ π, Intimate M) := by
  constructor
  · rintro ⟨V, hV⟩ M hM A
    rcases V.mem_or_compl_mem A with hA | hA
    · refine Or.inl (fun hbot => hπ.proper ?_)
      have := hπ.inf_mem M hM (block A) ((hV A).mp hA)
      rwa [hbot] at this
    · refine Or.inr (fun hbot => hπ.proper ?_)
      have := hπ.inf_mem M hM (block Aᶜ) ((hV Aᶜ).mp hA)
      rwa [hbot] at this
  · intro hint
    have htop : (⊤ : Submodule ℝ H) ∈ π := by
      refine hπ.finCodim_mem ⊤ (by simp) ?_
      rw [Submodule.top_orthogonal_eq_bot]
      infer_instance
    set F : Filter ℕ :=
      { sets := {S | block S ∈ π}
        univ_sets := by
          show block univ ∈ π
          rw [block_univ]
          exact htop
        sets_of_superset := by
          intro S T hS hST
          exact hπ.upward _ hS _ (isClosed_block T) (block_mono hST)
        inter_sets := by
          intro S T hS hT
          show block (S ∩ T) ∈ π
          rw [block_inter]
          exact hπ.inf_mem _ hS _ hT } with hF
    have hmemF : ∀ S : Set ℕ, S ∈ F ↔ block S ∈ π := fun _ => Iff.rfl
    have hdich : ∀ S : Set ℕ, block S ∈ π ∨ block Sᶜ ∈ π := by
      intro S
      by_contra hcon
      push_neg at hcon
      obtain ⟨N, hN, hNbot⟩ := (hπ.decides (block S) (isClosed_block S)).resolve_left hcon.1
      obtain ⟨N', hN', hN'bot⟩ :=
        (hπ.decides (block Sᶜ) (isClosed_block Sᶜ)).resolve_left hcon.2
      have hMπ : N ⊓ N' ∈ π := hπ.inf_mem N hN N' hN'
      rcases hint (N ⊓ N') hMπ S with h | h
      · exact h (le_bot_iff.mp (le_trans (by
          exact inf_le_inf_right (block S) inf_le_left) (le_of_eq (by
            rw [inf_comm] at hNbot; exact hNbot))))
      · exact h (le_bot_iff.mp (le_trans (by
          exact inf_le_inf_right (block Sᶜ) inf_le_right) (le_of_eq (by
            rw [inf_comm] at hN'bot; exact hN'bot))))
    have hult : ∀ S : Set ℕ, Sᶜ ∉ F ↔ S ∈ F := by
      intro S
      constructor
      · intro h
        exact (hdich S).resolve_right (fun hc => h ((hmemF Sᶜ).mpr hc))
      · intro hS hSc
        refine hπ.proper ?_
        have := hπ.inf_mem _ ((hmemF S).mp hS) _ ((hmemF Sᶜ).mp hSc)
        rwa [← block_inter, inter_compl_self, block_empty] at this
    exact ⟨Ultrafilter.ofComplNotMemIff F hult, fun S => hmemF S⟩

/-  E2, contract statement, preserved verbatim:

theorem diagonalizable_iff_extends_phiOmega (π : Set (Submodule ℝ H))
    (hπ : PlufPackage π) :
    (∃ V : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ V ↔ block S ∈ π) ↔
      (∃ U : Ultrafilter ℕ, ∀ M : Submodule ℝ H, PhiOmega U M → M ∈ π)

    This form is not provable: every member of `π` is closed
    (`PlufPackage.mem_closed`), while for every ultrafilter `U` there are
    *non-closed* subspaces `M` with `PhiOmega U M` — see
    `exists_phiOmega_not_isClosed` below. Hence the right-hand side is
    false for every `π` satisfying the package axioms, and the forward
    implication would require the left-hand side to be false as well,
    i.e. that no package family is diagonalizable, which is not a
    theorem of this development (and is refuted by the companion paper's
    Corollary 5.3(a)). The marked minimal repair restricts the quantifier
    to closed subspaces, which is what the paper's proof uses. -/

/-- For every ultrafilter there is a non-closed subspace in `Φ(U)`; this is
    the obstruction to the contract form of E2. -/
theorem exists_phiOmega_not_isClosed (U : Ultrafilter ℕ) :
    ∃ M : Submodule ℝ H, PhiOmega U M ∧ ¬ IsClosed (M : Set H) := by
  classical
  obtain ⟨S, hSU, hTinf⟩ : ∃ S ∈ U, (Sᶜ : Set ℕ).Infinite := by
    by_cases h : {n : ℕ | Even n} ∈ U
    · refine ⟨_, h, Set.infinite_of_injective_forall_mem
        (f := fun i : ℕ => 2 * i + 1) (fun p q hpq => by simp only [] at hpq; omega) (fun i => ?_)⟩
      simp only [mem_compl_iff, mem_setOf_eq, Nat.not_even_iff_odd]
      exact ⟨i, rfl⟩
    · refine ⟨_, Ultrafilter.compl_mem_iff_notMem.mpr h, ?_⟩
      rw [compl_compl]
      exact Set.infinite_of_injective_forall_mem
        (f := fun i : ℕ => 2 * i) (fun p q hpq => by simp only [] at hpq; omega) (fun i => ⟨i, by ring⟩)
  set D : Submodule ℝ H := Submodule.span ℝ {v : H | ∃ n ∈ (Sᶜ : Set ℕ), v = evec n} with hD
  set M : Submodule ℝ H := block S ⊔ D with hM
  refine ⟨M, ⟨S, hSU, ⊤, by simp, by rw [Submodule.top_orthogonal_eq_bot]; infer_instance,
    by rw [hM, inf_top_eq]; exact le_sup_left⟩, ?_⟩
  intro hclosed
  -- every element of `D` has finite support
  have hfinsupp : ∀ d ∈ D, {n : ℕ | (d : ∀ _ : ℕ, ℝ) n ≠ 0}.Finite := by
    intro d hd
    rw [hD] at hd
    refine Submodule.span_induction (p := fun (v : H) _ => {n : ℕ | (v : ∀ _ : ℕ, ℝ) n ≠ 0}.Finite)
      ?_ ?_ ?_ ?_ hd
    · rintro v ⟨n, -, rfl⟩
      refine Set.Finite.subset (Set.finite_singleton n) (fun m hm => ?_)
      simp only [mem_setOf_eq, evec_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
        imp_false, Decidable.not_not] at hm
      exact hm
    · simp
    · intro u v _ _ hu hv
      refine Set.Finite.subset (hu.union hv) (fun m hm => ?_)
      simp only [mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at hm
      by_contra hcon
      simp only [mem_union, mem_setOf_eq, not_or, not_not] at hcon
      exact hm (by rw [hcon.1, hcon.2]; ring)
    · intro c v _ hv
      refine Set.Finite.subset hv (fun m hm => ?_)
      simp only [mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ne_eq,
        mul_eq_zero, not_or] at hm
      exact hm.2
  -- `M` has trivial orthogonal complement
  have horth : Mᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hcoord : ∀ n : ℕ, (z : ∀ _ : ℕ, ℝ) n = 0 := by
      intro n
      have hmem : evec n ∈ M := by
        rw [hM]
        by_cases hn : n ∈ S
        · exact Submodule.mem_sup_left (evec_mem_block hn)
        · exact Submodule.mem_sup_right (Submodule.subset_span ⟨n, hn, rfl⟩)
      have := hz (evec n) hmem
      rwa [inner_evec_left] at this
    exact lp.ext (funext hcoord)
  haveI : CompleteSpace ↥M := hclosed.completeSpace_coe
  have hMtop : M = ⊤ := by
    have := Submodule.orthogonal_orthogonal M
    rw [horth, Submodule.bot_orthogonal_eq_top] at this
    exact this.symm
  -- but the constraint vector of `Sᶜ` is not in `M`
  have hx : constraintVec (Sᶜ : Set ℕ) ∈ M := by rw [hMtop]; trivial
  rw [hM, Submodule.mem_sup] at hx
  obtain ⟨y, hy, d, hd, hyd⟩ := hx
  have hdcoord : ∀ n ∈ (Sᶜ : Set ℕ), (d : ∀ _ : ℕ, ℝ) n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n hn
    have h1 : (constraintVec (Sᶜ : Set ℕ) : ∀ _ : ℕ, ℝ) n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [constraintVec_apply, if_pos hn]
    have h2 : (y : ∀ _ : ℕ, ℝ) n = 0 := (mem_block_iff S y).mp hy n hn
    have h3 : ((y + d : H) : ∀ _ : ℕ, ℝ) n = (y : ∀ _ : ℕ, ℝ) n + (d : ∀ _ : ℕ, ℝ) n := rfl
    rw [← hyd, h3, h2, zero_add] at h1
    exact h1
  refine absurd (hfinsupp d hd) (Set.Infinite.mono (fun n hn => ?_) hTinf)
  simp only [mem_setOf_eq]
  rw [hdcoord n hn]
  positivity

/-- E2 (Corollary 5.2(a)), minimal repair: the quantifier on the right is
    restricted to closed subspaces (see the comment above). A package
    family is diagonalizable iff it contains the closed members of the
    block filter of some ultrafilter. -/
theorem diagonalizable_iff_extends_phiOmega (π : Set (Submodule ℝ H))
    (hπ : PlufPackage π) :
    (∃ V : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ V ↔ block S ∈ π) ↔
      (∃ U : Ultrafilter ℕ, ∀ M : Submodule ℝ H, IsClosed (M : Set H) →
        PhiOmega U M → M ∈ π) := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨V, fun M hMclosed ⟨S, hSU, N, hNclosed, hNfin, hle⟩ => ?_⟩
    have hSπ : block S ∈ π := (hV S).mp hSU
    have hNπ : N ∈ π := hπ.finCodim_mem N hNclosed hNfin
    exact hπ.upward _ (hπ.inf_mem _ hSπ _ hNπ) M hMclosed hle
  · rintro ⟨U, hU⟩
    refine ⟨U, fun S => ⟨fun hS => ?_, fun hS => ?_⟩⟩
    · refine hU (block S) (isClosed_block S) ⟨S, hS, ⊤, by simp, ?_, by simp⟩
      rw [Submodule.top_orthogonal_eq_bot]
      infer_instance
    · by_contra hSU
      have hSc : Sᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hSU
      have hScπ : block Sᶜ ∈ π := by
        refine hU (block Sᶜ) (isClosed_block Sᶜ) ⟨Sᶜ, hSc, ⊤, by simp, ?_, by simp⟩
        rw [Submodule.top_orthogonal_eq_bot]
        infer_instance
      refine hπ.proper ?_
      have := hπ.inf_mem _ hS _ hScπ
      rwa [← block_inter, inter_compl_self, block_empty] at this

end Diagonal

end

end PlufWO5
