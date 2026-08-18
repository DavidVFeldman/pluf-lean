/-
  PlufWO12/Basic.lean — shared infrastructure for Work Order 12.

  Small lattice/dimension/topology facts about closed subspaces of
  `PlufWO1.H` that Parts A and B both use:

    * finite meets of closed subspaces are closed;
    * infinite-dimensionality is inherited upwards;
    * the "room" principle: cutting an infinite-dimensional subspace by
      the orthogonal complement of a finite-dimensional subspace leaves
      an infinite-dimensional subspace;
    * an infinite orthonormal family inside a subspace certifies that the
      subspace is infinite-dimensional.
-/
import RequestProject.PlufWO11
import RequestProject.PlufWO13

open Set

namespace PlufWO12

abbrev H := PlufWO1.H

/-! ### Dimension bookkeeping -/

/-- Infinite-dimensionality passes to larger subspaces. -/
theorem not_finiteDimensional_mono {M M' : Submodule ℝ H} (hle : M ≤ M')
    (hM : ¬ FiniteDimensional ℝ ↥M) : ¬ FiniteDimensional ℝ ↥M' := by
  intro hM'
  exact hM (Submodule.finiteDimensional_of_le hle)

/-- The room principle, in positive form: if `M ⊓ Wᗮ` is finite-dimensional
    and `W` is finite-dimensional, then `M` is finite-dimensional. -/
theorem finiteDimensional_of_inf_orthogonal {M W : Submodule ℝ H}
    (hW : FiniteDimensional ℝ ↥W) (hfin : FiniteDimensional ℝ ↥(M ⊓ Wᗮ)) :
    FiniteDimensional ℝ ↥M := by
  haveI : CompleteSpace ↥W := FiniteDimensional.complete ℝ W
  set g : ↥M →ₗ[ℝ] H := (W.starProjection : H →L[ℝ] H).toLinearMap.comp M.subtype with hg
  have hmem : ∀ v : H, W.starProjection v = 0 ↔ v ∈ Wᗮ := by
    intro v
    rw [← Submodule.ker_starProjection (𝕜 := ℝ) W]
    rfl
  have hker : LinearMap.ker g = Submodule.comap M.subtype (M ⊓ Wᗮ) := by
    ext x
    simp only [hg, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      ContinuousLinearMap.coe_coe, Submodule.mem_comap, Submodule.mem_inf]
    rw [hmem]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  haveI : FiniteDimensional ℝ ↥(LinearMap.ker g) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : M ⊓ Wᗮ ≤ M)).symm.finiteDimensional
  haveI : FiniteDimensional ℝ ↥(LinearMap.range g) := by
    have hle : LinearMap.range g ≤ W := by
      rintro _ ⟨x, rfl⟩
      exact W.starProjection_apply_mem x
    exact Submodule.finiteDimensional_of_le hle
  haveI : FiniteDimensional ℝ (↥M ⧸ LinearMap.ker g) :=
    (LinearMap.quotKerEquivRange g).symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/-- The room principle (A1 in essence): finitely many orthogonality
    constraints cannot exhaust an infinite-dimensional subspace. -/
theorem not_finiteDimensional_inf_orthogonal {M W : Submodule ℝ H}
    (hM : ¬ FiniteDimensional ℝ ↥M) (hW : FiniteDimensional ℝ ↥W) :
    ¬ FiniteDimensional ℝ ↥(M ⊓ Wᗮ) :=
  fun hfin => hM (finiteDimensional_of_inf_orthogonal hW hfin)

/-- An infinite orthonormal family inside a subspace forces it to be
    infinite-dimensional. -/
theorem not_finiteDimensional_of_orthonormal {M : Submodule ℝ H} {v : ℕ → H}
    (hv : Orthonormal ℝ v) (hmem : ∀ n, v n ∈ M) :
    ¬ FiniteDimensional ℝ ↥M := by
  intro hfin
  have hli : LinearIndependent ℝ (fun n : ℕ => (⟨v n, hmem n⟩ : ↥M)) := by
    have h := hv.linearIndependent
    exact LinearIndependent.of_comp M.subtype (by simpa using h)
  have := hli.finite_of_isNoetherian
  exact (Set.infinite_univ (α := ℕ)) (Set.finite_univ_iff.mpr this)

/-! ### Closedness of finite meets -/

theorem isClosed_finsetInf (s : Finset (Submodule ℝ H))
    (hs : ∀ M ∈ s, IsClosed ((M : Submodule ℝ H) : Set H)) :
    IsClosed (((s.inf id : Submodule ℝ H)) : Set H) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert M s hM ih =>
      have h1 : IsClosed ((M : Submodule ℝ H) : Set H) := hs M (Finset.mem_insert_self M s)
      have h2 : IsClosed (((s.inf id : Submodule ℝ H)) : Set H) :=
        ih (fun M' hM' => hs M' (Finset.mem_insert_of_mem hM'))
      rw [Finset.inf_insert]
      simpa [Submodule.coe_inf, id] using h1.inter h2

end PlufWO12
