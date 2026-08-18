/-
  PlufWO15/PartC.lean — Work Order 15, Part C: Paper I, Theorem 5.7.

  The pluf is the upward closure among closed subspaces of the union of
  the ω₁-chain of Part B. Maximality comes from `PlufWO6.isPluf_of_criterion`
  fed by the decision property; nonprincipality is a finite-codimension
  ("room") argument: an ample member cannot meet the hyperplane `(ℝ ∙ v)ᗮ`
  trivially, since it would then embed in the line `ℝ`.
-/
import RequestProject.PlufWO15.PartB

open Set Cardinal PlufWO13

namespace PlufWO15

/-- An ample subspace meets every hyperplane `(ℝ ∙ v)ᗮ` nontrivially: were
    the meet zero, the inner product with `v` would embed it in `ℝ`. -/
theorem inf_orthogonal_singleton_ne_bot {g : Submodule ℝ H} (hg : Ample g) (v : H) :
    g ⊓ (ℝ ∙ v)ᗮ ≠ ⊥ := by
  intro hbot
  refine infinite_dimensional_of_ample hg ?_
  have hinj : Function.Injective
      (fun x : ↥g => inner (𝕜 := ℝ) v (x : H)) := by
    intro x y hxy
    have hzero : inner (𝕜 := ℝ) v ((x : H) - (y : H)) = 0 := by
      simp only at hxy
      rw [inner_sub_right, hxy, sub_self]
    have hmem : ((x : H) - (y : H)) ∈ g ⊓ (ℝ ∙ v)ᗮ := by
      refine ⟨g.sub_mem x.2 y.2, ?_⟩
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr hzero
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact Subtype.ext hmem
  exact FiniteDimensional.of_injective
    ((innerSL ℝ v).toLinearMap.comp (g.subtype : ↥g →ₗ[ℝ] H)) hinj

/-- C1 (Paper I, Theorem 5.7), as consumed by Part D. -/
theorem exists_pluf_all_ample_aux (hCH : continuum = aleph 1) :
    ∃ σ : Set (Submodule ℝ H), PlufWO6.IsPluf σ ∧
      (∀ v : H, v ≠ 0 → ∃ M ∈ σ, v ∉ M) ∧
      (∀ M ∈ σ, Ample M) := by
  classical
  obtain ⟨c, hmono, hadm, -, hdec⟩ := exists_admissible_chain_aux hCH
  set U : Set (Submodule ℝ H) := {N | ∃ a, a < (aleph.{0} 1).ord ∧ N ∈ c a} with hU
  set σ : Set (Submodule ℝ H) := {M | IsClosed (M : Set H) ∧ ∃ N ∈ U, N ≤ M} with hσdef
  have hUample : ∀ N ∈ U, Ample N := by
    rintro N ⟨a, ha, hN⟩
    exact (hadm a ha).ample N hN
  have hUσ : U ⊆ σ := fun N hN => ⟨(hUample N hN).2.1, N, hN, le_rfl⟩
  have hample : ∀ M ∈ σ, Ample M := by
    rintro M ⟨hMcl, N, hN, hNM⟩
    exact ample_of_ample_le (hUample N hN) hMcl hNM
  have hpluf : PlufWO6.IsPluf σ := by
    refine PlufWO6.isPluf_of_criterion σ (fun M hM => hM.1) ?_ ?_ ?_ ?_
    · rintro M ⟨-, N, hN, hNM⟩ P hP hMP
      exact ⟨hP, N, hN, hNM.trans hMP⟩
    · rintro M ⟨hMcl, N, ⟨a, ha, hNa⟩, hNM⟩ M' ⟨hM'cl, N', ⟨b, hb, hN'b⟩, hN'M'⟩
      have hab : max a b < (aleph.{0} 1).ord := max_lt ha hb
      refine ⟨PlufWO6.isClosed_inf hMcl hM'cl, N ⊓ N', ⟨max a b, hab, ?_⟩,
        inf_le_inf hNM hN'M'⟩
      exact (hadm _ hab).inf_closed N (hmono a _ (le_max_left a b) hab hNa)
        N' (hmono b _ (le_max_right a b) hab hN'b)
    · rintro ⟨-, N, hN, hNbot⟩
      exact (hUample N hN).1 (le_bot_iff.mp hNbot)
    · intro M hM
      obtain ⟨a, ha, hd⟩ := hdec M hM
      rcases hd with h | ⟨g, hg, hgM⟩
      · exact Or.inl (hUσ ⟨a, ha, h⟩)
      · refine Or.inr ⟨g, hUσ ⟨a, ha, hg⟩, ?_⟩
        rw [inf_comm]
        exact hgM
  refine ⟨σ, hpluf, ?_, hample⟩
  intro v hv
  obtain ⟨a, ha, hd⟩ := hdec ((ℝ ∙ v)ᗮ) (Submodule.isClosed_orthogonal _)
  rcases hd with h | ⟨g, hg, hgL⟩
  · refine ⟨(ℝ ∙ v)ᗮ, hUσ ⟨a, ha, h⟩, ?_⟩
    intro hvmem
    exact hv (inner_self_eq_zero.mp
      ((Submodule.mem_orthogonal_singleton_iff_inner_right).mp hvmem))
  · exact absurd hgL (inf_orthogonal_singleton_ne_bot ((hadm a ha).ample g hg) v)

/-- C2 (the failure of RSP). Every member of `σ` being ample, the gap
    between the two Rayleigh values is the constant `1 - 1/16`, so it
    never closes.

    (The contract's `hσ` and `hne` are printed and kept; the constant gap
    argument needs neither.) -/
theorem not_rsp_of_all_ample_aux {σ : Set (Submodule ℝ H)}
    (hamp : ∀ M ∈ σ, Ample M) :
    ¬ PlufWO6.RSP σ T := by
  intro hrsp
  obtain ⟨M, hM, hlt⟩ := hrsp (15/16) (by norm_num)
  rw [upper_eq_one_of_ample (hamp M hM), lower_eq_sixteenth_of_ample (hamp M hM)] at hlt
  norm_num at hlt

end PlufWO15
