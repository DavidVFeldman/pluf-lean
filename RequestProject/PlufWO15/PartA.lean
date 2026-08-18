/-
  PlufWO15/PartA.lean — Work Order 15, Part A: the stage step.

  A1 internalizes the paper's three cases so that the recursion of Part B
  never branches at run time; A2 is the limit bookkeeping.
-/
import RequestProject.PlufWO15.Basic

open Set Cardinal PlufWO13

namespace PlufWO15

/-- A1 (the stage step), as consumed by Part B. -/
theorem exists_admissible_decides_aux {F : Set (Submodule ℝ H)} (hF : Admissible F)
    (htop : (⊤ : Submodule ℝ H) ∈ F)
    (p : Submodule ℝ H) (hp : IsClosed (p : Set H)) :
    ∃ F', Admissible F' ∧ (⊤ : Submodule ℝ H) ∈ F' ∧ F ⊆ F' ∧ Decides F' p := by
  by_cases hI : ∃ g ∈ F, g ⊓ p = ⊥
  · -- Case I: `p` is already missed by a member; nothing to do.
    exact ⟨F, hF, htop, subset_rfl, Or.inr hI⟩
  · push_neg at hI
    by_cases hII : ∀ g ∈ F, Ample (g ⊓ p)
    · -- Case II: every meet with `p` is ample; adjoin `p`.
      obtain ⟨hadm, htop', hsub, hmem⟩ := admissible_adjoin hF htop p hII
      exact ⟨_, hadm, htop', hsub, Or.inl hmem⟩
    · -- Case III: some meet fails to be ample; block `p` by WO-14.
      push_neg at hII
      obtain ⟨q, hq, hqp⟩ := hII
      obtain ⟨R, hRcl, hRp, hRg, -⟩ :=
        PlufWO14.blocking_lemma F hF.countable hF.ample
          (fun M hM M' hM' => ⟨M ⊓ M', hF.inf_closed M hM M' hM', le_rfl⟩)
          p hp hq hqp hI
      obtain ⟨hadm, htop', hsub, hmem⟩ :=
        admissible_adjoin hF htop R (fun g hg => by rw [inf_comm]; exact hRg g hg)
      exact ⟨_, hadm, htop', hsub, Or.inr ⟨R, hmem, hRp⟩⟩

/-- The contract's printed form of A2 — with no nonemptiness hypothesis on
    the index type — is refutable: over an empty index type the union is
    `∅`, which is not admissible and does not contain `⊤`, while all three
    hypotheses hold vacuously. -/
theorem admissible_iUnion_counterexample :
    ¬ ∀ (ι : Type) (_ : Countable ι) (F : ι → Set (Submodule ℝ H)),
        (∀ i, Admissible (F i)) → (∀ i, (⊤ : Submodule ℝ H) ∈ F i) →
        (∀ i j, ∃ k, F i ⊆ F k ∧ F j ⊆ F k) →
        Admissible (⋃ i, F i) ∧ (⊤ : Submodule ℝ H) ∈ ⋃ i, F i := by
  intro h
  have hmem := (h Empty inferInstance (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim)).2
  simp at hmem

/-- A2 (unions of chains stay admissible), as consumed by Part B.

    NOTE (repair, reported): the contract's printed form omits any
    nonemptiness hypothesis on the index type `ι`, and is FALSE for `ι`
    empty — the union is then `∅`, which contains no `⊤` and is not
    `Admissible` (the `nonempty` field fails). `[Nonempty ι]` is added;
    Part B applies it with an index type that is nonempty by
    construction. -/
theorem admissible_iUnion_aux {ι : Type*} [Countable ι] [Nonempty ι]
    (F : ι → Set (Submodule ℝ H))
    (hF : ∀ i, Admissible (F i)) (htop : ∀ i, (⊤ : Submodule ℝ H) ∈ F i)
    (hdir : ∀ i j, ∃ k, F i ⊆ F k ∧ F j ⊆ F k) :
    Admissible (⋃ i, F i) ∧ (⊤ : Submodule ℝ H) ∈ ⋃ i, F i := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨⟨Set.countable_iUnion (fun i => (hF i).countable),
    ⟨⊤, Set.mem_iUnion.mpr ⟨i₀, htop i₀⟩⟩, ?_, ?_⟩,
    Set.mem_iUnion.mpr ⟨i₀, htop i₀⟩⟩
  · rintro M hM N hN
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hM
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hN
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact Set.mem_iUnion.mpr ⟨k, (hF k).inf_closed M (hik hi) N (hjk hj)⟩
  · rintro M hM
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hM
    exact (hF i).ample M hi

end PlufWO15
