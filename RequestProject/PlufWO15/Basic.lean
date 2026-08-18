/-
  PlufWO15/Basic.lean — Work Order 15, shared definitions.

  The two notions of the commission (`Admissible`, `Decides`) live here so
  that the part files can be built on top of them and the contract file
  `RequestProject/PlufWO15.lean` can discharge its statements from them.
  Both carry the contract's docstrings verbatim.
-/
import RequestProject.PlufWO14
import RequestProject.PlufWO12

open Set Cardinal PlufWO13

namespace PlufWO15

abbrev H := PlufWO1.H

/-- A family is *admissible* at a stage: countable, closed under binary
    meets, every member ample. (Ampleness gives nonzero and
    infinite-dimensional, so no separate clause is needed —
    `PlufWO13.infinite_dimensional_of_ample`.) -/
structure Admissible (F : Set (Submodule ℝ H)) : Prop where
  countable : F.Countable
  nonempty : F.Nonempty
  inf_closed : ∀ M ∈ F, ∀ N ∈ F, M ⊓ N ∈ F
  ample : ∀ M ∈ F, Ample M

/-- The decision property (∗) of the paper: at stage `p`, either `p` has
    joined the family or some member misses it. -/
def Decides (F : Set (Submodule ℝ H)) (p : Submodule ℝ H) : Prop :=
  p ∈ F ∨ ∃ g ∈ F, g ⊓ p = ⊥

/-- Members of an admissible family are closed. -/
theorem Admissible.isClosed {F : Set (Submodule ℝ H)} (hF : Admissible F)
    {M : Submodule ℝ H} (hM : M ∈ F) : IsClosed (M : Set H) :=
  (hF.ample M hM).2.1

/-- The family `{⊤}` is admissible. -/
theorem admissible_singleton_top : Admissible ({⊤} : Set (Submodule ℝ H)) where
  countable := Set.countable_singleton _
  nonempty := ⟨⊤, rfl⟩
  inf_closed := by
    rintro M rfl N rfl
    simp
  ample := by
    rintro M rfl
    exact ample_top

/-- Adjoining `X` to `F` by meeting every member with it: the resulting
    family is admissible, still contains `⊤`, extends `F`, and contains
    `X` itself (as `⊤ ⊓ X`), provided every meet `g ⊓ X` is ample. This
    is the common shape of Cases II and III of the stage step. -/
theorem admissible_adjoin {F : Set (Submodule ℝ H)} (hF : Admissible F)
    (htop : (⊤ : Submodule ℝ H) ∈ F) (X : Submodule ℝ H)
    (hX : ∀ g ∈ F, Ample (g ⊓ X)) :
    Admissible (F ∪ (fun g => g ⊓ X) '' F) ∧
      (⊤ : Submodule ℝ H) ∈ F ∪ (fun g => g ⊓ X) '' F ∧
      F ⊆ F ∪ (fun g => g ⊓ X) '' F ∧
      X ∈ F ∪ (fun g => g ⊓ X) '' F := by
  refine ⟨⟨hF.countable.union (hF.countable.image _),
    hF.nonempty.mono Set.subset_union_left, ?_, ?_⟩,
    Or.inl htop, Set.subset_union_left, ?_⟩
  · rintro M (hM | ⟨g, hg, rfl⟩) N (hN | ⟨h, hh, rfl⟩)
    · exact Or.inl (hF.inf_closed M hM N hN)
    · exact Or.inr ⟨M ⊓ h, hF.inf_closed M hM h hh, by simp only; rw [inf_assoc]⟩
    · refine Or.inr ⟨g ⊓ N, hF.inf_closed g hg N hN, ?_⟩
      simp only
      rw [inf_assoc, inf_assoc, inf_comm X N]
    · refine Or.inr ⟨g ⊓ h, hF.inf_closed g hg h hh, ?_⟩
      simp only
      rw [inf_assoc, inf_assoc, ← inf_assoc X h X, inf_comm X h, inf_assoc h X X,
        inf_idem]
  · rintro M (hM | ⟨g, hg, rfl⟩)
    · exact hF.ample M hM
    · exact hX g hg
  · exact Or.inr ⟨⊤, htop, by simp⟩

end PlufWO15
