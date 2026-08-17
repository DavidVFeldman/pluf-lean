/-
  PlufWO6/Basic.lean — Work Order 6, shared infrastructure.

  The definition `IsPluf` of the contract, verbatim, together with named
  accessors for its five clauses and the two elementary consequences used
  throughout: closedness of a meet of two closed subspaces, and the fact
  that a pluf on a nonzero space contains `⊤` (hence is nonempty).
-/
import RequestProject.PlufWO5

open Set
open scoped Classical

namespace PlufWO6

/-! ### Setting

The ambient space is a real Hilbert space `E`. Where separability or a
basis is needed (Parts D–G at the concrete level) we work in
`PlufWO1.H = lp (fun _ : ℕ => ℝ) 2`, as in the earlier work orders; Parts
A–C are stated for a general `E` if that costs nothing, and may be
specialized to `PlufWO1.H` with a report if it does. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The closed subspaces of `E`: the lattice `P(H)` of the papers, rendered
    as submodules carrying a closedness predicate. Meets are intersections;
    joins are closures of sums. The development below never needs joins
    except in Part B, where `M ⊔ N` for closed `M, N` should be read as the
    topological closure `(M ⊔ N).topologicalClosure`. -/
def IsPluf (π : Set (Submodule ℝ E)) : Prop :=
  (∀ M ∈ π, IsClosed (M : Set E)) ∧
  (∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π) ∧
  (∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π) ∧
  ((⊥ : Submodule ℝ E) ∉ π) ∧
  (∀ σ : Set (Submodule ℝ E), (∀ M ∈ σ, IsClosed (M : Set E)) →
    (∀ M ∈ π, M ∈ σ) → (∀ M ∈ σ, ∀ N ∈ σ, M ⊓ N ∈ σ) →
    ((⊥ : Submodule ℝ E) ∉ σ) → (∀ M ∈ σ, M ∈ π))

omit [CompleteSpace E] in
/-- A meet of two closed subspaces is closed. -/
theorem isClosed_inf {M N : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hN : IsClosed (N : Set E)) : IsClosed ((M ⊓ N : Submodule ℝ E) : Set E) := by
  rw [Submodule.coe_inf]
  exact hM.inter hN

namespace IsPluf

variable {π : Set (Submodule ℝ E)}

omit [CompleteSpace E]

/-- Every member of a pluf is closed. -/
theorem mem_closed (h : IsPluf π) : ∀ M ∈ π, IsClosed (M : Set E) := h.1

/-- A pluf is upward closed among closed subspaces. -/
theorem upward (h : IsPluf π) : ∀ M ∈ π, ∀ N : Submodule ℝ E,
    IsClosed (N : Set E) → M ≤ N → N ∈ π := h.2.1

/-- A pluf is closed under binary meets. -/
theorem inf_mem (h : IsPluf π) : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π := h.2.2.1

/-- A pluf is proper. -/
theorem proper (h : IsPluf π) : (⊥ : Submodule ℝ E) ∉ π := h.2.2.2.1

/-- Maximality: any proper meet-closed family of closed subspaces
    containing `π` is contained in `π`. -/
theorem maximal (h : IsPluf π) : ∀ σ : Set (Submodule ℝ E),
    (∀ M ∈ σ, IsClosed (M : Set E)) → (∀ M ∈ π, M ∈ σ) →
    (∀ M ∈ σ, ∀ N ∈ σ, M ⊓ N ∈ σ) → ((⊥ : Submodule ℝ E) ∉ σ) →
    (∀ M ∈ σ, M ∈ π) := h.2.2.2.2

/-- No member of a pluf is `⊥`. -/
theorem ne_bot (h : IsPluf π) {M : Submodule ℝ E} (hM : M ∈ π) :
    M ≠ ⊥ := by
  rintro rfl; exact h.proper hM

/-- Two members of a pluf meet nontrivially. -/
theorem inf_ne_bot (h : IsPluf π) {M N : Submodule ℝ E} (hM : M ∈ π) (hN : N ∈ π) :
    M ⊓ N ≠ ⊥ := h.ne_bot (h.inf_mem M hM N hN)

/-- On a nonzero space, a pluf contains `⊤`; in particular it is nonempty.
    (Over the zero space the empty family satisfies `IsPluf`, which is the
    source of the degenerate counterexamples recorded in Part A.) -/
theorem top_mem [Nontrivial E] (h : IsPluf π) : (⊤ : Submodule ℝ E) ∈ π := by
  refine h.maximal (π ∪ {⊤}) ?_ (fun M hM => Or.inl hM) ?_ ?_ ⊤ (Or.inr rfl)
  · rintro M (hM | rfl)
    · exact h.mem_closed M hM
    · simp only [Submodule.top_coe]
      exact isClosed_univ
  · rintro M (hM | rfl) N (hN | rfl)
    · exact Or.inl (h.inf_mem M hM N hN)
    · rw [inf_top_eq]
      exact Or.inl hM
    · rw [top_inf_eq]
      exact Or.inl hN
    · rw [top_inf_eq]
      exact Or.inr rfl
  · rintro (hbot | hbot)
    · exact h.proper hbot
    · exact (bot_ne_top (α := Submodule ℝ E)) hbot

/-- On a nonzero space a pluf is nonempty. -/
theorem nonempty [Nontrivial E] (h : IsPluf π) : π.Nonempty :=
  ⟨⊤, h.top_mem⟩

end IsPluf

end PlufWO6
