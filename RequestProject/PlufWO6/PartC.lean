/-
  PlufWO6/PartC.lean — Work Order 6, Part C: the space of plufs
  (Paper I, Proposition 2.4), set level.

  C1 is returned under the codified counterexample licence: without a
  closedness hypothesis on `M` and `N` the identity `M̂ ∩ N̂ = (M ⊓ N)^`
  fails, because a non-closed subspace lies in no pluf while its meet with
  a line inside it may lie in many. The marked minimal repair adds the two
  closedness hypotheses (which the paper's `M, N ∈ P(H)` carries).
  C2 needs `E ≠ 0`, as A1 does.

  The topological packaging of Proposition 2.4 is in
  `RequestProject.PlufWO6.PartCTop`.
-/
import RequestProject.PlufWO6.PartA

open Set
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Principal plufs -/

/-- The principal filter of the line through `v`. -/
def principalPluf (v : E) : Set (Submodule ℝ E) :=
  {M : Submodule ℝ E | IsClosed (M : Set E) ∧ (ℝ ∙ v) ≤ M}

theorem mem_principalPluf {v : E} {M : Submodule ℝ E} :
    M ∈ principalPluf v ↔ IsClosed (M : Set E) ∧ v ∈ M := by
  simp only [principalPluf, Set.mem_setOf_eq, Submodule.span_singleton_le_iff_mem]

/-- The principal filter of a line is a pluf. -/
theorem isPluf_principalPluf {v : E} (hv : v ≠ 0) : IsPluf (principalPluf v) := by
  have hspan : IsClosed ((ℝ ∙ v : Submodule ℝ E) : Set E) := by
    haveI : FiniteDimensional ℝ ↥(ℝ ∙ v : Submodule ℝ E) := FiniteDimensional.span_singleton ℝ v
    exact Submodule.closed_of_finiteDimensional _
  refine isPluf_of_criterion _ (fun M hM => hM.1) ?_ ?_ ?_ ?_
  · rintro M ⟨-, hMv⟩ N hN hMN
    exact ⟨hN, hMv.trans hMN⟩
  · rintro M ⟨hMcl, hMv⟩ N ⟨hNcl, hNv⟩
    exact ⟨isClosed_inf hMcl hNcl, le_inf hMv hNv⟩
  · rintro ⟨-, hbot⟩
    rw [le_bot_iff, Submodule.span_singleton_eq_bot] at hbot
    exact hv hbot
  · intro M hM
    by_cases hvM : v ∈ M
    · exact Or.inl ⟨hM, (Submodule.span_singleton_le_iff_mem v M).mpr hvM⟩
    · refine Or.inr ⟨ℝ ∙ v, ⟨hspan, le_refl _⟩, ?_⟩
      rw [Submodule.eq_bot_iff]
      rintro x ⟨hxM, hxv⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      · exact absurd (by simpa [hc] using M.smul_mem c⁻¹ hxM) hvM

/-! ### C1: the basic sets and their meets -/

/-  C1 (first clause), contract statement, preserved verbatim:

theorem pluf_sets_inter (M N : Submodule ℝ E) :
    {π | IsPluf π ∧ M ∈ π} ∩ {π | IsPluf π ∧ N ∈ π}
      = {π | IsPluf π ∧ M ⊓ N ∈ π}

    This form is false: `M̂` is empty for every non-closed `M`, while
    `(M ⊓ N)^` need not be. Concretely, in `PlufWO1.H` take `M` the span
    of the standard basis vectors (a non-closed subspace) and
    `N = ℝ ∙ evec 0`; then the left side is empty and the right side
    contains the principal pluf of `evec 0` — see
    `pluf_sets_inter_counterexample`. The marked minimal repair adds the
    hypotheses `IsClosed M`, `IsClosed N`, which is what the paper's
    `M, N ∈ P(H)` means. -/

/-- C1 (Proposition 2.4, first clause), minimal repair: `M` and `N`
    closed. `M̂ ∩ N̂ = (M ⊓ N)^`. -/
theorem pluf_sets_inter (M N : Submodule ℝ E)
    (hM : IsClosed (M : Set E)) (hN : IsClosed (N : Set E)) :
    {π | IsPluf π ∧ M ∈ π} ∩ {π | IsPluf π ∧ N ∈ π}
      = {π | IsPluf π ∧ M ⊓ N ∈ π} := by
  ext π
  constructor
  · rintro ⟨⟨hπ, hMπ⟩, ⟨-, hNπ⟩⟩
    exact ⟨hπ, hπ.inf_mem M hMπ N hNπ⟩
  · rintro ⟨hπ, hinf⟩
    exact ⟨⟨hπ, hπ.upward _ hinf M hM inf_le_left⟩,
      ⟨hπ, hπ.upward _ hinf N hN inf_le_right⟩⟩

/-! ### The counterexample to the unrestricted C1 -/

section Counterexample

open PlufWO1

/-- Every element of the span of the standard basis vectors has finite
    support. -/
theorem finite_support_of_mem_spanEvec {x : H}
    (hx : x ∈ Submodule.span ℝ (Set.range (evec : ℕ → H))) :
    {n : ℕ | (x : ∀ _ : ℕ, ℝ) n ≠ 0}.Finite := by
  refine Submodule.span_induction
    (p := fun (v : H) _ => {n : ℕ | (v : ∀ _ : ℕ, ℝ) n ≠ 0}.Finite) ?_ ?_ ?_ ?_ hx
  · rintro v ⟨n, rfl⟩
    refine Set.Finite.subset (Set.finite_singleton n) (fun m hm => ?_)
    simp only [Set.mem_setOf_eq, evec_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, Decidable.not_not] at hm
    exact hm
  · simp
  · intro u v _ _ hu hv
    refine Set.Finite.subset (hu.union hv) (fun m hm => ?_)
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at hm
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    exact hm (by rw [hcon.1, hcon.2]; ring)
  · intro c v _ hv
    refine Set.Finite.subset hv (fun m hm => ?_)
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ne_eq,
      mul_eq_zero, not_or] at hm
    exact hm.2

/-- The span of the standard basis vectors is not closed. -/
theorem not_isClosed_spanEvec :
    ¬ IsClosed ((Submodule.span ℝ (Set.range (evec : ℕ → H)) : Submodule ℝ H) : Set H) := by
  intro hclosed
  set M : Submodule ℝ H := Submodule.span ℝ (Set.range (evec : ℕ → H)) with hMdef
  haveI : CompleteSpace ↥M := hclosed.completeSpace_coe
  have horth : Mᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hcoord : ∀ n : ℕ, (z : ∀ _ : ℕ, ℝ) n = 0 := by
      intro n
      have hmem : evec n ∈ M := Submodule.subset_span ⟨n, rfl⟩
      have := hz (evec n) hmem
      rwa [PlufWO5.inner_evec_left] at this
    exact lp.ext (funext hcoord)
  have hMtop : M = ⊤ := by
    have h := Submodule.orthogonal_orthogonal M
    rw [horth, Submodule.bot_orthogonal_eq_top] at h
    exact h.symm
  have hx : constraintVec (univ : Set ℕ) ∈ M := by rw [hMtop]; trivial
  refine absurd (finite_support_of_mem_spanEvec hx) (Set.Infinite.mono (fun n _ => ?_)
    (Set.infinite_univ (α := ℕ)))
  simp only [Set.mem_setOf_eq]
  rw [constraintVec_apply, if_pos (Set.mem_univ n)]
  positivity

/-- The counterexample to the unrestricted form of C1: with `M` the span
    of the standard basis vectors and `N` the line through `evec 0`, the
    left-hand side of C1 is empty while the right-hand side is not. -/
theorem pluf_sets_inter_counterexample :
    ({π | IsPluf π ∧ Submodule.span ℝ (Set.range (evec : ℕ → H)) ∈ π} ∩
        {π | IsPluf π ∧ (ℝ ∙ evec 0) ∈ π} : Set (Set (Submodule ℝ H))) = ∅ ∧
      ({π | IsPluf π ∧
          Submodule.span ℝ (Set.range (evec : ℕ → H)) ⊓ (ℝ ∙ evec 0) ∈ π} :
        Set (Set (Submodule ℝ H))).Nonempty := by
  constructor
  · ext π
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨hπ, hmem⟩
    exact absurd (hπ.mem_closed _ hmem) not_isClosed_spanEvec
  · refine ⟨principalPluf (evec 0), isPluf_principalPluf (evec_ne_zero 0), ?_⟩
    have hle : (ℝ ∙ evec 0) ≤ Submodule.span ℝ (Set.range (evec : ℕ → H)) := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨0, rfl⟩
    rw [inf_comm, inf_eq_left.mpr hle]
    exact mem_principalPluf.mpr ⟨by
      haveI : FiniteDimensional ℝ ↥(ℝ ∙ evec 0 : Submodule ℝ H) :=
        FiniteDimensional.span_singleton ℝ (evec 0)
      exact Submodule.closed_of_finiteDimensional _, Submodule.mem_span_singleton_self _⟩

end Counterexample

/-! ### C2: the complement of a basic set -/

/-  C2, contract statement, preserved verbatim:

theorem pluf_compl_eq_iUnion (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    {π | IsPluf π ∧ M ∈ π}ᶜ ∩ {π | IsPluf π}
      = {π | IsPluf π ∧ ∃ N ∈ π, M ⊓ N = ⊥}

    As with A1 this fails over the zero space (`π = ∅`, `M = ⊥`); the
    marked minimal repair adds `[Nontrivial E]`. -/

/-- C2 (Proposition 2.4, clopenness), minimal repair: `E ≠ 0`. The
    complement of `M̂` inside the space of plufs is the set of plufs having
    a member meeting `M` trivially — the union of the `N̂` with
    `M ⊓ N = ⊥`, by A1. -/
theorem pluf_compl_eq_iUnion [Nontrivial E] (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    {π | IsPluf π ∧ M ∈ π}ᶜ ∩ {π | IsPluf π}
      = {π | IsPluf π ∧ ∃ N ∈ π, M ⊓ N = ⊥} := by
  ext π
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, not_and]
  constructor
  · rintro ⟨hnot, hπ⟩
    exact ⟨hπ, (maximality_criterion π hπ M hM).resolve_left (hnot hπ)⟩
  · rintro ⟨hπ, N, hN, hNbot⟩
    refine ⟨fun _ hMπ => ?_, hπ⟩
    exact hπ.proper (hNbot ▸ hπ.inf_mem M hMπ N hN)

end PlufWO6
