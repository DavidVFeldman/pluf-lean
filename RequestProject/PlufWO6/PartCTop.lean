/-
  PlufWO6/PartCTop.lean — Work Order 6, Part C, topological packaging
  (Paper I, Proposition 2.4).

  GATE VERDICT (recorded in REPORT-WO6.md): Mathlib's generated-topology
  API is CHEAP ENOUGH, and the packaging is delivered in full.  What is
  used: `TopologicalSpace.generateFrom`,
  `TopologicalSpace.IsTopologicalBasis.mk` (whose three obligations are
  exactly the set-level lemmas of `PartC.lean`), and
  `TopologicalSpace.IsTopologicalBasis.dense_iff`.  All four clauses of
  Proposition 2.4 are proved:

  * `isTopologicalBasis_plufBasis` — the sets `M̂` form a basis;
  * `isClopen_hat` — every `M̂` is clopen (zero-dimensionality);
  * `t2Space` — distinct plufs are separated (Hausdorff);
  * `hat_line_eq_singleton`, `isOpen_singleton_principal` — principal
    plufs are isolated, and `dense_principal` — they are dense;
  * `not_compactSpace` — the space is not compact, by the paper's
    argument: inside a two-dimensional `M` the set `M̂` is an infinite
    closed discrete subspace.

  As in Part C proper this needs `E ≠ 0` (`[Nontrivial E]`), the empty
  family being a pluf over the zero space.
-/
import RequestProject.PlufWO6.PartC

open Set
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace PlufWO6

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The space of plufs of `E`, the `Π` of Proposition 2.4. -/
@[ext]
structure PlufSpace where
  /-- The underlying family of closed subspaces. -/
  carrier : Set (Submodule ℝ E)
  /-- It is a pluf. -/
  isPluf' : IsPluf carrier

variable {E}

namespace PlufSpace

/-- The basic set `M̂ = {π | M ∈ π}`. -/
def hat (M : Submodule ℝ E) : Set (PlufSpace E) := {p | M ∈ p.carrier}

omit [CompleteSpace E] in
theorem mem_hat {M : Submodule ℝ E} {p : PlufSpace E} : p ∈ hat M ↔ M ∈ p.carrier := Iff.rfl

/-- The family of basic sets, indexed by the closed subspaces. -/
def plufBasis : Set (Set (PlufSpace E)) :=
  {s | ∃ M : Submodule ℝ E, IsClosed (M : Set E) ∧ s = hat M}

instance : TopologicalSpace (PlufSpace E) := TopologicalSpace.generateFrom plufBasis

omit [CompleteSpace E] in
/-- C1 at the level of the pluf space: `M̂ ∩ N̂ = (M ⊓ N)^` for closed
    `M`, `N`. -/
theorem hat_inter {M N : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hN : IsClosed (N : Set E)) : hat M ∩ hat N = hat (M ⊓ N) := by
  ext p
  simp only [Set.mem_inter_iff, mem_hat]
  constructor
  · rintro ⟨h1, h2⟩
    exact p.isPluf'.inf_mem M h1 N h2
  · intro h
    exact ⟨p.isPluf'.upward _ h M hM inf_le_left, p.isPluf'.upward _ h N hN inf_le_right⟩

omit [CompleteSpace E] in
theorem hat_bot : hat (⊥ : Submodule ℝ E) = ∅ := by
  ext p
  simp only [mem_hat, Set.mem_empty_iff_false, iff_false]
  exact p.isPluf'.proper

omit [CompleteSpace E] in
theorem hat_top [Nontrivial E] : hat (⊤ : Submodule ℝ E) = Set.univ := by
  ext p
  simp only [mem_hat, Set.mem_univ, iff_true]
  exact p.isPluf'.top_mem

omit [CompleteSpace E] in
/-- Proposition 2.4, packaging: the sets `M̂` form a basis of the
    topology. -/
theorem isTopologicalBasis_plufBasis [Nontrivial E] :
    TopologicalSpace.IsTopologicalBasis (plufBasis (E := E)) := by
  refine TopologicalSpace.IsTopologicalBasis.mk ?_ ?_ rfl
  · rintro t₁ ⟨M, hM, rfl⟩ t₂ ⟨N, hN, rfl⟩ p hp
    exact ⟨hat (M ⊓ N), ⟨M ⊓ N, isClosed_inf hM hN, rfl⟩,
      by rw [← hat_inter hM hN]; exact hp, by rw [hat_inter hM hN]⟩
  · refine Set.eq_univ_of_univ_subset (fun p _ => ?_)
    refine ⟨hat (⊤ : Submodule ℝ E), ⟨⊤, ?_, rfl⟩, ?_⟩
    · simp
    · rw [hat_top]; trivial

omit [CompleteSpace E] in
theorem isOpen_hat {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) : IsOpen (hat M) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨M, hM, rfl⟩

/-- C2 at the level of the pluf space: the complement of `M̂` is the union
    of the `N̂` for which `M ⊓ N = ⊥`.  Hence every `M̂` is clopen and the
    space is zero-dimensional. -/
theorem compl_hat [Nontrivial E] {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) :
    (hat M)ᶜ = ⋃ N ∈ {N : Submodule ℝ E | IsClosed (N : Set E) ∧ M ⊓ N = ⊥}, hat N := by
  ext p
  simp only [Set.mem_compl_iff, mem_hat, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · intro hp
    rcases maximality_criterion p.carrier p.isPluf' M hM with h | ⟨N, hN, hMN⟩
    · exact absurd h hp
    · exact ⟨N, ⟨p.isPluf'.mem_closed N hN, hMN⟩, hN⟩
  · rintro ⟨N, ⟨-, hMN⟩, hNp⟩ hMp
    have : (⊥ : Submodule ℝ E) ∈ p.carrier := by
      rw [← hMN]
      exact p.isPluf'.inf_mem M hMp N hNp
    exact p.isPluf'.proper this

theorem isClopen_hat [Nontrivial E] {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) :
    IsClopen (hat M) := by
  refine ⟨?_, isOpen_hat hM⟩
  rw [← isOpen_compl_iff, compl_hat hM]
  exact isOpen_biUnion (fun N hN => isOpen_hat hN.1)

/-- Proposition 2.4, Hausdorff. -/
instance t2Space [Nontrivial E] : T2Space (PlufSpace E) := by
  refine ⟨fun p q hpq => ?_⟩
  have hsep : ∀ p q : PlufSpace E, ∀ M : Submodule ℝ E, M ∈ p.carrier → M ∉ q.carrier →
      ∃ U V : Set (PlufSpace E), IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V := by
    intro p q M hMp hMq
    have hMc : IsClosed (M : Set E) := p.isPluf'.mem_closed M hMp
    rcases maximality_criterion q.carrier q.isPluf' M hMc with h | ⟨N, hN, hMN⟩
    · exact absurd h hMq
    have hNc : IsClosed (N : Set E) := q.isPluf'.mem_closed N hN
    refine ⟨hat M, hat N, isOpen_hat hMc, isOpen_hat hNc, hMp, hN, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty, hat_inter hMc hNc, hMN, hat_bot]
  have hne : p.carrier ≠ q.carrier := fun h => hpq (PlufSpace.ext h)
  have hex : ∃ M : Submodule ℝ E,
      (M ∈ p.carrier ∧ M ∉ q.carrier) ∨ (M ∈ q.carrier ∧ M ∉ p.carrier) := by
    by_contra hc
    push_neg at hc
    refine hne (Set.ext fun M => ⟨fun h => (hc M).1 h, fun h => (hc M).2 h⟩)
  rcases hex with ⟨M, hM | hM⟩
  · exact hsep p q M hM.1 hM.2
  · obtain ⟨U, V, hU, hV, hqU, hpV, hd⟩ := hsep q p M hM.1 hM.2
    exact ⟨V, U, hV, hU, hpV, hqU, hd.symm⟩

/-! ### Principal plufs -/

/-- The point of the pluf space determined by a nonzero vector. -/
def principal {v : E} (hv : v ≠ 0) : PlufSpace E :=
  ⟨principalPluf v, isPluf_principalPluf hv⟩

omit [CompleteSpace E] in
/-- A nonzero submodule of a line is the line. -/
theorem eq_span_of_le_of_ne_bot {v : E} {K : Submodule ℝ E} (hK : K ≤ (ℝ ∙ v))
    (hKbot : K ≠ ⊥) : K = (ℝ ∙ v) := by
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKbot
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hK hwK)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hw0 (by simpa using hc.symm)
  refine le_antisymm hK ?_
  rw [Submodule.span_singleton_le_iff_mem]
  have : v = c⁻¹ • w := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]
  exact K.smul_mem _ hwK

/-- Proposition 2.4: a principal pluf is an isolated point, its basic
    neighbourhood `L̂` being a singleton. -/
theorem hat_line_eq_singleton {v : E} (hv : v ≠ 0) :
    hat (ℝ ∙ v) = {principal hv} := by
  have hspan : IsClosed ((ℝ ∙ v : Submodule ℝ E) : Set E) := by
    haveI : FiniteDimensional ℝ ↥(ℝ ∙ v : Submodule ℝ E) := FiniteDimensional.span_singleton ℝ v
    exact Submodule.closed_of_finiteDimensional _
  ext p
  simp only [mem_hat, Set.mem_singleton_iff]
  constructor
  · intro hp
    refine PlufSpace.ext ?_
    ext N
    simp only [principal, mem_principalPluf]
    constructor
    · intro hN
      refine ⟨p.isPluf'.mem_closed N hN, ?_⟩
      have hinf : N ⊓ (ℝ ∙ v) ∈ p.carrier := p.isPluf'.inf_mem N hN _ hp
      have hbot : N ⊓ (ℝ ∙ v) ≠ ⊥ := p.isPluf'.ne_bot hinf
      have heq : N ⊓ (ℝ ∙ v) = (ℝ ∙ v) := eq_span_of_le_of_ne_bot inf_le_right hbot
      have : (ℝ ∙ v) ≤ N := by rw [← heq]; exact inf_le_left
      exact this (Submodule.mem_span_singleton_self v)
    · rintro ⟨hNc, hvN⟩
      exact p.isPluf'.upward _ hp N hNc (by rwa [Submodule.span_singleton_le_iff_mem])
  · rintro rfl
    exact (mem_principalPluf).mpr ⟨hspan, Submodule.mem_span_singleton_self v⟩

theorem isOpen_singleton_principal [Nontrivial E] {v : E} (hv : v ≠ 0) :
    IsOpen ({principal hv} : Set (PlufSpace E)) := by
  rw [← hat_line_eq_singleton hv]
  refine isOpen_hat ?_
  haveI : FiniteDimensional ℝ ↥(ℝ ∙ v : Submodule ℝ E) := FiniteDimensional.span_singleton ℝ v
  exact Submodule.closed_of_finiteDimensional _

/-- Proposition 2.4: the principal plufs are dense. -/
theorem dense_principal [Nontrivial E] :
    Dense {p : PlufSpace E | ∃ v : E, ∃ hv : v ≠ 0, p = principal hv} := by
  rw [isTopologicalBasis_plufBasis.dense_iff]
  rintro s ⟨M, hM, rfl⟩ ⟨p, hp⟩
  have hMbot : M ≠ ⊥ := p.isPluf'.ne_bot hp
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMbot
  exact ⟨principal hv0, (mem_principalPluf).mpr ⟨hM, hvM⟩, v, hv0, rfl⟩

/-! ### Non-compactness -/

section NotCompact

variable {u v : E}

omit [CompleteSpace E] in
/-- A line inside the plane spanned by an independent pair is either the
    line of `v` or the line of `u + t • v`. -/
theorem line_in_span_pair
    {w : E} (hw : w ∈ Submodule.span ℝ ({u, v} : Set E)) (hw0 : w ≠ 0) :
    (ℝ ∙ w) = (ℝ ∙ v) ∨ ∃ t : ℝ, (ℝ ∙ w) = (ℝ ∙ (u + t • v)) := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
  rcases eq_or_ne a 0 with rfl | ha
  · left
    have hb : b ≠ 0 := by
      rintro rfl
      exact hw0 (by simpa using hab.symm)
    have : w = b • v := by rw [← hab]; simp
    rw [this, Submodule.span_singleton_smul_eq (IsUnit.mk0 b hb)]
  · right
    refine ⟨b / a, ?_⟩
    have : w = a • (u + (b / a) • v) := by
      rw [← hab, smul_add, smul_smul, mul_div_cancel₀ _ ha]
    rw [this, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha)]

omit [CompleteSpace E] in
theorem add_smul_ne_zero (hind : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) (t : ℝ) :
    u + t • v ≠ 0 := by
  intro h
  have := (hind 1 t (by simpa using h)).1
  norm_num at this

omit [CompleteSpace E] in
theorem not_mem_span_v (hind : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) (t : ℝ) :
    u + t • v ∉ (ℝ ∙ v) := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have h0 : (1 : ℝ) • u + (t - c) • v = 0 := by
    have hexp : (1 : ℝ) • u + (t - c) • v = (u + t • v) - c • v := by module
    rw [hexp, ← hc, sub_self]
  have := (hind 1 (t - c) h0).1
  norm_num at this

omit [CompleteSpace E] in
theorem eq_of_mem_span_add_smul (hind : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0)
    {t s : ℝ} (h : u + t • v ∈ (ℝ ∙ (u + s • v))) : t = s := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have h0 : (1 - c) • u + (t - c * s) • v = 0 := by
    have hexp : (1 - c) • u + (t - c * s) • v = (u + t • v) - c • (u + s • v) := by module
    rw [hexp, ← hc, sub_self]
  obtain ⟨h1, h2⟩ := hind _ _ h0
  have hc1 : c = 1 := by linarith
  rw [hc1] at h2
  linarith

/-- Proposition 2.4, non-compactness: if `E` has a two-dimensional
    subspace then the pluf space is not compact.  Inside the plane
    `M = span {u, v}` the closed set `M̂` consists exactly of the principal
    plufs of the lines of `M`, an infinite discrete family. -/
theorem not_compactSpace [Nontrivial E]
    (hind : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) :
    ¬ CompactSpace (PlufSpace E) := by
  intro hcomp
  set M : Submodule ℝ E := Submodule.span ℝ ({u, v} : Set E) with hMdef
  haveI hMfin : FiniteDimensional ℝ ↥M :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_singleton v).insert u)
  have hMclosed : IsClosed (M : Set E) := Submodule.closed_of_finiteDimensional M
  have huM : u ∈ M := Submodule.subset_span (by simp)
  have hvM : v ∈ M := Submodule.subset_span (by simp)
  have hv0 : v ≠ 0 := by
    intro h
    have := (hind 0 1 (by simp [h])).2
    norm_num at this
  -- the cover of `M̂` by the lines of `M`
  set U : Option ℝ → Set (PlufSpace E) := fun i =>
    match i with
    | none => hat (ℝ ∙ v)
    | some t => hat (ℝ ∙ (u + t • v)) with hUdef
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none =>
        refine isOpen_hat ?_
        haveI : FiniteDimensional ℝ ↥(ℝ ∙ v : Submodule ℝ E) := FiniteDimensional.span_singleton ℝ v
        exact Submodule.closed_of_finiteDimensional _
    | some t =>
        refine isOpen_hat ?_
        haveI : FiniteDimensional ℝ ↥(ℝ ∙ (u + t • v) : Submodule ℝ E) :=
          FiniteDimensional.span_singleton ℝ _
        exact Submodule.closed_of_finiteDimensional _
  have hcover : hat M ⊆ ⋃ i, U i := by
    intro p hp
    obtain ⟨L, hL1, hL⟩ := principal_of_finiteDimensional p.carrier p.isPluf' M hp hMfin
    have hLbot : L ≠ ⊥ := by
      intro h
      rw [h] at hL1
      simp at hL1
    obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLbot
    haveI : FiniteDimensional ℝ ↥L :=
      Module.finite_of_finrank_pos (by rw [hL1]; norm_num)
    have hLeq : (ℝ ∙ w) = L := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rwa [Submodule.span_singleton_le_iff_mem]
      · rw [hL1, finrank_span_singleton hw0]
    have hLclosed : IsClosed (L : Set E) := Submodule.closed_of_finiteDimensional L
    have hLmem : L ∈ p.carrier := (hL L hLclosed).mpr le_rfl
    have hLM : L ≤ M := (hL M hMclosed).mp hp
    have hwM : w ∈ M := hLM hwL
    rcases line_in_span_pair hwM hw0 with hcase | ⟨t, hcase⟩
    · refine Set.mem_iUnion.mpr ⟨none, ?_⟩
      show (ℝ ∙ v) ∈ p.carrier
      rw [← hcase, hLeq]
      exact hLmem
    · refine Set.mem_iUnion.mpr ⟨some t, ?_⟩
      show (ℝ ∙ (u + t • v)) ∈ p.carrier
      rw [← hcase, hLeq]
      exact hLmem
  have hMcompact : IsCompact (hat M) := (isClopen_hat hMclosed).1.isCompact
  obtain ⟨F, hF⟩ := hMcompact.elim_finite_subcover U hUopen hcover
  -- every `t` contributes its own index
  have hmem : ∀ t : ℝ, (some t) ∈ F := by
    intro t
    have hne := add_smul_ne_zero hind t
    have hpM : principal hne ∈ hat M := by
      show M ∈ (principal hne).carrier
      exact (mem_principalPluf).mpr ⟨hMclosed, M.add_mem huM (M.smul_mem t hvM)⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hF hpM)
    obtain ⟨hiF, hiU⟩ := Set.mem_iUnion.mp hi
    cases i with
    | none =>
        exfalso
        have : (ℝ ∙ v) ∈ (principal hne).carrier := hiU
        exact not_mem_span_v hind t ((mem_principalPluf).mp this).2
    | some s =>
        have hmm : (ℝ ∙ (u + s • v)) ∈ (principal hne).carrier := hiU
        have := eq_of_mem_span_add_smul hind ((mem_principalPluf).mp hmm).2
        rwa [this]
  have hinj : Function.Injective (fun t : ℝ => (⟨some t, hmem t⟩ : {i // i ∈ F})) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa using this
  haveI : Finite {i // i ∈ F} := inferInstance
  haveI : Finite ℝ := Finite.of_injective _ hinj
  exact not_finite ℝ

end NotCompact

end PlufSpace

end PlufWO6
