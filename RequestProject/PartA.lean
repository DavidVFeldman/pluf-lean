/-
  PartA.lean — Part A of Work Order 1 for the pluf project (Feldman–Wilce):
  σ-Q-point combinatorics for ultrafilters on a well-ordered type.
-/
import Mathlib

open Set

namespace PlufWO1

/-! ### Part A: σ-Q-points -/

section SigmaQ

variable {κ : Type*} [LinearOrder κ] [WellFoundedLT κ]

/-- A partial selector meets each piece of a family at most once. -/
def IsPartialSelector (S : Set κ) {ι : Type*} (P : ι → Set κ) : Prop :=
  ∀ i, (S ∩ P i).Subsingleton

/-- `U` is a σ-Q-point: every countable-to-one function is injective on a
    set of `U`. This is the κ-analogue of the Q-point property, with
    "finite-to-one" promoted to "countable-to-one". -/
def SigmaQPoint (U : Ultrafilter κ) : Prop :=
  ∀ g : κ → κ, (∀ y, (g ⁻¹' {y}).Countable) → ∃ S ∈ U, Set.InjOn g S

/-- `U` has the Fodor property: every function regressive on a set of `U`
    is constant on a set of `U`. (For a normal measure this is the standard
    Fodor/pressing-down lemma; we take it as the defining hypothesis so that
    Part A is free of large-cardinal machinery.) -/
def FodorProperty (U : Ultrafilter κ) : Prop :=
  ∀ f : κ → κ, {x | f x < x} ∈ U → ∃ y, {x | f x = y} ∈ U

omit [LinearOrder κ] [WellFoundedLT κ] in
/-- A1. Union of two non-members of an ultrafilter is a non-member. -/
theorem not_mem_union_of_not_mem (U : Ultrafilter κ) {A B : Set κ}
    (hA : A ∉ U) (hB : B ∉ U) : A ∪ B ∉ U := by
  simpa [Ultrafilter.union_mem_iff] using And.intro hA hB

/-- Auxiliary construction shared by A2′ and A3: for a partition of `κ` into
    pairwise disjoint, countable, nonempty pieces, the "least element of my
    piece" function `g`.  It is countable-to-one, regressive-or-equal,
    stays inside the piece, and is constant on each piece. -/
private theorem exists_piece_min_fun {ι : Type*} (P : ι → Set κ)
    (hdisj : Pairwise (Function.onFun Disjoint P))
    (hctble : ∀ i, (P i).Countable) (hne : ∀ i, (P i).Nonempty)
    (hcover : (⋃ i, P i) = univ) :
    ∃ g : κ → κ, (∀ y, {x | g x = y}.Countable) ∧ (∀ x, g x ≤ x) ∧
      (∀ i, ∀ x ∈ P i, g x ∈ P i) ∧ (∀ i, ∀ x ∈ P i, ∀ y ∈ P i, g x = g y) := by
  classical
  have hex : ∀ x : κ, ∃ i, x ∈ P i := by
    intro x
    have hx : x ∈ (⋃ i, P i) := by rw [hcover]; trivial
    simpa using hx
  set idx : κ → ι := fun x => (hex x).choose with hidx
  have hmemidx : ∀ x, x ∈ P (idx x) := fun x => (hex x).choose_spec
  have hunique : ∀ (i : ι) (x : κ), x ∈ P i → idx x = i := by
    intro i x hx
    by_contra hne'
    exact Set.disjoint_left.mp (hdisj hne') (hmemidx x) hx
  set mn : ι → κ := fun i => wellFounded_lt.min (P i) (hne i) with hmn
  have hmnmem : ∀ i, mn i ∈ P i := fun i => wellFounded_lt.min_mem _ _
  have hmnle : ∀ (i : ι) (x : κ), x ∈ P i → mn i ≤ x := fun i x hx =>
    not_lt.mp (wellFounded_lt.not_lt_min (P i) (hne i) hx)
  refine ⟨fun x => mn (idx x), ?_, ?_, ?_, ?_⟩
  · -- countable fibers
    intro y
    rcases Set.eq_empty_or_nonempty {x | mn (idx x) = y} with h | ⟨x0, hx0⟩
    · rw [h]; exact Set.countable_empty
    · refine Set.Countable.mono ?_ (hctble (idx x0))
      intro x hx
      have h1 : mn (idx x) = mn (idx x0) := by
        simp only [Set.mem_setOf_eq] at hx hx0
        rw [hx, hx0]
      have h3 : mn (idx x) ∈ P (idx x0) := by rw [h1]; exact hmnmem _
      have h4 := (hunique _ _ (hmnmem (idx x))).symm.trans (hunique _ _ h3)
      rw [← h4]
      exact hmemidx x
  · intro x
    exact hmnle _ _ (hmemidx x)
  · intro i x hx
    show mn (idx x) ∈ P i
    rw [hunique i x hx]
    exact hmnmem i
  · intro i x hx y hy
    show mn (idx x) = mn (idx y)
    rw [hunique i x hx, hunique i y hy]

/-- A2 (partition form ⇒ function form). If every partition of `κ` into
    countable nonempty pieces admits a partial selector in `U`, then `U` is a
    σ-Q-point. (The pieces are the fibers of `g`; injectivity on `S` is the
    selector property.)

    Restatement note: the index type `ι` of the hypothesis is taken in the
    same universe as `κ` rather than in `Type`; this is forced, since the
    partition applied to is the fiber partition of `g`, whose index type is a
    subtype of `κ`.  For `κ : Type` the statement below is verbatim the
    contract statement (see `sigmaQ_of_partition_selectors₀`). -/
theorem sigmaQ_of_partition_selectors {κ : Type u} [LinearOrder κ] [WellFoundedLT κ]
    (U : Ultrafilter κ)
    (h : ∀ {ι : Type u} (P : ι → Set κ), Pairwise (Function.onFun Disjoint P) →
      (∀ i, (P i).Countable) → (∀ i, (P i).Nonempty) →
      (⋃ i, P i) = univ → ∃ S ∈ U, IsPartialSelector S P) :
    SigmaQPoint U := by
  intro g hg
  have hdisj : Pairwise (Function.onFun Disjoint (fun y : Set.range g => g ⁻¹' {(y : κ)})) := by
    intro y z hyz
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    apply hyz
    have : (y : κ) = (z : κ) := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
      rw [← hx, ← hx']
    exact Subtype.ext this
  obtain ⟨S, hSU, hS⟩ := h (fun y : Set.range g => g ⁻¹' {(y : κ)}) hdisj
    (fun y => hg _)
    (fun y => by obtain ⟨x, hx⟩ := y.2; exact ⟨x, by simp [hx]⟩)
    (by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨⟨g x, x, rfl⟩, by simp⟩)
  refine ⟨S, hSU, ?_⟩
  intro a ha b hb hab
  have hya : g a ∈ Set.range g := ⟨a, rfl⟩
  exact hS ⟨g a, hya⟩ ⟨ha, by simp⟩ ⟨hb, by simp [hab]⟩

/-- A2 at `κ : Type`: verbatim the contract statement. -/
theorem sigmaQ_of_partition_selectors₀ {κ : Type} [LinearOrder κ] [WellFoundedLT κ]
    (U : Ultrafilter κ)
    (h : ∀ {ι : Type} (P : ι → Set κ), Pairwise (Function.onFun Disjoint P) →
      (∀ i, (P i).Countable) → (∀ i, (P i).Nonempty) →
      (⋃ i, P i) = univ → ∃ S ∈ U, IsPartialSelector S P) :
    SigmaQPoint U :=
  sigmaQ_of_partition_selectors U (fun P => h P)

/-- A2′ (function form ⇒ partition form). The converse: from σ-Q-ness,
    selectors for every partition into countable nonempty pieces, via the
    least-element-of-my-piece function. (`ι` is lifted from `Type` to
    `Type*`, a free strengthening.) -/
theorem partition_selectors_of_sigmaQ (U : Ultrafilter κ)
    (hU : SigmaQPoint U) {ι : Type*} (P : ι → Set κ)
    (hdisj : Pairwise (Function.onFun Disjoint P))
    (hctble : ∀ i, (P i).Countable) (hne : ∀ i, (P i).Nonempty)
    (hcover : (⋃ i, P i) = univ) :
    ∃ S ∈ U, IsPartialSelector S P := by
  obtain ⟨g, hgc, -, -, hgconst⟩ := exists_piece_min_fun P hdisj hctble hne hcover
  obtain ⟨S, hSU, hSinj⟩ := hU g (fun y => hgc y)
  refine ⟨S, hSU, ?_⟩
  intro i a ha b hb
  exact hSinj ha.1 hb.1 (hgconst i a ha.2 b hb.2)

/-- A3 (normal ⇒ σ-Q, sharp form). Under the Fodor property and countable
    incompleteness-avoidance (no countable set in `U`), the set of
    piece-minima of any partition into countable nonempty pieces lies in `U`
    — and it is a partial selector. (`ι` is lifted from `Type` to `Type*`, a
    free strengthening.) -/
theorem minima_mem_of_fodor (U : Ultrafilter κ)
    (hfodor : FodorProperty U)
    (hcc : ∀ s : Set κ, s.Countable → s ∉ U)
    {ι : Type*} (P : ι → Set κ)
    (hdisj : Pairwise (Function.onFun Disjoint P))
    (hctble : ∀ i, (P i).Countable) (hne : ∀ i, (P i).Nonempty)
    (hcover : (⋃ i, P i) = univ) :
    ∃ S ∈ U, IsPartialSelector S P := by
  obtain ⟨g, hgc, hgle, -, hgconst⟩ := exists_piece_min_fun P hdisj hctble hne hcover
  have hM : {x | g x = x} ∈ U := by
    by_contra hM
    have hMc : {x | g x = x}ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hM
    have hreg : {x | g x < x} ∈ U := by
      refine Filter.mem_of_superset hMc ?_
      intro x hx
      exact lt_of_le_of_ne (hgle x) hx
    obtain ⟨y, hy⟩ := hfodor g hreg
    exact hcc _ (hgc y) hy
  refine ⟨_, hM, ?_⟩
  intro i a ha b hb
  have h1 : g a = g b := hgconst i a ha.2 b hb.2
  have h2 : g a = a := ha.1
  have h3 : g b = b := hb.1
  rw [← h2, ← h3, h1]

/-- A3′ packaging: Fodor plus countable-set avoidance implies σ-Q. -/
theorem sigmaQ_of_fodor (U : Ultrafilter κ)
    (hfodor : FodorProperty U)
    (hcc : ∀ s : Set κ, s.Countable → s ∉ U) :
    SigmaQPoint U := by
  refine sigmaQ_of_partition_selectors U ?_
  intro ι P hdisj hctble hne hcover
  exact minima_mem_of_fodor U hfodor hcc P hdisj hctble hne hcover

omit [LinearOrder κ] [WellFoundedLT κ] in
/-- A4 (transversal escape). Pairwise disjoint sets each containing two
    points admit a transversal outside the ultrafilter: choose two disjoint
    transversals; at most one lies in `U`. -/
theorem exists_transversal_not_mem (U : Ultrafilter κ) {ι : Type*}
    (σ : ι → Set κ) (hdisj : Pairwise (Function.onFun Disjoint σ))
    (h2 : ∀ i, ∃ a b, a ∈ σ i ∧ b ∈ σ i ∧ a ≠ b) :
    ∃ D : Set κ, (∀ i, (D ∩ σ i).Nonempty) ∧ D ∉ U := by
  classical
  choose a b ha hb hab using h2
  have hne : ∀ (i j : ι), a i ≠ b j := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact hab i
    · intro h
      exact Set.disjoint_left.mp (hdisj hij) (ha i) (h ▸ hb j)
  have hdisjAB : Disjoint (Set.range a) (Set.range b) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    exact hne i j hj.symm
  have hA : ∀ i, (Set.range a ∩ σ i).Nonempty := fun i => ⟨a i, ⟨i, rfl⟩, ha i⟩
  have hB : ∀ i, (Set.range b ∩ σ i).Nonempty := fun i => ⟨b i, ⟨i, rfl⟩, hb i⟩
  by_cases hmem : Set.range a ∈ U
  · refine ⟨Set.range b, hB, ?_⟩
    intro hb'
    have : (Set.range a ∩ Set.range b) ∈ U := U.inter_mem hmem hb'
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisjAB] at this
    exact U.empty_notMem this
  · exact ⟨Set.range a, hA, hmem⟩

end SigmaQ

end PlufWO1
