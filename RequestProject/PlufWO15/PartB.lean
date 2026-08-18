/-
  PlufWO15/PartB.lean — Work Order 15, Part B: the ω₁ recursion.

  The pattern is WO-12's, and is used unchanged: plain well-founded
  recursion on `Ordinal.{u}` with the stage choice in a `dite`
  (`WellFounded.fix` + `WellFounded.fix_eq`), the stage invariant proved
  afterwards by `Ordinal.induction` over the history. No successor/limit
  split. The history `AccFam` and the stage predicate `StageOK` are
  top-level definitions.
-/
import RequestProject.PlufWO15.PartA

open Set Cardinal PlufWO13

namespace PlufWO15

universe u

/-- The history at stage `a`: everything produced strictly before `a`,
    together with `⊤` (so that the stage-zero history is already
    admissible). -/
def AccFam (c : Ordinal.{u} → Set (Submodule ℝ H)) (a : Ordinal.{u}) :
    Set (Submodule ℝ H) :=
  {⊤} ∪ {M | ∃ p, ∃ _ : p < a, M ∈ c p}

/-- The stage predicate: `F` is an admissible extension of the history `S`
    containing `⊤` and deciding `p`. -/
def StageOK (S : Set (Submodule ℝ H)) (p : Submodule ℝ H)
    (F : Set (Submodule ℝ H)) : Prop :=
  Admissible F ∧ (⊤ : Submodule ℝ H) ∈ F ∧ S ⊆ F ∧ Decides F p

/-- The history below a countable ordinal is admissible: A2 applied to the
    countable index `Option {p // p < a}` (the `none` branch contributing
    `{⊤}`, which makes the index nonempty even at `a = 0`). -/
theorem admissible_accFam {c : Ordinal.{u} → Set (Submodule ℝ H)} {a : Ordinal.{u}}
    (ha : a < (aleph.{u} 1).ord)
    (hadm : ∀ p, p < a → Admissible (c p))
    (htop : ∀ p, p < a → (⊤ : Submodule ℝ H) ∈ c p)
    (hmono : ∀ p q, p ≤ q → q < a → c p ⊆ c q) :
    Admissible (AccFam c a) ∧ (⊤ : Submodule ℝ H) ∈ AccFam c a := by
  classical
  haveI : Countable {p : Ordinal.{u} // p < a} :=
    (PlufWO11.countable_Iio_of_lt_omega1 ha).to_subtype
  set F : Option {p : Ordinal.{u} // p < a} → Set (Submodule ℝ H) :=
    fun i => match i with
      | none => {⊤}
      | some p => c p.1 with hF
  have hFadm : ∀ i, Admissible (F i) := by
    rintro (_ | p)
    · exact admissible_singleton_top
    · exact hadm p.1 p.2
  have hFtop : ∀ i, (⊤ : Submodule ℝ H) ∈ F i := by
    rintro (_ | p)
    · rfl
    · exact htop p.1 p.2
  have hFdir : ∀ i j, ∃ k, F i ⊆ F k ∧ F j ⊆ F k := by
    rintro (_ | p) (_ | q)
    · exact ⟨none, subset_rfl, subset_rfl⟩
    · exact ⟨some q, by simpa [hF] using Set.singleton_subset_iff.mpr (htop q.1 q.2),
        subset_rfl⟩
    · exact ⟨some p, subset_rfl, by
        simpa [hF] using Set.singleton_subset_iff.mpr (htop p.1 p.2)⟩
    · rcases le_total p.1 q.1 with h | h
      · exact ⟨some q, hmono p.1 q.1 h q.2, subset_rfl⟩
      · exact ⟨some p, subset_rfl, hmono q.1 p.1 h p.2⟩
  have hunion : (⋃ i, F i) = AccFam c a := by
    ext M
    simp only [Set.mem_iUnion, AccFam, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨(_ | p), hi⟩
      · exact Or.inl hi
      · exact Or.inr ⟨p.1, p.2, hi⟩
    · rintro (rfl | ⟨p, hp, hM⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨p, hp⟩, hM⟩
  have := admissible_iUnion_aux F hFadm hFtop hFdir
  rw [hunion] at this
  exact this

/-- B1 (the chain), as consumed by Part C. -/
theorem exists_admissible_chain_aux (hCH : continuum = aleph 1) :
    ∃ c : Ordinal.{u} → Set (Submodule ℝ H),
      (∀ a b, a ≤ b → b < (aleph.{u} 1).ord → c a ⊆ c b) ∧
      (∀ a, a < (aleph.{u} 1).ord → Admissible (c a)) ∧
      (∀ a, a < (aleph.{u} 1).ord → (⊤ : Submodule ℝ H) ∈ c a) ∧
      (∀ p : Submodule ℝ H, IsClosed (p : Set H) →
        ∃ a, a < (aleph.{u} 1).ord ∧ Decides (c a) p) := by
  classical
  obtain ⟨f, hf⟩ := PlufWO11.exists_enum_closedSubspaces hCH
  set sub : Ordinal.{u} → Submodule ℝ H :=
    fun o => if h : o < (aleph.{u} 1).ord then (f ⟨o, h⟩ : Submodule ℝ H) else ⊤ with hsub
  have hsubcl : ∀ o : Ordinal.{u}, IsClosed ((sub o : Submodule ℝ H) : Set H) := by
    intro o
    rw [hsub]
    dsimp only
    split
    · exact (f _).2
    · simp
  set Φ : (a : Ordinal.{u}) →
      ((p : Ordinal.{u}) → p < a → Set (Submodule ℝ H)) → Set (Submodule ℝ H) :=
    fun a ih =>
      if hex : ∃ F, StageOK ({⊤} ∪ {M | ∃ p, ∃ hp : p < a, M ∈ ih p hp}) (sub a) F then
        hex.choose
      else {⊤} with hΦ
  set c : Ordinal.{u} → Set (Submodule ℝ H) :=
    (inferInstanceAs (WellFoundedLT Ordinal.{u})).wf.fix Φ with hc
  have hceq : ∀ a : Ordinal.{u}, c a = Φ a (fun p _ => c p) := by
    intro a
    rw [hc]
    exact WellFounded.fix_eq _ Φ a
  have hgood : ∀ a : Ordinal.{u}, a < (aleph.{u} 1).ord →
      StageOK (AccFam c a) (sub a) (c a) := by
    intro a
    induction a using Ordinal.induction with
    | h a IH =>
        intro ha
        have hIH : ∀ p, p < a → StageOK (AccFam c p) (sub p) (c p) := fun p hp =>
          IH p hp (lt_trans hp ha)
        have hmono : ∀ p q, p ≤ q → q < a → c p ⊆ c q := by
          intro p q hpq hq M hM
          rcases eq_or_lt_of_le hpq with rfl | hlt
          · exact hM
          · exact (hIH q hq).2.2.1 (Or.inr ⟨p, hlt, hM⟩)
        obtain ⟨hAadm, hAtop⟩ :=
          admissible_accFam ha (fun p hp => (hIH p hp).1) (fun p hp => (hIH p hp).2.1) hmono
        obtain ⟨F, hFadm, hFtop, hFsub, hFdec⟩ :=
          exists_admissible_decides_aux hAadm hAtop (sub a) (hsubcl a)
        have hex : ∃ F, StageOK (AccFam c a) (sub a) F := ⟨F, hFadm, hFtop, hFsub, hFdec⟩
        have hca : c a = hex.choose := by
          rw [hceq a, hΦ]
          exact dif_pos hex
        rw [hca]
        exact hex.choose_spec
  refine ⟨c, ?_, fun a ha => (hgood a ha).1, fun a ha => (hgood a ha).2.1, ?_⟩
  · intro a b hab hb M hM
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact hM
    · exact (hgood b hb).2.2.1 (Or.inr ⟨a, hlt, hM⟩)
  · intro p hp
    obtain ⟨o, ho⟩ := hf ⟨p, hp⟩
    refine ⟨o.1, o.2, ?_⟩
    have hsubo : sub o.1 = p := by
      rw [hsub]
      dsimp only
      rw [dif_pos o.2]
      have : (⟨(o : Ordinal.{u}), o.2⟩ : {x : Ordinal.{u} // x < (aleph.{u} 1).ord}) = o :=
        Subtype.ext rfl
      rw [this, ho]
    have := (hgood o.1 o.2).2.2.2
    rwa [hsubo] at this

end PlufWO15
