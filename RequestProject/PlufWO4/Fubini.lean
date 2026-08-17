/-
  PlufWO4/Fubini.lean — Work Order 4, Part B: the Fubini product of two
  ultrafilters, its basic largeness facts, the full-selector property and
  its failure for the product, and the non-isomorphism packaging.
-/
import RequestProject.PlufWO4.Homog

open Set

namespace PlufWO4

/-! ### Part B: the Fubini product -/

section Fubini

universe u v

variable {κ : Type v} [LinearOrder κ]

/-- The Fubini product of two ultrafilters on `κ`, as an ultrafilter on
    `κ × κ`: a set is large iff `D₁`-many sections are `D₂`-large.

    Census note: Mathlib has no `Ultrafilter.prod`, but it does have the
    monadic `Ultrafilter.bind`, of which the Fubini product is the
    instance along `β ↦ (γ, β)`; `mem_fubini_iff` is the bridging lemma. -/
noncomputable def fubini (D₁ D₂ : Ultrafilter κ) : Ultrafilter (κ × κ) :=
  D₁.bind fun γ => Ultrafilter.map (fun β => (γ, β)) D₂

omit [LinearOrder κ] in
theorem mem_fubini_iff (D₁ D₂ : Ultrafilter κ) (X : Set (κ × κ)) :
    X ∈ fubini D₁ D₂ ↔ {γ | {β | (γ, β) ∈ X} ∈ D₂} ∈ D₁ := by
  constructor
  · intro hX
    exact hX
  · intro hX
    exact hX

/-- B1. The upper triangle of a set of `D` is large in the self-product.
    Needs that tails `{β | γ < β}` lie in `D`; taken as the hypothesis
    `htail` (true for any uniform/normal ultrafilter on a cardinal). -/
theorem triangle_mem_fubini (D : Ultrafilter κ)
    (htail : ∀ γ : κ, {β | γ < β} ∈ D) {H : Set κ} (hH : H ∈ D) :
    {p : κ × κ | p.1 ∈ H ∧ p.2 ∈ H ∧ p.1 < p.2} ∈ fubini D D := by
  rw [mem_fubini_iff]
  refine Filter.mem_of_superset hH ?_
  intro γ hγ
  have : H ∩ {β | γ < β} ∈ D := Filter.inter_mem hH (htail γ)
  refine Filter.mem_of_superset this ?_
  rintro β ⟨hβH, hβ⟩
  exact ⟨hγ, hβH, hβ⟩

omit [LinearOrder κ] in
/-- B2. Countable sets are small in the product, given that they are
    small in each factor. -/
theorem countableSmall_fubini (D : Ultrafilter κ)
    (hcs : ∀ s : Set κ, s.Countable → sᶜ ∈ D) :
    ∀ s : Set (κ × κ), s.Countable → sᶜ ∈ fubini D D := by
  intro s hs
  rw [mem_fubini_iff]
  have : {γ : κ | {β | (γ, β) ∈ sᶜ} ∈ D} = univ := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hsec : {β : κ | (γ, β) ∈ s}.Countable := by
      have : {β : κ | (γ, β) ∈ s} = (fun β : κ => (γ, β)) ⁻¹' s := rfl
      rw [this]
      exact hs.preimage (fun a b hab => by simpa using hab)
    have := hcs _ hsec
    exact this
  rw [this]
  exact Filter.univ_mem

/-- B3. No column `{γ} × κ` lies in the product. -/
theorem column_notMem_fubini (D : Ultrafilter κ)
    (hpr : ∀ γ : κ, {γ}ᶜ ∈ D) (γ : κ) :
    ({γ} ×ˢ (Set.univ : Set κ)) ∉ fubini D D := by
  rw [mem_fubini_iff]
  intro hmem
  have hsub : {γ' : κ | {β | (γ', β) ∈ ({γ} ×ˢ (Set.univ : Set κ))} ∈ D} ⊆ {γ} := by
    intro γ' hγ'
    simp only [Set.mem_setOf_eq] at hγ'
    by_contra hne
    have hempty : {β : κ | (γ', β) ∈ ({γ} ×ˢ (Set.univ : Set κ))} = ∅ := by
      ext β
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
        and_true, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne (by simpa using h)
    rw [hempty] at hγ'
    exact D.empty_notMem hγ'
  have : ({γ} : Set κ) ∈ D := Filter.mem_of_superset hmem hsub
  exact (Ultrafilter.compl_mem_iff_notMem.mp (hpr γ)) this

/-- The full-selector property: every partition into pieces outside the
    ultrafilter admits a set of the ultrafilter meeting each piece at
    most once. (No countability restriction; contrast `SigmaQPoint`.)
    This property mentions no order, hence is invariant under
    `Ultrafilter.map` along bijections. -/
def FullSelector {X : Type*} (U : Ultrafilter X) : Prop :=
  ∀ {ι : Type} (P : ι → Set X), Pairwise (Function.onFun Disjoint P) →
    (∀ i, P i ∉ U) → (⋃ i, P i) = univ →
    ∃ S ∈ U, PlufWO1.IsPartialSelector S P

/-- The same property with the index type in an arbitrary universe.  It is
    needed for B5/B7 at a `κ` outside `Type 0` (the column partition of
    `κ × κ` is indexed by `κ` itself); `FullSelector` is its instance at
    `Type 0`. -/
def FullSelectorAll {X : Type*} (U : Ultrafilter X) : Prop :=
  ∀ {ι : Type u} (P : ι → Set X), Pairwise (Function.onFun Disjoint P) →
    (∀ i, P i ∉ U) → (⋃ i, P i) = univ →
    ∃ S ∈ U, PlufWO1.IsPartialSelector S P

theorem fullSelector_of_all {X : Type*} {U : Ultrafilter X}
    (h : FullSelectorAll.{0} U) : FullSelector U :=
  fun P => h P

/-- B4 (Paper IV, Lemma 2.2), universe-polymorphic form. The Fodor
    property yields full selectors: the set of piece-minima lies in `D`.
    The proof is the certified minima argument of WO-1's A3 with
    countability of the pieces deleted: a `D`-large set inside one piece
    now contradicts `P i ∉ D` directly. -/
theorem fullSelectorAll_of_fodor {κ : Type} [LinearOrder κ] [WellFoundedLT κ]
    (D : Ultrafilter κ) (hfodor : PlufWO1.FodorProperty D) :
    FullSelectorAll.{u} D := by
  classical
  intro ι P hdisj hnot hcover
  have hex : ∀ x : κ, ∃ i, x ∈ P i := by
    intro x
    have hx : x ∈ (⋃ i, P i) := by rw [hcover]; trivial
    simpa using hx
  set idx : κ → ι := fun x => (hex x).choose with hidx
  have hmemidx : ∀ x, x ∈ P (idx x) := fun x => (hex x).choose_spec
  have huniq : ∀ (i : ι) (x : κ), x ∈ P i → idx x = i := by
    intro i x hx
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hmemidx x) hx
  set g : κ → κ := fun x => wellFounded_lt.min (P (idx x)) ⟨x, hmemidx x⟩ with hg
  have hgmem : ∀ x, g x ∈ P (idx x) := fun x => wellFounded_lt.min_mem _ _
  have hgle : ∀ x, g x ≤ x := fun x =>
    not_lt.mp (wellFounded_lt.not_lt_min (P (idx x)) ⟨x, hmemidx x⟩ (hmemidx x))
  have hgeq : ∀ x y : κ, idx x = idx y → g x = g y := by
    intro x y h
    simp only [hg]
    congr 1
    exact congrArg P h
  have hM : {x : κ | g x = x} ∈ D := by
    by_contra hM
    have hMc : {x : κ | g x = x}ᶜ ∈ D := Ultrafilter.compl_mem_iff_notMem.mpr hM
    have hreg : {x : κ | g x < x} ∈ D :=
      Filter.mem_of_superset hMc (fun x hx => lt_of_le_of_ne (hgle x) hx)
    obtain ⟨y, hy⟩ := hfodor g hreg
    -- every `x` with `g x = y` lies in the single piece containing `y`
    have hsub : {x : κ | g x = y} ⊆ P (idx y) := by
      intro x hx
      have hyP : y ∈ P (idx x) := by
        have := hgmem x
        rwa [hx] at this
      have : idx y = idx x := huniq _ _ hyP
      rw [this]
      exact hmemidx x
    exact hnot (idx y) (Filter.mem_of_superset hy hsub)
  refine ⟨_, hM, ?_⟩
  intro i a ha b hb
  have h1 : idx a = idx b := by rw [huniq i a ha.2, huniq i b hb.2]
  have h2 : g a = g b := hgeq a b h1
  have h3 : g a = a := ha.1
  have h4 : g b = b := hb.1
  rw [← h3, ← h4, h2]

/-- B4 (Paper IV, Lemma 2.2), contract form. -/
theorem fullSelector_of_fodor {κ : Type} [LinearOrder κ] [WellFoundedLT κ]
    (D : Ultrafilter κ) (hfodor : PlufWO1.FodorProperty D) :
    FullSelector D :=
  fullSelector_of_all (fullSelectorAll_of_fodor D hfodor)

/-- B5 (Paper IV, Proposition 2.3, combinatorial half), universe-polymorphic
    form. The self-product fails the full-selector property: the column
    partition has no piece in the product, and any partial selector has
    singleton sections. -/
theorem not_fullSelectorAll_fubini (D : Ultrafilter κ)
    (hpr : ∀ γ : κ, {γ}ᶜ ∈ D) :
    ¬ FullSelectorAll.{v} (fubini D D) := by
  intro hfs
  obtain ⟨S, hS, hsel⟩ := hfs (fun γ : κ => ({γ} ×ˢ (Set.univ : Set κ)))
    (by
      intro γ γ' hne
      refine Set.disjoint_left.mpr ?_
      rintro ⟨a, b⟩ ha ha'
      have h1 : a = γ := by simpa using ha
      have h2 : a = γ' := by simpa using ha'
      exact hne (h1 ▸ h2 ▸ rfl))
    (fun γ => column_notMem_fubini D hpr γ)
    (by
      ext p
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨p.1, by simp⟩)
  rw [mem_fubini_iff] at hS
  obtain ⟨γ, hγ⟩ := Filter.nonempty_of_mem hS
  simp only [Set.mem_setOf_eq] at hγ
  -- the section of a partial selector at `γ` is a subsingleton, hence not in `D`
  have hsub : {β : κ | (γ, β) ∈ S}.Subsingleton := by
    intro a ha b hb
    have h1 : ((γ, a) : κ × κ) ∈ S ∩ ({γ} ×ˢ (Set.univ : Set κ)) := ⟨ha, by simp⟩
    have h2 : ((γ, b) : κ × κ) ∈ S ∩ ({γ} ×ˢ (Set.univ : Set κ)) := ⟨hb, by simp⟩
    have := hsel γ h1 h2
    simpa using this
  rcases Set.Subsingleton.eq_empty_or_singleton hsub with h | ⟨β₀, h⟩
  · rw [h] at hγ
    exact D.empty_notMem hγ
  · rw [h] at hγ
    exact (Ultrafilter.compl_mem_iff_notMem.mp (hpr β₀)) hγ

/-  B5, CONTRACT STATEMENT (preserved verbatim; `κ : Type*` from the
    section variable):

theorem not_fullSelector_fubini (D : Ultrafilter κ)
    (hpr : ∀ γ : κ, {γ}ᶜ ∈ D) :
    ¬ FullSelector (fubini D D)
-/

/-- B5 (Paper IV, Proposition 2.3, combinatorial half), contract form.

    RESTATEMENT (reported): the contract index type of `FullSelector` is
    `Type 0`, so the refuting column partition — which is indexed by `κ`
    itself — is available only for `κ : Type 0`; the contract statement is
    proved here at `κ : Type`.  For `κ` in an arbitrary universe the same
    refutation is `not_fullSelectorAll_fubini` above, and B7 (which is what
    the paper's Proposition 2.3 is for) is proved verbatim for all `κ`. -/
theorem not_fullSelector_fubini {κ : Type} [LinearOrder κ] (D : Ultrafilter κ)
    (hpr : ∀ γ : κ, {γ}ᶜ ∈ D) :
    ¬ FullSelector (fubini D D) := by
  intro hfs
  exact not_fullSelectorAll_fubini D hpr (fun P => hfs P)

/-- Transport of the full-selector property along an isomorphism. -/
theorem fullSelectorAll_map {X : Type*} {Y : Type*} (e : X ≃ Y) (U : Ultrafilter X)
    (h : FullSelectorAll.{u} U) : FullSelectorAll.{u} (Ultrafilter.map e U) := by
  intro ι Q hdisj hnot hcover
  obtain ⟨S, hS, hsel⟩ := h (fun i => e ⁻¹' Q i)
    (by
      intro i j hij
      refine Set.disjoint_left.mpr ?_
      intro x hx hx'
      exact Set.disjoint_left.mp (hdisj hij) hx hx')
    (by
      intro i hi
      exact hnot i (by rwa [Ultrafilter.mem_map]))
    (by
      rw [← Set.preimage_iUnion, hcover, Set.preimage_univ])
  refine ⟨e '' S, ?_, ?_⟩
  · rw [Ultrafilter.mem_map, e.preimage_image]
    exact hS
  · intro i y hy y' hy'
    obtain ⟨x, hxS, rfl⟩ := hy.1
    obtain ⟨x', hx'S, rfl⟩ := hy'.1
    have hx : x ∈ S ∩ e ⁻¹' Q i := ⟨hxS, hy.2⟩
    have hx' : x' ∈ S ∩ e ⁻¹' Q i := ⟨hx'S, hy'.2⟩
    rw [hsel i hx hx']

theorem fullSelector_map {X : Type*} {Y : Type*} (e : X ≃ Y) (U : Ultrafilter X)
    (h : FullSelector U) : FullSelector (Ultrafilter.map e U) :=
  fullSelector_of_all (fullSelectorAll_map e U (fun P => h P))

theorem map_symm_map {X : Type*} {Y : Type*} (e : X ≃ Y) (U : Ultrafilter X) :
    Ultrafilter.map e.symm (Ultrafilter.map e U) = U := by
  rw [Ultrafilter.map_map]
  have : (e.symm ∘ e) = id := funext fun x => e.symm_apply_apply x
  rw [this, Ultrafilter.map_id]

/-- B6. `FullSelector` is invariant under isomorphism of ultrafilters. -/
theorem fullSelector_map_iff {X Y : Type*} (e : X ≃ Y) (U : Ultrafilter X) :
    FullSelector (Ultrafilter.map e U) ↔ FullSelector U := by
  refine ⟨fun h => ?_, fun h => fullSelector_map e U h⟩
  have h2 : FullSelector (Ultrafilter.map e.symm (Ultrafilter.map e U)) :=
    fullSelector_map e.symm _ h
  rwa [map_symm_map e U] at h2

/-- B6, universe-polymorphic form. -/
theorem fullSelectorAll_map_iff {X Y : Type*} (e : X ≃ Y) (U : Ultrafilter X) :
    FullSelectorAll.{u} (Ultrafilter.map e U) ↔ FullSelectorAll.{u} U := by
  refine ⟨fun h => ?_, fun h => fullSelectorAll_map e U h⟩
  have h2 : FullSelectorAll.{u} (Ultrafilter.map e.symm (Ultrafilter.map e U)) :=
    fullSelectorAll_map e.symm _ h
  rwa [map_symm_map e U] at h2

/-- B7 (Paper IV, Proposition 2.3). The self-product is isomorphic to no
    ultrafilter with the Fodor property on a well-ordered type: transport
    would give it the full-selector property, refuted by B5. -/
theorem fubini_not_iso_fodor (D : Ultrafilter κ)
    (hpr : ∀ γ : κ, {γ}ᶜ ∈ D)
    {κ' : Type} [LinearOrder κ'] [WellFoundedLT κ']
    (V : Ultrafilter κ') (hV : PlufWO1.FodorProperty V)
    (e : (κ × κ) ≃ κ') :
    Ultrafilter.map e (fubini D D) ≠ V := by
  intro hEq
  have hVfs : FullSelectorAll.{v} V := fullSelectorAll_of_fodor V hV
  rw [← hEq] at hVfs
  exact not_fullSelectorAll_fubini D hpr ((fullSelectorAll_map_iff e _).mp hVfs)

/-- B8 (Paper IV, Corollary 3.2). The self-product is a σ-Q-point, given
    the Part A hypotheses on `D`: instantiate A1 at the piece-index
    function of a countable-to-one map, and intersect the selector with a
    triangle set (off-triangle points are then irrelevant). -/
theorem sigmaQ_fubini (D : Ultrafilter κ)
    (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
    (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D) :
    PlufWO1.SigmaQPoint (fubini D D) := by
  intro g hg
  obtain ⟨H, hH, hinj⟩ := inj_on_pairs D h3 h4 hpiv htail (fun a b => g (a, b))
    (by
      intro v
      refine Set.Countable.mono ?_ (hg v)
      rintro p ⟨-, hp⟩
      exact hp)
  refine ⟨{p : κ × κ | p.1 ∈ H ∧ p.2 ∈ H ∧ p.1 < p.2}, triangle_mem_fubini D htail hH, ?_⟩
  rintro ⟨a, b⟩ ⟨haH, hbH, hab⟩ ⟨a', b'⟩ ⟨ha'H, hb'H, ha'b'⟩ hgg
  obtain ⟨rfl, rfl⟩ := hinj a haH b hbH a' ha'H b' hb'H hab ha'b' hgg
  rfl

end Fubini

end PlufWO4
