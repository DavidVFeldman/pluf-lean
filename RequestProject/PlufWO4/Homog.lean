/-
  PlufWO4/Homog.lean — Work Order 4, Part A: the homogeneity framework,
  the pattern analysis over increasing triples and quadruples, and the
  injectivity-on-a-square theorem (A1).

  The mathematical heart is `exists_avoiding_homog`: the twelve-pattern
  case analysis of Paper IV, Sections 3–4, packaged once and used both for
  A1 (Theorem 3.1) and for C2 (Theorem 4.1, `EPP_fubini`).
-/
import RequestProject.PlufWO3

open Set

namespace PlufWO4

/-! ### Part A: homogeneity and injectivity on a square -/

section Homog

variable {κ : Type*} [LinearOrder κ]

/-- Rowbottom homogeneity for `n`-tuples: every finite coloring of the
    strictly increasing `n`-tuples is constant on the increasing tuples
    from a set of `D`. For a normal measure this is Rowbottom's theorem;
    here it is a hypothesis, so everything is ZFC. -/
def RowbottomFor (D : Ultrafilter κ) (n : ℕ) : Prop :=
  ∀ {C : Type} [Fintype C] [Nonempty C] (F : (Fin n → κ) → C),
    ∃ H ∈ D, ∃ c : C, ∀ t : Fin n → κ,
      StrictMono t → (∀ i, t i ∈ H) → F t = c

/-- Every set of `D` contains a point with uncountably many predecessors
    in the set. (For a normal measure on a measurable cardinal this is
    immediate from the order type; taken as a hypothesis.) -/
def UncountablePivots (D : Ultrafilter κ) : Prop :=
  ∀ S ∈ D, ∃ β ∈ S, ¬ (S ∩ Set.Iio β).Countable

/-! #### Elementary consequences of the two largeness hypotheses -/

section Tools

variable {D : Ultrafilter κ}

/-- Members of `D` are uncountable, given uncountable pivots. -/
theorem not_countable_of_mem (hpiv : UncountablePivots D) {S : Set κ} (hS : S ∈ D) :
    ¬ S.Countable := by
  intro hcnt
  obtain ⟨β, -, hβ⟩ := hpiv S hS
  exact hβ (hcnt.mono Set.inter_subset_left)

/-- Tails of a member of `D` are members of `D`. -/
theorem inter_Ioi_mem (htail : ∀ γ : κ, {β | γ < β} ∈ D) {H : Set κ} (hH : H ∈ D) (γ : κ) :
    H ∩ Set.Ioi γ ∈ D :=
  Filter.inter_mem hH (htail γ)

/-- A member of `D` is uncountable above any point. -/
theorem not_countable_inter_Ioi (hpiv : UncountablePivots D)
    (htail : ∀ γ : κ, {β | γ < β} ∈ D) {H : Set κ} (hH : H ∈ D) (γ : κ) :
    ¬ (H ∩ Set.Ioi γ).Countable :=
  not_countable_of_mem hpiv (inter_Ioi_mem htail hH γ)

/-- A member of `D` has points above any point. -/
theorem exists_mem_gt (htail : ∀ γ : κ, {β | γ < β} ∈ D) {H : Set κ} (hH : H ∈ D) (γ : κ) :
    ∃ b ∈ H, γ < b := by
  obtain ⟨b, hb⟩ := Filter.nonempty_of_mem (inter_Ioi_mem htail hH γ)
  exact ⟨b, hb.1, hb.2⟩

/-- The pivot: a point of `H` with uncountably many `H`-predecessors. -/
theorem exists_pivot (hpiv : UncountablePivots D) {H : Set κ} (hH : H ∈ D) :
    ∃ b ∈ H, ¬ (H ∩ Set.Iio b).Countable := hpiv H hH

/-- The pivot above a given point: a point `b ∈ H` above `γ` with
    uncountably many points of `H` strictly between `γ` and `b`. -/
theorem exists_mid (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D)
    {H : Set κ} (hH : H ∈ D) (γ : κ) :
    ∃ b ∈ H, γ < b ∧ ¬ (H ∩ Set.Ioo γ b).Countable := by
  obtain ⟨b, hb, hbc⟩ := hpiv _ (inter_Ioi_mem htail hH γ)
  refine ⟨b, hb.1, hb.2, fun hcnt => hbc (hcnt.mono ?_)⟩
  rintro x ⟨⟨hxH, hxγ⟩, hxb⟩
  exact ⟨hxH, hxγ, hxb⟩

end Tools

omit [LinearOrder κ] in
/-- Uncountably many pairs with a fixed left coordinate cannot all lie in a
    countable set. -/
theorem absurd_left {T : Set κ} (hT : ¬ T.Countable) {a : κ} {s : Set (κ × κ)}
    (hs : s.Countable) (h : ∀ z ∈ T, (a, z) ∈ s) : False := by
  refine hT (Set.MapsTo.countable_of_injOn (f := fun z => (a, z)) h ?_ hs)
  intro u _ v _ huv
  simpa using huv

omit [LinearOrder κ] in
/-- Uncountably many pairs with a fixed right coordinate cannot all lie in a
    countable set. -/
theorem absurd_right {T : Set κ} (hT : ¬ T.Countable) {a : κ} {s : Set (κ × κ)}
    (hs : s.Countable) (h : ∀ z ∈ T, (z, a) ∈ s) : False := by
  refine hT (Set.MapsTo.countable_of_injOn (f := fun z => (z, a)) h ?_ hs)
  intro u _ v _ huv
  simpa using huv

/-! #### Simultaneous homogenization -/

theorem strictMono_fin3 {x y z : κ} (h1 : x < y) (h2 : y < z) : StrictMono ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals order

theorem strictMono_fin4 {x y z w : κ} (h1 : x < y) (h2 : y < z) (h3 : z < w) :
    StrictMono ![x, y, z, w] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals order

/-- Homogenization of a single property of increasing triples. -/
theorem homog3 {D : Ultrafilter κ} (h3 : RowbottomFor D 3) (Q : κ → κ → κ → Prop) :
    ∃ H ∈ D, (∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → Q x y z) ∨
      (∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → ¬ Q x y z) := by
  classical
  obtain ⟨H, hH, col, hcol⟩ := h3 (C := Bool) (fun t => decide (Q (t 0) (t 1) (t 2)))
  refine ⟨H, hH, ?_⟩
  have key : ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → decide (Q x y z) = col := by
    intro x hx y hy z hz hxy hyz
    have hmem : ∀ i : Fin 3, (![x, y, z] : Fin 3 → κ) i ∈ H := by
      intro i; fin_cases i <;> simpa
    simpa using hcol ![x, y, z] (strictMono_fin3 hxy hyz) hmem
  cases hcase : col with
  | true =>
      refine Or.inl fun x hx y hy z hz hxy hyz => of_decide_eq_true ?_
      rw [key x hx y hy z hz hxy hyz, hcase]
  | false =>
      refine Or.inr fun x hx y hy z hz hxy hyz => of_decide_eq_false ?_
      rw [key x hx y hy z hz hxy hyz, hcase]

/-- Homogenization of a single property of increasing quadruples. -/
theorem homog4 {D : Ultrafilter κ} (h4 : RowbottomFor D 4) (Q : κ → κ → κ → κ → Prop) :
    ∃ H ∈ D, (∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H, x < y → y < z → z < w → Q x y z w) ∨
      (∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H, x < y → y < z → z < w → ¬ Q x y z w) := by
  classical
  obtain ⟨H, hH, col, hcol⟩ := h4 (C := Bool) (fun t => decide (Q (t 0) (t 1) (t 2) (t 3)))
  refine ⟨H, hH, ?_⟩
  have key : ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H, x < y → y < z → z < w →
      decide (Q x y z w) = col := by
    intro x hx y hy z hz w hw hxy hyz hzw
    have hmem : ∀ i : Fin 4, (![x, y, z, w] : Fin 4 → κ) i ∈ H := by
      intro i; fin_cases i <;> simpa
    simpa using hcol ![x, y, z, w] (strictMono_fin4 hxy hyz hzw) hmem
  cases hcase : col with
  | true =>
      refine Or.inl fun x hx y hy z hz w hw hxy hyz hzw => of_decide_eq_true ?_
      rw [key x hx y hy z hz w hw hxy hyz hzw, hcase]
  | false =>
      refine Or.inr fun x hx y hy z hz w hw hxy hyz hzw => of_decide_eq_false ?_
      rw [key x hx y hy z hz w hw hxy hyz hzw, hcase]

/-! #### The twelve patterns

For an ordered pair `(x, y)` of distinct increasing pairs from a
homogeneous set, the union of the two pairs is a three- or four-element
increasing tuple; there are six ordered placement patterns on a triple, and
six on a quadruple (those in which the two pairs are coordinate disjoint).
Each of the twelve lemmas below homogenizes the corresponding colouring and
refutes the "yes" colour by exhibiting uncountably many points of `c a b`
for a single pair `(a, b)`. -/

section Patterns

variable {D : Ultrafilter κ} (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
  (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D)
  (c : κ → κ → Set (κ × κ)) (hc : ∀ a b, (c a b).Countable)

include h3 hpiv htail hc in
/-- Pattern 1: `x = (h₁,h₂)`, `y = (h₁,h₃)`; refuted by freeing `h₃` upward. -/
theorem pattern₁ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → (x, z) ∉ c x y := by
  obtain ⟨H, hH, hyes | hno⟩ := homog3 h3 (fun x y z => (x, z) ∈ c x y)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt htail hH x
    exact absurd_left (not_countable_inter_Ioi hpiv htail hH y) (hc x y)
      (fun z hz => hyes x hx y hy z hz.1 hxy hz.2)
  · exact ⟨H, hH, hno⟩

include h3 hpiv htail hc in
/-- Pattern 2: `x = (h₁,h₃)`, `y = (h₁,h₂)`; refuted by freeing `h₂` below an
    uncountable pivot `h₃`. -/
theorem pattern₂ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → (x, y) ∉ c x z := by
  obtain ⟨H, hH, hyes | hno⟩ := homog3 h3 (fun x y z => (x, y) ∈ c x z)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨z, hz, -, hmid⟩ := exists_mid hpiv htail hH x
    exact absurd_left hmid (hc x z) (fun y hy => hyes x hx y hy.1 z hz hy.2.1 hy.2.2)
  · exact ⟨H, hH, hno⟩

include h3 hpiv htail hc in
/-- Pattern 3: `x = (h₁,h₂)`, `y = (h₂,h₃)`; refuted by freeing `h₃` upward. -/
theorem pattern₃ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → (y, z) ∉ c x y := by
  obtain ⟨H, hH, hyes | hno⟩ := homog3 h3 (fun x y z => (y, z) ∈ c x y)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt htail hH x
    exact absurd_left (not_countable_inter_Ioi hpiv htail hH y) (hc x y)
      (fun z hz => hyes x hx y hy z hz.1 hxy hz.2)
  · exact ⟨H, hH, hno⟩

include h3 hpiv htail hc in
/-- Pattern 4: `x = (h₂,h₃)`, `y = (h₁,h₂)`; refuted by choosing `h₂` an
    uncountable pivot and freeing `h₁` below it. -/
theorem pattern₄ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → (x, y) ∉ c y z := by
  obtain ⟨H, hH, hyes | hno⟩ := homog3 h3 (fun x y z => (x, y) ∈ c y z)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨y, hy, hpivot⟩ := exists_pivot hpiv hH
    obtain ⟨z, hz, hyz⟩ := exists_mem_gt htail hH y
    exact absurd_right hpivot (hc y z) (fun x hx => hyes x hx.1 y hy z hz hx.2 hyz)
  · exact ⟨H, hH, hno⟩

include h3 hpiv htail hc in
/-- Pattern 5: `x = (h₁,h₃)`, `y = (h₂,h₃)`; refuted by freeing `h₂` below an
    uncountable pivot `h₃`. -/
theorem pattern₅ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → (y, z) ∉ c x z := by
  obtain ⟨H, hH, hyes | hno⟩ := homog3 h3 (fun x y z => (y, z) ∈ c x z)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨z, hz, -, hmid⟩ := exists_mid hpiv htail hH x
    exact absurd_right hmid (hc x z) (fun y hy => hyes x hx y hy.1 z hz hy.2.1 hy.2.2)
  · exact ⟨H, hH, hno⟩

include h3 hpiv htail hc in
/-- Pattern 6: `x = (h₂,h₃)`, `y = (h₁,h₃)`; refuted by choosing `h₂` an
    uncountable pivot and freeing `h₁` below it. -/
theorem pattern₆ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, x < y → y < z → (x, z) ∉ c y z := by
  obtain ⟨H, hH, hyes | hno⟩ := homog3 h3 (fun x y z => (x, z) ∈ c y z)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨y, hy, hpivot⟩ := exists_pivot hpiv hH
    obtain ⟨z, hz, hyz⟩ := exists_mem_gt htail hH y
    exact absurd_right hpivot (hc y z) (fun x hx => hyes x hx.1 y hy z hz hx.2 hyz)
  · exact ⟨H, hH, hno⟩

include h4 hpiv htail hc in
/-- Pattern 7: `x = (h₁,h₂)`, `y = (h₃,h₄)`; refuted by freeing `h₄` upward. -/
theorem pattern₇ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H,
    x < y → y < z → z < w → (z, w) ∉ c x y := by
  obtain ⟨H, hH, hyes | hno⟩ := homog4 h4 (fun x y z w => (z, w) ∈ c x y)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt htail hH x
    obtain ⟨z, hz, hyz⟩ := exists_mem_gt htail hH y
    exact absurd_left (not_countable_inter_Ioi hpiv htail hH z) (hc x y)
      (fun w hw => hyes x hx y hy z hz w hw.1 hxy hyz hw.2)
  · exact ⟨H, hH, hno⟩

include h4 hpiv htail hc in
/-- Pattern 8: `x = (h₃,h₄)`, `y = (h₁,h₂)`; refuted by freeing `h₂` below an
    uncountable pivot `h₃`. -/
theorem pattern₈ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H,
    x < y → y < z → z < w → (x, y) ∉ c z w := by
  obtain ⟨H, hH, hyes | hno⟩ := homog4 h4 (fun x y z w => (x, y) ∈ c z w)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨z, hz, -, hmid⟩ := exists_mid hpiv htail hH x
    obtain ⟨w, hw, hzw⟩ := exists_mem_gt htail hH z
    exact absurd_left hmid (hc z w)
      (fun y hy => hyes x hx y hy.1 z hz w hw hy.2.1 hy.2.2 hzw)
  · exact ⟨H, hH, hno⟩

include h4 hpiv htail hc in
/-- Pattern 9: `x = (h₁,h₃)`, `y = (h₂,h₄)`; refuted by freeing `h₄` upward. -/
theorem pattern₉ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H,
    x < y → y < z → z < w → (y, w) ∉ c x z := by
  obtain ⟨H, hH, hyes | hno⟩ := homog4 h4 (fun x y z w => (y, w) ∈ c x z)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt htail hH x
    obtain ⟨z, hz, hyz⟩ := exists_mem_gt htail hH y
    exact absurd_left (not_countable_inter_Ioi hpiv htail hH z) (hc x z)
      (fun w hw => hyes x hx y hy z hz w hw.1 hxy hyz hw.2)
  · exact ⟨H, hH, hno⟩

include h4 hpiv htail hc in
/-- Pattern 10: `x = (h₂,h₄)`, `y = (h₁,h₃)`; refuted by choosing `h₂` an
    uncountable pivot and freeing `h₁` below it. -/
theorem pattern₁₀ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H,
    x < y → y < z → z < w → (x, z) ∉ c y w := by
  obtain ⟨H, hH, hyes | hno⟩ := homog4 h4 (fun x y z w => (x, z) ∈ c y w)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨y, hy, hpivot⟩ := exists_pivot hpiv hH
    obtain ⟨z, hz, hyz⟩ := exists_mem_gt htail hH y
    obtain ⟨w, hw, hzw⟩ := exists_mem_gt htail hH z
    exact absurd_right hpivot (hc y w)
      (fun x hx => hyes x hx.1 y hy z hz w hw hx.2 hyz hzw)
  · exact ⟨H, hH, hno⟩

include h4 hpiv htail hc in
/-- Pattern 11: `x = (h₁,h₄)`, `y = (h₂,h₃)`; refuted by freeing `h₃` below an
    uncountable pivot `h₄`. -/
theorem pattern₁₁ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H,
    x < y → y < z → z < w → (y, z) ∉ c x w := by
  obtain ⟨H, hH, hyes | hno⟩ := homog4 h4 (fun x y z w => (y, z) ∈ c x w)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt htail hH x
    obtain ⟨w, hw, -, hmid⟩ := exists_mid hpiv htail hH y
    exact absurd_left hmid (hc x w)
      (fun z hz => hyes x hx y hy z hz.1 w hw hxy hz.2.1 hz.2.2)
  · exact ⟨H, hH, hno⟩

include h4 hpiv htail hc in
/-- Pattern 12: `x = (h₂,h₃)`, `y = (h₁,h₄)`; refuted by freeing `h₄` upward. -/
theorem pattern₁₂ : ∃ H ∈ D, ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H, ∀ w ∈ H,
    x < y → y < z → z < w → (x, w) ∉ c y z := by
  obtain ⟨H, hH, hyes | hno⟩ := homog4 h4 (fun x y z w => (x, w) ∈ c y z)
  · refine ⟨H, hH, ?_⟩
    exfalso
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hH
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt htail hH x
    obtain ⟨z, hz, hyz⟩ := exists_mem_gt htail hH y
    exact absurd_left (not_countable_inter_Ioi hpiv htail hH z) (hc y z)
      (fun w hw => hyes x hx y hy z hz w hw.1 hxy hyz hw.2)
  · exact ⟨H, hH, hno⟩

end Patterns

/-- The core of Paper IV, Sections 3–4: under Rowbottom homogeneity for
    triples and quadruples, uncountable pivots and tails, any assignment of
    countable sets `c a b` of pairs to increasing pairs `(a, b)` is mutually
    avoided by the increasing pairs from a set of `D`.

    A1 (`inj_on_pairs`) and C2 (`EPP_fubini`) are both instances of it. -/
theorem exists_avoiding_homog {D : Ultrafilter κ}
    (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
    (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D)
    (c : κ → κ → Set (κ × κ)) (hc : ∀ a b, (c a b).Countable) :
    ∃ H ∈ D, ∀ a ∈ H, ∀ b ∈ H, ∀ a' ∈ H, ∀ b' ∈ H, a < b → a' < b' →
      (a, b) ≠ (a', b') → (a', b') ∉ c a b := by
  obtain ⟨H₁, hH₁, N₁⟩ := pattern₁ h3 hpiv htail c hc
  obtain ⟨H₂, hH₂, N₂⟩ := pattern₂ h3 hpiv htail c hc
  obtain ⟨H₃, hH₃, N₃⟩ := pattern₃ h3 hpiv htail c hc
  obtain ⟨H₄, hH₄, N₄⟩ := pattern₄ h3 hpiv htail c hc
  obtain ⟨H₅, hH₅, N₅⟩ := pattern₅ h3 hpiv htail c hc
  obtain ⟨H₆, hH₆, N₆⟩ := pattern₆ h3 hpiv htail c hc
  obtain ⟨H₇, hH₇, N₇⟩ := pattern₇ h4 hpiv htail c hc
  obtain ⟨H₈, hH₈, N₈⟩ := pattern₈ h4 hpiv htail c hc
  obtain ⟨H₉, hH₉, N₉⟩ := pattern₉ h4 hpiv htail c hc
  obtain ⟨H₁₀, hH₁₀, N₁₀⟩ := pattern₁₀ h4 hpiv htail c hc
  obtain ⟨H₁₁, hH₁₁, N₁₁⟩ := pattern₁₁ h4 hpiv htail c hc
  obtain ⟨H₁₂, hH₁₂, N₁₂⟩ := pattern₁₂ h4 hpiv htail c hc
  refine ⟨H₁ ∩ H₂ ∩ H₃ ∩ H₄ ∩ H₅ ∩ H₆ ∩ H₇ ∩ H₈ ∩ H₉ ∩ H₁₀ ∩ H₁₁ ∩ H₁₂, ?_, ?_⟩
  · exact Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hH₁ hH₂) hH₃) hH₄) hH₅)
      hH₆) hH₇) hH₈) hH₉) hH₁₀) hH₁₁) hH₁₂
  intro a ha b hb a' ha' b' hb' hab ha'b' hne
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha1, ha2⟩, ha3⟩, ha4⟩, ha5⟩, ha6⟩, ha7⟩, ha8⟩, ha9⟩, ha10⟩, ha11⟩, ha12⟩ := ha
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩, hb7⟩, hb8⟩, hb9⟩, hb10⟩, hb11⟩, hb12⟩ := hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha'1, ha'2⟩, ha'3⟩, ha'4⟩, ha'5⟩, ha'6⟩, ha'7⟩, ha'8⟩, ha'9⟩, ha'10⟩,
    ha'11⟩, ha'12⟩ := ha'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb'1, hb'2⟩, hb'3⟩, hb'4⟩, hb'5⟩, hb'6⟩, hb'7⟩, hb'8⟩, hb'9⟩, hb'10⟩,
    hb'11⟩, hb'12⟩ := hb'
  rcases eq_or_ne a a' with rfl | haa'
  · -- same left coordinate
    have hbb' : b ≠ b' := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hbb' with h | h
    · exact N₁ a ha1 b hb1 b' hb'1 hab h
    · exact N₂ a ha2 b' hb'2 b hb2 ha'b' h
  · rcases eq_or_ne b b' with rfl | hbb'
    · -- same right coordinate
      rcases lt_or_gt_of_ne haa' with h | h
      · exact N₅ a ha5 a' ha'5 b hb5 h ha'b'
      · exact N₆ a' ha'6 a ha6 b hb6 h hab
    · rcases eq_or_ne a b' with rfl | hab'
      · exact N₄ a' ha'4 a ha4 b hb4 ha'b' hab
      · rcases eq_or_ne b a' with rfl | hba'
        · exact N₃ a ha3 b hb3 b' hb'3 hab ha'b'
        · -- four distinct points
          rcases lt_trichotomy b a' with hba | hba | hba
          · exact N₇ a ha7 b hb7 a' ha'7 b' hb'7 hab hba ha'b'
          · exact absurd hba hba'
          · rcases lt_trichotomy b' a with hb'a | hb'a | hb'a
            · exact N₈ a' ha'8 b' hb'8 a ha8 b hb8 ha'b' hb'a hab
            · exact absurd hb'a.symm hab'
            · rcases lt_trichotomy a a' with haa | haa | haa
              · rcases lt_trichotomy b b' with hbb | hbb | hbb
                · exact N₉ a ha9 a' ha'9 b hb9 b' hb'9 haa hba hbb
                · exact absurd hbb hbb'
                · exact N₁₁ a ha11 a' ha'11 b' hb'11 b hb11 haa ha'b' hbb
              · exact absurd haa haa'
              · rcases lt_trichotomy b b' with hbb | hbb | hbb
                · exact N₁₂ a' ha'12 a ha12 b hb12 b' hb'12 haa hab hbb
                · exact absurd hbb hbb'
                · exact N₁₀ a' ha'10 a ha10 b' hb'10 b hb10 haa hb'a hbb

/-  A1, CONTRACT STATEMENT (preserved verbatim; see the restatement note
    on `inj_on_pairs` below):

theorem inj_on_pairs (D : Ultrafilter κ)
    (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
    (hpiv : UncountablePivots D) {V : Type*} (g : κ → κ → V)
    (hfib : ∀ v : V, {p : κ × κ | p.1 < p.2 ∧ g p.1 p.2 = v}.Countable) :
    ∃ H ∈ D, ∀ a ∈ H, ∀ b ∈ H, ∀ a' ∈ H, ∀ b' ∈ H,
      a < b → a' < b' → g a b = g a' b' → a = a' ∧ b = b'
-/

/-- A1 (Injectivity on a square; Paper IV, Theorem 3.1, countable-fiber
    form). If `g` on the increasing pairs has countable fibers, then `g`
    is injective on the increasing pairs from some `H ∈ D`.

    RESTATEMENT (reported). The contract statement, preserved verbatim in
    the comment above, is proved here with one additional hypothesis,
    `htail`: every tail `{β | γ < β}` lies in `D`.  This is the paper's
    "H has order type κ, so pass to a tail of H" step, used in every
    pattern whose free coordinate varies *upward* (the three-element
    patterns `g(h₁,h₂) = g(h₁,h₃)`, `g(h₁,h₂) = g(h₂,h₃)` and all three
    four-element patterns); `UncountablePivots` supplies only the downward
    direction, and by itself does not make members of `D` unbounded.
    `htail` holds for every uniform (in particular normal) ultrafilter on a
    cardinal, and it is already part of the contract for B1, B8 and C2, so
    no downstream statement changes.

    Proof: instantiate the twelve-pattern analysis `exists_avoiding_homog`
    at `c a b := {p | p.1 < p.2 ∧ g p.1 p.2 = g a b}`, a fiber of `g`,
    hence countable. -/
theorem inj_on_pairs (D : Ultrafilter κ)
    (h3 : RowbottomFor D 3) (h4 : RowbottomFor D 4)
    (hpiv : UncountablePivots D) (htail : ∀ γ : κ, {β | γ < β} ∈ D)
    {V : Type*} (g : κ → κ → V)
    (hfib : ∀ v : V, {p : κ × κ | p.1 < p.2 ∧ g p.1 p.2 = v}.Countable) :
    ∃ H ∈ D, ∀ a ∈ H, ∀ b ∈ H, ∀ a' ∈ H, ∀ b' ∈ H,
      a < b → a' < b' → g a b = g a' b' → a = a' ∧ b = b' := by
  obtain ⟨H, hH, hHavoid⟩ := exists_avoiding_homog h3 h4 hpiv htail
    (fun a b => {p : κ × κ | p.1 < p.2 ∧ g p.1 p.2 = g a b}) (fun a b => hfib (g a b))
  refine ⟨H, hH, ?_⟩
  intro a ha b hb a' ha' b' hb' hab ha'b' hg
  by_contra hcon
  have hne : (a, b) ≠ (a', b') := by
    intro h
    rw [Prod.mk.injEq] at h
    exact hcon ⟨h.1, h.2⟩
  exact hHavoid a ha b hb a' ha' b' hb' hab ha'b' hne ⟨ha'b', hg.symm⟩

end Homog

end PlufWO4
