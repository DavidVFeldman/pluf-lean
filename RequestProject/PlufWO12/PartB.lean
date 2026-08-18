/-
  PlufWO12/PartB.lean — the ω₁ recursion of Work Order 12.

  Under CH we run an ordinary transfinite recursion of length ω₁.  At
  stage `o` the subspaces built so far are indexed by `{p // p < o}`,
  hence countable; their finite intersections form a countable downward
  directed family with all members infinite-dimensional, so B2 extracts a
  decreasing cofinal chain from them and Part A's stage construction (A3)
  produces the next member: a closed subspace which defeats the `o`-th
  orthonormal basis, blocks the line spanned by the `o`-th vector, and
  still meets every earlier finite intersection in infinite dimension.

  Packaging (as the work order asks to be reported): the delivered family
  is the set of ALL FINITE INTERSECTIONS of the subspaces produced by the
  recursion.  This is downward directed by construction and has the same
  finite-intersection property as the raw range.

  Recursion combinator (also to be reported): WO-9's `exists_omega1_chain`
  does not fit — it produces a chain in a fixed partial order with a step
  map that cannot see the stage index, whereas here the stage datum (the
  `o`-th basis and the `o`-th vector) and the whole set of previous values
  are both needed.  We use the plain well-founded recursor
  `WellFoundedLT.wf.fix` on `Ordinal` with a `dite` on the stage existence
  statement, and prove the stage invariant afterwards by
  `Ordinal.induction`.  That pattern is recorded here for reuse.
-/
import RequestProject.PlufWO12.PartA

open Set Cardinal

namespace PlufWO12

/-! ### B2: decreasing cofinal chains -/

/-- B2 (chain extraction). A countable downward directed family of
    subspaces admits a decreasing cofinal sequence. -/
theorem exists_decreasing_cofinal_aux {G : Set (Submodule ℝ H)}
    (hctble : G.Countable) (hne : G.Nonempty)
    (hdir : ∀ M ∈ G, ∀ M' ∈ G, ∃ P ∈ G, P ≤ M ⊓ M') :
    ∃ h : ℕ → Submodule ℝ H, (∀ n, h n ∈ G) ∧ (∀ n, h (n + 1) ≤ h n) ∧
      ∀ M ∈ G, ∃ n, h n ≤ M := by
  classical
  obtain ⟨g, hg⟩ := hctble.exists_eq_range hne
  have hgmem : ∀ n, g n ∈ G := by
    intro n
    rw [hg]
    exact ⟨n, rfl⟩
  choose sel hsel hsel' using fun (M : Submodule ℝ H) (hM : M ∈ G) (n : ℕ) =>
    hdir M hM (g n) (hgmem n)
  set h : ℕ → {M : Submodule ℝ H // M ∈ G} := fun n =>
    Nat.rec (motive := fun _ => {M : Submodule ℝ H // M ∈ G}) ⟨g 0, hgmem 0⟩
      (fun n P => ⟨sel P.1 P.2 (n + 1), hsel P.1 P.2 (n + 1)⟩) n with hhdef
  refine ⟨fun n => (h n).1, fun n => (h n).2, ?_, ?_⟩
  · intro n
    show (h (n + 1)).1 ≤ (h n).1
    have hstep : h (n + 1) = ⟨sel (h n).1 (h n).2 (n + 1), hsel (h n).1 (h n).2 (n + 1)⟩ := rfl
    rw [hstep]
    exact le_trans (hsel' (h n).1 (h n).2 (n + 1)) inf_le_left
  · intro M hM
    have hMr : M ∈ Set.range g := by rw [← hg]; exact hM
    obtain ⟨n, rfl⟩ := hMr
    refine ⟨n, ?_⟩
    cases n with
    | zero => exact le_rfl
    | succ n =>
        show (h (n + 1)).1 ≤ g (n + 1)
        have hstep : h (n + 1) = ⟨sel (h n).1 (h n).2 (n + 1), hsel (h n).1 (h n).2 (n + 1)⟩ := rfl
        rw [hstep]
        exact le_trans (hsel' (h n).1 (h n).2 (n + 1)) inf_le_right

/-! ### The stage predicate -/

/-- The set of values of `c` strictly below `a`. -/
def Prev (c : Ordinal → Submodule ℝ H) (a : Ordinal) : Set (Submodule ℝ H) :=
  {M | ∃ p, ∃ _ : p < a, c p = M}

/-- What one stage of the recursion has to deliver: a closed subspace
    which is not intimate for the given basis, blocks the given line, and
    meets every finite intersection of the earlier subspaces in infinite
    dimension. -/
def StageGood (S : Set (Submodule ℝ H)) (bb : HilbertBasis ℕ ℝ H) (v : H)
    (R : Submodule ℝ H) : Prop :=
  IsClosed ((R : Submodule ℝ H) : Set H) ∧ ¬ PlufWO10.IntimateB bb R ∧
    R ⊓ (ℝ ∙ v) = ⊥ ∧
    ∀ F : Finset (Submodule ℝ H), ↑F ⊆ S → ¬ FiniteDimensional ℝ ↥(R ⊓ F.inf id)

/-! ### The stage step -/

/-- The stage step: a countable family of closed subspaces with the finite
    intersection property can be extended by a subspace defeating a given
    basis and blocking a given line. -/
theorem exists_stageGood (S : Set (Submodule ℝ H)) (hctble : S.Countable)
    (hclS : ∀ M ∈ S, IsClosed ((M : Submodule ℝ H) : Set H))
    (hFIP : ∀ F : Finset (Submodule ℝ H), ↑F ⊆ S → ¬ FiniteDimensional ℝ ↥(F.inf id))
    (bb : HilbertBasis ℕ ℝ H) (v : H) :
    ∃ R : Submodule ℝ H, StageGood S bb v R := by
  classical
  -- the family of finite intersections
  set G : Set (Submodule ℝ H) := (fun t : Set (Submodule ℝ H) => sInf t) '' {t | t.Finite ∧ t ⊆ S}
    with hG
  have hGmem : ∀ F : Finset (Submodule ℝ H), ↑F ⊆ S → F.inf id ∈ G := by
    intro F hF
    exact ⟨(F : Set (Submodule ℝ H)), ⟨F.finite_toSet, hF⟩, (Finset.inf_id_eq_sInf F).symm⟩
  have hGfinset : ∀ M ∈ G, ∃ F : Finset (Submodule ℝ H), ↑F ⊆ S ∧ M = F.inf id := by
    rintro M ⟨t, ⟨htfin, htS⟩, rfl⟩
    refine ⟨htfin.toFinset, ?_, ?_⟩
    · simpa using htS
    · rw [Finset.inf_id_eq_sInf]
      simp
  have hGctble : G.Countable := Set.Countable.image (Set.countable_setOf_finite_subset hctble) _
  have hGne : G.Nonempty := ⟨(∅ : Finset (Submodule ℝ H)).inf id, hGmem ∅ (by simp)⟩
  have hGdir : ∀ M ∈ G, ∀ M' ∈ G, ∃ P ∈ G, P ≤ M ⊓ M' := by
    intro M hM M' hM'
    obtain ⟨F, hF, rfl⟩ := hGfinset M hM
    obtain ⟨F', hF', rfl⟩ := hGfinset M' hM'
    refine ⟨(F ∪ F').inf id, hGmem _ ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (by simpa using hx) with h | h
      · exact hF h
      · exact hF' h
    · rw [Finset.inf_union]
  have hGcl : ∀ M ∈ G, IsClosed ((M : Submodule ℝ H) : Set H) := by
    intro M hM
    obtain ⟨F, hF, rfl⟩ := hGfinset M hM
    exact isClosed_finsetInf F (fun M' hM' => hclS M' (hF (by simpa using hM')))
  have hGinf : ∀ M ∈ G, ¬ FiniteDimensional ℝ ↥M := by
    intro M hM
    obtain ⟨F, hF, rfl⟩ := hGfinset M hM
    exact hFIP F hF
  -- a decreasing cofinal chain in `G`
  obtain ⟨hch, hchG, hchmono, hchcof⟩ := exists_decreasing_cofinal_aux hGctble hGne hGdir
  -- Part A applies with `N` the line spanned by `v`
  haveI hlinefin : FiniteDimensional ℝ ↥(ℝ ∙ v) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_singleton v)
  obtain ⟨R, hRcl, hRint, hRN, hRinf⟩ :=
    exists_nonIntimate_blocking_aux bb hch (ℝ ∙ v) hchmono
      (fun n => hGcl _ (hchG n)) (fun n => hGinf _ (hchG n))
      (fun n => Submodule.finiteDimensional_of_le (inf_le_right : hch n ⊓ (ℝ ∙ v) ≤ ℝ ∙ v))
  refine ⟨R, hRcl, hRint, hRN, ?_⟩
  intro F hF
  obtain ⟨n, hn⟩ := hchcof (F.inf id) (hGmem F hF)
  exact not_finiteDimensional_mono (inf_le_inf_left R hn) (hRinf n)

/-! ### Bookkeeping for the recursion -/

/-- A finite family each of whose members dominates a finite intersection
    of `c`-values below `bound` itself dominates such an intersection. -/
theorem exists_finset_ordinal_le (c : Ordinal → Submodule ℝ H) (bound : Ordinal)
    (F : Finset (Submodule ℝ H))
    (hsub : ∀ M ∈ F, ∃ s : Finset Ordinal, (∀ p ∈ s, p < bound) ∧ s.inf c ≤ M) :
    ∃ s : Finset Ordinal, (∀ p ∈ s, p < bound) ∧ s.inf c ≤ F.inf id := by
  classical
  induction F using Finset.induction with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert M F hM ih =>
      obtain ⟨s, hs, hle⟩ := ih (fun M' hM' => hsub M' (Finset.mem_insert_of_mem hM'))
      obtain ⟨s', hs', hle'⟩ := hsub M (Finset.mem_insert_self M F)
      refine ⟨s' ∪ s, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_union.mp hp with h | h
        · exact hs' p h
        · exact hs p h
      · rw [Finset.inf_insert, Finset.inf_union]
        exact inf_le_inf hle' hle

/-- With every stage below `bound` good, every finite intersection of
    `c`-values below `bound` is infinite-dimensional. -/
theorem not_finiteDimensional_finsetInf_of_good {c : Ordinal → Submodule ℝ H}
    {bas : Ordinal → HilbertBasis ℕ ℝ H} {vec : Ordinal → H} {bound : Ordinal}
    (hgood : ∀ p, p < bound → StageGood (Prev c p) (bas p) (vec p) (c p))
    (s : Finset Ordinal) (hs : ∀ p ∈ s, p < bound) :
    ¬ FiniteDimensional ℝ ↥(s.inf c) := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · rw [Finset.inf_empty]
    intro hfin
    haveI := hfin
    exact PlufWO11.not_finiteDimensional_H (LinearEquiv.finiteDimensional Submodule.topEquiv)
  · set p := s.max' hne with hp
    have hpmem : p ∈ s := s.max'_mem hne
    have hpb : p < bound := hs p hpmem
    have hsplit : s.inf c = c p ⊓ (s.erase p).inf c := by
      conv_lhs => rw [← Finset.insert_erase hpmem]
      rw [Finset.inf_insert]
    have hsubPrev : ↑((s.erase p).image c) ⊆ Prev c p := by
      intro M hM
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hM)
      have hqs : q ∈ s := Finset.mem_of_mem_erase hq
      have hqne : q ≠ p := Finset.ne_of_mem_erase hq
      exact ⟨q, lt_of_le_of_ne (s.le_max' q hqs) hqne, rfl⟩
    have := (hgood p hpb).2.2.2 ((s.erase p).image c) hsubPrev
    rw [Finset.inf_image] at this
    rw [hsplit]
    exact this

/-! ### B3: the recursion -/

section CH

variable (hCH : continuum = aleph 1)

include hCH

/-- B1 (the vector enumeration), from WO-11's cardinal computation. -/
theorem exists_enum_vectors_aux :
    ∃ f : {o : Ordinal // o < (aleph 1).ord} → H, ∀ v : H, v ≠ 0 → ∃ o, f o = v := by
  obtain ⟨f, hf⟩ := PlufWO11.enumShift hCH PlufWO11.mk_H
  exact ⟨f, fun v _ => hf v⟩

/-- B3 (the recursion). -/
theorem exists_witness_family_aux :
    ∃ R : Set (Submodule ℝ H),
      R.Nonempty ∧
      (∀ M ∈ R, IsClosed ((M : Submodule ℝ H) : Set H)) ∧
      (∀ M ∈ R, ∀ M' ∈ R, ∃ P ∈ R, P ≤ M ⊓ M') ∧
      (∀ F : Finset (Submodule ℝ H), ↑F ⊆ R → ¬ Module.Finite ℝ ↥(F.inf id)) ∧
      sInf R = ⊥ ∧
      (∀ b : HilbertBasis ℕ ℝ H, ∃ M ∈ R, ¬ PlufWO10.IntimateB b M) := by
  classical
  obtain ⟨fvec, hfvec⟩ := exists_enum_vectors_aux hCH
  obtain ⟨fbas, hfbas⟩ := PlufWO11.exists_enum_hilbertBases hCH
  set vec : Ordinal.{0} → H := fun o => if h : o < (aleph.{0} 1).ord then fvec ⟨o, h⟩ else 0 with hvec
  set bas : Ordinal.{0} → HilbertBasis ℕ ℝ H :=
    fun o => if h : o < (aleph.{0} 1).ord then fbas ⟨o, h⟩ else PlufWO9.stdHilbertBasis with hbas
  -- the recursion
  set Φ : (a : Ordinal.{0}) → ((p : Ordinal.{0}) → p < a → Submodule ℝ H) → Submodule ℝ H :=
    fun a ih =>
      if hex : ∃ R, StageGood {M | ∃ p, ∃ hp : p < a, ih p hp = M} (bas a) (vec a) R then
        hex.choose
      else ⊤ with hΦ
  set c : Ordinal.{0} → Submodule ℝ H := (inferInstanceAs (WellFoundedLT Ordinal.{0})).wf.fix Φ with hc
  have hceq : ∀ a : Ordinal.{0}, c a = Φ a (fun p _ => c p) := by
    intro a
    rw [hc]
    exact WellFounded.fix_eq _ Φ a
  -- every stage below ω₁ is good
  have hgood : ∀ a : Ordinal.{0}, a < (aleph.{0} 1).ord → StageGood (Prev c a) (bas a) (vec a) (c a) := by
    intro a
    induction a using Ordinal.induction with
    | h a IH =>
        intro ha
        have hIH : ∀ p, p < a → StageGood (Prev c p) (bas p) (vec p) (c p) := by
          intro p hp
          exact IH p hp (lt_trans hp ha)
        -- the family accumulated so far
        have hctble : (Prev c a).Countable := by
          have himg : Prev c a = c '' (Set.Iio a) := by
            ext M
            constructor
            · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
            · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
          rw [himg]
          exact (PlufWO11.countable_Iio_of_lt_omega1 ha).image c
        have hclS : ∀ M ∈ Prev c a, IsClosed ((M : Submodule ℝ H) : Set H) := by
          rintro M ⟨p, hp, rfl⟩
          exact (hIH p hp).1
        have hFIP : ∀ F : Finset (Submodule ℝ H), ↑F ⊆ Prev c a →
            ¬ FiniteDimensional ℝ ↥(F.inf id) := by
          intro F hF
          obtain ⟨s, hs, hle⟩ := exists_finset_ordinal_le c a F (by
            intro M hM
            obtain ⟨p, hp, rfl⟩ := hF (by simpa using hM)
            exact ⟨{p}, by simpa using hp, by simp⟩)
          exact not_finiteDimensional_mono hle
            (not_finiteDimensional_finsetInf_of_good hIH s hs)
        obtain ⟨R, hR⟩ := exists_stageGood (Prev c a) hctble hclS hFIP (bas a) (vec a)
        have hex : ∃ R, StageGood (Prev c a) (bas a) (vec a) R := ⟨R, hR⟩
        have hca : c a = hex.choose := by
          rw [hceq a, hΦ]
          exact dif_pos hex
        rw [hca]
        exact hex.choose_spec
  -- the delivered family: all finite intersections
  set Rset : Set (Submodule ℝ H) :=
    {M | ∃ s : Finset Ordinal.{0}, (∀ p ∈ s, p < (aleph.{0} 1).ord) ∧ M = s.inf c} with hRset
  have hmemRset : ∀ p, p < (aleph.{0} 1).ord → c p ∈ Rset := by
    intro p hp
    exact ⟨{p}, by simpa using hp, by simp⟩
  refine ⟨Rset, ⟨⊤, ⟨∅, by simp, by simp⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- closedness
    rintro M ⟨s, hs, rfl⟩
    have : s.inf c = (s.image c).inf id := by rw [Finset.inf_image]; rfl
    rw [this]
    refine isClosed_finsetInf _ ?_
    intro M' hM'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hM'
    exact (hgood p (hs p hp)).1
  · -- directedness
    rintro M ⟨s, hs, rfl⟩ M' ⟨s', hs', rfl⟩
    refine ⟨(s ∪ s').inf c, ⟨s ∪ s', ?_, rfl⟩, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact hs p h
      · exact hs' p h
    · rw [Finset.inf_union]
  · -- the finite intersection property
    intro F hF
    obtain ⟨s, hs, hle⟩ := exists_finset_ordinal_le c (aleph.{0} 1).ord F (by
      intro M hM
      obtain ⟨s, hs, rfl⟩ := hF (by simpa using hM)
      exact ⟨s, hs, le_rfl⟩)
    exact not_finiteDimensional_mono hle (not_finiteDimensional_finsetInf_of_good hgood s hs)
  · -- trivial intersection
    refine le_antisymm ?_ bot_le
    intro x hx
    by_contra hx0
    have hxne : x ≠ 0 := by simpa using hx0
    obtain ⟨o, ho⟩ := hfvec x hxne
    have hovec : vec o.1 = x := by
      have hval : vec o.1 = fvec o := by
        rw [hvec]
        exact dif_pos o.2
      rw [hval]
      exact ho
    have hmem : x ∈ c o.1 := (Submodule.mem_sInf.mp hx) _ (hmemRset o.1 o.2)
    have hline : x ∈ (ℝ ∙ vec o.1) := by
      rw [hovec]
      exact Submodule.mem_span_singleton_self x
    have := (hgood o.1 o.2).2.2.1
    have hbot : x ∈ (⊥ : Submodule ℝ H) := this ▸ (⟨hmem, hline⟩ : x ∈ c o.1 ⊓ (ℝ ∙ vec o.1))
    exact hxne (by simpa using hbot)
  · -- a non-intimate member for every basis
    intro b
    obtain ⟨o, ho⟩ := hfbas b
    have hob : bas o.1 = b := by
      have hval : bas o.1 = fbas o := by
        rw [hbas]
        exact dif_pos o.2
      rw [hval]
      exact ho
    refine ⟨c o.1, hmemRset o.1 o.2, ?_⟩
    have := (hgood o.1 o.2).2.1
    rwa [hob] at this

end CH

end PlufWO12
