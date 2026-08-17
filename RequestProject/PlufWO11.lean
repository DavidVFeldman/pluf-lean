/-
  PlufWO11.lean — Work Order 11 for the pluf project (Feldman–Wilce).

  Scope: the cardinal infrastructure shared by the two remaining
  transfinite commissions (WO-12, Paper II Theorem 5.4; WO-15, Paper I
  Theorem 5.7 and Proposition 5.9). Paid once here, consumed twice:
    (A) the three cardinality computations: the closed subspaces of H, the
        ℕ-indexed orthonormal bases of H, and the bounded operators on H,
        each of cardinality 𝔠;
    (B) the CH enumerations: under CH as a hypothesis, each of those three
        sets is enumerated by the countable ordinals, in the shape WO-9's
        recursion combinator consumes;
    (C) the bookkeeping lemmas the recursions need at each stage: proper
        initial segments of ω₁ are countable, and the countable-union
        closure that keeps a stage's accumulated data countable.

  NOTHING HERE IS ANALYSIS. If an item starts to require Hilbert-space
  argument beyond the separability of H and the existence of its standard
  basis, that is a sign the contract is wrong — REPORT it.

  CH is a hypothesis (`Cardinal.continuum = Cardinal.aleph 1`), never an
  axiom, and appears only in Part B. Part A and Part C are ZFC.

  A NOTE ON GENERALITY. Every statement below is contracted concretely at
  `PlufWO1.H`, the standard separable infinite-dimensional real Hilbert
  space of this project, rather than at an abstract space. This is
  deliberate: the last two commissions each caught a false contract of the
  form "every separable complete space admits an ℕ-indexed Hilbert basis"
  (`E = ℝ` refutes it). If a general form is wanted, it needs
  `¬ FiniteDimensional` and separability, and its statement should be
  derived from the concrete one rather than replacing it. Generalize only
  if cheap, and REPORT.

  Base: the WO-10 artifact (181 theorems; CI runs #1–#10). All prior
  theorems must remain green; `PlufWO7a.lean` remains the census record.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  ---------------------------------------------------------------------
  DELIVERY NOTE (WO-11).

  * Part A is proved as contracted (A1–A4), by way of the shared
    infrastructure of §A0: `mk_H` (`#H = 𝔠`) and the two "determined by
    countably much data" injections (a continuous linear map on `H` is
    determined by its values on the standard basis; a closed subspace is
    determined by its orthogonal projection). Routes taken:
      - A1 upper: `M ↦ starProjection M` into `H →L[ℝ] H`;
        A1 lower: the blocks `PlufWO1.block S`, `S ⊆ ℕ`, separated by the
        constraint vectors `PlufWO1.constraintVec {n}` (only
        `PlufWO1.mem_block_iff` is used), as the work order suggested.
      - A2 upper: `b ↦ (fun n => b.repr (stdBasis n))` into `ℕ → H`;
        A2 lower: the *reindexings* of the standard basis along
        `Equiv.Perm ℕ` — there are `2 ^ ℵ₀ = 𝔠` of those, so no rotation
        needs to be built by hand (the work order's parenthetical "those
        are only countably many" concerns the *finitary* permutations;
        the full permutation group of ℕ has size 𝔠).
      - A3/A4 upper: `T ↦ (fun n => T (stdBasis n))` into `ℕ → H`;
        A3/A4 lower: the scalar multiples `r • 1`, which are self-adjoint
        and so serve both counts at once (cheaper than the `{0,1}`
        diagonal operators).
  * Part B: WO-9's E1 (`PlufWO9.exists_enumeration_of_CH`) does deliver the
    general statement, so B1–B3 are pure instantiations of it against the
    Part A counts. The only mismatch is cosmetic: E1 is stated with
    `Set.Iio (Ordinal.omega 1)` and the WO-11 contract with
    `{o : Ordinal // o < (Cardinal.aleph 1).ord}`; these are the same type
    up to `Cardinal.ord_aleph`, and `enumShift` below is the one-line
    bridge. E1's universe handling is in the right place (it is stated for
    `α : Type`, and every type counted here is a `Type`), so no lifting is
    needed at the call site.
  * Part C: C1 and C2 as contracted. C3 is REPORTED FALSE in both of the
    forms the placeholder proposes; see the C3 block below for the
    verbatim contract text, two counterexamples, and the marked minimal
    repair that is supplied in its place (`exists_orthogonal_of_countable`
    is the *algebraic* escape lemma, proved by Baire).
-/
import RequestProject.PlufWO10

open Set Cardinal

namespace PlufWO11

/-- Abbreviation for the working space. -/
abbrev H := PlufWO1.H

/-! ### Part A0: shared infrastructure

The standard basis of `H`, the fact that `#H = 𝔠`, and the two
"determined by countably much data" injections that give every upper
bound of Part A. -/

/-- The standard Hilbert basis of `H`, from WO-9. -/
noncomputable abbrev stdBasis : HilbertBasis ℕ ℝ H := PlufWO9.stdHilbertBasis

theorem dense_span_stdBasis :
    Dense (Submodule.span ℝ (Set.range ⇑stdBasis) : Set H) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr stdBasis.dense_span

theorem stdBasis_injective : Function.Injective ⇑stdBasis := by
  intro i j hij
  by_contra hne
  have h0 : inner (𝕜 := ℝ) (stdBasis i) (stdBasis j) = 0 := stdBasis.orthonormal.2 hne
  rw [hij, real_inner_self_eq_norm_sq, stdBasis.orthonormal.1 j] at h0
  norm_num at h0

theorem stdBasis_ne_zero (n : ℕ) : stdBasis n ≠ 0 := by
  intro h
  have hn := stdBasis.orthonormal.1 n
  rw [h] at hn
  norm_num at hn

/-- A continuous linear map out of `H` is determined by its values on the
    standard basis. This is the only "separability" input Part A needs. -/
theorem clm_ext_stdBasis {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : H →L[ℝ] X} (h : ∀ n, f (stdBasis n) = g (stdBasis n)) : f = g :=
  ContinuousLinearMap.ext_on dense_span_stdBasis (by rintro x ⟨n, rfl⟩; exact h n)

/-- `H` has cardinality the continuum. -/
theorem mk_H : #H = continuum := by
  refine le_antisymm ?_ ?_
  · have h1 : #H ≤ #(ℕ → ℝ) :=
      Cardinal.mk_le_of_injective (f := fun x : H => (x : ∀ _ : ℕ, ℝ))
        (fun _ _ h => lp.ext_iff.mpr h)
    have h2 : #(ℕ → ℝ) = continuum := by
      rw [Cardinal.mk_arrow]
      simp [Cardinal.mk_real, Cardinal.continuum_power_aleph0]
    exact h2 ▸ h1
  · have hinj : Function.Injective (fun r : ℝ => r • stdBasis 0) := by
      intro r s hrs
      have hrs' : r • stdBasis 0 = s • stdBasis 0 := hrs
      have h0 : (r - s) • stdBasis 0 = 0 := by
        rw [sub_smul, hrs', sub_self]
      rcases smul_eq_zero.mp h0 with h | h
      · linarith [sub_eq_zero.mp h]
      · exact absurd h (stdBasis_ne_zero 0)
    calc continuum = #ℝ := Cardinal.mk_real.symm
      _ ≤ #H := Cardinal.mk_le_of_injective hinj

/-- Countable sequences in `H` number the continuum. -/
theorem mk_nat_arrow_H : #(ℕ → H) = continuum := by
  rw [Cardinal.mk_arrow]
  simp [mk_H, Cardinal.continuum_power_aleph0]

/-- `H` is infinite-dimensional. -/
theorem not_finiteDimensional_H : ¬ FiniteDimensional ℝ H := by
  intro hfin
  exact PlufWO5.not_finite_of_orthonormal (⇑stdBasis) stdBasis.orthonormal ⊤
    (fun _ => trivial) inferInstance

/-! ### Part A: the three cardinality computations -/

/-- Auxiliary: the operator count, upper bound. A continuous linear map is
    determined by its values on the standard basis, i.e. by a sequence. -/
theorem mk_continuousLinearMaps_le : #(H →L[ℝ] H) ≤ continuum := by
  have hinj : Function.Injective (fun (T : H →L[ℝ] H) (n : ℕ) => T (stdBasis n)) :=
    fun _ _ h => clm_ext_stdBasis (fun n => congrFun h n)
  calc #(H →L[ℝ] H) ≤ #(ℕ → H) := Cardinal.mk_le_of_injective hinj
    _ = continuum := mk_nat_arrow_H

/-- Auxiliary: the operator count, lower bound, via the scalar multiples of
    the identity — all of them self-adjoint. -/
theorem continuum_le_mk_selfAdjoint :
    continuum ≤ #{T : H →L[ℝ] H // IsSelfAdjoint T} := by
  have hsa : ∀ r : ℝ, IsSelfAdjoint (r • (1 : H →L[ℝ] H)) :=
    fun r => (IsSelfAdjoint.all r).smul (IsSelfAdjoint.one (H →L[ℝ] H))
  have hinj : Function.Injective
      (fun r : ℝ => (⟨r • (1 : H →L[ℝ] H), hsa r⟩ : {T : H →L[ℝ] H // IsSelfAdjoint T})) := by
    intro r s hrs
    have h1 : (r • (1 : H →L[ℝ] H)) = s • (1 : H →L[ℝ] H) := congrArg Subtype.val hrs
    have h2 : r • stdBasis 0 = s • stdBasis 0 := by
      simpa using congrArg (fun T : H →L[ℝ] H => T (stdBasis 0)) h1
    have h0 : (r - s) • stdBasis 0 = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h (stdBasis_ne_zero 0)
  calc continuum = #ℝ := Cardinal.mk_real.symm
    _ ≤ _ := Cardinal.mk_le_of_injective hinj

/-- A3. The bounded operators on `H` number exactly the continuum, and so
    do the self-adjoint ones. (Upper bound: continuity plus separability
    make an operator determined by its values on a countable dense set.
    Lower bound: the scalar multiples of the identity, or the diagonal
    operators with entries in `{0,1}` — the latter give `𝔠` directly and
    are self-adjoint, serving both statements at once.) -/
theorem mk_continuousLinearMaps : #(H →L[ℝ] H) = continuum :=
  le_antisymm mk_continuousLinearMaps_le
    (continuum_le_mk_selfAdjoint.trans (Cardinal.mk_subtype_le _))

theorem mk_selfAdjoint :
    #{T : H →L[ℝ] H // IsSelfAdjoint T} = continuum :=
  le_antisymm ((Cardinal.mk_subtype_le _).trans mk_continuousLinearMaps_le)
    continuum_le_mk_selfAdjoint

/-- Auxiliary: the closed subspaces inject into the bounded operators via
    orthogonal projection. -/
noncomputable def projOf (M : {M : Submodule ℝ H // IsClosed (M : Set H)}) : H →L[ℝ] H :=
  haveI := PlufWO8.hasOrthogonalProjection_of_isClosed M.2
  Submodule.starProjection (M : Submodule ℝ H)

theorem projOf_injective : Function.Injective projOf := by
  intro M N h
  haveI := PlufWO8.hasOrthogonalProjection_of_isClosed M.2
  haveI := PlufWO8.hasOrthogonalProjection_of_isClosed N.2
  have hM : projOf M = Submodule.starProjection (M : Submodule ℝ H) := rfl
  have hN : projOf N = Submodule.starProjection (N : Submodule ℝ H) := rfl
  rw [hM, hN] at h
  refine Subtype.ext (SetLike.ext fun x => ?_)
  rw [← Submodule.starProjection_eq_self_iff (K := (M : Submodule ℝ H)),
    ← Submodule.starProjection_eq_self_iff (K := (N : Submodule ℝ H)), h]

/-- A1. The closed subspaces of `H` number exactly the continuum.

    Upper bound: a closed subspace is determined by any countable dense
    subset of it (`H` is separable, so every subspace is separable), so the
    assignment into countable sequences from `H` is injective, giving
    `𝔠 ^ ℵ₀ = 𝔠`. Lower bound: the lines `ℝ ∙ v` for `v` on the unit
    sphere are pairwise distinct up to sign, and the sphere has cardinality
    `𝔠`; a cleaner lower bound, if preferred, is the blocks `block S` for
    `S ⊆ ℕ`, which are pairwise distinct — that route needs only
    `PlufWO1.mem_block_iff` and is probably shortest. Prover's choice,
    reported. -/
theorem mk_closedSubspaces :
    #{M : Submodule ℝ H // IsClosed (M : Set H)} = continuum := by
  refine le_antisymm
    ((Cardinal.mk_le_of_injective projOf_injective).trans mk_continuousLinearMaps_le) ?_
  have key : ∀ (U : Set ℕ) (n : ℕ), PlufWO1.constraintVec {n} ∈ PlufWO1.block U ↔ n ∈ U := by
    intro U n
    rw [PlufWO1.mem_block_iff]
    constructor
    · intro hU
      by_contra hn
      have h := hU n hn
      rw [PlufWO1.constraintVec_apply, if_pos (Set.mem_singleton_iff.mpr rfl)] at h
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
      linarith
    · intro hn m hm
      rw [PlufWO1.constraintVec_apply, if_neg]
      rintro rfl
      exact hm hn
  have hinj : Function.Injective (fun S : Set ℕ =>
      (⟨PlufWO1.block S, PlufWO1.isClosed_block S⟩ :
        {M : Submodule ℝ H // IsClosed (M : Set H)})) := by
    intro S T hST
    have h : PlufWO1.block S = PlufWO1.block T := congrArg Subtype.val hST
    ext n
    rw [← key S n, ← key T n, h]
  calc continuum = #(Set ℕ) := by
        simp [Cardinal.mk_set, Cardinal.two_power_aleph0]
    _ ≤ _ := Cardinal.mk_le_of_injective hinj

/-- Auxiliary: reindexing the standard basis along a permutation of ℕ. -/
noncomputable def permBasis (σ : Equiv.Perm ℕ) : HilbertBasis ℕ ℝ H :=
  HilbertBasis.mk (stdBasis.orthonormal.comp σ σ.injective)
    (by
      have hr : Set.range (⇑stdBasis ∘ ⇑σ) = Set.range ⇑stdBasis :=
        σ.surjective.range_comp _
      rw [hr]
      exact le_of_eq stdBasis.dense_span.symm)

theorem permBasis_injective : Function.Injective permBasis := by
  intro σ τ h
  have hc : ⇑(permBasis σ) = ⇑(permBasis τ) := by rw [h]
  rw [permBasis, permBasis, HilbertBasis.coe_mk, HilbertBasis.coe_mk] at hc
  ext n
  exact stdBasis_injective (congrFun hc n)

/-- A2. The ℕ-indexed orthonormal bases of `H` number exactly the
    continuum.

    Upper bound: a `HilbertBasis ℕ ℝ H` is determined by the underlying
    function `ℕ → H`, so `𝔠 ^ ℵ₀ = 𝔠`. Lower bound: the reindexings of the
    standard basis along the permutations of ℕ, of which there are
    `2 ^ ℵ₀ = 𝔠`. -/
theorem mk_hilbertBases : #(HilbertBasis ℕ ℝ H) = continuum := by
  refine le_antisymm ?_ ?_
  · have hinj : Function.Injective
        (fun (b : HilbertBasis ℕ ℝ H) (n : ℕ) => b.repr (stdBasis n)) := by
      intro b₁ b₂ h
      have hclm := clm_ext_stdBasis (f := b₁.repr.toLinearIsometry.toContinuousLinearMap)
        (g := b₂.repr.toLinearIsometry.toContinuousLinearMap) (fun n => congrFun h n)
      have hfun : ⇑b₁.repr = ⇑b₂.repr := congrArg (fun T : H →L[ℝ] H => ⇑T) hclm
      have hrepr : b₁.repr = b₂.repr := LinearIsometryEquiv.ext (fun x => congrFun hfun x)
      rcases b₁ with ⟨r₁⟩
      rcases b₂ with ⟨r₂⟩
      exact congrArg HilbertBasis.ofRepr hrepr
    calc #(HilbertBasis ℕ ℝ H) ≤ #(ℕ → H) := Cardinal.mk_le_of_injective hinj
      _ = continuum := mk_nat_arrow_H
  · calc continuum = #(Equiv.Perm ℕ) := by
          rw [Cardinal.mk_perm_eq_two_power]
          simp [Cardinal.two_power_aleph0]
      _ ≤ _ := Cardinal.mk_le_of_injective permBasis_injective

/-! ### Part B: the CH enumerations -/

section CH

-- The continuum hypothesis, as a hypothesis.
variable (hCH : continuum = aleph 1)

include hCH

/-- The bridge between WO-9's `Set.Iio (Ordinal.omega 1)` and the
    `{o // o < (aleph 1).ord}` shape contracted here: they are the same
    type, by `Cardinal.ord_aleph`. -/
theorem enumShift {α : Type} (hcard : #α = continuum) :
    ∃ f : {o : Ordinal // o < (aleph 1).ord} → α, Function.Surjective f := by
  obtain ⟨f, hf⟩ := PlufWO9.exists_enumeration_of_CH hcard hCH
  have hord : (aleph 1).ord = Ordinal.omega 1 := Cardinal.ord_aleph 1
  refine ⟨fun o => f ⟨o.1, by rw [← hord]; exact o.2⟩, fun a => ?_⟩
  obtain ⟨i, hi⟩ := hf a
  refine ⟨⟨i.1, by rw [hord]; exact i.2⟩, ?_⟩
  simpa using hi

/-- B1. Under CH, the closed subspaces of `H` are enumerated by the
    countable ordinals: there is a surjection from `{o : Ordinal // o <
    ω₁}` onto them. -/
theorem exists_enum_closedSubspaces :
    ∃ f : {o : Ordinal // o < (aleph 1).ord} → {M : Submodule ℝ H // IsClosed (M : Set H)},
      Function.Surjective f :=
  enumShift hCH mk_closedSubspaces

/-- B2. Under CH, the ℕ-indexed orthonormal bases are enumerated by the
    countable ordinals. (This is what Paper II's Theorem 5.4 recursion
    consumes: one basis defeated per stage.) -/
theorem exists_enum_hilbertBases :
    ∃ f : {o : Ordinal // o < (aleph 1).ord} → HilbertBasis ℕ ℝ H,
      Function.Surjective f :=
  enumShift hCH mk_hilbertBases

/-- B3. Under CH, the self-adjoint operators are enumerated by the
    countable ordinals. (This is what Paper I's Theorem 5.7 recursion
    consumes: one operator rounded per stage.) -/
theorem exists_enum_selfAdjoint :
    ∃ f : {o : Ordinal // o < (aleph 1).ord} → {T : H →L[ℝ] H // IsSelfAdjoint T},
      Function.Surjective f :=
  enumShift hCH mk_selfAdjoint

end CH

/-! ### Part C: stage bookkeeping -/

/-- C1. Every proper initial segment of ω₁ is countable. This is the fact
    that makes the recursions work: at stage `α`, the data accumulated so
    far is indexed by `{β // β < α}`, which is countable, so a countable
    construction suffices to pass to the next stage. -/
theorem countable_Iio_of_lt_omega1 {α : Ordinal} (hα : α < (aleph 1).ord) :
    (Set.Iio α).Countable := by
  have hα' : α < Ordinal.omega 1 := by rwa [Cardinal.ord_aleph] at hα
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one]
  have h := (Ordinal.isInitial_omega 1).card_lt_card (a := α)
  rw [Ordinal.card_omega] at h
  exact h.mpr hα'

/-- C2. A countable union of countable sets indexed below a countable
    ordinal is countable — the closure property each limit stage needs. -/
theorem countable_iUnion_Iio {α : Ordinal} (hα : α < (aleph 1).ord)
    (s : Ordinal → Set H) (hs : ∀ β, (s β).Countable) :
    (⋃ β ∈ Set.Iio α, s β).Countable :=
  Set.Countable.biUnion (countable_Iio_of_lt_omega1 hα) fun β _ => hs β

/-! #### C3 — REPORTED FALSE, with the marked minimal repair

The contract for C3 reads, verbatim:

```
/-- C3. The span of a countable set of vectors is separable, and its
    closure is a proper closed subspace whenever the set is countable and
    `H` is infinite-dimensional — the fact that leaves room at each stage.
    State the form the recursions want: a countable family of vectors
    never spans `H` densely enough to exhaust it, i.e. its closed span has
    an orthogonal complement of infinite dimension, OR at minimum is not
    all of `H`. The stronger form (infinite-dimensional complement) is
    what the ampleness arguments of Paper I §5 will need; supply it if it
    is no harder, and REPORT which was proved. -/
theorem exists_orthogonal_of_countable (s : Set H) (hs : s.Countable) :
    True := by
  sorry
```

Both proposed forms are FALSE, and for the same reason: `H` is
*separable*, so countable sets can have dense span. The standard basis is
already a counterexample — it is countable, its closed span is `⊤`, and
the orthogonal complement of that closed span is `⊥`
(`closedSpan_countable_eq_top_counterexample`,
`exists_orthogonal_of_countable_false`). Even the weakened demand "the
closed span is proper ⇒ the complement is infinite-dimensional" fails:
deleting one basis vector leaves a countable set whose closed span is
proper with a *one*-dimensional complement
(`orthogonal_finiteDimensional_counterexample`).

MARKED MINIMAL REPAIR. What survives — and what the stagewise recursions
can actually use — is the *algebraic* escape lemma: the (not closed) span
of a countable set is never all of `H`. This is Baire, not analysis in the
Hilbert-space sense, and it upgrades for free to "infinite codimension",
since adjoining finitely many vectors keeps the set countable. It is
supplied as `exists_orthogonal_of_countable` (contract name retained),
with the two auxiliary forms `span_ne_top_of_countable` and
`exists_notMem_of_countable_closed_proper` that the recursions will cite,
and with the orthogonal-complement statement in the only form in which it
is true, `orthogonal_ne_bot_of_isClosed_ne_top`. -/

/-- Counterexample to C3, part 1: a countable set whose closed span is all
    of `H`. -/
theorem closedSpan_countable_eq_top_counterexample :
    ∃ s : Set H, s.Countable ∧
      (Submodule.span ℝ s).topologicalClosure = ⊤ :=
  ⟨Set.range ⇑stdBasis, Set.countable_range _, stdBasis.dense_span⟩

/-- Counterexample to C3, part 2 (the contract as stated): there is a
    countable set whose closed span has *zero*-dimensional orthogonal
    complement, so neither "the complement is infinite-dimensional" nor
    "the closed span is not all of `H`" can hold for countable sets. -/
theorem exists_orthogonal_of_countable_false :
    ¬ (∀ s : Set H, s.Countable →
        ((Submodule.span ℝ s).topologicalClosure ≠ ⊤)) := by
  intro hcon
  obtain ⟨s, hs, htop⟩ := closedSpan_countable_eq_top_counterexample
  exact hcon s hs htop

/-- Counterexample to C3, part 3: even for a countable set whose closed
    span *is* proper, the orthogonal complement can be finite-dimensional
    (here: one-dimensional). So the "stronger form" of C3 is not available
    even after repairing the "proper" clause. -/
theorem orthogonal_finiteDimensional_counterexample :
    ∃ s : Set H, s.Countable ∧
      (Submodule.span ℝ s).topologicalClosure ≠ ⊤ ∧
      FiniteDimensional ℝ ((Submodule.span ℝ s).topologicalClosureᗮ) := by
  have hKB : (Submodule.span ℝ (⇑stdBasis '' {n : ℕ | n ≠ 0})).topologicalClosure
      = PlufWO9.blockB stdBasis {n : ℕ | n ≠ 0} := rfl
  refine ⟨⇑stdBasis '' {n : ℕ | n ≠ 0}, (Set.to_countable _).image _, ?_, ?_⟩
  · intro htop
    have hmem : stdBasis 0 ∈ PlufWO9.blockB stdBasis {n : ℕ | n ≠ 0} := by
      rw [← hKB, htop]; exact Submodule.mem_top
    have h := (PlufWO9.mem_blockB_iff stdBasis {n : ℕ | n ≠ 0} (stdBasis 0)).mp hmem 0 (by simp)
    rw [HilbertBasis.repr_self] at h
    simp [lp.single_apply] at h
  · have hle : ((Submodule.span ℝ (⇑stdBasis '' {n : ℕ | n ≠ 0})).topologicalClosure)ᗮ
        ≤ PlufWO1.block ({0} : Set ℕ) := by
      intro v hv
      rw [← PlufWO9.blockB_stdBasis_eq, PlufWO9.mem_blockB_iff]
      intro i hi
      have hiK : stdBasis i ∈ PlufWO9.blockB stdBasis {n : ℕ | n ≠ 0} :=
        PlufWO9.basis_mem_blockB stdBasis _ (by simpa using hi)
      have h0 : inner (𝕜 := ℝ) (stdBasis i) v = 0 :=
        (Submodule.mem_orthogonal _ _).mp hv _ (hKB ▸ hiK)
      rw [HilbertBasis.repr_apply_apply]
      exact h0
    haveI : Module.Finite ℝ (PlufWO1.block ({0} : Set ℕ)) :=
      PlufWO5.finite_block (Set.finite_singleton 0)
    exact Submodule.finiteDimensional_of_le hle

/-- Repair, auxiliary form: a countable family of proper closed subspaces
    of `H` never covers `H` (Baire). -/
theorem exists_notMem_of_countable_closed_proper (M : ℕ → Submodule ℝ H)
    (hcl : ∀ n, IsClosed ((M n : Set H))) (hne : ∀ n, M n ≠ ⊤) :
    ∃ v : H, ∀ n, v ∉ M n := by
  by_contra hcon
  push_neg at hcon
  have hcover : (⋃ n, (M n : Set H)) = Set.univ := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, SetLike.mem_coe]
    exact hcon v
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hcl hcover
  exact hne n (Submodule.eq_top_of_nonempty_interior' _ hn)

/-- Repair, main form: the span of a countable set of vectors is never all
    of `H`. -/
theorem span_ne_top_of_countable (s : Set H) (hs : s.Countable) :
    Submodule.span ℝ s ≠ ⊤ := by
  intro htop
  rcases Set.eq_empty_or_nonempty s with rfl | hne
  · rw [Submodule.span_empty] at htop
    refine stdBasis_ne_zero 0 ?_
    have hmem : stdBasis 0 ∈ (⊥ : Submodule ℝ H) := htop ▸ Submodule.mem_top
    simpa using hmem
  obtain ⟨f, rfl⟩ := hs.exists_eq_range hne
  set F : ℕ → Submodule ℝ H := fun n => Submodule.span ℝ (f '' Set.Iic n) with hF
  have hfin : ∀ n, FiniteDimensional ℝ (F n) :=
    fun n => FiniteDimensional.span_of_finite ℝ ((Set.finite_Iic n).image f)
  have hclosed : ∀ n, IsClosed ((F n : Set H)) := by
    intro n
    haveI := hfin n
    exact Submodule.closed_of_finiteDimensional _
  have hproper : ∀ n, F n ≠ ⊤ := by
    intro n htop'
    refine not_finiteDimensional_H ?_
    haveI : FiniteDimensional ℝ ((⊤ : Submodule ℝ H)) := htop' ▸ hfin n
    exact Module.Finite.equiv (Submodule.topEquiv)
  obtain ⟨v, hv⟩ := exists_notMem_of_countable_closed_proper F hclosed hproper
  have hmono : Monotone F := by
    intro m n hmn
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr hmn))
  have hsup : Submodule.span ℝ (Set.range f) = ⨆ n, F n := by
    have hunion : (⋃ n, f '' Set.Iic n) = Set.range f := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Iic, Set.mem_range]
      constructor
      · rintro ⟨n, m, -, rfl⟩; exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩; exact ⟨m, m, le_refl m, rfl⟩
    rw [← hunion, Submodule.span_iUnion]
  have hmem : v ∈ ⨆ n, F n := by rw [← hsup, htop]; exact Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed F hmono.directed_le).mp hmem
  exact hv n hn

/-- C3, as supplied (marked minimal repair of a false contract; see the
    block comment above). A countable set of vectors never exhausts `H`:
    there is always a vector outside its span, and indeed outside the span
    of that set together with any finite set of further vectors. This is
    the form the stagewise recursions can use; the contracted
    orthogonal-complement form is false in `H`. -/
theorem exists_orthogonal_of_countable (s : Set H) (hs : s.Countable) :
    ∀ t : Finset H, ∃ v : H, v ∉ Submodule.span ℝ (s ∪ (t : Set H)) := by
  intro t
  have hcount : (s ∪ (t : Set H)).Countable := hs.union t.countable_toSet
  have hne := span_ne_top_of_countable _ hcount
  by_contra hcon
  push_neg at hcon
  exact hne (eq_top_iff.mpr fun v _ => hcon v)

/-- The orthogonal-complement statement in the only form in which it is
    true: for a *closed* subspace, properness is exactly nontriviality of
    the complement. -/
theorem orthogonal_ne_bot_of_isClosed_ne_top {M : Submodule ℝ H}
    (hcl : IsClosed (M : Set H)) (hne : M ≠ ⊤) : Mᗮ ≠ ⊥ := by
  haveI := PlufWO8.hasOrthogonalProjection_of_isClosed hcl
  intro h
  exact hne (Submodule.orthogonal_eq_bot_iff.mp h)

/-! ### Reported generalizations

The work order asks for generalizations only if they are cheap, and asks
that they be *derived from* the concrete statements rather than replacing
them. Two are cheap, because an `ℕ`-indexed Hilbert basis is exactly an
isometric identification with `H`; both are derived from Part A below.
Note that the hypothesis is the existence of the basis, not separability
plus completeness — that is the false contract the previous commissions
caught (`E = ℝ` refutes it). Nothing else generalized cheaply: the closed
subspaces and the Hilbert bases of an abstract `E` would need the transfer
of those *sets* along the identification, which is more work than the
concrete proofs above. -/

/-- Generalization of `mk_H`: a real inner product space with an
    `ℕ`-indexed Hilbert basis has cardinality the continuum. -/
theorem mk_eq_continuum_of_hilbertBasis {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis ℕ ℝ E) : #E = continuum := by
  rw [Cardinal.mk_congr b.repr.toEquiv]
  exact mk_H

/-- Generalization of A3: the bounded operators on a real inner product
    space with an `ℕ`-indexed Hilbert basis number the continuum. -/
theorem mk_continuousLinearMaps_of_hilbertBasis {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis ℕ ℝ E) : #(E →L[ℝ] E) = continuum := by
  have e : (E →L[ℝ] E) ≃ (H →L[ℝ] H) :=
    (ContinuousLinearEquiv.arrowCongr b.repr.toContinuousLinearEquiv
      b.repr.toContinuousLinearEquiv).toEquiv
  rw [Cardinal.mk_congr e]
  exact mk_continuousLinearMaps

/-! ### Axiom audit -/

#print axioms mk_closedSubspaces
#print axioms mk_hilbertBases
#print axioms mk_continuousLinearMaps
#print axioms mk_selfAdjoint
#print axioms exists_enum_closedSubspaces
#print axioms exists_enum_hilbertBases
#print axioms exists_enum_selfAdjoint
#print axioms countable_Iio_of_lt_omega1
#print axioms countable_iUnion_Iio
#print axioms exists_orthogonal_of_countable
#print axioms span_ne_top_of_countable
#print axioms exists_notMem_of_countable_closed_proper
#print axioms orthogonal_ne_bot_of_isClosed_ne_top
#print axioms exists_orthogonal_of_countable_false
#print axioms closedSpan_countable_eq_top_counterexample
#print axioms orthogonal_finiteDimensional_counterexample
#print axioms mk_eq_continuum_of_hilbertBasis
#print axioms mk_continuousLinearMaps_of_hilbertBasis

end PlufWO11
