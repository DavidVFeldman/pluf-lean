/-
  PlufWO15.lean — Work Order 15 for the pluf project (Feldman–Wilce).

  THE FINAL COMMISSION. Paper I, Theorem 5.7 and Proposition 5.9:
    (A) the three-case stage step, packaged so that the recursion never
        splits on cases at run time;
    (B) the ω₁ recursion producing the increasing chain of countable,
        intersection-closed, ample families satisfying (∗);
    (C) Theorem 5.7 — under CH, a nonprincipal pluf every member of which
        is ample, hence with every slice of eccentricity 4 and no round
        slices for T;
    (D) Proposition 5.9 — the set of φ(T) over the state face is the whole
        interval [1/16, 1].

  On completion, every assertion of Papers I–IV is machine-checked, and
  the campaign's target of total verification (modulo the four quarantined
  classical imports — Mathias, MSS, Blecher–Weaver, Rowbottom) is met.

  THE RECURSION PATTERN IS SETTLED — DO NOT REDERIVE IT. WO-12's report
  is definitive and is included in this tarball; §"The recursion
  combinator" prescribes:
    * `PlufWO9.exists_omega1_chain` DOES NOT FIT (its step map cannot see
      the stage index, and stages need the whole set of earlier values,
      not a supremum). Do not attempt it.
    * Use plain well-founded recursion on `Ordinal` with the stage choice
      in a `dite`: `WellFounded.fix` + `WellFounded.fix_eq`, with the
      stage invariant proved AFTERWARDS by `Ordinal.induction` over the
      history `Prev c a = c '' Set.Iio a`. No successor/limit split.
    * Pin the universe (`Ordinal.{0}` annotations) or `(aleph 1).ord`'s
      universe is left as a metavariable.
    * Keep the history and the stage predicate as top-level definitions so
      the `dite` rewrite is a one-liner.
  WO-12's `PlufWO12/PartB.lean` is the worked precedent; read it first.

  INHERITED WARNING. WO-11's C3 came back FALSE in its orthogonality-based
  forms and was repaired to the ALGEBRAIC (Baire) escape statement:
  `PlufWO11.exists_orthogonal_of_countable` is about the SPAN of a
  countable set, not its closed span, and there is no
  "infinite-dimensional orthogonal complement" available. Any room
  argument here must use finite codimension (WO-14's
  `finCodim_of_constraints`, WO-13's C2) — not a countable-set escape.

  Base: the merged tree after WO-12 and WO-14 (233 theorems; CI runs
  #1–#13). All prior theorems must remain green; `PlufWO7a.lean` is the
  census record and is not to be edited.

  CH is a hypothesis (`Cardinal.continuum = Cardinal.aleph 1`), never an
  axiom.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  ---

  DELIVERY NOTES (see REPORT-WO15.md).

  * The new material lives in `RequestProject/PlufWO15/`
    (`Basic.lean`, `PartA.lean`, `PartB.lean`, `PartC.lean`, `PartD.lean`);
    this file keeps the contract statements and discharges them from
    there. As in WO-12, the duplicate `abbrev H` is dropped (it comes
    from `PlufWO15/Basic.lean`) and the two contracted definitions
    `Admissible` and `Decides` live, with their docstrings verbatim, in
    `PlufWO15/Basic.lean`, so that the part files can be stated in terms
    of them.
  * `⊤ ∈ F` is carried as a side hypothesis, not as a field of
    `Admissible` (reported): Case II needs it only to know that
    `p = ⊤ ⊓ p` joins the family, and the recursion maintains it from the
    history `{⊤} ∪ ⋯`.
  * A2 is repaired: as printed it is FALSE for an empty index type (the
    empty union is neither `Admissible` — the `nonempty` field fails —
    nor does it contain `⊤`). `[Nonempty ι]` is added; the original is
    preserved, commented out, immediately below.
-/
import RequestProject.PlufWO15.PartD

open Set Cardinal PlufWO13

namespace PlufWO15

/-! ### Part A: the stage step -/

/-- A1 (the stage step). Given an admissible `F` and any closed `p`, there
    is an admissible `F' ⊇ F` deciding `p`.

    The paper's three cases, which this lemma internalizes so that Part B
    never branches:
      I.   some `g ∈ F` has `g ⊓ p = ⊥` — take `F' = F`;
      II.  `g ⊓ p` is ample for every `g ∈ F` — take
           `F' = F ∪ {p} ∪ {g ⊓ p : g ∈ F}` (note `p = ⊤ ⊓ p` is ample
           provided `⊤ ∈ F`, which the recursion maintains from
           `F₀ = {⊤}`; if it is cleaner to require `⊤ ∈ F` as an
           `Admissible` field, add it and REPORT);
      III. otherwise all `g ⊓ p ≠ ⊥` but some `q ⊓ p` is not ample —
           apply `PlufWO14.blocking_lemma` with `N = p` to get `R`, and
           take `F' = F ∪ {R} ∪ {g ⊓ R : g ∈ F}`.

    Case III is where the campaign's summit result is consumed:
    `blocking_lemma`'s hypotheses are exactly countability, directedness
    (from meet-closure), ampleness of members, and the existence of `q`
    with `q ⊓ p` not ample — plus the `hGN` clause, which is the negation
    of Case I and is available here (it is flagged unused in WO-14, but
    supply it: the contract prints it).

    Meet-closure of `F'` in Cases II/III uses associativity and the
    meet-closure of `F`; ampleness of the new members is
    `blocking_lemma`'s clause (ii) in Case III and the case hypothesis in
    Case II; countability is preserved since the added sets are images of
    `F`. -/
theorem exists_admissible_decides {F : Set (Submodule ℝ H)} (hF : Admissible F)
    (htop : (⊤ : Submodule ℝ H) ∈ F)
    (p : Submodule ℝ H) (hp : IsClosed (p : Set H)) :
    ∃ F', Admissible F' ∧ (⊤ : Submodule ℝ H) ∈ F' ∧ F ⊆ F' ∧ Decides F' p :=
  exists_admissible_decides_aux hF htop p hp

/-  A2, contract statement, preserved verbatim:

theorem admissible_iUnion {ι : Type*} [Countable ι] (F : ι → Set (Submodule ℝ H))
    (hF : ∀ i, Admissible (F i)) (htop : ∀ i, (⊤ : Submodule ℝ H) ∈ F i)
    (hdir : ∀ i j, ∃ k, F i ⊆ F k ∧ F j ⊆ F k) :
    Admissible (⋃ i, F i) ∧ (⊤ : Submodule ℝ H) ∈ ⋃ i, F i

    This is FALSE for an empty index type: `⋃ (i : Empty), F i = ∅`, which
    contains no `⊤` and fails the `nonempty` field of `Admissible`, while
    all three hypotheses hold vacuously. The refutation is recorded as
    `admissible_iUnion_counterexample`. The marked minimal repair adds
    `[Nonempty ι]`. -/

/-- A2 (unions of chains stay admissible), minimal repair: `ι ≠ ∅`. A
    countable increasing union of admissible families containing `⊤` is
    admissible and contains `⊤`. This is the limit-stage bookkeeping; in
    the history formulation it is applied to `⋃ (Prev c a)` and its
    countability comes from `PlufWO11.countable_Iio_of_lt_omega1`.

    Form chosen (reported): a countable *and nonempty* index type with the
    stated directedness hypothesis. Part B consumes it at
    `ι = Option {p // p < a}`, the `none` branch contributing `{⊤}`, which
    makes the index nonempty even at stage `0` and at limit stages. -/
theorem admissible_iUnion {ι : Type*} [Countable ι] [Nonempty ι]
    (F : ι → Set (Submodule ℝ H))
    (hF : ∀ i, Admissible (F i)) (htop : ∀ i, (⊤ : Submodule ℝ H) ∈ F i)
    (hdir : ∀ i j, ∃ k, F i ⊆ F k ∧ F j ⊆ F k) :
    Admissible (⋃ i, F i) ∧ (⊤ : Submodule ℝ H) ∈ ⋃ i, F i :=
  admissible_iUnion_aux F hF htop hdir

/-! ### Part B: the ω₁ recursion -/

section Recursion

variable (hCH : continuum = aleph 1)

include hCH

/-- B1 (the chain). Under CH there is a monotone family of admissible
    families indexed by the countable ordinals, containing `⊤` at every
    stage, whose stage `a` decides the `a`-th closed subspace (WO-11's
    `exists_enum_closedSubspaces`).

    Follow WO-12's pattern exactly (see the header): `WellFounded.fix` on
    `Ordinal` with the stage choice in a `dite`, the invariant established
    afterwards by `Ordinal.induction` over the history. At stage `a` the
    accumulated family is `⋃ (c '' Set.Iio a)` together with `{⊤}`:
    admissible by A2, and A1 extends it to decide the `a`-th subspace.

    Deliver `c` together with: monotonicity, admissibility at every stage,
    `⊤ ∈ c a`, and the decision property. -/
theorem exists_admissible_chain :
    ∃ c : Ordinal → Set (Submodule ℝ H),
      (∀ a b, a ≤ b → b < (aleph 1).ord → c a ⊆ c b) ∧
      (∀ a, a < (aleph 1).ord → Admissible (c a)) ∧
      (∀ a, a < (aleph 1).ord → (⊤ : Submodule ℝ H) ∈ c a) ∧
      (∀ p : Submodule ℝ H, IsClosed (p : Set H) →
        ∃ a, a < (aleph 1).ord ∧ Decides (c a) p) :=
  exists_admissible_chain_aux hCH

end Recursion

/-! ### Part C: Theorem 5.7 -/

/-- C1 (Paper I, Theorem 5.7). Assume CH. There is a nonprincipal pluf
    every member of which is ample.

    Take `σ` = the upward closure among closed subspaces of `⋃ a, c a`.
    Membership: proper because ample subspaces are nonzero; upward closed
    and meet-closed by construction (meets: two members contain members of
    a common stage by monotonicity, and stages are meet-closed); ampleness
    of every member by `PlufWO13.ample_of_ample_le`; maximality via
    `PlufWO6.isPluf_of_criterion` fed by the decision property;
    nonprincipality because ample subspaces are infinite-dimensional, so
    no line lies in every member — route through
    `PlufWO6.principal_iff_sInf_ne_bot` or directly, prover's choice,
    reported. -/
theorem exists_pluf_all_ample (hCH : continuum = aleph 1) :
    ∃ σ : Set (Submodule ℝ H), PlufWO6.IsPluf σ ∧
      (∀ v : H, v ≠ 0 → ∃ M ∈ σ, v ∉ M) ∧
      (∀ M ∈ σ, Ample M) :=
  exists_pluf_all_ample_aux hCH

/-- C2 (the radius assertions, and the failure of RSP). For such a `σ`,
    every slice has minor radius 1, major radius 4 and eccentricity 4 —
    WO-13's B1′ (`minorRadius_of_ample`, `majorRadius_of_ample`,
    `eccentricity_of_ample`) applied to each member — and `σ` fails RSP
    for `T`, since `PlufWO6.upper T M = 1` and
    `PlufWO6.lower T M = 1/16` for every member (WO-13's
    `upper_eq_one_of_ample`, `lower_eq_sixteenth_of_ample`) so the gap
    never closes. State the RSP failure as `¬ PlufWO6.RSP σ T`.

    (`hσ` and `hne` are printed by the contract and are kept; the constant
    gap argument uses neither.) -/
theorem not_rsp_of_all_ample {σ : Set (Submodule ℝ H)} (hσ : PlufWO6.IsPluf σ)
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty) :
    ¬ PlufWO6.RSP σ T :=
  not_rsp_of_all_ample_aux hamp

/-- C2, the radius clauses: every slice of an all-ample family has minor
    radius `1`, major radius `4`, and hence eccentricity `4`. -/
theorem radii_of_all_ample {σ : Set (Submodule ℝ H)}
    (hamp : ∀ M ∈ σ, Ample M) :
    ∀ M ∈ σ, PlufWO6.minorRadius T M = 1 ∧ PlufWO6.majorRadius T M = 4 ∧
      PlufWO6.eccentricity T M = 4 := fun M hM =>
  ⟨minorRadius_of_ample (hamp M hM), majorRadius_of_ample (hamp M hM),
    eccentricity_of_ample (hamp M hM)⟩

/-! ### Part D: Proposition 5.9 — the limit is an interval -/

/-- D1 (⊆). For a pluf all of whose members are ample, every state of the
    face has `φ T ∈ [1/16, 1]`. Immediate from WO-6's sandwich
    characterization (`PlufWO6.face_iff_sandwich`) with `upper ≡ 1`,
    `lower ≡ 1/16`. -/
theorem face_apply_mem_Icc {σ : Set (Submodule ℝ H)} (hσ : PlufWO6.IsPluf σ)
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty)
    (φ : (H →L[ℝ] H) →L[ℝ] ℝ) (hφ : PlufWO6.IsState φ)
    (hface : ∀ M ∈ σ, ∀ hM : IsClosed (M : Set H), φ M.starProjection = 1) :
    inner (𝕜 := ℝ) (φ T) (1 : ℝ) ∈ Icc (1/16 : ℝ) 1 := by
  have h := face_apply_mem_Icc_aux hσ hamp hne φ hφ hface
  simpa using h

/-- D2 (⊇, the substance). For every `c ∈ [1/16, 1]` there is a state in
    the face with `φ T = c`.

    Paper's proof: define `ψ (a • I + b • T) = a + b * c` on
    `span {I, T}`. For `b ≥ 0` the upper limit of `a • I + b • T` along
    `σ` is `a + b ≥ a + b*c`; for `b < 0` it is `a + b/16 ≥ a + b*c`. So
    `ψ` is dominated by the sublinear `T ↦ sInf (upper T '' σ)` and
    extends by Hahn–Banach to a linear functional squeezed between the
    lower and upper limits, hence a state of the face by
    `PlufWO6.face_iff_sandwich`.

    WO-6 established that this sublinear functional is defined on all of
    `B(H)` (not merely the self-adjoints) and used
    `exists_extension_of_le_sublinear` for `face_nonempty`; reuse that
    machinery. The two-dimensional domain `span {I, T}` needs `I` and `T`
    linearly independent — true since `T` is not a scalar (its diagonal
    takes two values); prove the small independence lemma if not
    available.

    If the domination inequality is cleaner with the sublinear functional
    stated as `fun A => sInf (PlufWO6.upper A '' σ)`, restate and REPORT;
    the contract fixes the conclusion, not the route.

    Route taken (reported): the domination is fed to WO-6's
    `exists_state_with_value`, i.e. Hahn–Banach along the ray through `T`
    against `PlufWO6.plimsup σ = fun A => sInf (upper A '' σ)`. The
    normalization at `I` is part of `IsState`, so no two-dimensional
    domain and no independence lemma are needed. -/
theorem exists_face_state_apply_eq {σ : Set (Submodule ℝ H)} (hσ : PlufWO6.IsPluf σ)
    (hamp : ∀ M ∈ σ, Ample M) (hne : σ.Nonempty)
    {c : ℝ} (hc : c ∈ Icc (1/16 : ℝ) 1) :
    ∃ φ : (H →L[ℝ] H) →L[ℝ] ℝ, PlufWO6.IsState φ ∧
      (∀ M ∈ σ, ∀ hM : IsClosed (M : Set H), φ M.starProjection = 1) ∧
      φ T = c :=
  exists_face_state_apply_eq_aux hσ hamp hne hc

/-- D3 (Paper I, Proposition 5.9). The set of values `φ T` over the state
    face of the pluf of Theorem 5.7 is exactly `[1/16, 1]`. -/
theorem face_values_eq_Icc (hCH : continuum = aleph 1) :
    ∃ σ : Set (Submodule ℝ H), PlufWO6.IsPluf σ ∧
      (∀ v : H, v ≠ 0 → ∃ M ∈ σ, v ∉ M) ∧
      (∀ M ∈ σ, Ample M) ∧
      {r : ℝ | ∃ φ : (H →L[ℝ] H) →L[ℝ] ℝ, PlufWO6.IsState φ ∧
        (∀ M ∈ σ, ∀ hM : IsClosed (M : Set H), φ M.starProjection = 1) ∧
        φ T = r} = Icc (1/16 : ℝ) 1 :=
  face_values_eq_Icc_aux hCH

/-! ### Axiom audit -/

#print axioms exists_admissible_decides
#print axioms admissible_iUnion
#print axioms admissible_iUnion_counterexample
#print axioms exists_admissible_chain
#print axioms exists_pluf_all_ample
#print axioms not_rsp_of_all_ample
#print axioms radii_of_all_ample
#print axioms face_apply_mem_Icc
#print axioms exists_face_state_apply_eq
#print axioms face_values_eq_Icc

end PlufWO15
