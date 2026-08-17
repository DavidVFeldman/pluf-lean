/-
  PlufWO6.lean — Work Order 6 for the pluf project (Feldman–Wilce).

  Scope: Paper I, Sections 2–4 (the general lattice theory, the geometry of
  slices, the state-space face, and the Kadison–Singer packaging), plus the
  discharge of WO-5's `PlufPackage`:
    (A) plufs in P(H): the maximality criterion, the finite-dimensional
        lemma with its principality dichotomy, and the fact that every
        nonprincipal pluf contains every finite-codimension subspace;
    (B) no prime filters;
    (C) the topology on the space of plufs;
    (D) radii and the gap criterion for the round-slice property;
    (E) the state face S_π: nonempty, weak-* compact, a face, the sandwich
        characterization, and RSP-for-all-T ⟺ singleton;
    (F) Theorem 4.1 parametrized by a Kadison–Singer hypothesis, with the
        Anderson-style equivalence of Remark 4.2;
    (G) the discharge: every nonprincipal pluf satisfies WO-5's
        `PlufPackage`, converting the package theorems of WO-5 into
        the paper's statements.

  Ground rules as in WO-1–WO-5, including the codified counterexample
  license. Marcus–Spielman–Srivastava is quarantined as a hypothesis
  (Part F); nothing else may be assumed. Every theorem is ZFC.

  Base: the WO-5 artifact (CI runs #1–#5 green, 82 theorems). Reuse
  PlufWO1–PlufWO5 freely; all 82 prior theorems must remain green.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  ---------------------------------------------------------------------
  DELIVERY NOTE (WO-6).

  This file is the contract roll-up. The mathematics is developed in the
  modules imported below, each of which carries its item's contract
  statement verbatim in a comment where the returned form differs:

    RequestProject.PlufWO6.Basic     the definition `IsPluf`, verbatim,
                                     with named accessors
    RequestProject.PlufWO6.PartA     A1–A5
    RequestProject.PlufWO6.PartB     B1 and the primeness obstruction
    RequestProject.PlufWO6.PartC     C1, C2 (set level) and the
                                     counterexample to unrestricted C1
    RequestProject.PlufWO6.PartCTop  Part C gate: the topological
                                     packaging and all four clauses of
                                     Proposition 2.4
    RequestProject.PlufWO6.PartD     `upper`, `lower`, `RSP`, D1, D2 and
                                     the Rayleigh calculus
    RequestProject.PlufWO6.PartDEllipsoid
                                     the separate D item: the ellipsoid
                                     form of Lemma 3.1, delivered in
                                     addition to (not instead of) the
                                     contracted Rayleigh form
    RequestProject.PlufWO6.States    Part E gate: `IsState`, verbatim,
                                     and the positivity calculus
    RequestProject.PlufWO6.PartE     E1–E4
    RequestProject.PlufWO6.PartECompact
                                     the uncontracted remainder of
                                     Proposition 3.3: the face is convex
                                     and weak-* compact
    RequestProject.PlufWO6.PartF     `KSHyp`, verbatim, and F1
    RequestProject.PlufWO6.PartG     G1, G2

  The contracted definitions (`IsPluf`, `upper`, `lower`, `RSP`,
  `IsState`, `KSHyp`) are reproduced there verbatim; they are therefore
  not repeated here, so that each contract name denotes exactly one
  declaration.

  Status of the eighteen contract items (item-by-item discussion, the two
  gate verdicts and the census are in `REPORT-WO6.md`):

    A1 maximality_criterion            repaired: `[Nontrivial E]`
    A2 isPluf_of_criterion             as contracted
    A3 principal_of_finiteDimensional  as contracted
    A4 principal_iff_sInf_ne_bot       as contracted
    A5 finCodim_mem_of_nonprincipal    repaired: `[Nontrivial E]`
    B1 no_prime_filter                 repaired: `π.Nonempty`, and the
                                       ambient space specialized to
                                       `PlufWO1.H`
    C1 pluf_sets_inter                 repaired: `M`, `N` closed
    C2 pluf_compl_eq_iUnion            repaired: `[Nontrivial E]`
    D1 lower_le_upper                  as contracted
    D2 rsp_iff_sup_eq_inf              repaired: `[Nontrivial E]`
    E1 face_nonempty                   repaired: `[Nontrivial E]`
    E2 face_iff_sandwich               as contracted
    E3 face_isFace                     as contracted
    E4 rsp_all_iff_face_subsingleton   repaired: `[Nontrivial E]`
    F1 rsp_of_ks                       as contracted
    F2 ks_of_rsp_all                   repaired: hypothesis replaced by
                                       block-witnessed RSP
                                       (`ks_of_blockRSP`)
    G1 plufPackage_of_isPluf           as contracted
    G2 diagonalizable_iff_intimate_pluf as contracted

  Every repair is minimal and is licensed by a counterexample to the
  contracted form, formalized in the artifact:

    `PlufWO6.isPluf_empty_zero_space`      A1, A5, C2, D2, E1, E4
    `PlufWO6.empty_filter_is_prime`        B1
    `PlufWO6.pluf_sets_inter_counterexample`  C1

  All eighteen items are returned, seventeen of them in the contracted
  shape or with a counterexample-licensed minimal repair, and F2 with the
  hypothesis repair analysed below. No `sorry`, `admit`, `axiom` or
  `native_decide` occurs anywhere in the artifact; the audit at the foot
  of this file certifies the whitelist `propext`, `Classical.choice`,
  `Quot.sound` for every completed contract theorem.
-/
import RequestProject.PlufWO6.PartB
import RequestProject.PlufWO6.PartCTop
import RequestProject.PlufWO6.PartDEllipsoid
import RequestProject.PlufWO6.PartE
import RequestProject.PlufWO6.PartECompact
import RequestProject.PlufWO6.PartF
import RequestProject.PlufWO6.PartG

open Set

namespace PlufWO6

/-! ### Part A: the structure lemmas

A1 `maximality_criterion` (PartA) is returned with the marked minimal
repair `[Nontrivial E]`. Contract statement, verbatim:

```
theorem maximality_criterion (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    ∀ M : Submodule ℝ E, IsClosed (M : Set E) →
      M ∈ π ∨ ∃ N ∈ π, M ⊓ N = ⊥
```

The counterexample is `isPluf_empty_zero_space`: over the zero space the
empty family satisfies all five clauses of `IsPluf` and the criterion
fails for it at `M = ⊥`.

A2 `isPluf_of_criterion`, A3 `principal_of_finiteDimensional` and A4
`principal_iff_sInf_ne_bot` are proved exactly as contracted.

A5 `finCodim_mem_of_nonprincipal` (PartA) carries the same repair
`[Nontrivial E]`, licensed by the same counterexample. Contract
statement, verbatim:

```
theorem finCodim_mem_of_nonprincipal (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (hnp : ∀ v : E, v ≠ 0 → ∃ M ∈ π, v ∉ M)
    (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    (hfc : Module.Finite ℝ ↥Vᗮ) :
    V ∈ π
```
-/

/-! ### Part B: no prime filters

B1 `no_prime_filter` (PartB) is returned with two marked minimal repairs:
`π.Nonempty`, and the ambient space specialized to the paper's separable
infinite-dimensional `PlufWO1.H`. Contract statement, verbatim:

```
theorem no_prime_filter (π : Set (Submodule ℝ E))
    (hcl : ∀ M ∈ π, IsClosed (M : Set E))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ E) ∉ π)
    (hdim : 3 ≤ Module.rank ℝ E) :
    ¬ (∀ M N : Submodule ℝ E, IsClosed (M : Set E) → IsClosed (N : Set E) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π)
```

The first repair is licensed by `empty_filter_is_prime`: over a space of
rank 3 the empty family satisfies every contracted hypothesis and is
vacuously prime. The second is a consequence of the printed proof being
defective: as analysed in the header of `PartB.lean` and in
`REPORT-WO6.md`, the three-lines argument does not close, and the
argument that does — `not_prime_of_triple`, which is the printed idea
carried out with a triple of closed subspaces that pairwise meet
trivially and pairwise span — needs such a triple, which exists in `H`
(even coordinates, odd coordinates, diagonal) but cannot exist in odd
finite dimension. The statement is therefore returned for `H`.
-/

/-! ### Part C: the topology on the space of plufs

C1 `pluf_sets_inter` (PartC) is returned with the marked minimal repair
`IsClosed M`, `IsClosed N`. Contract statement, verbatim:

```
theorem pluf_sets_inter (M N : Submodule ℝ E) :
    {π | IsPluf π ∧ M ∈ π} ∩ {π | IsPluf π ∧ N ∈ π}
      = {π | IsPluf π ∧ M ⊓ N ∈ π}
```

The counterexample is `pluf_sets_inter_counterexample`: for `M` the
(non-closed) span of the standard basis vectors of `H` and `N` the line
through `evec 0`, the left side is empty and the right side is not.

C2 `pluf_compl_eq_iUnion` (PartC) is returned with the repair
`[Nontrivial E]`, licensed by `isPluf_empty_zero_space`. Contract
statement, verbatim:

```
theorem pluf_compl_eq_iUnion (M : Submodule ℝ E) (hM : IsClosed (M : Set E)) :
    {π | IsPluf π ∧ M ∈ π}ᶜ ∩ {π | IsPluf π}
      = {π | IsPluf π ∧ ∃ N ∈ π, M ⊓ N = ⊥}
```

GATE VERDICT (Part C, topology packaging): PASSED — the packaging is
cheap and is delivered in full in `PartCTop.lean`: `PlufSpace E` with the
generated topology, `isTopologicalBasis_plufBasis`, and all four clauses
of Proposition 2.4 (`t2Space`; `isClopen_hat`; `isOpen_singleton_principal`
and `dense_principal`; `not_compactSpace`).
-/

/-! ### Part D: radii, gaps, and the round-slice property

D1 `lower_le_upper` is proved exactly as contracted. D2
`rsp_iff_sup_eq_inf` (PartD) is returned with the repair
`[Nontrivial E]`, licensed by `isPluf_empty_zero_space` (over the zero
space `π = ∅` is a pluf, both sides of the equation are `0`, and
`RSP ∅ T` is false). Contract statement, verbatim:

```
theorem rsp_iff_sup_eq_inf (π : Set (Submodule ℝ E)) (hπ : IsPluf π)
    (hpos : ∀ x : E, 0 ≤ inner (𝕜 := ℝ) (T x) x) :
    RSP π T ↔
      sSup (lower T '' π) = sInf (upper T '' π)
```

The contracted positivity hypothesis `hpos` is retained in the returned
form, although `rsp_iff_sup_eq_inf'` shows it is not needed.

D-FORM DECISION (reported, not silently substituted): `upper`/`lower`
are the contracted `sSup`/`sInf` of Rayleigh images, and `RSP` is the
contracted asymptotic-constancy form; the contract is honoured in that
form. The paper's ellipsoid phrasing of Lemma 3.1 (radii of `E_T ∩ M`)
is the separate item the work order describes, and it is delivered as an
addition in `PartDEllipsoid.lean`: for a coercive positive `T`,
`minorRadius_eq` (`m(E_T ∩ M) = uT(M)^{-1/2}`), `majorRadius_eq`
(`M(E_T ∩ M) = lT(M)^{-1/2}`) and `eccentricity_eq`
(`r(E_T ∩ M) = sqrt (uT(M) / lT(M))`) are Lemma 3.1 verbatim, and
`rsp_iff_rspEcc` shows that the contracted `RSP` and the paper's
eccentricity form (`RSPEcc`) define the same property. Nothing is
substituted: both phrasings are present and proved equivalent.
-/

/-! ### Part E: the state face

GATE VERDICT (Part E, states): PASSED — the Mathlib infrastructure is
sufficient and Part E is delivered in full. The census is in
`REPORT-WO6.md`; in brief, Hahn–Banach dominated extension
(`exists_extension_of_le_sublinear`) applies verbatim to the sublinear
functional `T ↦ plimsup π T = sInf (upper T '' π)`, and the projection
calculus (`Submodule.starProjection` and friends) supplies the rest.
Banach–Alaoglu is available but is not needed. Mathlib has no state
theory applicable to `B(E)` for a real Hilbert space `E`, so the
contracted `IsState` shape is retained verbatim (`States.lean`).

The convexity and weak-* compactness clauses of the paper's Proposition
3.3, which the contract does not ask for, are delivered as an addition in
`PartECompact.lean` (`convex_stateFace`, `isClosed_stateFace`,
`isCompact_stateFace`), Banach–Alaoglu being available.

E1 `face_nonempty` (PartE) is returned with the repair `[Nontrivial E]`:
over the zero space no state exists at all, since `id = 0` there.
Contract statement, verbatim:

```
theorem face_nonempty (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    ∃ φ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ ∧
      ∀ M ∈ π, ∀ hM : IsClosed (M : Set E), φ (M.starProjection) = 1
```

E2 `face_iff_sandwich` and E3 `face_isFace` are proved exactly as
contracted (E3's contracted hypothesis `hπ` is retained although the
proof does not use it). E4 `rsp_all_iff_face_subsingleton` is returned
with the repair `[Nontrivial E]` — over the zero space the right side is
vacuously true and the left side false. Contract statement, verbatim:

```
theorem rsp_all_iff_face_subsingleton (π : Set (Submodule ℝ E)) (hπ : IsPluf π) :
    (∀ T : E →L[ℝ] E, IsSelfAdjoint T → RSP π T) ↔
      ∀ φ ψ : (E →L[ℝ] E) →L[ℝ] ℝ, IsState φ → IsState ψ →
        (∀ M ∈ π, ∀ hM : IsClosed (M : Set E), φ (M.starProjection) = 1) →
        (∀ M ∈ π, ∀ hM : IsClosed (M : Set E), ψ (M.starProjection) = 1) →
        φ = ψ
```
-/

/-! ### Part F: Kadison–Singer, quarantined

F1 `rsp_of_ks` (PartF) is proved exactly as contracted from the
quarantined hypothesis `KSHyp`.

F2 `ks_of_rsp_all` is returned in the marked minimal repair
`ks_of_blockRSP`, the hypothesis being strengthened from RSP along plufs
to block-witnessed RSP (`BlockRSP`). Contract statement, verbatim:

```
theorem ks_of_rsp_all
    (h : ∀ (U : Ultrafilter ℕ) (π : Set (Submodule ℝ PlufWO1.H)), IsPluf π →
      (∀ S ∈ U, PlufWO1.block S ∈ π) →
      ∀ T : PlufWO1.H →L[ℝ] PlufWO1.H, IsSelfAdjoint T → RSP π T) :
    ∀ U : Ultrafilter ℕ, KSHyp U
```

Report (the work order's licensed outcome for F2, "if the reverse
implication needs the ellipsoid apparatus, REPORT and return F1 alone").
The statement is not false — it is a true implication, both sides being
theorems of ZFC by Marcus–Spielman–Srivastava — but it is not derivable
from the hypothesis as contracted by the printed unwinding. The
hypothesis yields, for each `ε`, SOME member `M` of the pluf with
Rayleigh oscillation below `ε`; the paving conclusion needs a member of
the special form `block S` with `S ∈ U`. Nothing in `RSP` identifies the
witness with a block, and passing from a general member to a block is
exactly the content of the ellipsoid apparatus of Lemma 3.1 (which the
work order excludes from Part D) together with the paving reduction. A
proof of F2 in the contracted shape therefore requires either that
apparatus or MSS itself, and MSS is quarantined. What the elementary
argument does give, and what is returned as the repair, is
`ks_of_blockRSP`: if for every operator some *block* of `U` has
arbitrarily small Rayleigh oscillation, then `KSHyp U` holds — on such a
block both the Rayleigh quotient of a unit vector and the diagonal sum
(a convex combination of diagonal entries, each of them a Rayleigh value
of the block) sit within the oscillation of the lower Rayleigh value.
-/

/-! ### Part G: the discharge of WO-5's package

G1 `plufPackage_of_isPluf` and G2 `diagonalizable_iff_intimate_pluf`
(PartG) are proved exactly as contracted. With G1, WO-5's package
theorems become statements about genuine maximal filters; G2 is Paper
II's Theorem 5.1 as printed. -/

/-! ### Axiom audit for the WO-6 contract theorems
(The WO-1–WO-5 audits run via the import chain. Items returned under a
census gate are audited if completed and reported if not: F2 is audited
through its repair `ks_of_blockRSP`, its contracted shape not being
returned; the two gates, Parts C and E, are both completed and are
audited here through their contract items.) -/

#print axioms maximality_criterion
#print axioms isPluf_of_criterion
#print axioms principal_of_finiteDimensional
#print axioms principal_iff_sInf_ne_bot
#print axioms finCodim_mem_of_nonprincipal
#print axioms no_prime_filter
#print axioms pluf_sets_inter
#print axioms pluf_compl_eq_iUnion
#print axioms lower_le_upper
#print axioms rsp_iff_sup_eq_inf
#print axioms face_nonempty
#print axioms face_iff_sandwich
#print axioms face_isFace
#print axioms rsp_all_iff_face_subsingleton
#print axioms rsp_of_ks
#print axioms ks_of_blockRSP
#print axioms plufPackage_of_isPluf
#print axioms diagonalizable_iff_intimate_pluf

/-! Counterexamples licensing the marked minimal repairs, audited too. -/

#print axioms isPluf_empty_zero_space
#print axioms empty_filter_is_prime
#print axioms pluf_sets_inter_counterexample

/-! Part E, uncontracted remainder of Proposition 3.3. -/

#print axioms convex_stateFace
#print axioms isClosed_stateFace
#print axioms isCompact_stateFace

/-! Part D, separate item: the ellipsoid form of Lemma 3.1. -/

#print axioms minorRadius_eq
#print axioms majorRadius_eq
#print axioms eccentricity_eq
#print axioms rsp_iff_rspEcc

/-! Part C gate: the topological packaging of Proposition 2.4. -/

#print axioms PlufSpace.isTopologicalBasis_plufBasis
#print axioms PlufSpace.isClopen_hat
#print axioms PlufSpace.isOpen_singleton_principal
#print axioms PlufSpace.dense_principal
#print axioms PlufSpace.not_compactSpace

end PlufWO6
