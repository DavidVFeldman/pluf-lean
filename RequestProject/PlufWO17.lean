/-
  PlufWO17.lean — Work Order 17 for the pluf project (Feldman, Wilce).

  Scope: the remainder of Paper V — Sections 4, 5 and 6 — completing its
  verification:
    (A) the scrawl vocabulary, defined here rather than imported, and
        Theorem 4.3: the support family satisfies (S1) outright and (S2) for
        finite deleted sets;
    (B) Theorem 5.2: the finite-rank classification, with the theorem of
        Aroca et al. quarantined as a named hypothesis;
    (C) Lemma 6.1 (zeros of an exponential sum), Example 6.2 (the model
        space realizes every cofinite set), and the conditional consequence
        of Section 6.

  ON VOCABULARY. The WO-16 census reported that Mathlib's `Matroid` supports
  infinite ground sets, circuits, elimination and duality, but offers no
  constructor building a matroid from a circuit family, and no scrawls,
  cofinitary duals or representability. This work order does NOT wait on that.
  Everything Paper V asserts is a statement about families of subsets of ℕ and
  about kernels of matrices, and Part A defines the three predicates it needs
  from scratch — `IsCircuitFamily`, `IsScrawlFamily`, and the maximality axiom
  — in a dozen lines. Do not import `Mathlib.Data.Matroid`; do not attempt to
  build a `Matroid` instance. If a later Mathlib gains the constructor, the
  bridge is one lemma and is not this commission's business.

  ON THE MODEL SPACE. Paper V's Example 6.2 has been rewritten since the WO-16
  census: the generalized Vandermonde determinant and Cramer's rule are gone,
  replaced by a dimension count against Lemma 6.1. That census reported
  Vandermonde positivity absent from Mathlib and recommended leaving Section 6
  alone; the rewrite removes the dependency, and Part C is contracted against
  the new proof. The only analytic input is Rolle's theorem.

  Base: the tree after WO-16 (261 theorems; CI runs #1–#15).
  `PlufWO17.lean` imports `RequestProject.PlufWO16`. All 261 prior theorems
  must remain green; `PlufWO7a.lean` is the census record and is not to be
  edited.

  Scalars: over ℝ, as in WO-16, and for the same reason.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  ---------------------------------------------------------------------
  DELIVERY NOTE (WO-17).

  This file is the contract roll-up. The mathematics is developed in the
  modules imported below, all in namespace `PlufWO17`:

    RequestProject.PlufWO17.Basic  the contracted definitions
                                   `IsCircuitFamily`, `IndepOf`, `HasSM`,
                                   `IsScrawlFamily`, `suppFamily`, `AroKaHyp`
                                   and `geom`, verbatim, together with the
                                   coordinate map `PlufWO16.toFun` reported
                                   under B1
    RequestProject.PlufWO17.PartA  A1, A2
    RequestProject.PlufWO17.PartB  B1, B2, B3
    RequestProject.PlufWO17.PartC  C1, C2, C3

  Status of the nine contract items:

    A1  suppFamily_sUnion_closed               as contracted
    A2  suppFamily_elimination_finite          as contracted
    B1  suppFamily_eq_coords                   as contracted
    B2  exists_realization_in_lp               as contracted
    B3  suppFamily_isScrawlFamily              as contracted
    C1  expSum_zeros_lt                        as contracted
        (from expSum_card_zeros_lt; see below)
    C2  geom, geom_apply, exists_supp_compl_finite   as contracted
    C3  not_isScrawlFamily_of_cofiniteOnly     as contracted

  No repair was needed: every contracted statement is returned in the printed
  shape, so the counterexample license was not invoked. The reportable
  findings, each recorded at the declaration concerned and in
  `REPORT-WO17.md`:

    * VOCABULARY (Part A). The three predicates are defined from scratch, as
      directed; nothing from `Mathlib.Data.Matroid` is imported and no
      `Matroid` instance is built. The definitions are self-contained and were
      used exactly as printed: A1 and A2 need only `suppFamily`, and C3 needs
      only the `nonempty`, `ne_empty` and `antichain` fields of
      `IsCircuitFamily`.

    * A2's hypothesis `hXw : ↑X ⊆ supp x` is not used. The correction term
      `∑_{p ∈ X} (x p / (u p) p) • u p` kills each `p ∈ X` and misses `z`
      whether or not the deleted coordinates lie in `supp x`; if some `p ∈ X`
      has `x p = 0` the corresponding coefficient is simply `0`. The
      hypothesis is retained verbatim, as contracted.

    * C3's hypotheses `hM` (closedness) and the (SM) clause of
      `IsScrawlFamily` are not used. The paper's chain runs through the
      failure of (SM); the shorter argument formalized here uses only that a
      circuit is a member of the family — hence, by `hcof`, cofinite — and
      that deleting one of its points leaves a cofinite set, which by `hall`
      is again a member and so a union of circuits, producing a circuit
      properly inside a circuit against the antichain axiom. Both hypotheses
      are retained verbatim, as contracted.

    * B1's coordinate map. `PlufWO16` exports no map `H → (ℕ → ℝ)`; the one
      the contract names, `PlufWO16.toFun`, is introduced in
      `PlufWO17/Basic.lean` as the ℝ-linear map carried by the `lp` coercion,
      and is injective by `lp.ext`.

    * B2's rescaling. Given a finite generating set `t` of `W`, the weights
      are `weight t n = 2⁻ⁿ / (1 + ∑_{v ∈ t} |v n|) > 0`, so that
      `|weight t n * v n| ≤ 2⁻ⁿ` for each generator `v`, and the realization
      is the submodule of `ℓ²` of all vectors whose coordinates are
      `weight t n * f n` for some `f ∈ W`.

    * B3's closedness. `Submodule.closed_of_finiteDimensional` applies in
      exactly the form needed; see `PlufWO17.isClosed_of_finite`.

    * C1's form. The induction is run in the cardinality form
      `expSum_card_zeros_lt` (Finset of exponents, Finset of zeros, strict
      inequality `#Z < #s`), and the contracted negative form
      `expSum_zeros_lt` is derived from it; C2 consumes only the latter.

  No `sorry`, `admit`, `axiom` or `native_decide` occurs anywhere in the
  artifact; the audit at the foot of this file certifies the whitelist
  `propext`, `Classical.choice`, `Quot.sound` for every contract theorem.
-/
import RequestProject.PlufWO17.PartA
import RequestProject.PlufWO17.PartB
import RequestProject.PlufWO17.PartC

namespace PlufWO17

/-! ### Axiom audit -/

#print axioms suppFamily_sUnion_closed
#print axioms suppFamily_elimination_finite
#print axioms suppFamily_eq_coords
#print axioms exists_realization_in_lp
#print axioms suppFamily_isScrawlFamily
#print axioms expSum_zeros_lt
#print axioms geom_apply
#print axioms exists_supp_compl_finite
#print axioms not_isScrawlFamily_of_cofiniteOnly

-- the cardinality form of C1 actually proved, and the two reported auxiliaries
#print axioms expSum_card_zeros_lt
#print axioms isClosed_of_finite

end PlufWO17
