/-
  PlufWO16.lean — Work Order 16 for the pluf project (Feldman, Wilce).

  Scope: the verifiable core of Paper V ("Support families of closed subspaces
  of ℓ², with an application to diagonalizable projection filters"):
    (A) support families and closure under unions — Lemma 2.1,
        Proposition 2.2, Corollary 2.3 — and the elimination property,
        Proposition 3.2;
    (B) the diagonal block: the families D(M) and I(M), the trace formula,
        diagonal consistency, and the covering criterion — Section 7;
    (C) the transfers to the series: intimacy is the covering condition at
        level three, the collapse on plufs, the covering number of Gowers's
        subspace, and the constraint on addable blockers — Section 8.

  Sections 4-6 of the paper (scrawl axioms, the finite-rank classification
  through the theorem of Aroca et al., and the model-space example) are NOT
  contracted; the census verdict on each is in `REPORT-WO16.md`.

  A NOTE ON SCALARS. Paper V is stated over ℂ, because its finite-rank
  classification is representability and the theorem it invokes is
  field-sensitive. Everything contracted here is field-blind, and the paper
  says so in its conventions: Sections 7 and 8 use no property of the scalars.
  This work order therefore mechanizes over ℝ, against the existing
  development. SCALAR FINDING: none of the seventeen contracted items needed
  a property of ℝ beyond what the paper's conventions allow, namely that
  there are more scalars than coordinates — used exactly once, in the
  counting step `exists_pos_lt_notMem` behind A1 and A2, and in the form "an
  interval of ℝ is uncountable". Ordering of ℝ is used only for convenience
  (the coefficients are taken positive rather than merely nonzero, and the
  frozen minima are real minima); over ℂ the same proofs run with moduli.
  See `REPORT-WO16.md`.

  Base: the v1.0 release tree (243 theorems; CI runs #1-#14). `PlufWO16.lean`
  imports `RequestProject.PlufWO15`. All prior theorems remain green;
  `PlufWO7a.lean` is untouched.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  ---------------------------------------------------------------------
  DELIVERY NOTE (WO-16).

  This file is the contract roll-up. The mathematics is developed in the
  modules imported below, all in namespace `PlufWO16`:

    RequestProject.PlufWO16.Basic  the contracted definitions `supp`, `cD`,
                                   `cI`, `DiagonallyConsistent`,
                                   `HasFiniteCover`, `pair`, verbatim, and
                                   the support/block dictionary
    RequestProject.PlufWO16.PartA  A1-A4
    RequestProject.PlufWO16.PartB  B1-B4
    RequestProject.PlufWO16.PartC  C1-C5, including C4a as supplied

  Status of the seventeen contract items:

    A1  exists_supp_union                        as contracted
    A2  exists_supp_iUnion                       as contracted
    A3  exists_supp_sUnion                       as contracted
    A4  exists_supp_elimination                  as contracted
    B1  mem_cD_iff, cI_downward                  as contracted
    B2  trace_subset, mem_trace_of_forall_cD     as contracted
    B3  diagonallyConsistent_iff                 as contracted
    B4  diagonallyConsistent_iff_not_finiteCover as contracted
    C1  intimate_iff_no_two_cover                as contracted
    C2  diagonallyConsistent_of_mem_diagonalizable  as contracted
    C3  diagonalizable_iff_all_diagonallyConsistent as contracted
    C4a gowersX_pairSum_rec                      statement supplied (below)
    C4b mem_cI_gowersX_iff                       as contracted
    C4  gowersX_threeCover                       as contracted
    C5  diagonallyConsistent_of_addableBlocker   as contracted

  No repair was needed: every contracted statement is returned in the printed
  shape, so the counterexample license was not invoked. Two reportable
  observations, both recorded at the theorems concerned and in
  `REPORT-WO16.md`:

    * A4's minimality hypotheses `hminx` and `hminy` are not used. The
      eliminated vector `y_p • x - x_p • y` is nonzero as soon as
      `supp x ≠ supp y`, since vanishing would make `x` and `y`
      proportional. The hypotheses are retained verbatim, as contracted.

    * `PlufWO16.supp` is definitionally `PlufWO2.supp` at the standard space
      (`PlufWO16.supp_eq_plufWO2_supp` is `rfl`); it is introduced only
      because the contract names it.

  C4a, the item whose statement the contract left open, was contracted as

  ```
  theorem gowersX_pairSum_rec {x : H} (hx : x ∈ PlufWO5.gowersX) (k : ℕ) :
      True
  ```

  and is supplied as the general pair-sum recursion carried by the constraint
  vectors, in the form the development already supports:

  ```
  theorem gowersX_pairSum_rec {x : H} (hx : x ∈ PlufWO5.gowersX) (k : ℕ) :
      pairSum x k = (((k : ℝ) + 2) / ((k : ℝ) + 1)) * pairSum x (k + 1)
  ```

  together with its converse `mem_gowersX_iff_pairSum_rec`, which states that
  the recursion *is* membership, and the consequence actually used by C4b,
  `gowersX_pairSum_eq_zero_of_eq_zero` (one vanishing pair sum forces all of
  them). `PlufWO5.gowersX_pairSum_eq_zero` — the finitely supported case
  proved in `PlufWO5/PartD.lean` — is the special case obtained by running
  the recursion from a pair beyond the support.

  INDEXING. The development is 0-indexed: `PlufWO5.gowersX` is the joint
  kernel of the constraint vectors `PlufWO5.gowersV n`, whose pairs are
  `pair k = {2k, 2k+1}` for `k ≥ 0`. The paper displays the pairs 1-indexed,
  `P_i = {2i-1, 2i}` for `i ≥ 1`; the two agree under `i = k + 1`, and every
  statement here is in the 0-indexed convention.

  A2 RECURSION SHAPE. `PlufWO14.exists_seq_of_step` does apply, with
  `α = ℝ`: the stage constraint refers to the accumulated partial sum, but
  the partial sum at stage `n` is a function of the coefficient history below
  `n`, so the stage predicate `PlufWO16.stepPred` is a predicate of `n`, of
  the history below `n`, and of the new coefficient, which is exactly the
  gadget's shape. What the paper's phrasing hides is that the stage predicate
  must be satisfiable for an *arbitrary* history; the surviving clause is
  therefore only that the new coefficient kills no coordinate at which the
  new vector is nonzero, and "every coordinate caught so far stays alive" is
  a separate induction over the chosen sequence
  (`PlufWO16.psum_ne_zero`). Details in `REPORT-WO16.md`.

  No `sorry`, `admit`, `axiom` or `native_decide` occurs anywhere in the
  artifact; the audit at the foot of this file certifies the whitelist
  `propext`, `Classical.choice`, `Quot.sound` for every contract theorem.
-/
import RequestProject.PlufWO16.PartA
import RequestProject.PlufWO16.PartB
import RequestProject.PlufWO16.PartC

namespace PlufWO16

/-! ### Axiom audit -/

-- Part A
#print axioms exists_supp_union                        -- A1
#print axioms exists_supp_iUnion                       -- A2
#print axioms exists_supp_sUnion                       -- A3
#print axioms exists_supp_elimination                  -- A4

-- Part B
#print axioms mem_cD_iff                               -- B1
#print axioms cI_downward                              -- B1
#print axioms trace_subset                             -- B2
#print axioms mem_trace_of_forall_cD                   -- B2
#print axioms diagonallyConsistent_iff                 -- B3
#print axioms diagonallyConsistent_iff_not_finiteCover -- B4

-- Part C
#print axioms intimate_iff_no_two_cover                -- C1
#print axioms diagonallyConsistent_of_mem_diagonalizable   -- C2
#print axioms diagonalizable_iff_all_diagonallyConsistent  -- C3
#print axioms gowersX_pairSum_rec                      -- C4a
#print axioms mem_gowersX_iff_pairSum_rec              -- C4a, converse half
#print axioms mem_cI_gowersX_iff                       -- C4b
#print axioms gowersX_threeCover                       -- C4
#print axioms diagonallyConsistent_of_addableBlocker   -- C5

end PlufWO16
