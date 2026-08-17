/-
  PlufWO5.lean — Work Order 5 for the pluf project (Feldman–Wilce).

  Scope: Paper II ("Intimate subspaces, block filters, and the
  diagonalization of maximal projection filters"), Sections 2–5, minus
  Theorem 5.4 (the CH recursion, deferred to WO-7):
    (A) the zero–cofinite dichotomy: the gliding-hump theorem (Thm 2.1),
        its relativization (Cor 2.2), and the dense-zero-set consequence
        (Prop 4.2, second clause);
    (B) the block filter at ω with finite-codimension adjunction, and the
        membership/addability criteria (Lemma 3.2);
    (C) Theorem 3.4: necessity in full (the witness subspace is unadded yet
        addable), and sufficiency parametrized by a Mathias hypothesis;
    (D) Gowers's intimate subspace (Thm 4.1): intimacy, the dimension
        bound, and the no-cofinite corollary;
    (E) Theorem 5.1 (diagonalizable ⟺ every member intimate) and
        Corollary 5.2(a), stated against a package of lattice facts
        consumed from Paper I (to be discharged in WO-6);
    (F) OPTIONAL, census-gated: Propositions 5.5–5.6 (one-witness
        reduction; chains never suffice), which quantify over arbitrary
        orthonormal bases.

  The Hilbert space is PlufWO1.H = lp (fun _ : ℕ => ℝ) 2 with its standard
  basis; blocks are PlufWO1.block. The paper indexes from 1 and this
  development from 0; reindexing adjustments are licensed and reportable.
  Mathias's theorem is quarantined as a hypothesis (Part C); nothing else
  may be assumed.

  Base: the WO-4 artifact (CI runs #1–#4 green, 65 theorems). Reuse
  PlufWO1–PlufWO4 freely; in particular PlufWO1.{H, block, mem_block_iff,
  isClosed_block, constraintVec, W, mem_W_iff, thin,
  inner_constraintVec_eq_zero_of_disjoint}, PlufWO4's Blockers lemmas, and
  the WO-3 two-point-witness technique. All 65 prior theorems must remain
  green.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.
-/
import RequestProject.PlufWO5.Basic
import RequestProject.PlufWO5.PartA
import RequestProject.PlufWO5.PartB
import RequestProject.PlufWO5.PartC
import RequestProject.PlufWO5.PartD
import RequestProject.PlufWO5.PartE

/-!
  FILE LAYOUT.  The contract file is split into modules, all in namespace
  `PlufWO5`:
    * `RequestProject.PlufWO5.Basic` — shared coordinate, block and
      finite-dimensionality infrastructure, and `FinCodimIn`;
    * `RequestProject.PlufWO5.PartA` — the zero-cofinite dichotomy (A1-A3);
    * `RequestProject.PlufWO5.PartB` — the block filter at omega (B1-B3);
    * `RequestProject.PlufWO5.PartC` — Theorem 3.4 (C1-C4);
    * `RequestProject.PlufWO5.PartD` — Gowers's intimate subspace (D0-D3);
    * `RequestProject.PlufWO5.PartE` — diagonalization (E1-E2).
  Restatements under the codified licence are marked in the docstring of
  the theorem concerned, with the contract statement preserved verbatim in
  a comment beside it; `REPORT-WO5.md` collects them.

  Part F (Propositions 5.5-5.6) is census-gated; see `REPORT-WO5.md` for
  the assessment of Mathlib's `HilbertBasis` API against its needs.
-/

namespace PlufWO5

/-! ### Axiom audit for the WO-5 contract theorems
(The WO-1–WO-4 audits run via the import chain.) -/

#print axioms gliding_hump                       -- A1
#print axioms relativized_dichotomy              -- A2
#print axioms dense_zero_set                     -- A3
#print axioms phiOmega_iff_finCodim              -- B1
#print axioms addable_iff_infDim                 -- B2
#print axioms bot_not_phiOmega                   -- B3
#print axioms witness_not_mem                    -- C1
#print axioms witness_infDim                     -- C2
#print axioms necessity                          -- C3
#print axioms decides_of_mathias                 -- C4
#print axioms isClosed_gowersX                   -- D0
#print axioms gowersX_intimate                   -- D1
#print axioms gowersX_dim_bound                  -- D2
#print axioms gowersX_no_finCodim                -- D3
#print axioms diagonalizable_iff_intimate        -- E1
#print axioms diagonalizable_iff_extends_phiOmega
-- commissioner addition at merge (2026-08-17): audit the formalized E2
-- obstruction, per the WO-3/WO-4 precedent for counterexamples.
#print axioms exists_phiOmega_not_isClosed -- E2

end PlufWO5
