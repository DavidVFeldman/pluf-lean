/-
  PlufWO4.lean — Work Order 4 for the pluf project (Feldman–Wilce).

  Scope: the fourth paper of the series (products of normal measures), plus
  its ω-lemmas:
    (A) the homogeneity framework and the injectivity-on-a-square theorem;
    (B) the Fubini product as an ultrafilter, its basic largeness facts, the
        full-selector property and its failure for the product, and the
        non-isomorphism packaging;
    (C) the exact-paving property (EPP): paving of the product from
        homogeneity (the centerpiece), EPP ⇒ σ-Q, and the transfer of the
        WO-2/WO-3 theory to EPP hypotheses, instantiated at the product;
    (D) constraints on addable blockers at ℕ: generalized thinness, the
        support lemma, and the Baire piece-spread lemma.

  As always, NO large-cardinal machinery is axiomatized. Rowbottom
  homogeneity, the Fodor property, uncountable pivots, and smallness enter
  only as hypotheses; every theorem below is ZFC.

  This WO builds on the WO-3 artifact; `PlufWO1`–`PlufWO3` are unchanged and
  all 39 prior theorems remain green (their audits re-run via the import
  chain).

  FILE LAYOUT.  The contract file is split into four modules, all in
  namespace `PlufWO4`:
    * `RequestProject.PlufWO4.Homog`    — Part A (A1) and the twelve-pattern
      core `exists_avoiding_homog` shared by A1 and C2;
    * `RequestProject.PlufWO4.Fubini`   — Part B (B0–B8);
    * `RequestProject.PlufWO4.EPP`      — Part C (C1–C7);
    * `RequestProject.PlufWO4.Blockers` — Part D (D1–D3).
  Restatements under the codified licence are marked in the docstring of the
  theorem concerned, with the contract statement preserved verbatim in a
  comment beside it; `REPORT.md` collects them.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.
-/
import RequestProject.PlufWO4.Homog
import RequestProject.PlufWO4.Fubini
import RequestProject.PlufWO4.EPP
import RequestProject.PlufWO4.Blockers

namespace PlufWO4

/-! ### Axiom audit for the WO-4 contract theorems
(The WO-1/WO-2/WO-3 audits run via the import chain.) -/

#print axioms inj_on_pairs               -- A1
#print axioms mem_fubini_iff             -- B0
#print axioms triangle_mem_fubini        -- B1
#print axioms countableSmall_fubini      -- B2
#print axioms column_notMem_fubini       -- B3
#print axioms fullSelector_of_fodor      -- B4
#print axioms not_fullSelector_fubini    -- B5
#print axioms fullSelector_map_iff       -- B6
#print axioms fubini_not_iso_fodor       -- B7
#print axioms sigmaQ_fubini              -- B8
#print axioms sigmaQ_of_EPP              -- C1
#print axioms EPP_fubini                 -- C2
#print axioms exact_paving_of_EPP        -- C3
#print axioms exact_dichotomy_of_EPP     -- C4
#print axioms quadratic_flat_of_EPP      -- C5
#print axioms PhiU_decides_of_EPP        -- C6
#print axioms product_decides            -- C7
#print axioms gen_thin                   -- D1
#print axioms inter_infinite_iff_mem     -- D2a
#print axioms rank_le_of_le_block_finite -- D2b
#print axioms support_mem                -- D2
#print axioms baire_spread               -- D3

/-! ### Audit of the auxiliary results supplied by this work order -/

#print axioms exists_avoiding_homog      -- the twelve-pattern core (A1, C2)
#print axioms fullSelectorAll_of_fodor   -- B4, universe-polymorphic
#print axioms not_fullSelectorAll_fubini -- B5, universe-polymorphic
#print axioms fullSelectorAll_map_iff    -- B6, universe-polymorphic

end PlufWO4
