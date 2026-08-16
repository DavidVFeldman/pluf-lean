/-
  PlufWO1.lean — Work Order 1 for the pluf project (Feldman–Wilce): root file.

  The mathematical content is split across
    * `RequestProject.PartA` — Part A, σ-Q-point combinatorics (A1–A4);
    * `RequestProject.PartB` — Part B, the witness subspace and thinness
      (B1a–B1d, B2);
    * `RequestProject.PartC` — Part C, the block-intersection identity and the
      no-disjointly-supported-blocker proposition (C1, C2).

  Every item of the work order is proved; there is no `sorry`, `admit`,
  `axiom` or `native_decide` anywhere in the artifact.  The `#print axioms`
  output for each contract theorem is below; each one uses only the whitelist
  `propext`, `Classical.choice`, `Quot.sound`.
-/
import RequestProject.PartA
import RequestProject.PartB
import RequestProject.PartC

namespace PlufWO1

/-! ### Axiom audit -/

-- Part A
#print axioms not_mem_union_of_not_mem              -- A1
#print axioms sigmaQ_of_partition_selectors         -- A2
#print axioms sigmaQ_of_partition_selectors₀        -- A2, contract universe
#print axioms partition_selectors_of_sigmaQ         -- A2′
#print axioms minima_mem_of_fodor                   -- A3
#print axioms sigmaQ_of_fodor                       -- A3′
#print axioms exists_transversal_not_mem            -- A4

-- Part B
#print axioms constraintVec_apply                   -- B1a
#print axioms constraintVec_ne_zero                 -- B1a
#print axioms mem_block_iff                         -- B1b
#print axioms isClosed_block                        -- B1c
#print axioms inner_constraintVec_eq_zero_of_disjoint -- B1d
#print axioms mem_W_iff                             -- B1b/W
#print axioms thin                                  -- B2

-- Part C
#print axioms closure_span_inter_block              -- C1
#print axioms noblock                               -- C2

end PlufWO1
