# Summary of changes for run f4bed4cf-0bc3-4ed5-84cc-303e41480fa5
Work Order 17 (Paper V, Sections 4–6) is delivered complete and machine-checked.

**What was built.** The base tree from the tarball was unpacked into the project and the WO-17 contract was formalized in `RequestProject/PlufWO17.lean` (contract roll-up, with the `#print axioms` audit) together with `RequestProject/PlufWO17/{Basic,PartA,PartB,PartC}.lean`. The full project — the prior work-order tree plus the new module — builds cleanly; `PlufWO7a.lean` is untouched, and no base file was edited.

**All nine contract items are proved, in the printed statements, with no `sorry`, `admit`, `axiom` or `native_decide`.** Each contract theorem's `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

- A1 `suppFamily_sUnion_closed` — (S1), cited from the existing `exists_supp_sUnion` as directed.
- A2 `suppFamily_elimination_finite` — (S2) for finite deleted sets, via the finite correction term.
- B1 `suppFamily_eq_coords`; B2 `exists_realization_in_lp`; B3 `suppFamily_isScrawlFamily` (conditional on the quarantined hypothesis `AroKaHyp`, which is supplied and never discharged).
- C1 `expSum_zeros_lt` (Lemma 6.1); C2 `geom`, `geom_apply`, `exists_supp_compl_finite` (Example 6.2); C3 `not_isScrawlFamily_of_cofiniteOnly`.

The vocabulary (`IsCircuitFamily`, `IndepOf`, `HasSM`, `IsScrawlFamily`, `suppFamily`, `AroKaHyp`) is defined from scratch, verbatim from the contract; nothing was imported from Mathlib's matroid API and no matroid instance was built. The definition the contract left open, `geom`, is filled in with its square-summability proof.

**Report.** `REPORT-WO17.md` contains the census and every requested finding: the C1 form actually proved (the cardinality form `expSum_card_zeros_lt`, from which the contracted negative form is derived, with a purpose-built Rolle counting lemma since Mathlib has none); the coercion used in B1 (`PlufWO16.toFun`, which the base tree did not export and which is introduced here as the linear map carried by the ℓ² coercion); the rescaling in B2 (`weight n = 2⁻ⁿ / (1 + Σ_{v ∈ t} |v n|)` for a finite generating set); the answer to B3's closedness question (`Submodule.closed_of_finiteDimensional` applies verbatim, recorded as `isClosed_of_finite`); and the vocabulary finding for Part A. Two hypotheses are recorded as unused but retained verbatim as contracted — A2's `hXw`, and C3's closedness `hM` (C3's proof also needs only the antichain axiom, not the (SM) clause). The residue is exactly the two intended items: the quarantined `AroKaHyp` and the paper's open Question 9.3.

All work is committed and pushed.