# Summary of changes for run b1ab724c-217c-40c8-8892-19123800e50a
Work Order 8 is complete: every contract item of `PlufWO8.lean` (Parts A–F) is discharged in Lean, the project builds clean, and the deliverable report is written.

**Artifact.** `RequestProject/PlufWO8.lean` is the contract roll-up (18 theorems), with the mathematics developed in `RequestProject/PlufWO8/{Limits,Proj,Singular,Additive,Face,BW,Compacts}.lean`.

- A1/A2: `phiLim` (U-limit of the diagonal, via WO-3's `exists_ulim` with bound ‖T‖), its defining property `phiLim_spec`, and the bundled state `phiLimCLM` / `isState_phiLim`.
- B1/B2: `phiLim_rankOne_eq_zero`, `phiLim_finiteDimensional_eq_zero`. **Delivered in addition** (as the work order invited): the finite-rank-operator form `phiLim_finiteRank_eq_zero` and the compact-operator form `phiLim_compact_eq_zero`.
- C1/C2/C3: `phiLim_iSup_eq_zero`, `phiLim_iSup` (tsum form, returned in full), `phiLim_iSup_eq_zero_generic`.
- D1/D2: `phiLim_mem_face` and `phiLim_pure` (purity derived from the face machinery, not assumed).
- E1–E4: `oneSet`, `BWPackage`, `oneSet_upward`, `oneSet_inf`, `bot_notMem_oneSet`, `exists_oneSet_inf_eq_bot`, `isPluf_oneSet`, `oneSet_nonprincipal`.
- F1: `oneSet_phiLim_eq_PhiU`.

**Verification.** `lake build` succeeds. No `sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]` anywhere in the artifact (the only textual matches are prose in docstrings). The build emits 133 `#print axioms` lines — the 115 of the base roll-ups, all still green, plus the 18 new ones — and every one reports exactly `[propext, Classical.choice, Quot.sound]`. Quarantine respected: Blecher–Weaver enters only through `BWPackage`; Marcus–Spielman–Srivastava appears nowhere.

**Findings (report-rather-than-repair).** No contract item was false. One structural finding: `Submodule.starProjection` needs `[HasOrthogonalProjection]`, synthesizable only when the closedness/finiteness hypothesis is a *binder*, so C1/C2/C3, `oneSet`, `BWPackage.excision` and E4 as contracted do not elaborate. Each contract text is preserved verbatim in a comment beside a marked minimal repair (instance binders; dependent pair for the conjunction/bounded existential; a named finiteness binder), propositionally identical to the contract. Route reports are recorded for C1/C3 (a shorter argument than the contracted ε2⁻ⁿ; C3's `hctble` is unused but retained), D2 (via flattening + compression rather than `rsp_all_iff_face_subsingleton`), and the compact-operator item (a finite ε/2-net, so no Hilbert basis or finite-rank-density theorem was needed — both absent from Mathlib). No item needed ℂ.

**Report.** `WO8-REPORT.md` at the repo root contains the census (base / Mathlib / newly built / confirmed absent), the item-by-item report including the A2 bundling, B2 and C2/C3 outcomes, the D2 phrasing, unused-hypothesis notes, the elaboration finding with its repair table, the scalar finding, the axiom audit summary, and the recommendation that a scoping census (WO-7a) be the next step.

All work is committed and pushed.