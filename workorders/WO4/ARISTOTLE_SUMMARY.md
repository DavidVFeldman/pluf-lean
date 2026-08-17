# Summary of changes for run 40ced8ed-cd84-4a3f-ac09-c9910f5ffbb7
Work Order WO-4 (mechanization of Paper IV) is complete and green.

**Artifact.** The Lean development lives in `RequestProject/PlufWO4.lean` (root module: header, imports, and the axiom audit) with four submodules:
- `RequestProject/PlufWO4/Homog.lean` — Part A: `RowbottomFor`, `UncountablePivots`, the ordered-pattern analysis (`pattern₁`–`pattern₁₂`, packaged as `exists_avoiding_homog`), and A1 `inj_on_pairs`.
- `RequestProject/PlufWO4/Fubini.lean` — Part B: `fubini` and B0–B8.
- `RequestProject/PlufWO4/EPP.lean` — Part C: `EPP` and C1–C7.
- `RequestProject/PlufWO4/Blockers.lean` — Part D: D1, D2a, D2b, D2, D3.

**Status.** `lake build` succeeds (8038 jobs, no errors). All 22 contract theorems are proved, plus 4 auxiliaries (`exists_avoiding_homog`, `fullSelectorAll_of_fodor`, `not_fullSelectorAll_fubini`, `fullSelectorAll_map_iff`). No `sorry`, `admit`, `axiom`, or `native_decide` occurs anywhere in the new files. Every contract theorem carries a `#print axioms` line; each reports exactly `[propext, Classical.choice, Quot.sound]`, within the agreed whitelist. The 39 theorems of the earlier work orders (`PlufWO1`–`PlufWO3`) are untouched and still build.

**Reported deviations (report-rather-than-repair, with minimal restatement; the contract statements are preserved verbatim in comments beside each theorem).**
1. *A1 restated*: the hypothesis `htail : ∀ γ, {β | γ < β} ∈ D` (every tail belongs to D) is required — it is the paper's "pass to a tail of H" step, used by every pattern whose free coordinate varies upward. It is already contracted for B1, B8 and C2, so nothing downstream changes.
2. *B5 restated*: the contract's `FullSelector` quantifies its index type over `Type 0`, while the refuting column partition of `κ × κ` is indexed by `κ` itself; the contract-shaped statement is therefore proved at `κ : Type`. A universe-polymorphic variant `FullSelectorAll` is supplied and refuted for all `κ`, and B7 — the proposition the paper's Section 2 is aimed at — is proved verbatim for `κ` in any universe.

**Pattern-analysis finding.** The case analysis needs twelve *ordered* placement patterns rather than the paper's two regimes as literally stated: two of them require choosing a point strictly between an already-fixed coordinate and a pivot, which is not available from the pivot hypothesis applied to `H`. The fix is the small lemma `exists_mid`, applying the pivot hypothesis to the tail `H ∩ (γ, →)`.

**C4–C6 refactoring decision.** Option (ii) was taken: fresh EPP-based proofs inside `PlufWO4`, reusing the WO-2/WO-3 auxiliaries, with the base files left untouched. Two further route notes: C3 needs no adjoint (EPP is symmetric in the two coordinates, so one family of supports serves both halves), and the contracted hypotheses `hsmall` (C4, C6) and `hcof` (D2) are retained as contracted but turn out to be unused.

**Deliverables.** `REPORT.md` contains the census and the item-by-item report, including the two restatements, the pattern finding, the C4–C6 decision, and the unused-hypothesis notes. The Properties table lists all 22 contract items, the auxiliary pattern lemma, and the definitions they are stated in terms of. All work is committed and pushed.