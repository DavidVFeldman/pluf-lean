# Work Order WO-8 — pluf project (Feldman–Wilce)

**Ground truth:** this tarball (`pluf-wo8.tar.gz`). Contract: `PlufWO8.lean`.
Paper source: Paper III §§4–5 (`paper3.pdf`, included), whose proofs are the
reference; Paper I §6 (`paper1.pdf`, included) for the F1 restatement.

**Base:** the WO-6 artifact (CI runs #1–#6 green; 115 theorems; full project
under `base/`). `PlufWO8.lean` imports `RequestProject.PlufWO6`. All 115
prior theorems must remain green.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-6)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment +
marked minimal repair; ratification at audit). No
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per completed
contract theorem; whitelist `propext`, `Classical.choice`, `Quot.sound`.
Partial completion order: A → B → E → D → C → F.

**Quarantine discipline.** The Blecher–Weaver regularity/excision theory
enters ONLY through the `BWPackage` structure of Part E. Marcus–Spielman–
Srivastava must not appear anywhere: the entire point of Paper III §4 is
that these existence statements avoid it. If any item appears to need
paving, that is a finding — REPORT it rather than importing a hypothesis.

**Scalars.** The project is over ℝ; the literature states this material
over ℂ. The contracted arguments use only positivity, the quadratic form,
and completeness, so they should be scalar-agnostic. If an item genuinely
needs ℂ, report rather than restate.

## Item notes

**Part A.** `phiLim` is the U-limit of the diagonal; WO-3's `exists_ulim`
supplies existence, with boundedness from `‖T‖`. A2 asks for the bundled
`(Hk κ →L[ℝ] Hk κ) →L[ℝ] ℝ` together with `PlufWO6.IsState`; linearity of
ultrafilter limits and the bound `|φ T| ≤ ‖T‖` are the content. The
bundling shape is the prover's choice, reported.

**Part B.** B1 is the countable-support argument (`PlufWO2.countable_supp`
plus `CountableSmall`). B2 extends to finite rank. The paper says
"annihilates the compacts"; the finite-rank form is contracted because it
is what Part F consumes — if the compact-operator statement is cheap
(finite-rank approximation plus continuity of `φ`), return it in addition
and report.

**Part C.** C1 is the paper's ε2^{-n} argument, and is the item Part E and
the paper's Theorem 4.2 actually consume. C2 (the tsum form) and C3 (the
generic-index `<κ`-additive form, in the style of WO-3's `iInf_mem_PhiU`)
are wanted but secondary: if the bookkeeping in either proves
disproportionate, return C1 and report. Note C3's contracted expansion
hypothesis is deliberately weak (an ε-approximation from finite
subfamilies) so as to avoid committing to an unconditional-sum API;
strengthen or restate if Mathlib offers something cleaner.

**Part D.** Purity is NOT assumed: it is derived from WO-6's face
machinery, which is the reason WO-6 preceded this commission. D2's route
is `rsp_all_iff_face_subsingleton` fed by WO-3's `quadratic_flat` at
`L = phiLim T`. The contracted conclusion is uniqueness of the face
element; if extremality in Mathlib's `Set.extremePoints` sense is wanted
verbatim, state it and report.

**Part E.** The heart. `BWPackage` bundles exactly the two Blecher–Weaver
facts the proof of Theorem 4.2 uses: σ-filtration of the 1-set and
excision. E2 is the paper's excision computation; E3 assembles it with
WO-6's `isPluf_of_criterion`; E4 is the nonprincipality clause via WO-6's
`principal_of_finiteDimensional`. Note E3 needs `[Nontrivial E]`, per the
WO-6 ratifications.

**Part F.** F1 identifies the 1-set of the limit state with the block
filter — the sentence Paper I §6 summarizes. Both inclusions are noted in
the docstring.

## Deliverables

Census; compiling artifact with all 115 prior theorems green;
`#print axioms` for every completed contract theorem; item-by-item report
including the A2 bundling, the B2 and C2/C3 outcomes, the D2 phrasing, and
any scalar findings.

## Context

WO-8 completes the state-theoretic layer of the series. With it, Papers
I–IV are verified except for: Paper I §5 and Paper II Theorem 5.4 (the
transfinite CH constructions), Paper II Propositions 5.5–5.6, and Paper I
Proposition 2.3 in odd finite dimension — all collected in the projected
WO-7, whose infrastructure (essential spectrum; `HilbertBasis` assembly and
reindexing) is absent from Mathlib per the WO-5 and WO-6 censuses. A
scoping census WO-7a is the recommended next step after this commission,
before any proof obligations in that direction are contracted.
