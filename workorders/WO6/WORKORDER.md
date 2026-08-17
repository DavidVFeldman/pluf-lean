# Work Order WO-6 — pluf project (Feldman–Wilce)

**Ground truth:** this tarball (`pluf-wo6.tar.gz`). Contract: `PlufWO6.lean`.
Paper source: Paper I, Sections 2–4, included as `paper1.pdf`; all contracted
proofs appear there.

**Base:** WO-5 artifact (CI runs #1–#5 green; 82 theorems; full project under
`base/`). `PlufWO6.lean` imports `RequestProject.PlufWO5`. All 82 prior
theorems must remain green.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-5)

Census first — and this commission's census carries **two gates** (Parts C
and E) whose verdicts are themselves primary deliverables. Report-rather-
than-repair with the codified license (false contract ⇒ counterexample +
verbatim contract in comment + marked minimal repair; ratification at
audit). No `sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per
completed contract theorem; whitelist `propext`, `Classical.choice`,
`Quot.sound`. Order if partial: A → G → B → D → C → F → E (note: **G early**
— it is short and it retroactively upgrades WO-5's Part E, so it is the
highest value-per-line item in the commission).

## The two gates

**Part C (topology packaging).** The set-level lemmas are contracted
unconditionally. The `TopologicalSpace`/`IsTopologicalBasis` packaging, and
the four clauses of Proposition 2.4 (Hausdorff, zero-dimensional, principal
plufs isolated and dense, non-compactness), are gated: prove them if
Mathlib's generated-topology API makes them cheap; otherwise return the
set-level lemmas with an assessment.

**Part E (states).** CENSUS-CRITICAL and expected to be the pivotal finding.
The paper needs states on `B(H)`, their weak-* topology, Banach–Alaoglu, and
Hahn–Banach extension from a sublinear functional on self-adjoints. Report
precisely what Mathlib offers (`ContinuousLinearMap` positivity, any state
API for C*-algebras, `WeakDual` compactness) and whether the `IsState`
shape contracted here should be replaced — it is a placeholder, not a
statement to honor literally if a better rendering exists. If the
infrastructure is absent or disproportionate, return Parts A–D and F–G with
the assessment; that is a fully acceptable outcome and will determine
whether WO-8 (Paper III §§4–5, which needs the same machinery plus
Blecher–Weaver) is commissioned at all or restructured.

## Item notes

**Part A.** A1 is the most-cited fact of the series; A2 is its converse and
the two together are what Part G needs. A3's argument (least finite
dimension; a proper line inside a member of dimension ≥ 2 defeats
maximality) needs care about which subspaces are closed — in finite
dimensions all are. A5 is the fact WO-5's package assumed.

**Part B.** The paper's printed proof of Proposition 2.3 is compressed and
visibly hedged (a parenthetical aside mid-argument). Treat the *statement*
as the contract and the printed argument as a sketch: if the three-line
argument does not survive formalization, report with a corrected argument or
a counterexample to the printed reasoning — the statement itself we believe,
and the Kochen–Specker route is the conceptual backstop (but is NOT to be
formalized here).

**Part D.** `upper`/`lower` are contracted via `sSup`/`sInf` of Rayleigh
images; positivity and boundedness of `T` make these finite. If the paper's
ellipsoid phrasing (Lemma 3.1: radii of `E_T ∩ M`) is wanted verbatim rather
than the Rayleigh form, that is a separate item — report rather than
silently substitute.

**Part F.** `KSHyp` is the quarantined MSS import, contracted in a paving
shape that mentions only the diagonal and a `U`-set. F2's reverse direction
may need the ellipsoid apparatus; if so, report and return F1 alone.

**Part G.** The payoff item, and short: A1 + A5 + the lattice axioms give
`PlufWO5.PlufPackage`, and G2 is the resulting restatement of Paper II's
Theorem 5.1 for genuine plufs. Do this early.

## Deliverables

Census (including both gate verdicts); compiling artifact with all 82 prior
theorems green; `#print axioms` for every completed contract theorem;
item-by-item report including the `IsState` rendering, the Part B outcome,
and the D-form decision.

## Context

WO-6 is the last commission of ordinary size. After it, the campaign's
remaining work is: WO-8 (Paper III §§4–5 and Paper I §6 residue, gated on
Part E's verdict), and WO-7 — the long pole — comprising Paper I §5 and
Paper II Theorem 5.4, both transfinite recursions requiring
essential-spectrum infrastructure and the `HilbertBasis` machinery whose
absence WO-5's census already documented. `CAMPAIGN.md` in the repo holds
the map; WO-7a (a scoping census for that infrastructure) may be
commissioned in parallel with WO-6 if capacity allows.
