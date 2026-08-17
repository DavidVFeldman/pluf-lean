# Work Order WO-5 — pluf project (Feldman–Wilce)

**Ground truth:** this tarball (`pluf-wo5.tar.gz`). Contract: `PlufWO5.lean`.
Paper source: Paper II, Sections 2–5 minus Theorem 5.4, included as
`paper2.pdf`; every contracted proof appears there in full.

**Base:** WO-4 artifact (CI runs #1–#4 green; 65 theorems; full project under
`base/`). `PlufWO5.lean` imports `RequestProject.PlufWO4`. All 65 prior
theorems must remain green.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-4, with the codified license)

Census first — and for this commission the census carries a decision:
Part F is **census-gated** (see below). Report-rather-than-repair with the
WO-3/WO-4 license: false contract ⇒ formalize a counterexample where
feasible, preserve the contract verbatim in a comment, MAY supply a marked
minimal repair; ratification at audit. No
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` per contract
theorem; whitelist `propext`, `Classical.choice`, `Quot.sound`. If the
commission is too large for one run, complete A → B → C → D → E → F and
return what is green.

## Items and notes

**Part A.** A1 is the analytically richest single item of the commission:
the recursion (finitely many linear conditions leave a nonzero vector in an
infinite-dimensional space; a tail threshold via summability), then the
1/48 estimate (Cauchy–Schwarz on the tail; the geometric sum). A2 needs a
transport of A1 into `block S₀` along the enumeration of an infinite subset
of ℕ; whether by an explicit isometry `block S₀ ≃ H` or by re-running the
recursion inside the block is the prover's choice, reported. The
`FinCodimIn` rendering of relative codimension may be restated (see its
docstring) — B1/C1/D3 must then be restated consistently, all reported.

**Part B.** B1(⇐) is the paper's construction `V = (M ⊓ block S) ⊕ block Sᶜ`
— note `V` must be shown closed and of finite codimension; B1(⇒) is
monotonicity. B2 is the two standard facts about finite codimension and
finite dimension, quantified through the generating intersections.

**Part C.** C1–C2 are the necessity computations, reduced from the paper's
dimension formulas to exactly what the theorem consumes: C1 = "every U-set
touches infinitely many pieces" (finite union of pieces in U forces a piece
in U) plus linear independence of the restricted constraint vectors inside
the relative orthocomplement; C2 = the two-point witnesses (reuse the WO-3
technique; witnesses from distinct pairs have supports meeting in at most
one point and are linearly independent — organize the pairs per piece as
consecutive pairs if that is cleaner) plus the deletion argument, which
needs `hcof` to keep the pruned set in `U`. C4 consumes `MathiasHyp`, A2,
and B1; the derivation of `MathiasHyp` from selectivity is the quarantined
classical import and is NOT in scope.

**Part D.** All concrete. The 0-indexed `gowersU n = e n − ((n+2)/(n+1)) •
e (n+1)` is orthogonal to `w = (1/(n+1))_n`; the duplication and its
ℓ²-membership are bookkeeping. D1's split case builds the twisted weight
vector along the selector `a_i ∈ {2i, 2i+1}` and collapses its pairings by
duplication. D2's echelon argument: order the 2-to-1 index set, exhibit for
each row a witness position where all later rows vanish. D3 composes with
A-machinery. Reindexing from the paper's 1-based display is licensed.

**Part E.** `PlufPackage` bundles exactly the companion-paper facts the
proofs consume; do not attempt to derive the package from maximality (that
is WO-6). E1's two directions are as docstringed; note the trace's
ultrafilter axioms each come from a named package field. E2 forward uses
the trace; backward, an ultrafilter contained in a complementary-pair-free
deciding family equals the trace.

**Part F — OPTIONAL, census-gated.** F1–F2 quantify over `HilbertBasis`.
First deliverable of the census: an assessment of Mathlib's `HilbertBasis`
API against the needs listed in the Part F comment. If the cost is
reasonable, prove F1–F2 and append their audits; if not, return Parts A–E
with the assessment — a fully acceptable outcome, and the basis machinery
will be commissioned separately (it is also wanted for WO-7).

## Deliverables

Census (including the Part F verdict); compiling artifact with all 65 prior
theorems green; `#print axioms` for the 16 contract theorems of Parts A–E
(plus Part F if taken); item-by-item report including the A2 transport
route, any `FinCodimIn` restatement, and the C2 pair organization.

## Context

With WO-5, Paper II is verified except for: Theorem 5.4 (WO-7), the
selectivity⇒Mathias import (quarantined by design), Corollary 5.2(b)–(c)
(one-line compositions and MSS-dependent state facts, deferred to
WO-6/WO-8), and — if the census gates it out — Propositions 5.5–5.6. The
campaign then proceeds per `CAMPAIGN.md` to WO-6 (Paper I structure theory
and states), which among other things discharges `PlufPackage` for genuine
maximal filters, converting Part E's package theorems into the paper's
statements.
