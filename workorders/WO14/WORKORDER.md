# Work Order WO-14 — pluf project (Feldman–Wilce)

**Paper I, Lemma 5.6 — the blocking lemma.** The technical heart of Paper I
and the hardest single item of this campaign. The census budgeted Paper I §5
at ~3–4 commissions with this lemma as the dominant cost, and issued a
standing recommendation: if the budget binds, quarantine the lemma as a
named hypothesis rather than force it. This work order structures both the
attempt and the fallback.

**Ground truth:** this tarball (`pluf-wo14.tar.gz`). Contract:
`PlufWO14.lean`. Paper source: `paper1.pdf`, Lemma 5.6 and its proof — the
contract docstrings restate that proof completely, including the
perturbation step's algebra and the exact-diagonality endgame, and the
skeleton was drafted against the paper's text line by line, not from a
summary. `REPORT-WO13.md` is included: its §6 (D1's final signature and the
notes for WO-14) is the interface this commission consumes, and the S2
docstring quotes its prescription verbatim.

**Base:** the merged tree after WO-13 (216 theorems; CI runs #1–#12).
`PlufWO14.lean` imports `RequestProject.PlufWO13`. All prior theorems must
remain green; `PlufWO7a.lean` is the census record, not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-13)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment + marked
minimal repair; ratification at audit). No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` per contract theorem; whitelist `propext`,
`Classical.choice`, `Quot.sound`. Partial order: S0 → S1 → S2 → P1 → W0 →
W2 → W1 → W3 — note W2 BEFORE W1: the assembly-side lemmas are cheaper and
their final shapes may inform how W1's clauses are best delivered.

## The quarantine fallback (read first)

If W1 — the recursion — cannot be closed within this commission, deliver
everything else plus the conditional assembly:

    theorem blocking_lemma_of_sequence
      (hseq : <W1's conclusion, verbatim, as a hypothesis>) : <W3's conclusion>

audited like any contract theorem, and report precisely where W1 failed
(which stage, which clause, which missing API). That outcome converts the
blocking lemma into a named quarantined hypothesis whose entire consumption
is machine-checked — the sanctioned fallback, and a fully acceptable return.
W3 unconditional is the primary target; do not sacrifice the S/P/W2 items to
chase it.

## The three design disciplines (bound into the contracts)

**1. Rayleigh only.** S1 and S2 conclude with `|⟪T w, w⟫ − λ| ≤ ε`, never
with a defect-norm bound in `H`. S1's route goes through the compression to
a finite-codimension cut, and Rayleigh values transfer exactly through
compressions while defect norms do not. The recursion's clause (a) consumes
only Rayleigh. Do not strengthen S1: the stronger statement is not provable
by this route and is not needed.

**2. Escape only at the blocked value.** λ₀ (missing from
`essSpec (compress (q ⊓ N))`) supports S2; λ₁ does not — nothing excludes
`λ₁ ∈ essSpec (compress (h ⊓ N))`. The odd stage MUST go through P1's
perturbation: S1 at λ₁ for `w'`, S2 at λ₀ for `z ∉ N` (two extra
constraints: `z ⊥ w'`, `z ⊥ T w'`), then the η-perturbation. A draft
applying S2 at λ₁ is wrong even if it elaborates.

**3. Exact orthogonality throughout.** All stage constraints are linear and
imposed exactly; no error accumulates; W2's compressions are exactly
diagonal. This is the paper's highlighted methodological point and the
reason the endgame needs no approximation bookkeeping.

## Item notes

**S0.** Check `PlufWO13/Basic.lean` first — its finiteness-transfer lemmas
may already contain this; cite rather than reprove if so.

**S2.** The WO-13 report's prescription, followed exactly: `escape` at
tolerance ε, constraints cut `K` to finite codimension, clause (iii) of
`escape` prevents the cut from falling into `N`, and
`quadratic_estimate_of_bound` converts. `escape`'s `hVN` binder is derivable
from `hnot` (a missing value refutes ampleness); supply it, do not
hypothesize it.

**P1.** The full algebra is in the docstring. Over ℝ, self-adjointness makes
one constraint (`z ⊥ T w'`) kill both cross terms; the displacement bound is
`η²`-clean via `T_bounds`; the bad set for clause (iii) is at most one point
of η. This lemma is what replaces the orthogonal decomposition of the stage
subspace along N — non-distributivity forbids that decomposition, which is
why the paper's odd stage exists at all.

**W0.** A duplicate of WO-12's B2 (in flight, not importable); accepted,
reconciled at merge.

**W1.** The recursion. The constraint list at stage n is finite and
explicit: `w ⊥ w j`, `w ⊥ T (w j)`, `w ⊥ P_{Nᗮ}(w j)` for `j < n` — the
second gives T-orthogonality in both orders by self-adjointness, the third
gives the y-orthogonality via idempotence and self-adjointness of the
projection. The missing-value hypothesis descends from `h 0 ⊓ N` to
`h n ⊓ N` by the contrapositive of `essSpec_compress_mono`. The ε-rate
`1/(n+1)` is contracted for definiteness; restate if another is cleaner.

**W2.** Generic in the orthonormal T-orthogonal system; no recursion, pure
Hilbert-space algebra. The eigenvector packaging (identity in `↥(R j)` vs
starProjection identity in `H`) is the prover's choice — pick the form W3's
essential-spectrum step consumes most directly, and report.

**W3.** The assembly, with the paper's statement verbatim. Extraction of λ₀
covers the degenerate `q ⊓ N = ⊥` via `notMem_essSpec_compress_bot`. The
essential-spectrum membership step reuses WO-13 A3's route (orthonormal
exact-eigenvalue sequences, weakly null in the compression); if the
witnessing criterion is not exported, prove the bridging lemma and report.
The hypothesis `g ⊓ N ≠ ⊥ ∀ g` is contracted for fidelity to the paper and
expected to be flagged unused — retain it.

## Deliverables

Census (including the S0 verdict and the essSpec-membership-criterion
verdict); compiling artifact with all 216 prior theorems green;
`#print axioms` for every contract theorem (or, under the fallback, for
everything plus `blocking_lemma_of_sequence`); report with: the W2
packaging, the W1 constraint bookkeeping as implemented, the rate restated
if changed, and — if the fallback was taken — the precise failure analysis.

## Context

This is the campaign's summit. After it: only **WO-15** remains — Paper I
Theorem 5.7 and Proposition 5.9, the CH recursion consuming WO-11's
enumerations, W3 (or its quarantined form), and whichever ω₁-recursion
pattern WO-12 reports as workable. WO-12 runs in parallel and shares nothing
with this commission except the accepted W0 duplication. A reminder
inherited from WO-11 for the WO-15 drafter: the stage-room lemma there is
the ALGEBRAIC (Baire) escape form; orthogonality-based forms are false.
