# CLAUDE.md — pluf-lean

Lean 4 verification repository for the **pluf project** (Feldman–Wilce):
maximal filters in the projection lattice of a Hilbert space. This file
encodes the working protocol so any Claude session (or collaborator) can
continue without re-deriving conventions.

## Pipeline

Claude drafts mathematics and Lean work orders → **Aristotle** (Harmonic)
executes the formalization → this repo + CI provide the independent compile →
GitHub release tag → Zenodo archival.

- Aristotle requires **Lean v4.28.0** exactly; `lean-toolchain` and
  `lake-manifest.json` pin the toolchain and Mathlib. Do not bump either
  except as part of a deliberate migration WO.
- Work-order inputs to Aristotle are **tar.gz**; archives for David's own
  use are **zip**. The WO input tarball is the ground truth for each
  commission and is preserved under `workorders/WOn/`.

## Protocol constants (binding)

1. **Tarball as ground truth.** Each `workorders/WOn/` keeps the exact WO
   input archive, the WORKORDER, Aristotle's REPORT and SUMMARY.
2. **Census-first.** Every WO instructs Aristotle to return an item-by-item
   census (Mathlib API, feasibility) before or with the proofs.
3. **Report-rather-than-repair.** Renaming/idiom changes fine; changes to
   mathematical content are not — obstructions are reported, never silently
   patched. False-looking statements come back as reports.
4. **Closure discipline.** No `sorry`, `admit`, `axiom`, `native_decide`.
   Every contract theorem carries `#print axioms`; whitelist:
   `propext`, `Classical.choice`, `Quot.sound`. **No closure claim in any
   paper until this repo's CI is green on the relevant artifact** — the
   claimed axiom lines must appear in an independent build log, not only in
   Aristotle's report.
5. `scripts/check_axioms.py` is the machine form of (4); it must list every
   contract theorem of every merged WO. Extend the list when merging a WO.

## Repo conventions

- Two-component version tags (`v1.0`, `v1.1`, …), tagged only on green CI.
- Zenodo: cite **concept DOIs**, not version DOIs.
- Paper front matter and metadata email: `dvfinnh@gmail.com`.
- David works on Windows 10 (GitHub Desktop, CMD/PowerShell): give
  Windows-native commands in instructions; CI itself runs Linux.

## Layout

    RequestProject/      Lean sources (PartA/PartB/PartC + PlufWO1 root
                         which runs the axiom audit; Main.lean is
                         Aristotle's options file, harmless)
    workorders/WOn/      per-commission trail (input tarball, WORKORDER,
                         REPORT, SUMMARY)
    scripts/             CI audit tooling
    .github/workflows/   CI

## Verification status (update on every merge)

| Result (paper) | Lean name | WO | Status |
|---|---|---|---|
| Paper II Lemma 3.6 (thinness) | `PlufWO1.thin` | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |
| Paper II Prop 3.7 (no disjointly supported blocker) | `PlufWO1.noblock` | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |
| Paper III Lemma 5.2 (normal ⇒ σ-Q, minima form) | `PlufWO1.minima_mem_of_fodor` (+ `sigmaQ_of_fodor`) | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |
| supporting: σ-Q equivalences, transversal escape, W/block infrastructure, C1 | Part A/B/C | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |

Axiom footprint of every merged theorem (149 after WO-7a; 133 verified through
CI run #7), including all formalized counterexamples and obstructions:
`propext`, `Classical.choice`, `Quot.sound`.

| Paper I Prop 2.3 **in every dimension ≥ 2**, no Kochen–Specker input | `PlufWO7a.no_prime_filter_of_finrank_ge_two` (+`exists_pair_sup_top_notMem`) | WO-7a | **verified** (CI #8, 2026-08-17) |
| WO-7 scoping probes (essential spectrum, bases, ω₁-recursion) | `PlufWO7a` (16 audited) | WO-7a | **verified** (CI #8, 2026-08-17) |

| Paper I Prop 2.3, paper-facing, **every dim ≥ 2 and every space with an infinite orthonormal basis** | `PlufWO9` Part A | WO-9 | **verified** (CI #9, 2026-08-17) |
| Essential-spectrum API (`essSpec`, closedness, finite-codim invariance) | `PlufWO9` Part B | WO-9 | **verified** (CI #9, 2026-08-17) |
| Approximate-eigenvector substitute for spectral subspaces | `PlufWO9.approx_eigen_span_spec` (+C1) | WO-9 | **verified** (CI #9, 2026-08-17) |
| General `HilbertBasis` block API (+ corrected Q2, reindexing) | `PlufWO9` Part D | WO-9 | **verified** (CI #9, 2026-08-17) |
| ω₁-recursion combinator (CH as hypothesis) | `PlufWO9` Part E | WO-9 | **verified** (CI #9, 2026-08-17) |

| Paper II Prop 5.5 (one-witness reduction) **as printed, over all bases** | `PlufWO10.one_witness_reduction` (+E0 `diagonalizableB_iff_intimateB`) | WO-10 | **verified** (CI #10, 2026-08-17) |
| Paper II Prop 6.1 (chains never suffice) | `PlufWO10.chains_never_suffice` | WO-10 | **verified** (CI #10, 2026-08-17) |
| Zorn extension for plufs; chain coordinatization; `blockB` lattice API | `PlufWO10` Parts A–C | WO-10 | **verified** (CI #10, 2026-08-17) |

| Cardinal infrastructure: #closed subspaces = #bases = #operators = #self-adjoint = 𝔠 | `PlufWO11` Part A | WO-11 | **verified** (CI #11, 2026-08-17) |
| CH enumerations of subspaces / bases / self-adjoints by countable ordinals | `PlufWO11` Part B | WO-11 | **verified** (CI #11, 2026-08-17) |
| ω₁ stage bookkeeping (countable initial segments, unions) + Baire escape | `PlufWO11` Part C | WO-11 | **verified** (CI #11, 2026-08-17) |

| Paper I §5: `T`, ampleness, Lemma 5.2 (+ radii as printed) | `PlufWO13` Parts A–B | WO-13 | **verified** (CI #12, 2026-08-17) |
| Paper I Lemmas 5.3, 5.4 (upward inheritance; finite codimension) | `PlufWO13` Part C | WO-13 | **verified** (CI #12, 2026-08-17) |
| Paper I Lemma 5.5 (escape), approximate-eigenvector formulation | `PlufWO13.escape` (+D2, D3) | WO-13 | **verified** (CI #12, 2026-08-17) |

| **Paper I Lemma 5.6 — THE BLOCKING LEMMA, unconditional** | `PlufWO14.blocking_lemma` | WO-14 | **verified** (CI #13, 2026-08-17) |
| Selection/perturbation machinery (S0–S2, P1, odd-stage lemma) | `PlufWO14` Parts S, P | WO-14 | **verified** (CI #13, 2026-08-17) |
| The blocking recursion; exact diagonality; conditional assembly | `PlufWO14.exists_blocking_sequence`, `compress_exact_diagonal`, `blocking_lemma_of_sequence` | WO-14 | **verified** (CI #13, 2026-08-17) |

| **Paper II Thm 5.4 (CH: nonprincipal pluf, diagonalizable via no basis)** | `PlufWO12.exists_nonprincipal_nondiagonalizable` | WO-12 | **verified** (CI #13, 2026-08-17) |
| Stage construction (constrained selection, two-coordinate lemma, non-intimate blocker) | `PlufWO12` Part A | WO-12 | **verified** (CI #13, 2026-08-17) |
| CH vector enumeration; cofinal chains; the ω₁ witness family | `PlufWO12` Part B | WO-12 | **verified** (CI #13, 2026-08-17) |

| **Paper I Thm 5.7 (CH: nonprincipal pluf, all members ample; no round slices)** | `PlufWO15.exists_pluf_all_ample`, `not_rsp_of_all_ample`, `radii_of_all_ample` | WO-15 | **verified** (CI #14, 2026-08-17) |
| **Paper I Prop 5.9 (face values of T = [1/16, 1])** | `PlufWO15.face_values_eq_Icc` (+D1, D2) | WO-15 | **verified** (CI #14, 2026-08-17) |
| Stage step (three cases internalized); ω₁ chain | `PlufWO15` Parts A–B | WO-15 | **verified** (CI #14, 2026-08-17) |

| Paper V §2–3 (union closure; elimination) | `PlufWO16` Part A | WO-16 | **verified** (CI #15, 2026-08-18) |
| Paper V §7 (trace formula; covering criterion) | `PlufWO16` Part B | WO-16 | **verified** (CI #15, 2026-08-18) |
| Paper V §8 (intimacy = level three; collapse; χ(Gowers)=3; blocker constraint) | `PlufWO16` Part C | WO-16 | **verified** (CI #15, 2026-08-18) |

| Paper V Thm 4.3 (S1; S2 for finite deletions) | `PlufWO17` Part A | WO-17 | awaiting CI run #16 |
| Paper V Thm 5.2 (finite-rank classification, Aroca quarantined) | `PlufWO17.suppFamily_isScrawlFamily` (+B1, B2) | WO-17 | awaiting CI run #16 |
| Paper V Lemma 6.1, Example 6.2, and the §6 conditional | `PlufWO17` Part C | WO-17 | awaiting CI run #16 |

**WO-17 (Paper V §§4–6) delivered 2026-08-18: no false contracts. PAPER V IS
COMPLETE.** All nine items in the printed shape. **Both WO-16 census
recommendations were correctly overridden.** The matroid vocabulary
(`IsCircuitFamily`, `IndepOf`, `HasSM`, `IsScrawlFamily`) is defined from
scratch — verified at merge that no file imports `Mathlib.Data.Matroid` and no
matroid instance is built. Section 6 succeeded against the rewritten
Example 6.2: Mathlib has no counting form of Rolle, so one was built
(`expSum_card_zeros_lt` by induction on the exponent count), and the contracted
negative form derives from it. B1's coercion `PlufWO16.toFun` did not exist in
the base and was introduced here as the linear map carried by the ℓ² coercion.
B2's rescaling is `weight n = 2⁻ⁿ / (1 + Σ_{v ∈ t} |v n|)` over a finite
generating set. `Submodule.closed_of_finiteDimensional` applies verbatim
(`isClosed_of_finite`). Unused-retained: A2's `hXw`; C3's `hM` — and C3 needs
only the antichain axiom, not the (SM) clause, which is a stronger conclusion
than the paper claims. Residue is the two intended items: quarantined
`AroKaHyp`, and the open Question 9.3.

**WO-16 (Paper V) delivered 2026-08-18: no false contracts.** All 17 items in
the printed shape; counterexample license not invoked. **Scalar finding
confirms the paper:** no item needed a property of ℝ beyond uncountability of
the field, used once in the counting step behind A1/A2 — Paper V's
field-blindness claim for §§7–8 stands as printed. C4a supplied as
`pairSum x k = ((k+2)/(k+1)) * pairSum x (k+1)`, with converse and
vanishing-propagation; 0-indexed, dictionary to the paper's 1-indexing in the
report. C4's three-cover is explicit and concrete: `{0,5} ∪ evens≥6`,
`{1,2} ∪ odds≥6`, `{3,4}` — missing pairs 1, 2, 0 respectively. A2's recursion
reuses `PlufWO14.exists_seq_of_step` unchanged, with the caveat that the stage
predicate must be satisfiable for an arbitrary history, so only the new
vector's coordinates are protected per stage and the paper's freezing invariant
is a separate induction. **Finding: A4's two minimality hypotheses are
unnecessary** (retained verbatim as contracted). **Census verdicts on the
uncontracted sections:** §4 worth contracting only in support language
(Mathlib's infinite `Matroid` has circuits, elimination, duality — but no
circuit-axioms constructor, no scrawls, no cofinitary matroids, no
representability); §5 worth contracting as a transfer, the gap being analytic
and non-vacuous, with support-preserving realization inside ℓ² the item with
content; §6 stays uncontracted — Mathlib has no Blaschke products, no Hardy or
model spaces, no generalized Vandermonde positivity.

**WO-15 (FINAL COMMISSION) delivered 2026-08-17.** Every contracted item proved.
**A2 was FALSE as printed** (mine, eighth of the campaign, same species as the
rest): with an empty index type the union is neither admissible nor contains `⊤`.
Refutation machine-checked as `admissible_iUnion_counterexample`; repair is the
marked minimal `[Nonempty ι]`. B1 follows WO-12's settled pattern with one
reported divergence — the recursion runs at a declared universe variable rather
than pinned at `0`, because the contract statement auto-binds an ordinal
universe. `Admissible`/`⊤` packaging: side hypothesis, not a structure field.
Nonprincipality routed through a finite-codimension room argument at the
hyperplane `(ℝ ∙ v)ᗮ` — NOT a countable-set escape, per the inherited WO-11
warning. **D2 simplification:** the domination is fed to Mathlib's dominated-
extension lemma along the RAY through `T`, so neither a two-dimensional domain
nor an `{I, T}` independence lemma was needed.

**WO-12 delivered 2026-08-17: the deviation route CLOSED.** Theorem 5.4 proved
without the paper's three-case recursion — the family is built and
`PlufWO10.one_witness_reduction` supplies the pluf, nonprincipality and
non-diagonalizability. No repairs, no quarantined hypotheses. B3 packaging: the
family is taken to BE the set of finite intersections, so directedness is
automatic. **RECURSION VERDICT FOR WO-15: `PlufWO9.exists_omega1_chain` DOES NOT
FIT** — its step map cannot see the stage index, and stages need the whole set of
earlier values, not a supremum. Pattern used and recommended: plain well-founded
recursion on `Ordinal` with the stage choice in a `dite`, `WellFounded.fix` +
`WellFounded.fix_eq`, invariant proved afterwards by `Ordinal.induction` over the
history `Prev c a = c '' Set.Iio a`. **No successor/limit split at all.** Two
practical notes: (i) pin the universe (`Ordinal.{0}` annotations) or
`(aleph 1).ord`'s universe stays a metavariable; (ii) keep `Prev` and the stage
predicate top-level so the `dite` rewrite is a one-liner. Unused-retained: `hhc`
in A1, `hNcl` in A3 (the construction forces `R` orthogonal to `h 0 ⊓ N`).

**WO-14 (the summit) delivered 2026-08-17: QUARANTINE FALLBACK NOT NEEDED.**
W1 closed unconditionally, hence W3. `blocking_lemma_of_sequence` was delivered
anyway and used as the actual carrier: it proves W3's conclusion from W1's as a
hypothesis, and `blocking_lemma` is its one-line application — so the quarantined
form remains available to WO-15 at zero cost. 20 new theorems + `tailSpan`.
Recursion implemented via a reusable dependent-choice gadget `exists_seq_of_step`
(stage predicate depends only on earlier values; `hex` unconditional because the
selection lemmas accept an arbitrary finite constraint set — no invariant is
threaded). **S0 verdict: NOT in `PlufWO13/Basic.lean`** (its transfer lemmas move
between given finite-codimension statements; none manufactures finite codimension
from functionals) — proved here via `LinearMap.quotKerEquivRange`.
**essSpec-criterion verdict:** WO-13's `mem_essSpec_compress_of_seq` wants ambient
defect convergence but the recursion yields Rayleigh; bridged by a new
`mem_essSpec_compress_of_rayleigh_seq` using WO-13's `norm_T_sub_lam_sq_le`.
**W2 packaging: ambient starProjection identity — and W3 does NOT consume it**;
the assembly runs on the cheaper Rayleigh criterion, so exact diagonality is
recorded as contracted but not load-bearing. Unused-retained hypotheses: `hN` in
`perturb_unit` (the two-candidate η argument needs no closedness) and `hGN` in
`blocking_lemma` — as predicted in the contract.

**WO-13 delivered 2026-08-17: no false contracts.** All 13 items proved verbatim
to the contracted signatures. `T` realized as `(1/16)·id + (15/16)·P`, `P` the
even-block projection. **C1 rescaling verdict: no rescaling of `1 − T` needed** —
exact defect identities handle both `λ = 1` and `λ = 1/16` symmetrically.
**D1's signature is FINAL and unamended** — WO-14 is to be drafted from it:
clause (ii) holds for ALL `x ∈ K` (no normalization at call sites), clause (iii)
is quotient-form infinite codimension, and the "finitely many linear constraints
while staying off `N`" facility WO-14 needs is exactly C2 + clause (iii). `K` is
internally ample at `λ`; that membership can be exposed cheaply if WO-14 wants
it, but C1/C2 recover it from clause (ii). Beyond contract: **B1′ radii clauses
as printed** (`minorRadius = 1`, `majorRadius = 4`, `eccentricity = 4`) on WO-6's
ellipsoid API via `T_coercive`; and a **non-vacuity check** (`ample_top`,
`not_ample_bot`) confirming D1's hypotheses are satisfiable, so escape is not
vacuously true. Unused-retained: `hVN` in D1 (the `hnot` hypothesis suffices).

**WO-11 delivered 2026-08-17.** Part A routes: A1 lower bound by blocks
separated by constraint vectors; A2 lower by reindexing the standard basis
along `Equiv.Perm ℕ` (no rotations needed); A3/A4 lower by `r • 1`. **B is
pure instantiation** — WO-9's E1 delivers the general statement and its
universe handling is correctly placed; only a cosmetic `Set.Iio (Ordinal.omega
1)` vs `{o // o < (aleph 1).ord}` bridge (`enumShift`) was needed. **C3 REPORTED
FALSE in both proposed forms** (mine): `H` is separable, so a countable set can
have dense span — the standard basis itself refutes the properness form, and
`{eₙ : n ≠ 0}` refutes the infinite-dimensional-complement form. Two
counterexamples formalized; repair supplied under the contracted name as the
**algebraic (Baire) escape form**: the *span* of a countable set is never all
of `H` and stays proper after adjoining a finite set. **WO-15 must NOT be
written against an orthogonality-based C3.** (WO-13, already dispatched, does
not consume C3 and is unaffected.) Two cheap generalizations taken (`#E = 𝔠`
and `#(E →L[ℝ] E) = 𝔠` for any real inner product space with an ℕ-indexed
Hilbert basis), derived from the concrete forms.

**Audit-script fix (commissioner, 2026-08-17):** `strip_comments` now honours
NESTED Lean block comments. The previous non-greedy regex terminated at the
first inner `-/`, so preserved-contract text (which the protocol requires to
be quoted verbatim in comments, and which itself contains `-/`) leaked into
the token scan as apparent code — a spurious `sorry` hit on `PlufWO11.lean`
that would have failed CI. No regressions across the prior files.

**WO-10 (target (a) CLOSED) 2026-08-17:** **E0 taken and answered
affirmatively** — Theorem 5.2 holds at an arbitrary Hilbert basis of an
arbitrary real Hilbert space, so Prop 5.5 is proved **as printed**, quantified
over all ℕ-indexed orthonormal bases, with no silent specialization (only the
easy half of E0 is needed). Two contracts FALSE as printed (mine): B2 and D1
asserted an ℕ-indexed Hilbert basis with nothing forcing infinite dimension —
`E = ℝ` with the constant chain refutes both; counterexamples formalized
(`no_hilbertBasis_nat_real`, `..._false` pair), repair adds
`¬ FiniteDimensional ℝ E`, automatic in `PlufWO1.H`. **Base-API defect found:
WO-9's D4 (`exists_countable_hilbertBasis_of_decomposition`) requires the
ALGEBRAIC join `⨆ n, M n = ⊤`, which no infinite orthogonal decomposition
satisfies — the theorem is true but inapplicable to any infinite
decomposition. WO-10 proves the density variant
(`exists_hilbertBasis_of_orthogonal_family`); export that form in the
harvested API and prefer it in WO-12.** Also exported for WO-12:
`blockB_inf_blockB`, `blockB_mono/univ/empty/ne_bot`,
`intimateB_stdHilbertBasis_iff` (basis-relative intimacy at the standard
basis IS `PlufWO5.Intimate`).

**WO-9 (harvest) delivered 2026-08-17:** all eight `True`-placeholders supplied
and proved; no false contracts. Key signatures for downstream commissions —
**C2 tolerance clause is homogeneous**: `∀ x ∈ K, ‖T x − lam·x‖ ≤ (∑' n, ε n)·‖x‖`,
with infinite-dimensionality as `¬ FiniteDimensional`; chosen over unit-vector
and compression forms because callers in the escape/blocking arguments receive
unnormalized sums (both other forms derive from it in two lines). Tail bounds
come from shifting the sequence, not from an `N` parameter. **D2 is a
definitional equality** with WO-1's standard-basis `block` — no bridging
isometry, so all prior results transfer unchanged. B2 needs neither
self-adjointness nor Calkin/Fredholm input, and returns a strengthened
conclusion (orthonormal, hence weakly null, sequence inside V). **Bonus:
Proposition 2.3 now holds in every real Hilbert space with an infinite
orthonormal basis, separable or not** — the WO-6 triple argument runs at an
arbitrary basis. A2's contracted `hcl` retained but demonstrably unnecessary.

**WO-7a findings (2026-08-17):** **target (d) closed** — a prime filter in
finite dimension is principal at a line `ℝv` (Lemma 2.2), and `P = ℝw ⊕ C`,
`Q = ℝ(v+w) ⊕ C` join to `⊤` while omitting `v`; parity and Kochen–Specker are
both unnecessary, dimension ≥ 2 suffices. **Paper I erratum applied.** Probe Q2
(arbitrary-index basis assembly) is FALSE — counterexample formalized; the
corrected separable/countable form is what Paper II Prop 5.6 actually needs, so
the paper is unaffected. **Earlier census verdict revised: the `HilbertBasis`
API is adequate**, and coordinate blocks generalize to arbitrary bases free
(Q4). Confirmed absent: essential spectrum, Calkin, Fredholm, **Borel
functional calculus** — but a substitute was found and proved (closed spans of
rapidly-decaying orthonormal approximate-eigenvector sequences replace the
spectral subspaces in Paper I's escape and blocking lemmas), the largest cost
saving of the census. ω₁-recursion needs no successor/limit split; friction is
universe lifting. Costs, in commissions: (d) done; (a) Paper II Props 5.5/6.1
≈ 0.5; (c) Paper II Thm 5.4 ≈ 2–2.5; (b) Paper I §5 ≈ 3–4, with a
recommendation to quarantine the blocking lemma as a named hypothesis if the
budget binds, and against formalizing Borel functional calculus.

| Paper I Lemma 2.1 + converse (maximality criterion) | `PlufWO6.maximality_criterion`, `isPluf_of_criterion` | WO-6 | **verified** (CI #6, 2026-08-17) |
| Paper I Lemma 2.2 (finite-dim, principality, finite codim) | `PlufWO6` Part A | WO-6 | **verified** (CI #6, 2026-08-17) |
| Paper I Prop 2.3 (no prime filters) — **in H only** | `PlufWO6.no_prime_filter` (+`not_prime_of_triple`) | WO-6 | **verified** (CI #6, 2026-08-17) |
| Paper I Prop 2.4 (topology: Hausdorff, zero-dim, isolated/dense, non-compact) | `PlufWO6` PartCTop | WO-6 | **verified** (CI #6, 2026-08-17) |
| Paper I Lemma 3.1 (ellipsoid radii) + Prop 3.2 (gap criterion) | `PlufWO6` PartD/PartDEllipsoid | WO-6 | **verified** (CI #6, 2026-08-17) |
| Paper I Prop 3.3/3.4 (state face: nonempty, sandwich, face, convex, weak-* compact, RSP ⟺ singleton) | `PlufWO6` PartE/PartECompact | WO-6 | **verified** (CI #6, 2026-08-17) |
| Paper I Thm 4.1 (KS-parametrized) + partial converse | `PlufWO6.rsp_of_ks`, `ks_of_blockRSP` | WO-6 | **verified** (CI #6, 2026-08-17) |
| **Package discharge** → Paper II Thm 5.1 as printed | `PlufWO6.plufPackage_of_isPluf`, `diagonalizable_iff_intimate_pluf` | WO-6 | **verified** (CI #6, 2026-08-17) |

**WO-6 ratifications (2026-08-17):** six `[Nontrivial E]` repairs (A1, A5,
C2, D2, E1, E4) against the zero-space counterexample — the empty family is
vacuously a pluf there; matches the paper's standing hypothesis on H. C1
repaired with closedness hypotheses (counterexample: non-closed span of the
basis). B1 repaired with `π.Nonempty`. **B1 major finding: Paper I's printed
proof of Prop 2.3 does not close** — primeness does not put the spanning
plane into the filter. Replacement argument (`not_prime_of_triple`): a
triple pairwise-meeting-trivially with pairwise joins dense; realized in H by
even block / odd block / diagonal subspace. Such a triple cannot exist in odd
finite dimension, so the general "rank ≥ 3" claim is NOT established by this
route (Kochen–Specker backstop; separate item if wanted). **Paper I edit made
2026-08-17.** F2 repaired to `ks_of_blockRSP` (block-witnessed RSP ⇒ KSHyp);
contracted shape needs MSS. Beyond contract: ellipsoid form of Lemma 3.1 plus
`rsp_iff_rspEcc`, and weak-* compactness of the face.

| Paper III Thm 4.1 (φ_U singular, countably additive, pure) | `PlufWO8` Parts A–D | WO-8 | **verified** (CI #7, 2026-08-17) |
| Paper III Thm 4.2 (countably additive pure state ⇒ pluf) | `PlufWO8.isPluf_oneSet` (+E1–E4) | WO-8 | **verified** (CI #7, 2026-08-17) |
| Paper I §6 / Paper III: 1-set of φ_U = Φ(U) | `PlufWO8.oneSet_phiLim_eq_PhiU` | WO-8 | **verified** (CI #7, 2026-08-17) |

**WO-8 ratifications (2026-08-17):** no false contracts. Four elaboration
repairs (`Submodule.starProjection` needs `[HasOrthogonalProjection]` as a
*binder*): instance binders in C1–C3; dependent pairs in `oneSet` and
`BWPackage.excision`; named binder in E4 — each propositionally identical,
contracts preserved verbatim in comments. Beyond contract: compact-operator
singularity (`phiLim_compact_eq_zero`) via a finite ε/2-net, needing neither
Hilbert basis nor finite-rank density (both absent from Mathlib); and
`eq_phiLim_of_mem_face` (every face state *equals* φ_U), stronger than the
contracted uniqueness. Unused-retained: `hφ` in E1/E2/E4, `hctble` in C3.
**Scalar finding: no item needed ℂ** — the whole state layer is scalar-agnostic
over ℝ. MSS appears nowhere; Blecher–Weaver confined to `BWPackage`.

**Gate verdicts:** Part C topology packaging PASSED (cheap). Part E states
PASSED — Mathlib has no usable state theory for real B(H), so the contracted
`IsState` rendering is retained and suffices; Hahn–Banach via
`exists_extension_of_le_sublinear`. **WO-8 is commissionable**, with GNS/pure
states budgeted separately (absent from Mathlib, substantial).

| Paper II Thm 2.1 + Cor 2.2 (gliding hump; relativized dichotomy) | `PlufWO5.gliding_hump`, `relativized_dichotomy` | WO-5 | **verified** (CI #5, 2026-08-17) |
| Paper II Lemma 3.2 (membership/addability criteria) | `PlufWO5` Part B | WO-5 | **verified** (CI #5, 2026-08-17) |
| Paper II Thm 3.4 necessity (witness unadded + addable) | `PlufWO5.necessity` (+C1, C2) | WO-5 | **verified** (CI #5, 2026-08-17) |
| Paper II Thm 3.4 sufficiency (Mathias-parametrized) | `PlufWO5.decides_of_mathias` | WO-5 | **verified** (CI #5, 2026-08-17) |
| Paper II Thm 4.1 (Gowers's intimate subspace, all three clauses) | `PlufWO5` Part D | WO-5 | **verified** (CI #5, 2026-08-17) |
| Paper II Thm 5.1 + Cor 5.2(a) (diagonalizable ⟺ intimate; package form) | `PlufWO5.diagonalizable_iff_intimate`, repaired E2 | WO-5 | **verified** (CI #5, 2026-08-17) |

**WO-5 ratifications (2026-08-17):** E2 contract FALSE — `PhiOmega`
members need not be closed while package members are; obstruction
formalized (`exists_phiOmega_not_isClosed`, audited by commissioner
addition), contract preserved in comment, repair (closed quantifier)
ratified. D2 proved by the pair-sum route (all pair sums of a finitely
supported member vanish), superior to the paper's echelon argument —
candidate paper remark. A2 transport: recursion re-run inside the block
(`gliding_hump_rel`), no isometry. `FinCodimIn` kept verbatim (bridge:
`finCodimIn_iff_finite_orthocomplement`). Unused-retained hypotheses
noted in docstrings (A1 `hW`; A2 `hS₀`; B2 `hcof`,`hM`; various in
C1/C2). **Part F gated out** per census: Mathlib `HilbertBasis` lacks
countability of orthonormal sets in separable spaces, basis
assembly/reindexing from orthogonal families, and basis-relative blocks —
this is WO-7a's infrastructure list; Props 5.5–5.6 recommissioned then.

| Paper IV Thm 3.1 (injectivity on a square) | `PlufWO4.inj_on_pairs` (+12 patterns via `exists_avoiding_homog`) | WO-4 | **verified** (CI #4, 2026-08-17) |
| Paper IV Thm 4.1 (exact paving for the product) | `PlufWO4.EPP_fubini` | WO-4 | **verified** (CI #4, 2026-08-17) |
| Paper IV Prop 2.3 (product ≇ Fodor/normal) | `PlufWO4.fubini_not_iso_fodor` (+B4–B6) | WO-4 | **verified** (CI #4, 2026-08-17) |
| Paper IV Cor 3.2 (product is σ-Q) | `PlufWO4.sigmaQ_fubini` | WO-4 | **verified** (CI #4, 2026-08-17) |
| Paper IV Thm 5.2 + Cor 5.3 (EPP transfer; product decides) | `PlufWO4` Part C | WO-4 | **verified** (CI #4, 2026-08-17) |
| Paper IV §6 (gen. thinness, support, Baire spread) | `PlufWO4` Part D | WO-4 | **verified** (CI #4, 2026-08-17) |

**WO-4 ratifications (2026-08-17):** A1 restated with `htail` (tails in D) —
`UncountablePivots` alone leaves upward-varying patterns unreachable; true
for all uniform ultrafilters, contracted already in B1/B8/C2. B5 restated at
`κ : Type` (contract's `FullSelector` is Type-0-indexed; polymorphic
`FullSelectorAll` supplied, B7 verbatim polymorphic). **Pattern finding:**
the two-regime prose of Paper IV §4 under-describes four of the twelve
ordered patterns (P2/P5/P8/P11), where the mid-region between fixed
coordinates is the *only* source of the large family; mechanized fix is
`exists_mid` (pivots applied to a tail). Paper IV §4 amended with one
sentence naming the step. C4–C6 by option (ii) (fresh EPP proofs reusing
WO-2/3 auxiliaries; base untouched). Unused-but-retained: `hsmall` (C4/C6),
`hcof` (D2; proved by sharper contrapositive S = Tᶜ).

| Paper III Cor 2.2 (diagonal flattening; certified w/o self-adjointness) | `PlufWO3.quadratic_flat` (+`exists_ulim`) | WO-3 | **verified** (CI #3, 2026-08-16) |
| Paper III Cor 3.2, filter half (Φ(U): proper, upward, ∩-closed, generically complete, nonprincipal, decides) | `PlufWO3` Part H | WO-3 | **verified** (CI #3, 2026-08-16) |
| Paper III Prop 5.3, Hilbert half (κ-witness) | `PlufWO3.kappa_witness` (+Part I) | WO-3 | **verified** (CI #3, 2026-08-16) |

**WO-3 ratified repair:** contracted I3 (`Wk_inf_block_eq_bot_iff`) was FALSE
without a covering hypothesis; Aristotle formalized the counterexample
(`Wk_inf_block_eq_bot_iff_counterexample`), preserved the contract in a
comment, and repaired with `hcover` (present at all use sites). Ratified
2026-08-16; the paper is unaffected (its partition covers κ). Unused
contract hypotheses flagged and retained: `hcc` in G1 (boundedness suffices),
`hne` in I3/I4. G2 certified without self-adjointness.

**Protocol codification (from the WO-3 precedent):** future work orders
license the following on a false contract statement: formalize a
counterexample where feasible, preserve the contract verbatim in a comment,
and MAY supply a minimally repaired statement clearly marked as such —
subject to commissioner ratification at audit.

| Paper III Thm 2.1 (exact paving) | `PlufWO2.exact_paving` | WO-2 | **verified** (CI #2, 2026-08-16) |
| Paper III Thm 3.1 (exact dichotomy) | `PlufWO2.exact_dichotomy` | WO-2 | **verified** (CI #2, 2026-08-16) |
| Paper III Cor 3.2, lattice half | `PlufWO2.block_filter_decides` | WO-2 | **verified** (CI #2, 2026-08-16) |
| supporting: κ-infrastructure (countable supports, blocks, coordCLM at κ) | `PlufWO2` Part D | WO-2 | **verified** (CI #2, 2026-08-16) |

Everything else in Papers I–III is **hand-checked only**. In particular:
nothing of Paper I; Theorems A, C (both directions; sufficiency consumes
Mathias's theorem, absent from Mathlib — WO-era statements must be
hypothesis-parametrized), D, E, the blocking lemma and Theorem CH; at κ,
Paper III §§4–5 and Paper I §6 residue (WO-8, now commissionable per the
WO-6 Part E gate); Paper I §5 and Paper II Thm 5.4 (WO-7, the transfinite
constructions, gated on essential-spectrum and `HilbertBasis`
infrastructure); Paper II Props 5.5–5.6 (same infrastructure); Prop 2.3 in
odd finite dimension (Kochen–Specker route).

## Known mathematical debts (do not lose)

- **Rigidity Conjecture** (Paper II, Conj. 3.8): every pluf extension of
  Φ(U) contains the witness W. WO-1 verifies the two partial theorems.
- **σ-Q sufficiency** (Paper III, Q 5.5): is σ-Q equivalent to maximality
  of the block filter at κ? Test case D⊗D.
- An earlier draft of Paper II claimed incompatible maximalizations for
  non-selective U; **withdrawn** (quantifier error). Any circulating draft
  or the first-edition lecture notes carrying that remark needs the fix.
