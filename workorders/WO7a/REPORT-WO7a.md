# REPORT — Work Order WO-7a (pluf project, Feldman–Wilce)

**A scoping commission.** The deliverable is this report. The accompanying
Lean file `RequestProject/PlufWO7a.lean` contains the probes, in the state in
which they were left.

**Toolchain.** `leanprover/lean4:v4.28.0`, Mathlib as pinned in the base
artifact. Base: the WO-8 artifact, unmodified, 133 theorems, still green.

**Headline.** All eleven probes were resolved. Ten are proved outright; the
eleventh, **Q2, is false as stated** — it is refuted by an explicit
counterexample and replaced by a corrected form that is proved and that is
what Paper II actually needs. Three bonus theorems were added that were not
probed and that **close target (d) outright**, without Kochen–Specker. No
probe was returned undiagnosed, so no probe is excluded from the roll-up on
grounds of failure; the only excluded item is the original Q2 statement,
which is commented out in place with the refutation beside it.

---

## 0. Audit status of the probe file

`RequestProject/PlufWO7a.lean`, 848 lines, namespace `PlufWO7a`, 16 audited
theorems plus one definition. It compiles with no errors. There is no
`sorry`, `admit`, `axiom` or `native_decide` in live code (the single string
`sorry` in the file is inside the block comment that preserves the false Q2
statement). Every one of the sixteen `#print axioms` lines reports exactly

```
[propext, Classical.choice, Quot.sound]
```

| # | name | probe | lines |
|---|------|-------|-------|
| — | `essSpec` | P1 (definition supplied) | 5 |
| 1 | `tendsto_norm_proj_finiteDimensional_of_weaklyNull` | P4 | 23 |
| 2 | `exists_weyl_sequence_in_orthogonal` | helper for P3 | 66 |
| 3 | `essSpec_le_of_finCodim` | **P3** | 13 |
| 4 | `tendsto_inner_of_orthonormal` | helper (Bessel) | 10 |
| 5 | `exists_orthonormal_approx_eigenvectors` | helper (the engine) | 39 |
| 6 | `isClosed_essSpec` | **P2** | 31 |
| 7 | `countable_of_orthonormal` | **Q1** | 24 |
| 8 | `hilbertBasis_nat_of_decomposition_false` | **Q2 refutation** | 22 |
| 9 | `exists_countable_hilbertBasis_of_decomposition` | **Q2 corrected** | 76 |
| 10 | `hilbertBasis_reindex` | **Q3** | 12 |
| 11 | `mem_blockB_iff` | **Q4** | 42 |
| 12 | `exists_enumeration_of_CH` | **R1** | 17 |
| 13 | `exists_omega1_chain` | **R2** | 50 |
| 14 | `exists_pair_sup_top_notMem` | group D (bonus) | 66 |
| 15 | `no_prime_filter_of_finrank_ge_two` | group D (bonus) | 29 |
| 16 | `no_prime_filter_odd_finrank` | **target (d)** | 21 |

Two deliberate `unused variable` warnings remain and are documented in the
respective docstrings: `hT` in `essSpec_le_of_finCodim` (self-adjointness is
not needed) and `hodd` in `no_prime_filter_odd_finrank` (oddness is not
needed). Both hypotheses were retained because the work order asked for them.

---

## 1. Group P — essential spectrum

### 1.1 What Mathlib provides

**Absent.** A search of the pinned Mathlib for `essentialSpectrum`,
`Fredholm` and `Calkin` (case-insensitive, whole tree) returns exactly two
hits, both prose: a TODO in
`Mathlib/Analysis/Normed/Operator/Banach.lean:377` ("once mathlib has
Fredholm operators, generalise the next two lemmas accordingly") and a
sentence in a module docstring in
`Mathlib/Analysis/Normed/Module/ContinuousInverse.lean`. There is **no**
essential spectrum, **no** Calkin algebra, **no** Fredholm index, and no
quotient of `E →L[𝕜] E` by the compact ideal.

**Also absent, and this is the more expensive gap: Borel functional
calculus.** Mathlib has the *continuous* functional calculus (`cfc`) in
depth, but no spectral measure, no `1_{[a,b]}(T)`, and no spectral theorem
for bounded self-adjoint operators in the projection-valued-measure form.
Paper I, Lemma 5.5 (Escape) is stated in exactly that language —
`K^ε_λ(V) = 1_{[λ−ε,λ+ε]}(T_V) V`.

**Present and used.** `spectrum`; `IsCompactOperator` and the compact
operator ideal; the full orthogonal-projection API
(`Submodule.starProjection`, `Submodule.sub_starProjection_mem_orthogonal`,
`Submodule.orthogonal_orthogonal`, `Submodule.isClosed_orthogonal`,
`IsClosed.completeSpace_coe`); `stdOrthonormalBasis` and
`OrthonormalBasis.orthogonalProjection_apply_eq_sum`;
`Orthonormal.inner_products_summable` (Bessel);
`isSeqClosed_iff_isClosed`.

### 1.2 Probe outcomes

**P1 — answered, negatively; Weyl route taken.** With no notion in the
library, the Weyl-sequence definition supplied by the work order was
installed as `essSpec`:

```lean
def essSpec (T : E →L[ℝ] E) : Set ℝ :=
  {lam | ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
    (∀ y : E, Tendsto (fun n => ⟪x n, y⟫_ℝ) atTop (𝓝 0)) ∧
    Tendsto (fun n => ‖T (x n) - lam • x n‖) atTop (𝓝 0)}
```

This is the right definition to build the papers on: it is elementary, it is
equivalent to the usual one for bounded self-adjoint operators, and — the
decisive point — every use of the essential spectrum in Paper I §5 is a use
of *this* form (a weakly null approximate eigensequence), not of the
Calkin-algebra form.

**P4 — proved, 23 lines. Cheap.** The technical core turned out to be the
cheapest thing in the group. Expand the projection in
`stdOrthonormalBasis ℝ ↥W` via
`OrthonormalBasis.orthogonalProjection_apply_eq_sum`, and the whole statement
is a finite sum of scalar limits: `tendsto_finset_sum` closes it. This was
flagged in the work order as possibly "the only genuinely missing piece"; it
is not missing in any meaningful sense.

**P3 — proved, 13 lines on top of a 66-line helper. Cheap.** The
load-bearing probe. `exists_weyl_sequence_in_orthogonal` does the work:
subtract from a Weyl sequence its projection onto the finite-dimensional
`W = Vᗮ`, which tends to `0` by P4, and renormalise. The 66 lines are almost
entirely the renormalisation bookkeeping (norms eventually `≥ 1/2`, triangle
inequalities, `Filter.Tendsto` glue), not mathematics. P3 itself is then
`Submodule.orthogonal_orthogonal` plus the helper.

*Finding to record in the papers.* Paper I, Lemma 5.4 argues by "PV − PW has
finite rank, so TV and TW ⊕ 0 differ by a finite-rank operator" — an argument
that needs the Calkin quotient. **The Weyl route avoids it entirely** and
does not use self-adjointness either. `essSpec_le_of_finCodim` is proved for
an arbitrary bounded operator; the hypothesis `hT : IsSelfAdjoint T` is
retained but unused. Only the inclusion `σ_ess(T) ⊆ σ_ess(T_V)` was probed,
which is the direction Paper I uses; the reverse inclusion is upward
inheritance (Lemma 5.3) and is a separate, easier item.

**P2 — proved, 31 lines, plus a 39-line engine.** Closedness needed more
than expected, and the extra work is *reusable infrastructure*, which is the
main positive finding of the group. Sequential closedness reduces to: from
"for every finite-dimensional `W` and every `d > 0` there is a unit
`v ∈ Wᗮ` with `‖Tv − λv‖ < d`", produce a genuine Weyl sequence.
`exists_orthonormal_approx_eigenvectors` does this by recursion on a list of
previously chosen vectors, each new vector taken orthogonal to the
(finite-dimensional) span of its predecessors; the resulting sequence is
*exactly* orthonormal, hence weakly null by Bessel
(`tendsto_inner_of_orthonormal`).

### 1.3 What would have to be built — and the recommended substitute

The one genuine hole is Escape (Lemma 5.5), which as written needs
`1_{[λ−ε,λ+ε]}(T_V)`. Building Borel functional calculus for bounded
self-adjoint operators in Mathlib is a large undertaking on its own — a
spectral measure, its projection-valued integral, and the multiplicativity
and support lemmas — and would dwarf everything else in this campaign.

**It is not needed.** `exists_orthonormal_approx_eigenvectors` already
produces, at any `λ ∈ σ_ess(T_V)` and any tolerance sequence `ε_n ↓ 0`, an
infinite orthonormal family `(u_n)` in `V` with `‖T u_n − λ u_n‖ < ε_n`. Its
closed span `K` is infinite-dimensional and satisfies `λ ∈ σ_ess(T_K)`; that
is every property of `K^ε_λ(V)` that Lemmas 5.5 and 5.6 consume. The
recommendation is therefore explicit:

> **Replace the spectral subspace `1_{[λ−ε,λ+ε]}(T_V) V` throughout Paper I
> §5 by the closed span of a rapidly-decaying approximate-eigenvector
> sequence.** The statements of Lemmas 5.5 and 5.6 and of Theorem 5.7 are
> unaffected; only the proof of 5.5 changes, and it becomes shorter.

The one clause that needs care under the substitution is Escape's "`K ∩ N`
has infinite codimension in `K`": the paper's proof of it is by contradiction
from Lemmas 5.4 and 5.3, and that argument is insensitive to how `K` was
produced. It goes through verbatim.

Remaining to build for Group P: ampleness as a predicate (trivial on top of
`essSpec`); upward inheritance, Lemma 5.3 (an easy numeric estimate
`‖Tx − x‖² ≤ 2 − 2⟪Tx,x⟫` given `0 ≤ T ≤ 1`, plus the engine — small);
Lemma 5.2 via the WO-6 ellipsoid radii machinery (already present as
`PlufWO6.PartDEllipsoid`); the reverse inclusion in Lemma 5.4.

---

## 2. Group Q — bases as objects

### 2.1 What Mathlib provides

The WO-5 census reported this API absent. **That verdict should be revised:
Mathlib's `HilbertBasis` API is adequate, and the only thing genuinely
missing is the assembly step.** Present and used:

- `HilbertBasis ι 𝕜 E`, `HilbertBasis.repr`, `HilbertBasis.hasSum_repr`,
  `HilbertBasis.repr_apply_apply`, `HilbertBasis.orthonormal`;
- `exists_hilbertBasis` (every Hilbert space has one, indexed by a subset);
- `HilbertBasis.mkOfOrthogonalEqBot` — the assembly primitive: an
  orthonormal family whose span has trivial orthogonal complement *is* a
  Hilbert basis;
- `HilbertBasis.reindex` (answers Q3 in one line);
- `IsHilbertSum` / `OrthogonalFamily` in
  `Mathlib/Analysis/InnerProductSpace/l2Space.lean`;
- `Set.PairwiseDisjoint.countable_of_isOpen` (the separability argument);
- `Submodule.topologicalClosure_minimal`, `Submodule.starProjection`.

### 2.2 Probe outcomes

**Q1 — proved, 24 lines. Cheap.** Distinct members of an orthonormal set are
at distance `√2`, so the open balls of radius `√2/2` around them are pairwise
disjoint; `Set.PairwiseDisjoint.countable_of_isOpen` in a separable space.

**Q2 — FALSE AS STATED.** The probe asked for a `HilbertBasis ℕ ℝ E` from a
countable orthogonal decomposition. An `ℕ`-indexed Hilbert basis forces `E`
to be **both separable and infinite-dimensional**, and neither is implied by
the hypotheses. Counterexample, formalised as
`hilbertBasis_nat_of_decomposition_false`: `E = ℝ`, `M 0 = ⊤`, `M n = ⊥` for
`n ≠ 0`. All three hypotheses hold; `ℝ` admits no `ℕ`-indexed Hilbert basis,
since `b 0` and `b 1` would be orthogonal unit scalars. The original
statement is preserved, commented out, with the diagnosis attached.

**Q2 corrected — proved, 76 lines.** The right statement adds separability
and lets the index type be an arbitrary countable type:

```lean
theorem exists_countable_hilbertBasis_of_decomposition
    [TopologicalSpace.SeparableSpace E]
    (M : ℕ → Submodule ℝ E) (hMc : ∀ n, IsClosed ((M n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ M m, ∀ y ∈ M n, ⟪x, y⟫_ℝ = 0)
    (hspan : ⨆ n, M n = ⊤) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E), ∀ i, ∃ n, b i ∈ M n
```

Proof shape: pick a Hilbert basis of each `M n` (`exists_hilbertBasis`),
countable by Q1; take the sigma type; orthonormality is a two-case split;
totality is the only real work (a vector orthogonal to all of them is
orthogonal to each `M n` — via `HasSum` transported along
`(innerSL ℝ y).comp (M n).subtypeL` — hence to `⨆ n, M n = ⊤`); then
`HilbertBasis.mkOfOrthogonalEqBot`, with a reindexing along
`Countable.exists_injective_nat` to keep the index type in `Type`.

**The gap between the probe and what is provable is exactly: separability
must be hypothesised, and `ℕ` must be relaxed to a countable index type.**
Both are harmless for Paper II, whose `H` is separable throughout, and the
corrected form is precisely what Proposition 6.1 ("Chains never suffice")
consumes.

**Q3 — proved, 12 lines. Trivially cheap**, as expected:
`HilbertBasis.reindex` plus `HilbertBasis.coe_reindex`.

**Q4 — proved, 42 lines.** Basis-relative blocks generalise the WO-1
machinery essentially for free. The coordinate characterisation

```lean
x ∈ (span ℝ (b '' S)).topologicalClosure ↔ ∀ i ∉ S, ⟪x, b i⟫_ℝ = 0
```

holds for an arbitrary `HilbertBasis`, with no separability and no
countability of `ι`. Forward: the span is inside `(span {b i})ᗮ`, which is
closed, so `topologicalClosure_minimal` applies. Backward: show
`x − P_K x = 0` by checking all coordinates and using injectivity of
`b.repr`. **WO-1's `block` machinery does not need to be rebuilt**; it
should be restated once against `HilbertBasis` and the concrete `ℓ²` case
recovered as an instance.

### 2.3 What would have to be built

Little. Beyond the corrected Q2, target (a) needs one item that is genuinely
absent from the base artifact as well as from Mathlib:

- **Zorn extension for plufs**: every proper meet-closed upward-closed family
  of nonzero closed subspaces extends to an `IsPluf`. The base has
  `PlufWO6.IsPluf`, `PlufWO6.maximality_criterion` and
  `PlufWO6.isPluf_of_criterion`, but no extension theorem; a search of the
  artifact for `Zorn` returns nothing. Mathlib's `zorn_subset` supplies the
  skeleton; the work is checking that a union of a chain of such families is
  again one, and converting maximality-under-inclusion into the
  `IsPluf` maximality clause. Estimate: 150–250 lines.
- **Orthogonal complements relative to a subspace** (`M_k ⊖ M_{k+1}`) and the
  fact that `⋂ M_k`, the differences, and `H ⊖ M_1` together span. Mathlib
  has `Submodule.orthogonal` in the ambient space only; the relative version
  and its `iSup = ⊤` are the substance of Proposition 6.1. Estimate:
  250–400 lines.

---

## 3. Group R — transfinite recursion and CH

### 3.1 What Mathlib provides

- **CH has no predicate.** There is no `ContinuumHypothesis` in Mathlib. The
  idiomatic spelling is the equation `Cardinal.continuum = Cardinal.aleph 1`,
  and that is what the probe uses. On the ordinal side, `ω₁` is
  `Ordinal.omega 1`, with `Ordinal.card_omega : (Ordinal.omega n).card = ℵ_n`
  and `Ordinal.isInitial_omega`.
- Cardinal arithmetic: `Cardinal.lift_continuum`, `Cardinal.lift_aleph`,
  `Cardinal.lift_lift`, `Cardinal.mk_uLift`, `Cardinal.eq`,
  `Ordinal.mk_Iio_ordinal`, `Cardinal.countable_iff_lt_aleph_one`,
  `Cardinal.lift_lt_aleph_one`.
- Recursion: `WellFoundedLT Ordinal`, `WellFounded.fix`, `WellFounded.fix_eq`.
  There is no bespoke ordinal-recursion combinator with successor/limit
  cases, and — see below — none is wanted.

### 3.2 Probe outcomes

**R1 — proved, 17 lines. The friction is universe-theoretic, not
set-theoretic.** The statement `𝔠 = ℵ₁` is at one universe while
`Set.Iio ω₁` lives one universe up, so the whole proof is
`Cardinal.lift_inj` plus three lifting lemmas to line the two sides up,
followed by `Cardinal.eq`. Anyone writing the CH recursions of Paper I §5 and
Paper II §5 should expect to pay this tax once and factor it into a lemma;
it recurs at every enumeration.

**R2 — proved, 50 lines, and cheaper than the papers suggest.** The
significant finding:

> **No successor/limit case split is needed.** At every stage `a < ω₁` the
> initial segment `Set.Iio a` is *countable*
> (`Cardinal.countable_iff_lt_aleph_one` with `Ordinal.mk_Iio_ordinal` and
> `Ordinal.isInitial_omega`), so a single surjection `ℕ → Set.Iio a` feeds
> *all* previous values to the limit step, uniformly, and one application of
> the successor step on top makes the new value strictly larger than every
> earlier one.

Concretely, the recursion is `WellFounded.fix` over `Ordinal` with a single
clause, unfolded by `WellFounded.fix_eq`; monotonicity is one `calc`. This is
worth recording: the papers describe their recursions as "successor and limit
stages", and the formal version wants them merged. The bookkeeping that
*does* cost is the choice of the enumerating surjection as a function of the
stage (`Classical.choice` under a `dif_pos`, then a spec lemma), which is the
bulk of the 50 lines.

### 3.3 What would have to be built

The recursion pattern itself is now in hand and should be extracted as a
reusable combinator. The costs that R1/R2 do **not** measure, and that the
real constructions will pay, are two cardinality computations that Mathlib
does not have:

- `#{closed subspaces of H} = 𝔠` (needed to enumerate `P(H)` as
  `{p_i : i < ω₁}` under CH);
- `#{orthonormal bases of H} = 𝔠` (needed for `{B_i : i < ω₁}` in Paper II,
  Theorem 5.4).

Both are routine mathematics and both are real Lean work — upper bounds via
an injection into `𝔠^{ℵ₀}`-style counting of countable dense subsets, lower
bounds by exhibiting a continuum-sized family. Estimate: 300–500 lines
together. **This is the largest single hidden cost uncovered by Group R**,
and it is shared between targets (b) and (c).

---

## 4. Group D (unprobed, added) — target (d) is closed

Target (d) was priced as "a Kochen–Specker-style finite-dimensional
argument". Mathlib has no Kochen–Specker theorem and no Gleason theorem, so
that route would have been expensive.

**It is not needed.** WO-6 proved Proposition 2.3 for the paper's separable
infinite-dimensional `H` using a triple `A, B, C` of closed subspaces
pairwise meeting trivially and pairwise spanning, and recorded that no such
triple exists in odd finite dimension. The correct finite-dimensional
argument is different and elementary:

1. In finite dimension a nonempty meet-closed upward-closed proper family has
   a member `M₀` of least dimension, and `M₀` is contained in every member
   (else `M₀ ⊓ N` would be smaller).
2. `M₀ ≠ ⊥`, so pick `v ∈ M₀`, `v ≠ 0`. If `dim V ≥ 2`, there are two
   subspaces `P, Q` with `P ⊔ Q = ⊤` and `v ∉ P`, `v ∉ Q`
   (`exists_pair_sup_top_notMem`: take a hyperplane missing `v`, and a
   complementary-enough second subspace).
3. Primeness applied to `P ⊔ Q = ⊤ ∈ π` puts `P` or `Q` in `π`; either
   contains `M₀ ∋ v`. Contradiction.

Formalised as `no_prime_filter_of_finrank_ge_two` (29 lines) on top of
`exists_pair_sup_top_notMem` (66 lines), with the work order's exact shape
`no_prime_filter_odd_finrank` (21 lines) derived from it.

**Findings for the papers.** Dimension `≥ 2` suffices; **parity plays no
role** and the odd hypothesis should be dropped from Proposition 2.3. The
`hodd` hypothesis is retained in the Lean statement only because the work
order asked for it, and is flagged unused.

---

## 5. Cost estimates for targets (a)–(d)

**Unit.** One "commission" = one of WO-2 … WO-8, calibrated against the base
artifact: WO-2 ≈ 350 lines / 14 theorems; WO-3 ≈ 650 / 22; WO-4 ≈ 1370 / 56;
WO-5 ≈ 1720 / 62; WO-6 ≈ 3450 / 160 (a double-weight commission by any
measure); WO-8 ≈ 1520 / 76. Taking the median, **1 commission ≈ 1200–1800
lines of finished Lean, 25–60 theorems**, delivered green.

| target | estimate | confidence |
|---|---|---|
| **(d)** Paper I, Prop 2.3 in odd finite dimension | **0.05 commission** — *already done in this file* | certain |
| **(a)** Paper II, Props 5.5 & 6.1 | **0.5 commission** | high |
| **(c)** Paper II, Thm 5.4 | **2 – 2.5 commissions** | medium |
| **(b)** Paper I, §5 entire | **3 – 4 commissions** | medium-low |

### (d) — 0.05, and it is finished

The three theorems in group D are audited and sorry-free. All that remains is
to re-site them into a contracted file with the paper's own statement of
Proposition 2.3 and, if desired, to state the sharpened form (dimension `≥ 2`,
no parity). **Recommendation: close target (d) now and record the sharpening
as an erratum to Paper I.**

### (a) — 0.5

Three of the four ingredients exist. Theorem 5.2 (diagonalisable ⟺ every
member intimate) is `PlufWO5.diagonalizable_iff_intimate`, repaired in WO-6;
nonprincipality from `⋂ R = 0` is `PlufWO6.principal_iff_sInf_ne_bot`;
`Intimate` is defined. Proposition 5.5 is then a five-line composition once
the **Zorn extension theorem** is available (§2.3, 150–250 lines).
Proposition 6.1 needs the corrected Q2 (proved here) plus relative orthogonal
complements of a nested chain (§2.3, 250–400 lines) plus intimacy of blocks,
for which Q4 supplies the coordinate characterisation. Total new material:
~600–900 lines. **Group Q is no longer a blocker.**

### (c) — 2 to 2.5

The mathematics of Theorem 5.4 is a three-case ω₁-recursion whose stage
construction is a gliding-hump argument with thresholds `N₁ < N₂ < …` and
exact (not approximate) orthogonality — which, as the paper notes, removes
all analytic estimates. Against that:

- R1/R2 show the recursion skeleton is cheap (~150 lines with the universe
  tax factored out);
- the *invariant* is where the cost sits: "every member is
  infinite-dimensional, inherited by finite-codimension intersections" must
  be threaded through all three cases, and each stage's `R_i` needs the
  finite-codimension carving `C_n ⊆ h_n`, the `C_n \ N ≠ ∅` argument, and
  the "two nonzero coordinates" lemma (a subspace all of whose vectors are
  multiples of single basis vectors has dimension ≤ 1);
- the two **cardinality computations of §3.3** are prerequisites (300–500
  lines), and are not optional here: the enumeration of *all* orthonormal
  bases is the point of the theorem;
- the maximality-at-the-end step reuses `PlufWO6.maximality_criterion` and
  the Zorn extension built for (a).

Estimate ~3000–4000 lines. The paper's own verification status note ("a
transfinite recursion whose stage construction we have checked closely by
hand") is a fair description of the risk: nothing is deep, everything is
long.

### (b) — 3 to 4

The largest target, and the one where the estimate is least firm.

- Group P infrastructure: essential spectrum, closedness, finite-codimension
  invariance, the orthonormal-approximate-eigenvector engine — **already
  built here**, ~180 lines, reusable as is.
- Ampleness, Lemma 5.2 (radii, via the existing WO-6 ellipsoid machinery),
  Lemma 5.3 (upward inheritance), Lemma 5.4 (reverse inclusion): ~500 lines.
- Lemma 5.5 (Escape), **via the substitute of §1.3** rather than Borel
  functional calculus: ~400 lines. *Via* Borel functional calculus it would
  be 2–3 commissions on its own; this substitution is the single largest
  saving identified by this commission.
- Lemma 5.6 (the blocking lemma): **the heaviest single item in the whole
  campaign.** A recursion over `n` constructing unit vectors `w_n ∈ h_n`
  under five simultaneous constraints (a)–(e), including two-sided
  approximation `|⟪T w_n, w_n⟫ − μ_n| < ε_n` with `μ_n` alternating between
  the two spectral values, orthogonality to all `w_j` *and* `T w_j` for
  `j < n`, and the perturbation `w_n = (w'_n + η z_n)/‖w'_n + η z_n‖`. Every
  clause is a finite-codimension condition and the analysis is genuine, not
  bookkeeping. Alone: 1–1.5 commissions, ~1500 lines.
- Theorem 5.7 (three-case ω₁ recursion under CH): shares the cardinality
  computations and the recursion combinator with (c); if (c) is done first,
  ~600 lines, otherwise ~1000.
- Proposition 5.9 (the interval `[1/16, 1]` of essential extremes): depends
  on the WO-6 state-space material and on MSS, which is quarantined as a
  named hypothesis by design; ~400 lines given that quarantine.

Estimate ~4000–5500 lines.

**An honest negative, offered narrowly.** Nothing in (b) should stay
hand-checked *as a consequence of missing infrastructure* — the substitute of
§1.3 removes the one impassable dependency. But if the campaign's budget will
not stretch to 3–4 further commissions, the item to leave hand-checked is
**Lemma 5.6 alone**, quarantined as a named hypothesis in the manner already
used for Mathias, MSS, Blecher–Weaver and Rowbottom. Theorem 5.7 and
Proposition 5.9 would then be fully formal *modulo* a stated blocking lemma,
which is a defensible scope statement: the blocking lemma is a
construction, not a structural theorem, and its hypotheses and conclusion are
short enough to state precisely. Formalising Borel functional calculus in
order to follow Paper I's *literal* proof of Lemma 5.5 would, by contrast, be
disproportionate, and we recommend against it explicitly.

---

## 6. Recommended decomposition and order

**WO-9 — Target (d), plus the Q/R harvest.** (~0.5 commission.) Re-site the
group D theorems as contracted items; extract from this probe file the
reusable pieces: `essSpec` and its four supporting theorems, the corrected
Q2, Q4 restated as the general `HilbertBasis` block API superseding WO-1's
`block`, and the ω₁-recursion combinator of R2 with the universe tax
factored into a lemma. Cheap, and everything downstream depends on it.

**WO-10 — Target (a).** (~0.5 commission.) Zorn extension for plufs;
relative orthogonal complements of a nested chain; Propositions 5.5 and 6.1.
Self-contained, low risk, and closes a whole target.

**WO-11 — Cardinal infrastructure.** (~0.5 commission.) `#{closed
subspaces} = 𝔠` and `#{orthonormal bases} = 𝔠`, plus the CH enumeration
lemmas at fixed universe. Shared prerequisite of (b) and (c); isolating it
keeps it from being paid twice and de-risks both.

**WO-12 — Target (c), Paper II Theorem 5.4.** (~2 commissions, possibly
split in two: the stage construction of `R_i`, then the three-case
recursion.) Do this before (b): it is the same recursion skeleton with
strictly less analysis, so it debugs the pattern on the cheaper target.

**WO-13 — Paper I §5, part one: ampleness through Escape.** (~1
commission.) Lemmas 5.2–5.5, using the approximate-eigenvector substitute.

**WO-14 — Paper I §5, part two: the blocking lemma.** (~1.5 commissions.)
The one item to consider quarantining if the budget binds.

**WO-15 — Paper I §5, part three: Theorem 5.7 and Proposition 5.9.**
(~1 commission.) Trivial to re-plan if WO-14 is quarantined instead of
proved.

**Suggested order: WO-9, WO-10, WO-11, WO-12, WO-13, WO-14, WO-15** — i.e.
(d), then (a), then the shared cardinal layer, then (c), then (b) in three
parts. The rationale is that the two cheap targets close first and produce
infrastructure the expensive ones consume; the shared cardinal layer is paid
once; and the recursion pattern is exercised on (c) before (b) depends on it.

---

## 7. Numbering drift (for the papers' editors)

The work order's references and the printed numbering have drifted apart.
Recorded here so the future work orders can be written against the papers as
printed:

| work order says | Paper I as printed |
|---|---|
| Theorem 5.6 under CH | **Theorem 5.7** (ample nonprincipal pluf under CH) |
| the interval proposition | **Proposition 5.9** (`{φ(T)} = [1/16, 1]`) |
| — | Lemma 5.6 is the **blocking lemma** |

| work order says | Paper II as printed |
|---|---|
| Proposition 5.6 (countable chains coordinatizable) | **Proposition 6.1** ("Chains never suffice") |
| Proposition 5.5 (one-witness reduction) | Proposition 5.5 — unchanged |
| Theorem 5.4 | Theorem 5.4 — unchanged |

Note also that Paper II's Corollary 5.3(c) cites "[5], Theorem 5.6", which is
Paper I's Theorem 5.7 under the printed numbering.

---

## 8. Summary of findings

1. Mathlib has no essential spectrum, no Fredholm theory, no Calkin algebra
   and **no Borel functional calculus**. The Weyl-sequence definition is a
   complete substitute for Paper I §5, and the approximate-eigenvector span
   is a complete substitute for the spectral subspace of Lemma 5.5.
2. P3, the load-bearing probe, is **cheap** (13 + 66 lines) and does not need
   self-adjointness. P4 is cheaper still.
3. **Q2 is false as stated**; the corrected form (separable `E`, countable
   index type) is proved and is what Paper II needs.
4. Mathlib's `HilbertBasis` API is adequate; the WO-5 census verdict of
   "absent" should be revised. WO-1's block machinery generalises for free.
5. CH has no Mathlib predicate; the friction in R1/R2 is universe lifting,
   not set theory, and **ω₁-recursion needs no successor/limit case split**.
6. The unmeasured cost in R is the two **cardinality computations**
   (`#{closed subspaces} = #{orthonormal bases} = 𝔠`), shared by (b) and (c).
7. **Target (d) is closed by this commission**, without Kochen–Specker, and
   the odd-dimension hypothesis of Paper I, Proposition 2.3 is unnecessary:
   dimension `≥ 2` suffices.
