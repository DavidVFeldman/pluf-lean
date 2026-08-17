# REPORT — Work Order WO-13 (pluf project, Feldman–Wilce)

**The ZFC lemmas of Paper I, §5.** The deliverable is the contract file
`RequestProject/PlufWO13.lean` (namespace `PlufWO13`), its operator-free
support file `RequestProject/PlufWO13/Basic.lean` (namespace `PlufWO13.Aux`),
and this report.

**Toolchain.** `leanprover/lean4:v4.28.0`, Mathlib as pinned in the base
artifact. Base: the WO-10 artifact, **unmodified** — `diff -r` against the
supplied `base/RequestProject` reports no changed file, so all 181 prior
theorems remain green and `PlufWO7a.lean` was neither edited nor deleted.
Full-project build: `Build completed successfully`.

**Headline.**

* Every contracted item (A1, A2, A3, B1, C1, C2, D1, D2, D3) is delivered and
  **proved**, with the contract statements verbatim.
* The optional item **B1′ (the radii clauses of Lemma 5.2 as printed) is also
  proved**, on the WO-6 ellipsoid API: `m(E ∩ M) = 1`, `M(E ∩ M) = 4`,
  `r(E ∩ M) = 4` for every ample `M`.
* No `sorry`, `admit`, `axiom` or `native_decide`. Every audited theorem
  reports exactly `[propext, Classical.choice, Quot.sound]`; the
  `#print axioms` block at the foot of `PlufWO13.lean` covers all thirteen
  contract theorems plus B1′ and `ample_top`.
* 53 new theorems (44 in `PlufWO13.lean`, 9 in `PlufWO13/Basic.lean`), five
  new definitions (`tEntry`, `evenBlock`, `T`, `compress`, `Ample`).

---

## 1. Census

Read before anything was written: `REPORT-WO9.md` §1 (the signature table —
this commission is built on `essSpec`, `essSpec_le_of_finCodim`,
`tendsto_norm_proj_finiteDimensional_of_weaklyNull`,
`tendsto_inner_of_orthonormal`, `exists_orthonormal_approx_eigenvectors`,
`approxEigenSpan`, `approx_eigen_span_spec`, `compress`), `REPORT-WO10.md`,
`PlufWO1` Parts B and C (`H`, `block`, `evec`), `PlufWO6` Part D and
`PartDEllipsoid` (`upper`, `lower`, `rayleighSet`, `minorRadius`,
`majorRadius`, `eccentricity` and Lemma 3.1), and `paper1.pdf` §5.

What the census settled, item by item:

| item | Mathlib / base coverage | what had to be built |
|------|-------------------------|----------------------|
| A1 | `lp`, `Submodule.starProjection`; `PlufWO1.evec`, `PlufWO1.block` | the operator itself (see §2) |
| A2 | — | the two defect identities (§3) |
| A3 | `PlufWO9.tendsto_inner_of_orthonormal` | orthonormality of `evec`, the exact eigensequences |
| B1 | `PlufWO9.tendsto_norm_proj_finiteDimensional_of_weaklyNull` | `essSpec` is empty in finite dimensions |
| B1′ | `PlufWO6.minorRadius_eq` etc. | the two Rayleigh-value computations for ample `M` |
| C1 | — | the sequence interface (§4) + the defect identities |
| C2 | `PlufWO9.essSpec_le_of_finCodim` (one inclusion) | the reverse inclusion, and all the finite-codimension bookkeeping |
| D1 | `PlufWO9.exists_orthonormal_approx_eigenvectors`, `approx_eigen_span_spec` | the passage between the compression's defect and the ambient defect |
| D2, D3 | — | Cauchy–Schwarz; a quotient injection |

Mathlib still has no essential spectrum, no Calkin algebra, no Fredholm theory
and no Borel functional calculus, exactly as the WO-7a census recorded. Nothing
in this commission needed any of them.

## 2. Report-rather-than-repair items

* **`PlufWO1.evec` exists** (`RequestProject/PartC.lean`, `evec n = lp.single 2 n 1`),
  so A1's contract statement elaborates verbatim; no substitute basis was
  introduced.
* **`T` is defined as `(1/16) • id + (15/16) • P`**, with `P` the orthogonal
  projection onto `evenBlock = PlufWO1.block {n | Even n}`, rather than as a
  multiplication operator on `lp`. The contracted diagonality is delivered as
  `T_evec : T (evec n) = tEntry n • evec n`, and this presentation is what makes
  the identities of §3 one-liners. Nothing about the statement changes.
* **A2's form.** Delivered in the quadratic-form shape contracted
  (`(1/16)‖x‖² ≤ ⟪T x, x⟫ ≤ ‖x‖²`); no operator-order form was needed anywhere
  downstream.
* **D1's `hVN`.** The contracted hypothesis `¬ Ample (V ⊓ N)` is **not used**:
  `hnot` alone drives the argument, and in fact `hVN` *follows* from `hnot`
  (`not_ample_of_notMem_essSpec`, proved here). It is retained in the delivered
  statement because the contract prescribes it, and flagged in the docstring;
  the `unused variable hVN` warning in the build is therefore expected. This is
  the same convention as WO-9's `hcl`.
* **Nothing in the contract turned out to be false.** No counterexample license
  was exercised.

## 3. The `compress` reconciliation against WO-9

WO-9's compression is

```lean
noncomputable def PlufWO9.compress (T : E →L[ℝ] E) (V : Submodule ℝ E) [CompleteSpace ↥V] :
    ↥V →L[ℝ] ↥V := (V.orthogonalProjection).comp (T.comp V.subtypeL)
```

It is **reused, not re-defined**. The only obstacle is the instance argument:
the contracted `PlufWO13.compress` takes a bare `V : Submodule ℝ H` with no
closedness hypothesis, so no `[CompleteSpace ↥V]` is available at the point of
definition — and it must not be, since `Ample`, C1, C2 and D1 all mention
`compress V` for subspaces whose closedness is a *hypothesis* rather than an
instance. The definition therefore branches:

```lean
open Classical in
noncomputable def compress (V : Submodule ℝ H) : ↥V →L[ℝ] ↥V :=
  if h : CompleteSpace ↥V then (haveI := h; PlufWO9.compress T V) else 0

theorem compress_eq (V : Submodule ℝ H) [inst : CompleteSpace ↥V] :
    compress V = PlufWO9.compress T V
```

Every consumer in §5 supplies closedness, hence completeness, hence
`compress_eq`; the `else 0` branch is never reached in any proof of this file.
The pay-off is that `PlufWO9.essSpec (compress V)` is an instance-free
expression, which is what makes the contracted signatures of `Ample`, C1, C2 and
D1 elaborate at all.

The rest of the WO-9 API is used verbatim:
`essSpec`, `essSpec_le_of_finCodim` (C2, one inclusion),
`tendsto_norm_proj_finiteDimensional_of_weaklyNull` (B1 and C2's other
inclusion), `tendsto_inner_of_orthonormal` (A3, C2, D1),
`exists_orthonormal_approx_eigenvectors` (D1),
`approxEigenSpan` / `isClosed_approxEigenSpan` / `approx_eigen_span_spec` (D1).
No declaration of `PlufWO7a` is used.

## 4. The two defect identities, and the C1 rescaling verdict

With `P` the projection onto the even block, for every `y`:

```lean
theorem norm_T_sub_one_sq (y : H) :
    ‖T y - y‖ ^ 2 = (15/16 : ℝ) * (‖y‖ ^ 2 - inner (𝕜 := ℝ) (T y) y)

theorem norm_T_sub_sixteenth_sq (y : H) :
    ‖T y - (1/16 : ℝ) • y‖ ^ 2
      = (15/16 : ℝ) * (inner (𝕜 := ℝ) (T y) y - (1/16 : ℝ) * ‖y‖ ^ 2)
```

both immediate from `T y - y = -(15/16)(y - P y)`, `T y - (1/16) y = (15/16) P y`
and `⟪T y, y⟫ = (1/16)‖y‖² + (15/16)‖P y‖²`. A2 is the statement that the two
left-hand sides are nonnegative, and the unified corollary

```lean
theorem norm_T_sub_lam_sq_le {lam : ℝ} (hlam : lam = 1 ∨ lam = 1/16) (y : H) :
    ‖T y - lam • y‖ ^ 2 ≤ |inner (𝕜 := ℝ) (T y) y - lam * ‖y‖ ^ 2|
```

is what C1 and D1 actually consume.

**C1 rescaling verdict.** The paper handles `λ = 1/16` by applying the `λ = 1`
argument to a rescaled `1 − T`. That is **not** what is done here, and no
rescaling is needed: the two identities above are exact and symmetric, so both
cases of C1 are discharged by the single estimate `norm_T_sub_lam_sq_le`, with
no case analysis beyond `rcases hlam`. The paper's inequality
`‖T x − x‖² ≤ 2 − 2⟪T x, x⟫` is replaced by the sharper equality
`‖T x − x‖² = (15/16)(‖x‖² − ⟪T x, x⟫)`.

**The sequence interface.** Both directions of the translation between
`lam ∈ essSpec (compress V)` and ambient data are isolated, and are the reusable
core of Parts C and D:

```lean
theorem mem_essSpec_compress_of_seq (V : Submodule ℝ H) [CompleteSpace ↥V] {lam : ℝ}
    (y : ℕ → H) (hmem : ∀ n, y n ∈ V) (hnorm : ∀ n, ‖y n‖ = 1)
    (hweak : ∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0))
    (hdef : Filter.Tendsto (fun n => ‖T (y n) - lam • y n‖) Filter.atTop (nhds 0)) :
    lam ∈ PlufWO9.essSpec (compress V)

theorem exists_seq_of_mem_essSpec_compress (V : Submodule ℝ H) [CompleteSpace ↥V]
    {lam : ℝ} (h : lam ∈ PlufWO9.essSpec (compress V)) :
    ∃ y : ℕ → H, (∀ n, y n ∈ V) ∧ (∀ n, ‖y n‖ = 1) ∧
      (∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0)) ∧
      Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) (y n)) Filter.atTop (nhds lam)
```

(each also in a `starProjection`-level variant, `…_proj`, used by C2).

## 5. C2: what came from WO-9 and what is new

* **σ_ess(T_V) ⊆ σ_ess(T_W)** — WO-9's B2, `essSpec_le_of_finCodim`, applied
  *inside the Hilbert space `↥V`* to the subspace `W.comap V.subtype` and the
  operator `compress V`. New here: the bookkeeping that turns the contracted
  quotient hypothesis `Module.Finite ℝ (↥V ⧸ W.comap V.subtype)` into B2's
  hypothesis `Module.Finite ℝ ↥(W.comap V.subtype)ᗮ`
  (`Aux.finite_orthogonal_comap`, via `Submodule.quotientEquivOfIsCompl`), and
  the transfer of the resulting orthonormal sequence from `↥V` to `↥W`, using
  `P_W ∘ P_V = P_W` (`Aux.starProjection_starProjection_of_le`).
* **σ_ess(T_W) ⊆ σ_ess(T_V)** — new, and it does **not** go through C1: it holds
  for *every* `λ`, not only for `1` and `1/16`. The difference
  `d n = P_V(T y n) − P_W(T y n)` lies in the finite-dimensional space `V ⊓ Wᗮ`
  (`Aux.sub_starProjection_mem_inf_orthogonal`, `Aux.finite_inf_orthogonal`) and
  is weakly null because `T` is self-adjoint and `(y n)` is weakly null; so
  `‖d n‖ → 0` by WO-9's B3. This is the Lean rendering of the paper's
  "`P_V − P_W` has finite rank".

Consequently C2's statement is the contracted equality of full essential
spectra, with no restriction on `λ`.

## 6. D1's final signature — the interface decision

This is the item WO-14 will be drafted from. **Delivered exactly as
contracted**, with no added clause:

```lean
theorem escape {V N : Submodule ℝ H} (hV : Ample V)
    (hN : IsClosed (N : Set H)) (hVN : ¬ Ample (V ⊓ N))
    {lam : ℝ} (hlam : lam = 1 ∨ lam = 1/16)
    (hnot : lam ∉ PlufWO9.essSpec (compress (V ⊓ N)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Submodule ℝ H, K ≤ V ∧ IsClosed (K : Set H) ∧
      ¬ FiniteDimensional ℝ ↥K ∧
      (∀ x ∈ K, ‖T x - lam • x‖ ≤ δ * ‖x‖) ∧
      ¬ Module.Finite ℝ (↥K ⧸ ((K ⊓ N).comap K.subtype))
```

together with the corollary the recursion cites,

```lean
theorem quadratic_estimate_of_bound {K : Submodule ℝ H} {lam δ : ℝ}
    (h : ∀ x ∈ K, ‖T x - lam • x‖ ≤ δ * ‖x‖) (x : H) (hx : x ∈ K) :
    |inner (𝕜 := ℝ) (T x) x - lam * ‖x‖^2| ≤ δ * ‖x‖^2
```

Notes for WO-14:

1. `K` is a `PlufWO9.approxEigenSpan`: the closed span of an orthonormal
   sequence `y : ℕ → H` inside `V` with `‖T (y n) − λ y n‖ < δ/2/2ⁿ`. Clause
   (ii) is the homogeneous WO-9 tolerance clause with total mass exactly `δ`.
2. Clause (ii) is stated for **all** `x ∈ K`, not just unit vectors, so a
   recursion that forms sums and differences of vectors of `K` never has to
   normalize; D2 converts it to the Rayleigh estimate in one line.
3. Clause (iii) is contracted as infinite codimension of `K ⊓ N` in `K`, in the
   quotient form `¬ Module.Finite ℝ (↥K ⧸ (K ⊓ N).comap K.subtype)`. The
   converse direction of the same bookkeeping is available as
   `Aux.finite_quotient_of_finite_quotient` (finite codimension of `N` in `H`
   forces finite codimension of `K ⊓ N` in `K`), which is how D3 is derived.
4. Since `K` is itself ample-like at `λ` — the proof establishes
   `λ ∈ PlufWO9.essSpec (compress K)` internally — a further clause exposing
   that membership can be added cheaply if WO-14 wants it; it was not added
   because it is not in the contract, and because C1/C2 recover it from clause
   (ii) whenever needed. **No other clause was found to be missing while
   proving D3 against this interface.**

The `↥K`-relative machinery WO-14 needs to "impose finitely many linear
constraints while staying off `N`" is exactly C2 + clause (iii): a finite set of
constraints cuts `K` down to a finite-codimension closed subspace, whose
compression has the same essential spectrum (C2), while (iii) guarantees that
`N` cannot be reached this way.

## 7. Additions beyond the contract

* **B1′** — `minorRadius_of_ample`, `majorRadius_of_ample`,
  `eccentricity_of_ample` (Lemma 5.2 as printed), on the WO-6 ellipsoid API,
  via `upper_eq_one_of_ample : PlufWO6.upper T M = 1` and
  `lower_eq_sixteenth_of_ample : PlufWO6.lower T M = 1/16`. `T` is coercive with
  constant `1/16` (`T_coercive`), which is the hypothesis WO-6's Lemma 3.1 takes.
* **`ample_top : Ample (⊤ : Submodule ℝ H)`**, with `not_ample_bot` and
  `notMem_essSpec_compress_bot` — a non-vacuity check: taking `V = ⊤`, `N = ⊥`
  satisfies every hypothesis of D1, so the escape lemma is not vacuously true.
* **`PlufWO13.Aux`** (`PlufWO13/Basic.lean`), the operator-free layer:
  projection identities, `essSpec_eq_empty_of_finiteDimensional`, and the three
  finite-codimension transfer lemmas. All are stated for a general real inner
  product space and are reusable in WO-14/WO-15.

## 8. Axiom audit

`#print axioms` is emitted for all thirteen contract theorems plus the three
radii theorems and `ample_top`; every one reports

```
[propext, Classical.choice, Quot.sound]
```
