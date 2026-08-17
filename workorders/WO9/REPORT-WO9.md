# REPORT — Work Order WO-9 (pluf project, Feldman–Wilce)

**The harvest commission.** The deliverable is the contracted API in
`RequestProject/PlufWO9.lean` (namespace `PlufWO9`) together with this report,
whose first section is the signature table the work order asks for: WO-10
onward can be written against §1 without reading the source.

**Toolchain.** `leanprover/lean4:v4.28.0`, Mathlib as pinned in the base
artifact. Base: the WO-7a artifact, unmodified. `PlufWO7a.lean` was neither
edited nor deleted; all prior theorems remain green (full-project build:
`Build completed successfully`).

**Headline.**

* Every contracted item is delivered and **proved**, including all eight
  `True`-valued placeholders, whose statements are supplied here and reported
  verbatim in §1.
* `PlufWO9.lean` is **independent of the probe file**: although it imports
  `RequestProject.PlufWO7a` (as the contract prescribes, so that the census
  record stays in the build), it uses **no declaration of `PlufWO7a`** — every
  item is re-proved in place under its stable name. Dependence on the earlier
  work orders is retained only where the mathematics is theirs
  (`PlufWO6.no_prime_filter`, `PlufWO6.not_prime_of_triple`, `PlufWO1.H`,
  `PlufWO1.block`).
* The optional item was **cheap and is proved**: the WO-6 triple argument runs
  at an arbitrary infinite orthonormal basis, so Proposition 2.3 holds in every
  real Hilbert space with an infinite orthonormal basis, separable or not
  (`no_prime_filter_of_infinite_hilbertBasis`).
* No `sorry`, `admit`, `axiom` or `native_decide`. Every audited item reports
  exactly `[propext, Classical.choice, Quot.sound]`. CH appears only as a
  hypothesis.

---

## 1. Signature table (the deliverable)

All statements below are as elaborated, in namespace `PlufWO9`, with the
ambient section variables

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
```

(`[CompleteSpace E]` is `omit`ted where unused; this is noted per item).

### Part A — Proposition 2.3

**A1** (finite-dimensional regime; oddness dropped):

```lean
theorem no_prime_filter_finrank (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (h2 : 2 ≤ Module.finrank ℝ V)
    (π : Set (Submodule ℝ V)) (hne : π.Nonempty)
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ V, M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ V) ∉ π) :
    ¬ (∀ M N : Submodule ℝ V, M ⊔ N ∈ π → M ∈ π ∨ N ∈ π)
```

Supporting general form (no inner product, no topology, arbitrary real vector
space — this is what the argument actually needs, and what consumers should
quote):

```lean
theorem no_prime_filter_of_finrank_ge_two {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V]
    (h2 : 2 ≤ Module.finrank ℝ V) (π : Set (Submodule ℝ V))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ V, M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ V) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ V, M ⊔ N ∈ π → M ∈ π ∨ N ∈ π)
```

**A2** (infinite-dimensional regime), verbatim as contracted:

```lean
theorem no_prime_filter_paper (π : Set (Submodule ℝ PlufWO1.H))
    (hcl : ∀ M ∈ π, IsClosed (M : Set PlufWO1.H)) (hne : π.Nonempty)
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ PlufWO1.H,
      IsClosed (N : Set PlufWO1.H) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ PlufWO1.H) ∉ π) :
    ¬ (∀ M N : Submodule ℝ PlufWO1.H, IsClosed (M : Set PlufWO1.H) →
        IsClosed (N : Set PlufWO1.H) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π)
```

**A2 generalized** (the optional item):

```lean
theorem no_prime_filter_of_infinite_hilbertBasis {ι : Type*} [Infinite ι]
    (b : HilbertBasis ι ℝ E) (π : Set (Submodule ℝ E))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ E) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ E, IsClosed (M : Set E) → IsClosed (N : Set E) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π)
```

with the basis-level form it specializes,

```lean
theorem no_prime_filter_of_hilbertBasis_prod_bool {ι : Type*}
    (c : HilbertBasis (ι × Bool) ℝ E) (π : Set (Submodule ℝ E)) …
```

### Part B — the essential spectrum layer

**B0** (definition; `essSpec` is the stable name, redefined here rather than
re-exported):

```lean
def essSpec (T : E →L[ℝ] E) : Set ℝ :=
  {lam | ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
    (∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0)) ∧
    Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖) Filter.atTop (nhds 0)}

theorem mem_essSpec_iff (T : E →L[ℝ] E) (lam : ℝ) : …   -- `Iff.rfl` unfolding
```

**B1** (`omit [CompleteSpace E]`):

```lean
theorem isClosed_essSpec (T : E →L[ℝ] E) : IsClosed (essSpec T)
```

**B2** — the load-bearing item, statement supplied:

```lean
theorem essSpec_le_of_finCodim (T : E →L[ℝ] E) (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) (hfc : Module.Finite ℝ ↥Vᗮ)
    (lam : ℝ) (hlam : lam ∈ essSpec T) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ (∀ n, u n ∈ V) ∧
      Filter.Tendsto (fun n => ‖T (u n) - lam • u n‖) Filter.atTop (nhds 0)
```

and, for callers who prefer the operator form, the compression statement:

```lean
noncomputable def compress (T : E →L[ℝ] E) (V : Submodule ℝ E) [CompleteSpace ↥V] :
    ↥V →L[ℝ] ↥V :=
  (V.orthogonalProjection).comp (T.comp V.subtypeL)

theorem essSpec_subset_essSpec_compress (T : E →L[ℝ] E) (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) (hfc : Module.Finite ℝ ↥Vᗮ) :
    haveI : CompleteSpace ↥V := hV.completeSpace_coe
    essSpec T ⊆ essSpec (compress T V)
```

**Minimal hypotheses actually required for B2** (the work order asks for these
to be reported explicitly):

* `V` closed — needed only to know `Vᗮᗮ = V`, i.e. to place the corrected Weyl
  sequence back inside `V`;
* `Vᗮ` finite-dimensional (`Module.Finite ℝ ↥Vᗮ`) — this is "finite
  codimension" in the form the proof uses;
* completeness of the ambient `E`.

Not needed, and therefore **not** in the statement: self-adjointness of `T`
(the paper's argument uses it), compactness or finite rank of anything, the
Calkin algebra, Fredholm theory, and any spectral theorem. The conclusion is
also *stronger* than the contract's: the witnessing sequence is orthonormal,
hence automatically weakly null, which is what the consumers of ampleness in
WO-13/WO-14 want.

**B3** (`omit [CompleteSpace E]`):

```lean
theorem tendsto_norm_proj_finiteDimensional_of_weaklyNull
    (W : Submodule ℝ E) (hfin : Module.Finite ℝ ↥W) (x : ℕ → E)
    (hw : ∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ‖W.starProjection (x n)‖) Filter.atTop (nhds 0)
```

Auxiliary API of Part B, also stable and quotable:

```lean
theorem exists_weyl_sequence_in_orthogonal (T : E →L[ℝ] E) (W : Submodule ℝ E)
    (hfin : Module.Finite ℝ ↥W) (lam : ℝ) (x : ℕ → E) (hx1 : ∀ n, ‖x n‖ = 1) …
theorem tendsto_inner_of_orthonormal {u : ℕ → E} (hu : Orthonormal ℝ u) (y : E) : …
theorem exists_unit_approx_eigenvector_mem (T : E →L[ℝ] E) (lam : ℝ)
    (V : Submodule ℝ E) (hV : IsClosed (V : Set E)) (hfc : Module.Finite ℝ ↥Vᗮ)
    (hlam : lam ∈ essSpec T) (W : Submodule ℝ E) (hW : Module.Finite ℝ ↥W)
    (d : ℝ) (hd : 0 < d) :
    ∃ v : E, v ∈ V ∧ v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d
```

### Part C — the substitute for spectral subspaces

**C1** (engine; decay rate a parameter):

```lean
theorem exists_orthonormal_approx_eigenvectors (T : E →L[ℝ] E) (lam : ℝ)
    (hlam : lam ∈ essSpec T) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ ∀ n, ‖T (u n) - lam • u n‖ < ε n
```

and the version consumers will more often want, which also confines the
vectors to a closed subspace of finite codimension (C1 is the `V = ⊤` case,
B2 the `ε n = 1/(n+1)` case):

```lean
theorem exists_orthonormal_approx_eigenvectors_mem (T : E →L[ℝ] E) (lam : ℝ)
    (hlam : lam ∈ essSpec T) (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    (hfc : Module.Finite ℝ ↥Vᗮ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ (∀ n, u n ∈ V) ∧ ∀ n, ‖T (u n) - lam • u n‖ < ε n
```

together with the hypothesis-form engine, for callers who have their own
supply of approximate eigenvectors:

```lean
theorem exists_orthonormal_approx_eigenvectors_of_forall (T : E →L[ℝ] E) (lam : ℝ)
    (V : Submodule ℝ E) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (H : ∀ W : Submodule ℝ E, Module.Finite ℝ ↥W → ∀ d : ℝ, 0 < d →
      ∃ v : E, v ∈ V ∧ v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ (∀ n, u n ∈ V) ∧ ∀ n, ‖T (u n) - lam • u n‖ < eps n
```

**C2** — statement supplied; the substitute subspace and its two properties:

```lean
def approxEigenSpan (u : ℕ → E) : Submodule ℝ E :=
  (Submodule.span ℝ (Set.range u)).topologicalClosure

theorem isClosed_approxEigenSpan (u : ℕ → E) : IsClosed (approxEigenSpan u : Set E)
theorem mem_approxEigenSpan (u : ℕ → E) (n : ℕ) : u n ∈ approxEigenSpan u

theorem approx_eigen_span_spec (T : E →L[ℝ] E) (lam : ℝ) (u : ℕ → E)
    (hu : Orthonormal ℝ u) (ε : ℕ → ℝ)
    (hdef : ∀ n, ‖T (u n) - lam • u n‖ < ε n) (hsum : Summable ε) :
    (∀ n, u n ∈ approxEigenSpan u) ∧ ¬ FiniteDimensional ℝ ↥(approxEigenSpan u) ∧
      ∀ x ∈ approxEigenSpan u, ‖T x - lam • x‖ ≤ (∑' n, ε n) * ‖x‖
```

(`omit [CompleteSpace E]`: C2 needs no completeness.)

**The tolerance clause, and why this shape** (the interface decision the work
order flags as the most important one). Three shapes were considered:

1. *unit vectors only*: `∀ x ∈ K, ‖x‖ = 1 → ‖T x - lam • x‖ ≤ δ`;
2. *compression form*: `‖compress T K - lam • id‖ ≤ δ`;
3. *homogeneous form* (chosen): `∀ x ∈ K, ‖T x - lam • x‖ ≤ (∑' n, ε n) * ‖x‖`.

Shape 3 was chosen because (i) it is homogeneous, so a caller never has to
normalize a vector before applying it — in the escape and blocking arguments
the vectors arrive as sums or differences of members of several blocks, and
normalizing costs a division and a positivity side condition every time;
(ii) it needs no `CompleteSpace ↥K` instance and no compression operator, so
it applies verbatim to the closed span of *any* orthonormal sequence, however
obtained; (iii) shapes 1 and 2 both follow from it in two lines, whereas the
converse of (1) ⇒ (3) needs the normalization argument. The tolerance is the
*total* mass `∑' n, ε n` rather than a tail `∑' n ≥ N, ε n`: a caller wanting
tolerance `δ` chooses `ε n = δ / 2 ^ (n+1)`, and a caller wanting a *tail*
bound applies the theorem to the shifted sequence `fun n => u (n + N)`, which
is again orthonormal. Rejected alternative worth recording: making the
tolerance the tail `∑' n ≥ N, ε n` *inside* the statement, with `N` a
parameter — it makes every caller carry an `N` it usually does not need.

Infinite-dimensionality is delivered as `¬ FiniteDimensional ℝ ↥K` (rather
than, say, a statement about `Module.rank`), which is the form the ampleness
lemmas consume.

### Part D — the general HilbertBasis block API

Section variables: `{ι : Type*} (b : HilbertBasis ι ℝ E)`.

```lean
def blockB (S : Set ι) : Submodule ℝ E :=
  (Submodule.span ℝ (b '' S)).topologicalClosure

theorem mem_blockB_iff (S : Set ι) (x : E) :
    x ∈ blockB b S ↔ ∀ i ∉ S, b.repr x i = 0

theorem mem_blockB_iff_inner (S : Set ι) (x : E) :
    x ∈ blockB b S ↔ ∀ i ∉ S, inner (𝕜 := ℝ) x (b i) = 0

theorem isClosed_blockB (S : Set ι) : IsClosed (blockB b S : Set E)
```

**D2** — statement supplied. **No bridging isometry is needed**: for the
standard basis of `PlufWO1.H` the two subspaces are *equal*, so all existing
results about `PlufWO1.block` transfer without restatement.

```lean
noncomputable def stdHilbertBasis : HilbertBasis ℕ ℝ PlufWO1.H :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ PlufWO1.H)

theorem blockB_stdBasis_eq (S : Set ℕ) : blockB stdHilbertBasis S = PlufWO1.block S
```

**D3** — statement supplied (the probe was restricted to `Type`; the contracted
form is universe-polymorphic):

```lean
theorem hilbertBasis_reindex {ι ι' : Type*} (b : HilbertBasis ι ℝ E) (e : ι ≃ ι') :
    ∃ b' : HilbertBasis ι' ℝ E, ∀ i, b' (e i) = b i
```

**D4** — statement supplied; **must not be generalized** (the arbitrary-index
form is false, see `PlufWO7a.hilbertBasis_nat_of_decomposition_false`):

```lean
theorem exists_countable_hilbertBasis_of_decomposition
    [TopologicalSpace.SeparableSpace E]
    (M : ℕ → Submodule ℝ E) (hMc : ∀ n, IsClosed ((M n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ M m, ∀ y ∈ M n, inner (𝕜 := ℝ) x y = 0)
    (hspan : ⨆ n, M n = ⊤) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E), ∀ i, ∃ n, b i ∈ M n
```

with its supporting countability lemma

```lean
theorem countable_of_orthonormal [TopologicalSpace.SeparableSpace E]
    (s : Set E) (hs : Orthonormal ℝ ((↑) : s → E)) : s.Countable
```

Basis-coordinate utilities used by Part A's generalization, and reusable:

```lean
theorem eq_zero_of_repr_eq_zero (c : HilbertBasis κ ℝ E) {x : E}
    (h : ∀ p, c.repr x p = 0) : x = 0
theorem repr_basis_apply_self (c : HilbertBasis κ ℝ E) (p : κ) : c.repr (c p) p = 1
theorem repr_basis_apply_ne (c : HilbertBasis κ ℝ E) {p q : κ} (h : q ≠ p) :
    c.repr (c p) q = 0
theorem topologicalClosure_eq_top_of_basis_mem (c : HilbertBasis κ ℝ E)
    (K : Submodule ℝ E) (h : ∀ p, c p ∈ K) : K.topologicalClosure = ⊤
theorem basis_mem_blockB (c : HilbertBasis κ ℝ E) (S : Set κ) {p : κ} (hp : p ∈ S) :
    c p ∈ blockB c S
noncomputable def diagB (c : HilbertBasis (ι × Bool) ℝ E) : Submodule ℝ E
theorem mem_diagB (c : HilbertBasis (ι × Bool) ℝ E) (x : E) :
    x ∈ diagB c ↔ ∀ i : ι, c.repr x (i, false) = c.repr x (i, true)
theorem isClosed_diagB (c : HilbertBasis (ι × Bool) ℝ E) : IsClosed (diagB c : Set E)
theorem nonempty_equiv_prod_bool (ι : Type*) [Infinite ι] : Nonempty (ι ≃ ι × Bool)
```

### Part E — the ω₁ combinator

**E1** — statement supplied. The universe lifting is inside the proof; the
caller sees only `Set.Iio (Ordinal.omega 1)` and supplies CH as an equality of
cardinals (never as an axiom).

```lean
theorem exists_enumeration_of_CH {α : Type} (hcard : Cardinal.mk α = Cardinal.continuum)
    (hCH : Cardinal.continuum = Cardinal.aleph 1) :
    ∃ f : (Set.Iio (Ordinal.omega 1)) → α, Function.Surjective f
```

**E2** — statement supplied. One step function, one bookkeeping map, one
invariant; **no successor/limit case split** is exposed (nor needed
internally: at every stage `a < ω₁` the set `Set.Iio a` is countable, so a
single surjection `ℕ → Set.Iio a` feeds all previous values to `limit`).

```lean
theorem exists_omega1_chain {β : Type} [PartialOrder β]
    (step : β → β) (hstep : ∀ b, b < step b)
    (limit : (ℕ → β) → β) (hlimit : ∀ f : ℕ → β, ∀ n, f n ≤ limit f)
    (b₀ : β) :
    ∃ c : (Set.Iio (Ordinal.omega 1)) → β,
      ∀ i j : (Set.Iio (Ordinal.omega 1)), i < j → c i < c j
```

---

## 2. Census

Of the items contracted, the census (`REPORT-WO7a.md`) already had proofs for
the mathematics of A1, A2, B0, B1, B2, B3, C1 (in hypothesis form), D1, D3,
D4, E1, E2. What this commission adds, beyond stable names, docstrings and
minimal hypotheses:

| item | what was new here |
|------|-------------------|
| A1 | oddness hypothesis dropped; general vector-space form separated out |
| A2 | packaging decision (two corollaries); the optional generalization to arbitrary infinite orthonormal bases, which the census did not attempt |
| B2 | statement supplied: self-adjointness removed, conclusion strengthened to an orthonormal (hence weakly null) sequence inside `V`; compression form added |
| C1 | the probe's hypothesis `H` discharged from `lam ∈ essSpec T`, so the caller supplies only the point of the essential spectrum and the decay rate; a `V`-relative version added |
| C2 | statement supplied in full (the census had no closed-span statement) |
| D1 | `blockB` supplied as a definition with both characterizations and closedness |
| D2 | statement supplied: definitional agreement, no bridging isometry |
| D3 | universe-polymorphic |
| E1, E2 | re-sited unchanged; signatures reported verbatim above |

## 3. Report-rather-than-repair items

* **A2's `hcl`.** The contract's A2 carries `hcl : ∀ M ∈ π, IsClosed (M : Set H)`.
  It is **not needed** (the argument uses only `hup`, `hinf`, `hbot`, `hne`). It
  is retained in the delivered statement because the contract prescribes it, and
  flagged in the docstring; the `unused variable hcl` warning in the build is
  therefore expected and deliberate.
* **Q2/D4 stays un-generalized**, as instructed. The counterexample remains in
  the census record.
* **The engine's `V` parameter.** Rather than delivering B2 and C1 as two
  independent proofs, both are instances of one engine
  (`exists_orthonormal_approx_eigenvectors_of_forall`) plus one Weyl-datum
  lemma (`exists_unit_approx_eigenvector_mem`). The rejected alternative was to
  keep the probe's shape (engine with an abstract hypothesis `H`, no `V`) and
  re-run the correction argument inside each consumer; that would have made
  every ampleness lemma in WO-13 repeat the `Vᗮ`-projection step.

## 4. Axiom audit

`#print axioms` is emitted in the file for each contracted item, including
every item whose statement was supplied here, and for the added items
(`no_prime_filter_of_finrank_ge_two`, `no_prime_filter_of_infinite_hilbertBasis`,
`exists_orthonormal_approx_eigenvectors_mem`, `mem_blockB_iff_inner`,
`essSpec_subset_essSpec_compress`). Every line reports exactly

```
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `admit`, `axiom` or `native_decide` anywhere in
`PlufWO9.lean`, and CH occurs only as the hypothesis `hCH` of E1.

## 5. Note for WO-10 onward

* Paper II Proposition 6.1 (WO-10) should be written against `blockB`,
  `mem_blockB_iff` and D4; `blockB_stdBasis_eq` lets the WO-1/WO-2 block lemmas
  be used unchanged wherever the standard basis of `H` is the basis in play.
* Paper I §5 (WO-13/WO-14) should take its ampleness hypotheses in the shape of
  C2's tolerance clause, and obtain its subspaces from
  `exists_orthonormal_approx_eigenvectors_mem` + `approx_eigen_span_spec`;
  `essSpec_le_of_finCodim` is what makes ampleness survive passage to a block
  of finite codimension.
* WO-12 and WO-13 should quote E1 and E2 exactly as printed in §1.
