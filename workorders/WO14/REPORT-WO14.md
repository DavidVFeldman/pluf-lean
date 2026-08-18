# REPORT — Work Order WO-14 (pluf project, Feldman–Wilce)

**Paper I, Lemma 5.6 — the blocking lemma.** The deliverable is the contract
file `RequestProject/PlufWO14.lean` (namespace `PlufWO14`) and this report.

**Toolchain.** `leanprover/lean4:v4.28.0`, Mathlib as pinned in the base
artifact. Base: the merged WO-13 tree, **unmodified** — `diff -r` against the
supplied `base/RequestProject` reports `Only in RequestProject: PlufWO14.lean`,
so all 216 prior theorems remain green and `PlufWO7a.lean` was neither edited
nor deleted. Full-project build: `Build completed successfully`.

## Headline

* **Every contracted item is delivered verbatim and proved: S0, S1, S2, P1,
  W0, W1, W2, W3.** The quarantine fallback was **not** exercised: W1 (the
  recursion) is unconditional, and therefore so is W3.
* The fallback shape `blocking_lemma_of_sequence` is delivered as well — not
  as a fallback but as the actual carrier of the assembly: it proves W3's
  conclusion from W1's conclusion taken as a hypothesis, and `blocking_lemma`
  is the one-line application of it to `exists_blocking_sequence`. Both are
  audited.
* No `sorry`, `admit`, `axiom` or `native_decide`. `#print axioms` is emitted
  for all eight contract theorems plus `blocking_lemma_of_sequence` and the
  odd-stage selection lemma; every one reports exactly
  `[propext, Classical.choice, Quot.sound]`.
* 20 new theorems and one new definition (`tailSpan`).

## 1. Census

Read first: `WORKORDER.md`, `REPORT-WO13.md` §6 (D1's final signature — the
interface this commission consumes), `PlufWO13.lean` (`T`, `compress`, `Ample`,
`escape`, `quadratic_estimate_of_bound`, `essSpec_compress_mono`,
`essSpec_compress_eq_of_finCodim`, `ample_of_ample_le`,
`notMem_essSpec_compress_bot`, `not_ample_of_notMem_essSpec`, the sequence
interface `mem_essSpec_compress_of_seq` / `exists_seq_of_mem_essSpec_compress`,
and the defect estimate `norm_T_sub_lam_sq_le`), `PlufWO13/Basic.lean`
(`PlufWO13.Aux`), and `PlufWO9.lean` (`essSpec`, `tendsto_inner_of_orthonormal`).

Two census verdicts were explicitly requested.

* **S0 verdict.** `PlufWO13/Basic.lean` does **not** contain S0. Its
  finiteness-transfer lemmas move between three *given* finite-codimension
  statements (`Module.Finite ℝ (↥V ⧸ W.comap V.subtype)`,
  `Module.Finite ℝ ↥(W.comap V.subtype)ᗮ`, `Module.Finite ℝ ↥(V ⊓ Wᗮ)`); none
  of them produces finite codimension from a finite set of functionals. S0 is
  therefore proved here, directly: the map `↥V → (F → ℝ)`, `v ↦ (f v)_{f ∈ F}`,
  has kernel exactly the contracted `comap`, so the quotient embeds in a
  finite-dimensional space (`LinearMap.quotKerEquivRange`). Closedness is the
  intersection of `V` with the kernels of continuous functionals.
* **essSpec-membership-criterion verdict.** WO-13 exports
  `mem_essSpec_compress_of_seq`, whose defect hypothesis is the *ambient*
  `‖T yₙ − λ yₙ‖ → 0`; what the recursion produces is Rayleigh convergence.
  The bridging lemma is small and is proved here as
  `mem_essSpec_compress_of_rayleigh_seq`: at `λ ∈ {1, 1/16}` WO-13's identity
  `norm_T_sub_lam_sq_le` bounds the squared defect by
  `|⟪T y, y⟫ − λ‖y‖²|`, so Rayleigh convergence upgrades to defect convergence
  (`tendsto_zero_of_sq_le`). No other criterion was missing; in particular the
  A3 route (orthonormal ⇒ weakly null, via
  `PlufWO9.tendsto_inner_of_orthonormal`) applies verbatim.

Mathlib still has no essential spectrum, Calkin algebra, Fredholm theory or
Borel functional calculus; none was needed.

## 2. The three design disciplines, as implemented

1. **Rayleigh only.** S1, S2 and the odd-stage lemma conclude with
   `|⟪T w, w⟫ − λ| ≤ ε`. S1 is proved exactly as prescribed — S0 cuts `V` to
   the closed finite-codimension `C`, `essSpec_compress_eq_of_finCodim` keeps
   `λ ∈ essSpec (compress C)`, and WO-13's extraction
   `exists_seq_of_mem_essSpec_compress` yields unit vectors of `C` whose
   Rayleigh values converge to `λ`; one term of that sequence is the witness.
   (Because the extraction already delivers Rayleigh values, the Cauchy–Schwarz
   step of the contracted route is not needed at this point; it is used instead,
   in the reverse direction, in the membership bridge of §1.)
2. **Escape only at the blocked value.** `PlufWO13.escape` is applied at `λ₀`
   and nowhere else. Its `hVN` binder is supplied internally from `hnot` via
   `not_ample_of_notMem_essSpec`. The odd stage goes through S1 at `λ₁`, S2 at
   `λ₀` with the two extra constraints, and P1.
3. **Exact orthogonality.** All stage constraints are imposed exactly, as
   vanishing of the continuous functionals `⟪w j, ·⟫`, `⟪T (w j), ·⟫`,
   `⟪P_{Nᗮ}(w j), ·⟫`; nothing is approximate, and W2's compressions are
   exactly diagonal.

## 3. W2: the packaging

Delivered in the **ambient** form, an identity in `H`:

```lean
(tailSpan w j).starProjection (T (w m)) = ⟪T (w m), w m⟫ • w m   (j ≤ m)
```

(with `tailSpan w j` written out in the contract statement as
`(Submodule.span ℝ (range fun n : {n // j ≤ n} => w n)).topologicalClosure`).
The proof shows `T (w m) − d • w m` is annihilated by `⟪·, x⟫` for every
`x` in the tail span — the kernel of a continuous functional is a closed
subspace containing the generators, hence contains the closure — and then
applies `Submodule.eq_starProjection_of_mem_orthogonal`.

**Reported choice, and its consequence.** W3 does **not** consume W2. The
essential-spectrum step of the assembly is cheaper through the Rayleigh
criterion of §1: the even- and odd-indexed subsequences of `w` are orthonormal
(hence weakly null) sequences of unit vectors of `tailSpan w j` whose Rayleigh
values converge to `λ₀` and `λ₁`, and `mem_essSpec_compress_of_rayleigh_seq`
concludes. Exact diagonality is what makes the *statement* of W2 true and is
recorded as contracted, but the assembly needs only the diagonal Rayleigh
values, not the eigenvector identity.

## 4. W1: the constraint bookkeeping as implemented

The recursion runs on a general, reusable gadget proved here:

```lean
theorem exists_seq_of_step {α : Type*} [Nonempty α] (P : ℕ → (ℕ → α) → α → Prop)
    (hdep : ∀ n u v y, (∀ j < n, u j = v j) → P n u y → P n v y)
    (hex : ∀ n u, ∃ y, P n u y) : ∃ f : ℕ → α, ∀ n, P n f (f n)
```

(iterated `Function.update` on `ℕ → α`, with the stability lemma that indices
below the update point never change). The stage predicate is

```lean
P n u y := y ∈ h n ∧ ‖y‖ = 1 ∧
  (∀ j < n, ⟪u j, y⟫ = 0 ∧ ⟪T (u j), y⟫ = 0 ∧ ⟪P_{Nᗮ}(u j), y⟫ = 0) ∧
  y ∉ N ∧ |⟪T y, y⟫ − (if Even n then λ₀ else λ₁)| ≤ 1/(n+1)
```

so `hdep` is immediate and `hex` is unconditional — the selection lemmas accept
an arbitrary finite constraint set, so no invariant has to be threaded through
the recursion. The constraints at stage `n` are the finite set

```lean
F n u = (Finset.range n).biUnion fun j =>
  {innerSL ℝ (u j), innerSL ℝ (T (u j)), innerSL ℝ (P_{Nᗮ}(u j))}
```

Bookkeeping of the six delivered clauses:

* `w n ∈ h n`, `‖w n‖ = 1`, `w n ∉ N`, and the Rayleigh clause are read off `P`.
* **Orthonormality**: `⟪w j, w n⟫ = 0` for `j < n` from the first constraint,
  and `real_inner_comm` for the other order.
* **T-orthogonality in both orders**: `⟪T (w j), w n⟫ = 0` for `j < n` from the
  second constraint; for `n < m`, `T_inner_symm` plus `real_inner_comm`.
* **y-orthogonality**: with `P = P_{Nᗮ}` idempotent and self-adjoint,
  `⟪P a, P b⟫ = ⟪P a, b⟫`, so the third constraint gives
  `⟪P (w j), P (w n)⟫ = 0` for `j < n`, and `real_inner_comm` the other order.
* The missing value descends from `h 0 ⊓ N` to `h n ⊓ N` by the contrapositive
  of `essSpec_compress_mono` along `h n ⊓ N ≤ h 0 ⊓ N`.
* Even stages call S2 at `λ₀`; odd stages call the packaged odd-stage lemma
  `exists_unit_constrained_rayleigh_notMem_other` at `λ₁`.

**Rate.** The contracted rate `1/(n+1)` is kept, unchanged, in the delivered
statement. Internally the odd stage splits it as `ε/2 + ε/2` between S1's
tolerance and P1's displacement.

## 5. Report-rather-than-repair items

Nothing in the contract turned out to be false; the counterexample license was
not exercised. Two statements needed support that the contract did not mention,
and both are supplied without changing any contracted statement.

* **P1 gives no membership clause, and W1 needs `w ∈ h n`.** It is not missing:
  clause (ii) already implies it. If `w` were outside the closed subspace
  `span {w', z}`, the functional `⟪w − P_{span}w, ·⟫` would annihilate `w'` and
  `z` but not `w`. This Hilbert-space substitute for Hahn–Banach is proved as
  `mem_of_forall_annihilating_functional`, and the odd-stage lemma uses it to
  place the perturbed vector in `span {w', z} ≤ h n`. **P1's contracted
  statement is unchanged.**
* **P1's `hN : IsClosed N` is unused.** The proof keeps `w ∉ N` by a purely
  algebraic two-candidate argument: `w(η) ∈ N` implies `w' + η z ∈ N`, and if
  this held for both `η = t` and `η = t/2` then `(t/2) z ∈ N`, contradicting
  `z ∉ N`. No projection and no closedness is used. Retained and flagged, per
  protocol; the `unused variable hN` warning is expected.
* **W3's `hGN` is unused**, exactly as design note 3 predicts. Retained and
  flagged. The degenerate case `q ⊓ N = ⊥` is handled by
  `notMem_essSpec_compress_bot`, inside the extraction of `λ₀`.

## 6. W3: the assembly

`λ₀` is extracted by case analysis: `q ⊓ N` is closed and not ample, so if both
values were in `essSpec (compress (q ⊓ N))` then `q ⊓ N` would be ample —
`q ⊓ N ≠ ⊥` itself follows from the membership at `1` via
`notMem_essSpec_compress_bot`. W0 gives the decreasing cofinal chain `h` below
`q`, the missing value descends to `h 0 ⊓ N`, and W1 gives `w`. Put
`R = tailSpan w 0`, `R j = tailSpan w j`.

* **`R ⊓ N = ⊥`** without any series expansion: for each `m`, the continuous
  functionals `⟪P_{Nᗮ}(w m), ·⟫` and `‖P_{Nᗮ}(w m)‖² ⟪w m, ·⟫` agree on every
  `w n` (by idempotence, W1's y-orthogonality, and orthonormality), hence their
  difference has a closed kernel containing the span, hence containing `R`. For
  `x ∈ R ⊓ N` the left side vanishes (`P_{Nᗮ} x = 0`) and `‖P_{Nᗮ}(w m)‖² ≠ 0`,
  so `⟪w m, x⟫ = 0` for all `m`; the same closed-kernel argument applied to
  `⟪x, ·⟫` gives `⟪x, x⟫ = 0`, i.e. `x = 0`.
* **Ampleness**: `ample_tailSpan` proves `Ample (R j)` for every `j` by the
  Rayleigh criterion of §1 applied to the subsequences `k ↦ w (2(j+k))` and
  `k ↦ w (2(j+k)+1)`. Then `R j ≤ R ⊓ h j` (each `w n ∈ h n ≤ h j` for `n ≥ j`,
  by `antitone_nat_of_succ_le`), cofinality of the chain gives `j` with
  `h j ≤ g`, and `ample_of_ample_le` promotes ampleness to `R ⊓ g`; `j = 0`
  gives `Ample R`.

## 7. Additions beyond the contract

All are support material for the above, in `PlufWO14`:
`exists_seq_of_step` (index-dependent recursion),
`mem_of_forall_annihilating_functional`, `mem_constraint_inf_iff`,
`perturb_key` (the fixed-`η` algebra of P1),
`exists_unit_constrained_rayleigh_notMem_other` (the odd stage as a selection
lemma), `tendsto_zero_of_sq_le`, `mem_essSpec_compress_of_rayleigh_seq`,
`tailSpan` with `isClosed_tailSpan`, `mem_tailSpan`, `tailSpan_le`,
`ample_tailSpan`, and `blocking_lemma_of_sequence`.

## 8. Axiom audit

`#print axioms` at the foot of `PlufWO14.lean` covers
`finCodim_of_constraints`, `exists_unit_constrained_rayleigh`,
`exists_unit_constrained_rayleigh_notMem`,
`exists_unit_constrained_rayleigh_notMem_other`, `perturb_unit`,
`exists_decreasing_cofinal`, `exists_blocking_sequence`,
`compress_exact_diagonal`, `blocking_lemma_of_sequence` and `blocking_lemma`.
Every one reports

```
[propext, Classical.choice, Quot.sound]
```

## 9. Notes for WO-15

* The blocking lemma is available unconditionally as
  `PlufWO14.blocking_lemma`; no quarantined hypothesis has to be carried into
  Theorem 5.7 or Proposition 5.9.
* `PlufWO14.exists_seq_of_step` is the general ω-recursion gadget used here and
  is reusable for any stage-wise construction whose stage predicate depends on
  finitely many earlier choices.
* `PlufWO14.mem_essSpec_compress_of_rayleigh_seq` is the cheapest route to
  ampleness of a closed span: exhibit an orthonormal sequence inside it whose
  Rayleigh values converge to `1` and to `1/16`.
* `PlufWO14.tailSpan` and its four lemmas are the standard packaging of the
  closed span of a tail of a sequence.
