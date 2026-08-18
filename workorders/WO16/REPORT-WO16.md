# REPORT-WO16 — pluf project (Feldman, Wilce), Paper V

Artifact: `RequestProject/PlufWO16.lean` (contract roll-up) with
`RequestProject/PlufWO16/{Basic,PartA,PartB,PartC}.lean`. Toolchain
`leanprover/lean4:v4.28.0`, Mathlib as pinned. No `sorry`, `admit`, `axiom`
or `native_decide` anywhere; `#print axioms` for every contract theorem is at
the foot of `PlufWO16.lean` and reports the whitelist `propext`,
`Classical.choice`, `Quot.sound` in every case. The whole base tree
(WO-1 – WO-15) builds green; `PlufWO7a.lean` is untouched.

## 1. Census

### 1.1 What the base already supplies, and what was reused

| need | reused from base |
|---|---|
| ambient space, coordinates, blocks | `PlufWO1.H`, `coordL`, `coordCLM`, `block`, `mem_block_iff`, `isClosed_block` |
| support of a vector | `PlufWO2.supp` (see §2.1) |
| elementary block algebra | `PlufWO5.block_empty`, `block_univ`, `block_mono`, `block_inter`, `evec_mem_block` |
| plufs | `PlufWO6.IsPluf` and accessors, `PlufWO6.isClosed_inf`, `PlufWO6.nontrivial_H` |
| maximality criterion (B2) | `PlufWO6.maximality_criterion` |
| Zorn extension of a proper filter (B3) | `PlufWO10.IsProperFilter`, `PlufWO10.exists_pluf_extension` |
| Paper II diagonalization (C3) | `PlufWO6.diagonalizable_iff_intimate_pluf`, `PlufWO5.Intimate` |
| Gowers's subspace (C4) | `PlufWO5.gowersX`, `mem_gowersX_iff`, `pairDiff_mem_gowersX`, `pairDiff_ne_zero`, `pairDiff_mem_block`, `transversalVec`, `transversalVec_apply` |
| dependent choice with history (A2) | `PlufWO14.exists_seq_of_step` |

New material added by this commission: the counting step
(`exists_pos_lt_notMem`), the recursion apparatus of A2 (`psum`, `freeze`,
`stepPred`, `exists_step`, `exists_coeffs`, `psum_ne_zero`), the filter of
complements of finite unions of independent sets (`coverFilter`, B4), the
generated proper filter of B3 (`genFilter`), and the general pair-sum
recursion of C4a with its consequences.

### 1.2 Verdicts on the three uncontracted sections

**(1) Scrawl axioms (§4). Verdict: Theorem 4.3 in the *statement* form —
union closure plus finite-set elimination for `F(M)` — is cheap on top of
Part A and could be contracted now; but the *matroid-theoretic* packaging
(circuits, scrawls, duals, cofinitary matroids) is not cheap, because the
pieces Mathlib supplies are the wrong half of the interface.**

Mathlib's `Mathlib/Combinatorics/Matroid/` does support infinite ground sets
(`Matroid α` for arbitrary `α`, with a `Set α` ground set `M.E`), and has:
`Matroid.IsCircuit` with `IsCircuit.elimination`,
`IsCircuit.strong_elimination`, `IsCircuit.strong_multi_elimination`
(including the set-indexed form) and `Matroid.ext_isCircuit` (a matroid is
determined by its circuits); duality `Matroid.dual` (`M✶`) with cocircuits;
the class `Matroid.Finitary` and
`Matroid.finitary_iff_forall_isCircuit_finite`; closure, minors, rank.

What is missing is exactly what Theorem 4.3 needs in order to *produce* a
matroid:

* there is no constructor from a family of circuits. The available
  constructors are through independence (`IndepMatroid.ofFinitary`,
  `ofFinitaryCardAugment`, `ofBdd`, `ofFinite`, `ofFinset`, `ofBase`, …), all
  of which demand the augmentation axiom and, in the infinite case, the
  maximality axiom (SM) — which is precisely what Paper V's §6 shows can
  fail for `F(M)`. Building `circuitAxioms → Matroid` for infinite ground
  sets is a genuine piece of infrastructure (it is the Bruhn–Diestel–
  Kriesell–Pendavingh–Wollan theorem), not a wrapper;
* there is no notion of *scrawl* (union of circuits) and no Bowler–Carmesin
  scrawl axiomatization;
* there is no notion of *cofinitary* matroid, and no representability at all
  (the word appears only in doc comments).

Recommendation: contract Theorem 4.3 in the self-contained form "F(M) is
closed under arbitrary unions (this is A3) and satisfies the finite-deleted-
set elimination of Theorem 4.1", stated directly about supports, with no
`Matroid` in the statement. That is a short item given Part A: the
elimination is the finite linear combination `y = x - ∑_{p ∈ X} a_p u_p`
with `a_p = x_p / (u_p)_p`, and needs nothing beyond `Submodule.sum_mem` and
coordinate bookkeeping. Anything phrased through Mathlib's `Matroid` should
be deferred until a circuit-axioms constructor exists.

**(2) The finite-rank classification (§5). Verdict: worth contracting, but
only in the form of the *transfer*, and the exercise is not empty —
provided the quarantined hypothesis is stated as Aroca et al. state it
(about `T(W)` for finite-dimensional `W ⊆ K^E`), not about `F(M)`.**

The gap between hypothesis and conclusion is real, and it is analytic, not
combinatorial: Theorem 5.1 is about an arbitrary finite-dimensional subspace
of `K^E`, while Theorem 5.2 is about a finite-rank *closed* subspace of
`ℓ²(N)` and about which scrawl families are realized *there*. The transfer
therefore has to supply (i) that a finite-rank subspace of `ℓ²` is a
finite-dimensional subspace of `ℝ^N` (or `C^N`) with the same support family
— true and cheap, since `F` only sees coordinates; (ii) that every
finite-dimensional subspace of `K^E` with `E` countable is realized as a
closed subspace of `ℓ²` — true, and needs the (cheap, but non-vacuous)
observation that a finite-dimensional subspace of `ℓ²` is automatically
closed, plus a rescaling argument to place an arbitrary finite-dimensional
subspace of `K^N` inside `ℓ²` while preserving supports. Both directions are
formalizable at modest cost and neither is contained in the hypothesis. So
the exercise is not empty; but the value delivered is the transfer, and the
hypothesis carries the mathematics, exactly as with Mathias and MSS in
WO-5/WO-6. If the commissioner wants only one item from §5, the second half
of (ii) — support-preserving realization inside `ℓ²` — is the one with
content.

**(3) The model space (§6). Verdict: Mathlib has essentially nothing;
this section should stay uncontracted.**

* Blaschke products: absent (no occurrence anywhere in Mathlib).
* Hardy space `H²` of the disc, model spaces `K_Θ = H² ⊖ ΘH²`, reproducing
  kernels for `H²`: absent.
* Generalized Vandermonde positivity: absent. Mathlib has
  `Matrix.vandermonde` and its determinant for the classical (integer
  exponent) matrix only; the positivity of `det(λ_i^{α_j})` for real
  exponents `α_1 < … < α_m` and `0 < λ_1 < … < λ_m` is not there and is not
  a corollary of what is.
* Zero counts for exponential sums: absent in the needed generality. The
  nearest item is `Mathlib/Algebra/Polynomial/RuleOfSigns.lean` (Descartes'
  rule of signs for polynomials); the statement Example 6.1 uses — a nonzero
  real exponential sum `∑_{k<m} a_k λ_k^n` with distinct positive bases has
  at most `m-1` zeros on `N₀` — is a generalized Descartes statement that
  would have to be proved from scratch (by induction on `m` via division by
  `λ_m^n` and discrete Rolle, or via the generalized Vandermonde
  positivity).

Formalizing §6 therefore means building the generalized Vandermonde
determinant, the exponential-sum zero count, and enough of `H²`/Blaschke
theory to say what `K_Θ` is: three separate development efforts, of which
only the first two are needed if Example 6.1 is stated purely in `ℓ²(N₀)`
coordinates (which it can be — the model-space language is interpretation).
A cheap, honest fragment: Example 6.1 as a statement about the closed
subspace of `ℓ²` cut out by finitely many geometric-sequence functionals,
with the generalized Vandermonde positivity as the one lemma to prove. The
conditional chain that ends "F(K_Θ) is the scrawl family of no matroid"
depends on the open Question 9.3 and cannot be contracted at all.

## 2. Item notes, findings, conventions

### 2.1 `supp`

`PlufWO2.supp` is stated for `Hk κ`, and `PlufWO1.H` is `PlufWO2.Hk ℕ`, so at
the standard space the contract's `supp` and the existing one agree
definitionally: `PlufWO16.supp_eq_plufWO2_supp` is `rfl`. The contract's name
is kept because the contract names it; no duplication of theory follows,
since everything is proved through the block dictionary
`mem_block_iff_supp_subset`.

### 2.2 A2: the shape of the recursion (requested report)

`PlufWO14.exists_seq_of_step` **does** apply, at `α = ℝ`, and no new
dependent-choice gadget was needed. The reason the stage constraint's
reference to the accumulated partial sum is harmless: the partial sum

```
psum y u n k = ∑_{i < n} u i * (y i) k
```

is a function of the coefficient history `u` below `n`, and so is the frozen
minimum

```
freeze y u m = min { |psum y u (m+1) k| or 1 : k ≤ m }   (a Finset.inf')
```

for `m < n`. The stage predicate is therefore a predicate of `n`, of the
history below `n`, and of the new coefficient, which is exactly the gadget's
`P n u y` with its locality hypothesis `hdep` (discharged by
`psum_congr`/`freeze_congr`).

The one point where the paper's phrasing has to be adjusted: the gadget
requires the stage predicate to be satisfiable for an **arbitrary** history,
including histories that violate earlier stages. The clause "keep
`supp(s_m) = supp(s_{m-1}) ∪ supp(x^{(m)})`" is not satisfiable for an
arbitrary history — a coordinate already dead cannot be revived by a
coefficient at a place where the new vector vanishes. So the contracted
stage predicate is

```
stepPred y n u c :=
  0 < c ∧ c ≤ (1/2)^n ∧
  (∀ m < n, c ≤ (1/2)^(n-m+1) * freeze y u m) ∧
  (∀ k, (y n) k ≠ 0 → psum y u n k + c * (y n) k ≠ 0)
```

— only the *new* vector's coordinates are protected — and the invariant the
paper states,

```
psum_ne_zero : (∃ i ≤ n, (y i) k ≠ 0) → psum y c (n+1) k ≠ 0,
```

is proved afterwards, by induction over the chosen sequence: at stage `n+1`,
a coordinate with `(y (n+1)) k ≠ 0` is protected by the stage clause, and one
with `(y (n+1)) k = 0` is unchanged and survives by induction.

Three further deviations of bookkeeping from the printed proof, all
immaterial: coefficients are taken **positive** rather than merely nonzero
(the admissible set is then an interval `(0, ε)` minus a countable set, and
`ε` is a `Finset.inf'` over `range (n+1)` of the finitely many binding
constraints, so no punctured-disc geometry is needed); the normalization is
`y i = b i • x i` with `b i = ‖x i‖⁻¹` or `1`, so that `‖y i‖ ≤ 1` holds
including for `x i = 0` (the paper's normalization is illegal at zero
vectors, and the contract's hypothesis does not exclude them); and the tail
estimate is run against `N = max m k` rather than "once the index is large
enough", which is the same choice made explicit.

Membership of the limit in `M` is the one use of closedness, via
`IsClosed.mem_of_tendsto` applied to the net of finite partial sums.

### 2.3 A4: unused hypotheses (finding)

The minimality hypotheses `hminx`, `hminy` of A4 are not used. The
eliminated vector `y_p • x - x_p • y` is nonzero as soon as
`supp x ≠ supp y`, because vanishing makes `y` a nonzero multiple of `x` and
hence forces equal supports. Minimality is what makes Proposition 3.2 the
*circuit* elimination axiom, but it is not needed for the statement as
contracted. The hypotheses are retained verbatim.

### 2.4 B3, B4: the filters used

B3's forward direction builds `genFilter M U`, the closed subspaces above
some `M ⊓ block S` with `S ∈ U`, checks `PlufWO10.IsProperFilter` for it
(properness is exactly the hypothesis `U ⊆ cD M`), and extends by
`PlufWO10.exists_pluf_extension`. That the resulting trace is *exactly* `U`
uses `block S ⊓ block Sᶜ = block ∅ = ⊥` and properness of the pluf.

B4's backward direction needs the dual filter of the ideal generated by
`cI M`. Rather than `Filter.generate`, the artifact defines `coverFilter M`
directly as the sets containing the complement of a finite union of members
of `cI M`; the filter axioms are immediate, `NeBot` is literally
`¬ HasFiniteCover M`, and `Ultrafilter.of` finishes. Note that `cI M` is only
downward closed, not union-closed — the finite unions are what makes the
ideal — and this is where B1 is used.

The propositional forms of the covering number were adequate throughout;
a numerical `χ : ℕ∞` was never needed, including in Part C, so the
`ℕ∞`-arithmetic was avoided as the contract anticipated.

### 2.5 C4a: the statement supplied, and the indexing convention

The contract left C4a's statement open. It is supplied as

```
theorem gowersX_pairSum_rec {x : H} (hx : x ∈ PlufWO5.gowersX) (k : ℕ) :
    pairSum x k = (((k : ℝ) + 2) / ((k : ℝ) + 1)) * pairSum x (k + 1)
```

with `pairSum x k = x (2k) + x (2k+1)`, together with the converse
`mem_gowersX_iff_pairSum_rec` (the recursion *is* membership) and the
consequence that actually drives C4b,

```
gowersX_pairSum_eq_zero_of_eq_zero :
    x ∈ gowersX → pairSum x j = 0 → ∀ k, pairSum x k = 0,
```

proved by running the recursion forwards (dividing by the nonvanishing
factor) and backwards (multiplying) from `j`. `PlufWO5.gowersX_pairSum_eq_zero`
— the finitely supported case in `PlufWO5/PartD.lean` — is the special case
where the vanishing pair sum is found beyond the support. In fact the
general recursion was already present in the base as
`PlufWO5.mem_gowersX_iff`; C4a is its export in pair-sum language, and the
new content is the vanishing propagation.

**Indexing convention (requested report).** The development is 0-indexed:
`pair k = {2k, 2k+1}` for `k ≥ 0`, matching the constraint vectors
`PlufWO5.gowersV n`. The paper displays `P_i = {2i-1, 2i}` for `i ≥ 1`. The
dictionary is `i = k + 1`; the paper's `s_i = 1/i` weights are the
development's `pairSum = 1/(k+1)`. All statements in `PlufWO16` are
0-indexed, and the paper's "P₁ omits class 3, P₂ omits class 1, P₃ omits
class 2" becomes "pair 0 omits class 2, pair 1 omits class 0, pair 2 omits
class 1". The explicit three classes used are

```
coverS = {0, 5} ∪ {even n ≥ 6},  coverT = {1, 2} ∪ {odd n ≥ 6},  coverV = {3, 4}.
```

### 2.6 Scalar finding (requested report)

No contracted item needed a property of ℝ beyond the paper's stated
requirement that there be more scalars than coordinates. That requirement is
used exactly once, in `exists_pos_lt_notMem` ("a countable set of reals
misses a point of every interval `(0, ε)`"), and it feeds A1 and A2 only.
Parts B and C use no property of the scalars at all: their proofs are
lattice theory plus the block dictionary, exactly as the paper's conventions
claim for Sections 7–8.

The order structure of ℝ is used for convenience only, in two places:
coefficients are chosen positive rather than merely nonzero, and the frozen
minima are minima of real numbers. Over ℂ the same proofs run with `|·|` the
modulus and the admissible set a punctured disc minus a countable set, as the
paper describes; nothing else changes. So the paper's assertion that these
results are field-blind is confirmed by the mechanization, with the single
caveat that the scalar field must be uncountable (over a finite or countable
field A1 and A2 fail, as the paper itself says).

## 3. Deliverables checklist

* Census, with the three verdicts: §1.
* Compiling artifact, all prior theorems green, no `sorry`/`axiom`: yes.
* `#print axioms` for every contract theorem including C4a: foot of
  `RequestProject/PlufWO16.lean`; whitelist only.
* A2 recursion shape: §2.2. C4a statement: §2.5. Indexing convention: §2.5.
  Scalar finding: §2.6. Unused-hypothesis finding (A4): §2.3.
