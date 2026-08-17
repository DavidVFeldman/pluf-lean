# REPORT — Work Order WO-10 (pluf project, Feldman–Wilce)

**Target (a) of the WO-7a census.** Deliverable: `RequestProject/PlufWO10.lean`
(namespace `PlufWO10`), with the auxiliary module
`RequestProject/PlufWO10/Decomp.lean`, together with this report.

**Toolchain.** `leanprover/lean4:v4.28.0`, Mathlib as pinned in the base
artifact. Base: the WO-9 artifact, unmodified; `PlufWO7a.lean` was neither
edited nor deleted. Full-project build: `Build completed successfully
(8070 jobs)`, all prior theorems green.

**Headline.**

* Every contracted item is delivered and proved: A1, A2, B1 (statement
  supplied), B2, C1 (with the exported lattice identity), C2, D1, E1 — and
  the optional item **E0 was taken**: the basis-relative form of Paper II's
  Theorem 5.2 is proved, so E1 is proved **as printed**, quantified over all
  `ℕ`-indexed orthonormal bases, with no silent specialization.
* **Two contracted statements are false as printed** and were handled under
  the codified counterexample license: B2 (`exists_basis_blocks_of_chain`)
  and D1 (`chains_never_suffice`). Both assert the existence of a
  `HilbertBasis ℕ ℝ E` over an arbitrary separable complete `E`, with no
  hypothesis making `E` infinite-dimensional. The counterexamples are
  formalized, the contracts are preserved verbatim in comments, and the
  marked minimal repair (one extra hypothesis, `¬ FiniteDimensional ℝ E`)
  is proved under the contracted names. Ratification requested at audit.
* **WO-9's D4 could not be used as printed** and a density variant had to be
  proved (see §3). This is a report-rather-than-repair item about the base,
  not about this contract.
* No `sorry`, `admit`, `axiom` or `native_decide`. Every audited item
  reports exactly `[propext, Classical.choice, Quot.sound]`.

---

## 1. Census

Against the WO-9 signature table and the base artifact:

| item | already available in the base | what WO-10 adds |
|------|-------------------------------|-----------------|
| A1 | nothing (`PlufWO6.IsPluf`, `PlufWO6.isPluf_of_criterion` are the consumers) | the Zorn extension theorem, new |
| A2 | — | the family form, new |
| B1 | — | the decomposition and its statement, new |
| B2 | `PlufWO9.exists_countable_hilbertBasis_of_decomposition` (D4) — **not applicable as printed**, see §3; `PlufWO9.hilbertBasis_reindex` (D3); `PlufWO9.countable_of_orthonormal` | the density variant of D4, the `ℕ`-indexed refinement, and the coordinatization |
| C1 | `PlufWO9.mem_blockB_iff`, `PlufWO9.isClosed_blockB` | `blockB_inf_blockB` (exported for WO-12), `blockB_ne_bot`, `blockB_empty`, `blockB_mono`, `blockB_univ`, `intimateB_blockB` |
| C2 | — | one-line consequence of monotonicity of `⊓` |
| D1 | — | Proposition 6.1 from B2 + C1 + C2 |
| E0 | `PlufWO5.diagonalizable_iff_intimate` at the standard basis | the basis-relative form, at an arbitrary Hilbert basis of an arbitrary real Hilbert space |
| E1 | `PlufWO6.principal_iff_sInf_ne_bot`, `PlufWO6.diagonalizable_iff_intimate_pluf` | Proposition 5.5, from A2 + E0 |

## 2. The E0 verdict, and its consequence for E1

**E0 is cheap and is proved**, as
`PlufWO10.diagonalizableB_iff_intimateB`. The census's prediction is
confirmed: WO-5's proof of Theorem 5.2 uses only

* `blockB b univ = ⊤` (`blockB_univ`),
* monotonicity `S ⊆ T → blockB b S ≤ blockB b T` (`blockB_mono`),
* `blockB b S ⊓ blockB b T = blockB b (S ∩ T)` (`blockB_inf_blockB`),
* `blockB b ∅ = ⊥` (`blockB_empty`),
* closedness of blocks (`PlufWO9.isClosed_blockB`),

each of which holds at an arbitrary Hilbert basis, in an arbitrary real
Hilbert space and for an arbitrary index type. Two packaging notes:

* the package clause `PlufWO5.PlufPackage.finCodim_mem` is used in WO-5's
  proof **only** to place `⊤` in the family, so E0 is contracted with the
  weaker hypothesis `htop : (⊤ : Submodule ℝ E) ∈ π`, which every pluf on a
  nonzero space satisfies (`PlufWO6.IsPluf.top_mem`);
* E0 is stated for a general `E`, not for `PlufWO1.H`, and for an arbitrary
  index type `ι`, not `ℕ`.

**Consequence for E1.** With E0 available, E1 is stated and proved exactly
as printed — the conclusion quantifies over **all** `HilbertBasis ℕ ℝ H`,
matching Proposition 5.5. In fact only the **easy** direction of E0 is
needed, isolated as `PlufWO10.intimateB_of_diagonalizableB`: if the
`b`-block trace of `π` is an ultrafilter then every member of `π` is
`b`-intimate, which uses nothing but closure under meets and properness.
So the basis quantifier costs nothing at all in E1; E0 is delivered on its
own merits (and for WO-12).

Nonprincipality in E1 is likewise direct: a vector lying in every member of
a pluf `σ ⊇ R` lies in `sInf R = ⊥`. `PlufWO6.principal_iff_sInf_ne_bot`
is therefore not invoked; the conclusion is stated in the "no common
nonzero vector" form the contract prescribes, which is the right-hand side
of that equivalence.

## 3. B1's shape, and why WO-9's D4 could not be used

**B1's shape.** The three groups of the decomposition are reindexed into
one `ℕ`-indexed family `PlufWO10.chainPieces M`:

```
chainPieces M 0       = (M 0)ᗮ            -- the top complement
chainPieces M 1       = ⨅ k, M k          -- the intersection of the chain
chainPieces M (n + 2) = M n ⊓ (M (n+1))ᗮ  -- the successive differences
```

and B1 is delivered as the conjunction of the three clauses the
coordinatization consumes:

```lean
theorem chain_decomposition (hmono : ∀ k, M (k+1) ≤ M k)
    (hcl : ∀ k, IsClosed (M k : Set E)) :
    (∀ n, IsClosed ((chainPieces M n : Submodule ℝ E) : Set E)) ∧
    (Pairwise fun m n => ∀ x ∈ chainPieces M m, ∀ y ∈ chainPieces M n,
      inner (𝕜 := ℝ) x y = 0) ∧
    (⨆ n, chainPieces M n)ᗮ = ⊥
```

Two deliberate choices. (i) The two exceptional groups are placed at
indices `0` and `1` rather than appended, so that the family is total and
no `Option`/sum bookkeeping is needed. (ii) Density of the join is stated
as `(⨆ n, chainPieces M n)ᗮ = ⊥` rather than as
`(⨆ n, chainPieces M n).topologicalClosure = ⊤`. The two are equivalent
over a Hilbert space, but the orthogonal-complement form is what the basis
construction consumes and what the proof produces: no limits of projections
are needed, only the observation that a vector orthogonal to `(M 0)ᗮ` and
to every difference `M n ⊖ M (n+1)` lies in every `M k` by induction, hence
in `⨅ k, M k`, to which it is also orthogonal.

**Why D4 is not applicable.** WO-9's countable-decomposition theorem asks
for `hspan : ⨆ n, M n = ⊤` — an identity in the submodule lattice, i.e. the
*algebraic* span of the union is everything. No decomposition of an
infinite-dimensional Hilbert space into infinitely many nonzero orthogonal
closed subspaces satisfies it (an algebraic sum contains only finitely
supported combinations). The chain decomposition therefore cannot be fed to
D4 as printed. The fix is local: D4's proof uses `hspan` exactly once, to
conclude that a vector orthogonal to all the pieces is orthogonal to
everything. Replacing that step gives

```lean
theorem PlufWO10.exists_hilbertBasis_of_orthogonal_family
    [TopologicalSpace.SeparableSpace E]
    (N : ℕ → Submodule ℝ E) (hcl : ∀ n, IsClosed ((N n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ N m, ∀ y ∈ N n, inner (𝕜 := ℝ) x y = 0)
    (hperp : (⨆ n, N n)ᗮ = ⊥) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E), ∀ i, ∃ n, b i ∈ N n
```

in `RequestProject/PlufWO10/Decomp.lean`, together with the `ℕ`-indexed
refinement `exists_hilbertBasis_nat_of_orthogonal_family` (which needs
`¬ FiniteDimensional ℝ E`, see §4). **Recommendation for the audit:** the
density form should replace, or be exported alongside, D4 in the harvested
API; D4 as printed has no applications of the kind Papers I–IV need.

## 4. Report-rather-than-repair: B2 and D1 as printed are false

**The contracts** (preserved verbatim in comments in the artifact):

```lean
theorem exists_basis_blocks_of_chain [SeparableSpace E]
    (hmono : ∀ k, M (k+1) ≤ M k) (hcl : ∀ k, IsClosed (M k : Set E)) :
    ∃ b : HilbertBasis ℕ ℝ E, ∀ k, ∃ S : Set ℕ, M k = PlufWO9.blockB b S

theorem chains_never_suffice [SeparableSpace E] (M : ℕ → Submodule ℝ E)
    (hmono : ∀ k, M (k+1) ≤ M k) (hcl : ∀ k, IsClosed (M k : Set E))
    (hne : ∀ k, M k ≠ ⊥) :
    ∃ b : HilbertBasis ℕ ℝ E, ∀ k, ∀ N : Submodule ℝ E, M k ≤ N →
      IntimateB b N
```

**Why they fail.** Both conclusions assert the existence of an `ℕ`-indexed
Hilbert basis of `E`, i.e. of an infinite orthonormal family; but the
hypotheses (nestedness, closedness, nonzero-ness, separability,
completeness) are all satisfied by finite-dimensional spaces. Concretely,
take `E = ℝ` — separable, complete, a real inner product space — and the
constant chain `M k = ⊤`. Then `M (k+1) ≤ M k`, each `M k` is closed, and
`M k ≠ ⊥` (as `(1 : ℝ) ∉ ⊥`), while `HilbertBasis ℕ ℝ ℝ` is empty: `b 0`
and `b 1` would be nonzero reals with `b 1 * b 0 = ⟪b 0, b 1⟫ = 0`. This is
formalized as

```lean
theorem no_hilbertBasis_nat_real : IsEmpty (HilbertBasis ℕ ℝ ℝ)
theorem exists_basis_blocks_of_chain_false : ¬ (∀ (E : Type) [...] ...)
theorem chains_never_suffice_false        : ¬ (∀ (E : Type) [...] ...)
```

where the two `_false` statements are the contracted statements with the
ambient section variables universally quantified, verbatim otherwise.

This is the same phenomenon the census already recorded for probe Q2
(`PlufWO7a.hilbertBasis_nat_of_decomposition_false`, with the same witness
`E = ℝ`): an `ℕ`-indexed `HilbertBasis` forces the space to be separable
*and* infinite-dimensional, and the second half has to be hypothesised.
WO-9 dealt with it by weakening the conclusion (an arbitrary countable
index type); B2 and D1 cannot do that, because a `blockB`-statement about
`Set ℕ` is what Proposition 6.1 asserts and what Proposition 5.5's
hypothesis negates — hence the hypothesis-side repair. The refutation of
the `ℕ`-index itself is isolated here as the reusable
`PlufWO10.no_hilbertBasis_nat_real : IsEmpty (HilbertBasis ℕ ℝ ℝ)`.

A notational point: the contract writes the separability instance as
`[SeparableSpace E]`, which does not elaborate without `open
TopologicalSpace`; the artifact writes `[TopologicalSpace.SeparableSpace E]`
throughout, which is the same class.

**The marked minimal repair.** One hypothesis is added to each,
`hinf : ¬ FiniteDimensional ℝ E`, and nothing else changes; the repaired
theorems carry the contracted names. This is minimal in the sense that it
is exactly what is missing: for a separable **infinite-dimensional** real
Hilbert space the construction goes through, and the hypothesis is
implied by any statement of the paper's standing assumption on the ambient
space. It is automatic in the intended application: `PlufWO1.H = ℓ²(ℕ; ℝ)`
is separable and infinite-dimensional, and E1 — which is stated in `H` — is
unaffected.

**Separability (the question the work order asks about B2).** It is
contracted as a hypothesis, as instructed, and it is automatic in the
intended application (`PlufWO1.H` is separable). It is *not* implied by the
chain hypotheses in general, so it must stay in the statement of the
general form.

## 5. The `IntimateB` reconciliation

`PlufWO10.IntimateB b M` and `PlufWO5.Intimate M` agree at the standard
basis of `H`, and the reconciliation is one `simp` over WO-9's agreement
lemma `PlufWO9.blockB_stdBasis_eq` (no isometry, no transport):

```lean
theorem intimateB_stdHilbertBasis_iff (M : Submodule ℝ PlufWO1.H) :
    IntimateB PlufWO9.stdHilbertBasis M ↔ PlufWO5.Intimate M
```

Since `blockB stdHilbertBasis S = PlufWO1.block S` and the two definitions
are the same quantified disjunction over `A : Set ℕ`, the predicates are
pointwise equivalent; all WO-5/WO-6 results phrased with `PlufWO5.Intimate`
transfer to `IntimateB` at the standard basis by rewriting with this
lemma.

## 6. Design notes

* **A1's route.** Zorn (`zorn_subset_nonempty`) is run on the proper
  filters containing `π`, and Zorn-maximality is converted to
  `PlufWO6.IsPluf` through `PlufWO6.isPluf_of_criterion` — the smoother
  route the work order anticipated. The criterion's dichotomy is proved by
  exhibiting, for a closed `M` that neither belongs to the maximal filter
  `σ` nor meets a member of it trivially, the strictly larger proper filter
  `{K closed | ∃ N ∈ σ, M ⊓ N ≤ K}`. The chain step needs directedness only
  for the meet clause, as predicted.
* **A2's hypotheses.** `hinf` (finite intersections infinite-dimensional)
  is used only for singletons, to know that members of `R` are nonzero;
  `hdir` is used only for the meet clause. Both are retained in the
  contracted form. `hcl` is genuinely needed (the generated filter must
  consist of closed subspaces).
* **B2's basis.** The basis produced is not canonical: it is assembled from
  arbitrary Hilbert bases of the pieces. What is canonical is the index
  set: `S k = {i | b i ∈ M k}`, and `M k = blockB b (S k)` follows from the
  general recognition lemma `eq_blockB_of_basis_mem_or_orthogonal` — every
  basis vector lies in a piece, and each piece is either inside `M k` or
  orthogonal to it (`chainPieces_le_or_orthogonal`).
* **D1's nonemptiness.** The contract's `hne : ∀ k, M k ≠ ⊥` is used to
  make each `S k` nonempty, via `blockB_empty`; nonemptiness of `S k` is
  what `intimateB_blockB` consumes.

## 7. Axiom audit

`#print axioms` is emitted in `PlufWO10.lean` for every contract theorem
(including E0, the two counterexamples and the `IntimateB` reconciliation).
Every line reports exactly

```
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `admit`, `axiom` or `native_decide` anywhere in
`PlufWO10.lean` or `PlufWO10/Decomp.lean`.

## 8. Note for WO-11 / WO-12

* `blockB_inf_blockB` is exported on its own, as instructed, together with
  the further block identities `blockB_mono`, `blockB_univ`,
  `blockB_empty`, `blockB_ne_bot`, which are what a lattice-level argument
  at an arbitrary basis needs.
* WO-12's ω₁-recursion can quote E0 (`diagonalizableB_iff_intimateB`) at an
  arbitrary basis, and A1/A2 for the extension steps: `exists_pluf_extension`
  takes a proper filter, `exists_pluf_of_directed` a directed family with
  infinite-dimensional finite intersections.
* The density variant of D4 (§3) is the form to use whenever a basis is to
  be built from an orthogonal decomposition.
