# WO-5 report — pluf project (Feldman–Wilce, Paper II, §§2–5)

Artifact: `RequestProject/PlufWO5.lean` and the modules
`RequestProject/PlufWO5/{Basic,PartA,PartB,PartC,PartD,PartE}.lean`.
Build: `lake build RequestProject.PlufWO5` (green). No `sorry`, no
`admit`, no `axiom`, no `native_decide` anywhere in the artifact. All 16
contract theorems of Parts A–E carry a `#print axioms` line in
`RequestProject/PlufWO5.lean`; each reports exactly
`[propext, Classical.choice, Quot.sound]`. The WO-1–WO-4 base is
untouched and its 65 audits still run and remain green through the
import chain.

---

## 1. Census

### 1.1 Reused from the base (no re-derivation)

`PlufWO1.H`, `PlufWO1.evec`, `PlufWO1.evec_apply`, `PlufWO1.block`,
`PlufWO1.mem_block_iff`, `PlufWO1.isClosed_block`,
`PlufWO1.constraintVec`, `PlufWO1.constraintVec_apply`,
`PlufWO1.constraintVec_ne_zero`,
`PlufWO1.inner_constraintVec_eq_zero_of_disjoint`, `PlufWO1.W`,
`PlufWO1.mem_W_iff`, `PlufWO1.IsPartialSelector`,
`PlufWO4.inter_infinite_iff_mem`, `PlufWO4.rank_le_of_le_block_finite`.

### 1.2 Mathlib coverage that was found and used

* `lp` API: `lp.memℓp`, `memℓp_gen`, `lp.inner_eq_tsum`,
  `lp.inner_single_left`, `lp.norm_rpow_eq_tsum`, `lp.coeFn_add/sub/smul`,
  `lp.ext`.
* Orthogonality: `Submodule.orthogonal`, `Submodule.mem_orthogonal`,
  `Submodule.inf_orthogonal_eq_bot`, `Submodule.orthogonal_orthogonal`,
  `Submodule.top_orthogonal_eq_bot`, `Submodule.bot_orthogonal_eq_top`,
  `Submodule.starProjection` and `Submodule.sub_starProjection_mem_orthogonal`,
  `orthonormal_iff_ite`.
* Dimension: `Module.Finite`, `Module.finrank`, `Module.finrank_pi`,
  `LinearMap.finrank_le_finrank_of_injective`,
  `LinearMap.finrank_range_add_finrank_ker`,
  `Submodule.comapSubtypeEquivOfLe`, `LinearEquiv.finrank_eq`.
* Ultrafilters: `Ultrafilter.union_mem_iff`,
  `Ultrafilter.finite_biUnion_mem_iff` (this is the lemma behind C1's
  "a `U`-set inside a finite union of pieces puts a piece in `U`"),
  `Ultrafilter.compl_mem_iff_notMem`, `Ultrafilter.mem_or_compl_mem`,
  `Ultrafilter.ofComplNotMemIff` (used to build the trace ultrafilter of
  E1), `Set.Infinite.exists_subset_card_eq`,
  `Set.infinite_of_injective_forall_mem`.

### 1.3 Missing from Mathlib and built here (`PlufWO5/Basic.lean`)

Coordinate-level infrastructure: `summable_sq`, `norm_sq_eq_tsum`,
`inner_evec_left`, `orthonormal_evec`; the coordinate restriction `restr`
with `restr_apply_of_mem/notMem`, `restr_mem_block`, `norm_restr_le`,
`inner_eq_inner_restr`, `norm_sq_restr_gt`, `exists_tail_norm_le`;
block calculus `block_univ`, `block_empty`, `block_mono`, `block_inter`,
`evec_mem_block`, `infinite_of_mem`, `isClosed_inf`; the
finite-dimensionality criteria `not_finite_of_orthonormal`,
`not_finite_of_orthogonal_family`, `not_finite_block`, `finite_block`,
`card_le_finrank_block`, `finite_of_trivial_on_finite_codim`,
`inf_ne_bot_of_not_finite`; and the codimension bridge
`finCodimIn_iff_finite_orthocomplement`.

### 1.4 Part F verdict

**Gated out** (see §4). Parts A–E are returned complete, together with the
assessment of Mathlib's `HilbertBasis` API requested by the work order.

---

## 2. Item-by-item report

### Part A — the zero–cofinite dichotomy

* **A1 `gliding_hump`** (Thm 2.1). Proved. The recursion is packaged as
  `exists_mem_vanishing_below` → `gliding_step` → `gliding_sequence` →
  `gliding_hump_rel`, the last being the *relative* form (inside an
  arbitrary block `block S₀`). A1 is `gliding_hump_rel` at `S₀ = univ`.
  The contract hypothesis `hW` (closedness) is retained as stated but is
  not consumed; this is noted in the theorem's docstring.
* **A2 `relativized_dichotomy`** (Cor 2.2). Proved. **Transport route
  (reported):** *no* isometry `block S₀ ≃ H` is constructed. Instead the
  gliding-hump recursion of A1 is run directly inside `block S₀`
  (`gliding_hump_rel`), which avoids transporting summability and tail
  estimates along an enumeration; the contract's quotient rendering of
  relative codimension is converted to the relative orthocomplement by
  `finCodimIn_iff_finite_orthocomplement`. The contract hypothesis `hS₀`
  is retained but not consumed.
* **A3 `dense_zero_set`** (Prop 4.2, second clause). Proved, immediately
  from A2.

### Part B — the block filter at ω

* **B1 `phiOmega_iff_finCodim`** (Lemma 3.2(a)). Proved. For (⇐) the
  paper's `V = (M ⊓ block S) ⊕ block Sᶜ` is rendered as
  `V = ((M ⊓ block S)ᗮ ⊓ block S)ᗮ`, which is manifestly closed and whose
  orthocomplement is `(M ⊓ block S)ᗮ ⊓ block S`, finite-dimensional by
  hypothesis.
* **B2 `addable_iff_infDim`** (Lemma 3.2(b)). Proved. The contract
  hypotheses `hcof` and `hM` are retained as stated but not consumed
  (noted in the docstring).
* **B3 `bot_not_phiOmega`**. Proved.

### `FinCodimIn` — kept verbatim

The contract's rendering

```lean
def FinCodimIn (W V : Submodule ℝ H) : Prop :=
  Module.Finite ℝ (↥V ⧸ (W ⊓ V).comap V.subtype)
```

is **kept exactly as contracted**; no restatement was needed, so B1, C1
and D3 are stated against the contract definition unchanged. All work
with it goes through the single bridge lemma

```lean
theorem finCodimIn_iff_finite_orthocomplement (W V : Submodule ℝ H)
    (hWV : IsClosed ((W ⊓ V : Submodule ℝ H) : Set H)) :
    FinCodimIn W V ↔ Module.Finite ℝ ↥((W ⊓ V)ᗮ ⊓ V)
```

(proved by exhibiting the linear isomorphism `(W ⊓ V)ᗮ ⊓ V ≃ V ⧸ (W ⊓ V)`
via the orthogonal projection onto `W ⊓ V`; only closedness of `W ⊓ V` is
used).

### Part C — Theorem 3.4

* **`isClosed_W`.** Proved: `W A` is an intersection of kernels of the
  continuous functionals `⟪constraintVec (A k), ·⟫`.
* **C1 `witness_not_mem`.** Proved. Via B1 it suffices that for every
  `S ∈ U` the relative codimension of `W A` in `block S` is infinite.
  The set `K = {k | (A k ∩ S).Nonempty}` of touched pieces is infinite:
  otherwise `S ⊆ ⋃_{k ∈ K} A k ∈ U` and `Ultrafilter.finite_biUnion_mem_iff`
  puts some `A k` in `U`, contradicting `hpieces`. The vectors
  `constraintVec (A k ∩ S)`, `k ∈ K`, are nonzero, pairwise orthogonal
  (disjoint supports) and lie in `(W A ⊓ block S)ᗮ ⊓ block S` — the
  orthogonality to `W A ⊓ block S` uses that, against a vector supported
  in `S`, `constraintVec (A k ∩ S)` and `constraintVec (A k)` are
  indistinguishable (`inner_constraintVec_inter`).
* **C2 `witness_infDim`.** Proved. **Pair organization (reported):** the
  pairs are built by a recursion that makes them *consecutive and
  separated* rather than merely "meeting in at most one point". At stage
  `i` the tail `S ∩ {n | gᵢ < n}` is still in `U` (this is where `hcof`
  is consumed, through `gt_mem`), so `hsel` supplies two distinct points
  `aᵢ < bᵢ` of that tail lying in a single piece `A k`; the recursion
  then sets `gᵢ₊₁ := bᵢ`. Consequently the four indices of any two
  distinct pairs are pairwise distinct, and the two-point witnesses
  `wᵢ = 2^(aᵢ+1) • e aᵢ − 2^(bᵢ+1) • e bᵢ ∈ W A ⊓ block S` are nonzero and
  *pairwise orthogonal*; infinite-dimensionality then follows from
  `not_finite_of_orthogonal_family` (no linear-independence computation
  is needed).
* **C3 `necessity`.** Proved: C1 together with B2 applied to C2.
* **C4 `decides_of_mathias`.** Proved: on the "always meets" side of the
  Mathias hypothesis, A2 applied inside `block S` cannot produce an
  infinite sub-block missing `W`, so `FinCodimIn W (block S)` holds and
  B1 gives `W ∈ Φ(U)`; on the "never meets" side, `block S` itself is a
  member of `Φ(U)` meeting `W` trivially. The derivation of `MathiasHyp`
  from selectivity is quarantined, as contracted.
* **Section variables.** Lean 4 does not auto-include section variables
  in the statement of a theorem that does not mention them, so each of
  C1–C3 is preceded by an explicit
  `include hdisj hne hcover hcof hpieces hsel in`; without it the
  statements would be about an unconstrained partition (and false).
  Contract hypotheses that turn out to be unnecessary are nevertheless
  retained as contracted: `hne`, `hcof`, `hsel` are unused in C1, and
  `hne`, `hcover`, `hpieces` are unused in C2 (both noted in the
  docstrings).

### Part D — Gowers's intimate subspace (Theorem 4.1)

Reindexing to 0-based is used throughout, as licensed:
`gowersU n = e n − ((n+2)/(n+1)) • e (n+1)` and
`gowersV n = (e (2n) + e (2n+1)) − ((n+2)/(n+1)) • (e (2n+2) + e (2n+3))`,
with `gowersX = ⋂ₙ ker ⟪gowersV n, ·⟫`.

* **D0.** `gowersV_apply_two_mul` (the duplication identity),
  `mem_gowersX_iff` (membership in coordinates: the pair sums
  `sₙ = x(2n) + x(2n+1)` satisfy `sₙ = ((n+2)/(n+1)) sₙ₊₁`) and
  `isClosed_gowersX` are proved.
* **D1 `gowersX_intimate`.** Proved. If some pair `{2i, 2i+1}` lies
  inside `A` (resp. inside `Aᶜ`) then `e (2i) − e (2i+1)` is a nonzero
  member of `X ⊓ block A` (resp. of `X ⊓ block Aᶜ`). Otherwise `A` is a
  transversal of the pairs, and the twisted weight vector
  `transversalVec a` (weight `1/(i+1)` on the chosen representative
  `aᵢ ∈ {2i, 2i+1} ∩ A`) is a nonzero member of `X ⊓ block A`; its
  ℓ²-membership is proved from `∑ 1/(m+1)² < ∞`.
* **D2 `gowersX_dim_bound`.** Proved, **by a route different from the
  paper's echelon argument** (reported): for a finitely supported member
  of `X` a downward recursion on the relation `sₙ = ((n+2)/(n+1)) sₙ₊₁`
  (whose coefficient never vanishes) forces *all* pair sums to vanish
  (`gowersX_pairSum_eq_zero`), so such a vector satisfies
  `x(2k) = −x(2k+1)` and is determined by its values on the set
  `D = {m ∈ C | m even, m+1 ∈ C}` of complete pairs. The coordinate map
  `x ↦ (x m)_{m ∈ D}` is therefore injective and linear, giving
  `dim (X ⊓ block C) ≤ |D|`, while `D` and `D + 1` are disjoint subsets
  of `C`, giving `2|D| ≤ |C|`.
* **D3 `gowersX_no_finCodim`.** Proved by rank–nullity: if `X` had finite
  relative codimension `d` in `block S`, pick `C ⊆ S` with `|C| = 2d+1`;
  the composite `block C ↪ block S ↠ block S / (X ⊓ block S)` has kernel
  `X ⊓ block C`, so `|C| ≤ dim (block C) ≤ d + dim (X ⊓ block C) ≤ d + |C|/2`
  by D2, i.e. `2d + 1 ≤ 2d`.

### Part E — diagonalization

* **E1 `diagonalizable_iff_intimate`** (Thm 5.1). Proved. (⇒) uses
  `inf_mem` and `proper` only. (⇐) builds the trace filter
  `F = {S | block S ∈ π}` — its filter axioms come from the named package
  fields (`univ` from `finCodim_mem` at `⊤`, upward closure from
  `upward`, finite intersections from `inf_mem` through `block_inter`) —
  and upgrades it to an ultrafilter with `Ultrafilter.ofComplNotMemIff`:
  if neither `block S` nor `block Sᶜ` were in `π`, then `decides` would
  give `N, N' ∈ π` with `block S ⊓ N = ⊥ = block Sᶜ ⊓ N'`, and `N ⊓ N'`
  would violate intimacy; and `S, Sᶜ` cannot both be in `F` since
  `block S ⊓ block Sᶜ = block ∅ = ⊥ ∉ π`.
* **E2 — contract form is false; preserved verbatim and repaired.** The
  contract asked for

  ```lean
  (∃ V : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ V ↔ block S ∈ π) ↔
    (∃ U : Ultrafilter ℕ, ∀ M : Submodule ℝ H, PhiOmega U M → M ∈ π)
  ```

  Every member of `π` is closed (`PlufPackage.mem_closed`), whereas for
  *every* ultrafilter `U` there are non-closed subspaces `M` with
  `PhiOmega U M`. This obstruction is formalized as
  `exists_phiOmega_not_isClosed`: pick `S ∈ U` with `Sᶜ` infinite (one of
  the evens/odds is in `U`) and take
  `M = block S ⊔ span {e n : n ∈ Sᶜ}`; then `PhiOmega U M` (already
  `block S ⊓ ⊤ ≤ M`), `Mᗮ = ⊥` because `M` contains every basis vector,
  so if `M` were closed it would be `⊤` — but `constraintVec Sᶜ ∉ M`,
  since every element of the span part has finite support while
  `constraintVec Sᶜ` has all its `Sᶜ`-coordinates nonzero and `Sᶜ` is
  infinite. Hence the right-hand side of the contract form is false for
  every package family, and the equivalence would force "no package
  family is diagonalizable", which is not a theorem of this development.
  The contract statement is preserved verbatim in a comment in
  `PlufWO5/PartE.lean`, and the **marked minimal repair** restricts the
  right-hand quantifier to closed subspaces:

  ```lean
  (∃ U : Ultrafilter ℕ, ∀ M, IsClosed (M : Set H) → PhiOmega U M → M ∈ π)
  ```

  which is what the paper's proof uses, and is proved (forward: the trace
  ultrafilter, using `finCodim_mem`, `inf_mem`, `upward`; backward: `U`
  itself is the trace, using `proper` on `block S ⊓ block Sᶜ`).

---

## 3. Audit

`RequestProject/PlufWO5.lean` prints the axioms of the 16 contract
theorems A1, A2, A3, B1, B2, B3, C1, C2, C3, C4, D0 (`isClosed_gowersX`),
D1, D2, D3, E1, E2. Each reports
`[propext, Classical.choice, Quot.sound]` — inside the whitelist. The
WO-1–WO-4 audit lines run through the import chain and are unchanged.

---

## 4. Part F assessment (Propositions 5.5–5.6) — census verdict: **gate out**

Part F quantifies over arbitrary orthonormal bases, i.e. `HilbertBasis ι ℝ H`,
with basis-relative blocks `blockB b S = (span ℝ {b n | n ∈ S}).topologicalClosure`.
What Mathlib provides, and what is missing:

**Available.** `HilbertBasis` (as `ofRepr`, an isometry `E ≃ₗᵢ lp G 2`),
`HilbertBasis.mk` from an orthonormal family with topologically dense
span, `HilbertBasis.mkOfOrthogonalEqBot`, `HilbertBasis.coe_mk`,
`b.hasSum_repr`, `b.repr` and the `IsHilbertSum` API
(`IsHilbertSum.mk`, `IsHilbertSum.mkInternal`,
`OrthogonalFamily.linearIsometry`), plus `exists_hilbertBasis`.

**Missing, and needed by F1–F2.**

1. *ℕ-indexed bases.* `exists_hilbertBasis` returns a basis indexed by a
   *set* `w : Set E`, not by `ℕ`. F1 needs, for each closed subspace of
   the separable space `H`, a **countable** orthonormal basis; Mathlib
   has no lemma that an orthonormal set in a separable (or
   second-countable) inner product space is countable, so this must be
   built from scratch (the standard `‖x − y‖ = √2` separation argument
   against a countable dense set).
2. *Reindexing.* There is no `HilbertBasis.reindex` (transport of a
   `HilbertBasis` along an index equivalence) in the pinned Mathlib, and
   none of the `IsHilbertSum` lemmas assembles bases of an orthogonal
   family into a single basis of the whole space. F1's construction —
   bases of `⋂ Mᵢ`, of the successive differences `Mᵢ₊₁ ⊖ Mᵢ`, and of the
   complement of the top, concatenated into one ℕ-indexed basis —
   therefore requires: an internal-orthogonal-family version of
   `HilbertBasis.mk` (density of the span of the union), a sigma-type
   index with per-piece countable index sets of *varying, possibly
   finite* cardinality, and an explicit equivalence of that sigma type
   with `ℕ`, together with the bookkeeping identifying each `Mᵢ` with the
   block of the corresponding index segment.
3. *Basis-relative blocks.* `blockB` and its coordinate characterization
   (`x ∈ blockB b S ↔ ∀ n ∉ S, ⟪b n, x⟫ = 0`), its closedness, and the
   transfer of the results of Parts B–E from the standard basis to an
   arbitrary `b`, do not exist and would have to be developed from
   `b.hasSum_repr`. This alone duplicates most of `PlufWO5/Basic.lean` in
   basis-relative form.
4. F2 additionally needs a basis-relative restatement of `PlufPackage`
   and of E1, which is only meaningful once 1–3 exist.

Items 1–3 are a self-contained development of comparable size to the
whole of Parts A–E and are of independent value (they are also wanted for
WO-7). Following the census gate in the work order, Part F is therefore
**not** attempted here and no F-statements are added to the artifact;
Parts A–E are returned complete with this assessment.
