# WO-1 (pluf project) — census and item-by-item report

**Toolchain:** `leanprover/lean4:v4.28.0` with the matching Mathlib release.

**Artifact:** `RequestProject/PlufWO1.lean` (root, imports everything and runs
the axiom audit) together with

| file | contents |
|---|---|
| `RequestProject/PartA.lean` | A1–A4 |
| `RequestProject/PartB.lean` | B1a–B1d, B2 |
| `RequestProject/PartC.lean` | C1, C2 |

**Closure discipline:** no `sorry`, `admit`, `axiom` or `native_decide` occurs
anywhere in the artifact. `#print axioms` is run on every contract theorem in
the root file; every one reports exactly
`[propext, Classical.choice, Quot.sound]`.

**Status:** all items — A1, A2, A2′, A3, A3′, A4, B1a–B1d, B2, C1, C2 —
are **proved**, C1 in the contract's closed-span form. Three statements
carry a noted restatement, all of them universe bookkeeping in Part A
(items A2, A2′, A3); no mathematical content was altered, weakened, or
supplemented with new hypotheses.

---

## 1. Census

### Part A — σ-Q-point combinatorics

| item | relevant Mathlib API | assessment | statement-level concerns |
|---|---|---|---|
| A1 `not_mem_union_of_not_mem` | `Ultrafilter.union_mem_iff` | routine | none |
| A2 `sigmaQ_of_partition_selectors` | `Set.range`, `Set.InjOn` | routine | **universe**: see §2 |
| A2′ `partition_selectors_of_sigmaQ` | `wellFounded_lt`, `WellFounded.min`, `WellFounded.min_mem`, `WellFounded.not_lt_min`, `Set.Countable.mono` | moderate | `ι` liftable to `Type*` |
| A3 `minima_mem_of_fodor` | `Ultrafilter.compl_mem_iff_notMem`, `Filter.mem_of_superset` | moderate | `ι` liftable to `Type*` |
| A3′ `sigmaQ_of_fodor` | — (A2 + A3) | routine | inherits A2's universe note |
| A4 `exists_transversal_not_mem` | `Set.disjoint_left`, `Ultrafilter.inter_mem`, `Ultrafilter.empty_notMem` | routine | none; the order hypotheses on `κ` are unused (`omit`ted) |

No large-cardinal machinery is used: Fodor and countable-set avoidance appear
only as hypotheses, exactly as required.

### Part B — witness subspace and thinness

| item | relevant Mathlib API | assessment | statement-level concerns |
|---|---|---|---|
| B1a `constraintVec` | `lp`, `Memℓp`, `memℓp_gen`, `Set.indicator`, `summable_geometric_of_lt_one`, `Summable.of_nonneg_of_le`, `Real.rpow_natCast` | routine | none |
| B1b `block`, `mem_block_iff` | `LinearMap.ker`, `Submodule.mem_iInf` | routine | none |
| B1c `isClosed_block` | `LinearMap.mkContinuous`, `lp.norm_apply_le_norm`, `isClosed_biInter`, `isClosed_eq` | routine | none |
| B1d `inner_constraintVec_eq_zero_of_disjoint` | `lp.inner_eq_tsum`, `tsum_congr`, `tsum_zero` | routine | none |
| B2 `thin` | `innerSL`, `LinearMap.ker_eq_bot`, `LinearMap.rank_le_of_injective`, `rank_self` | moderate | none |

Mathlib has no ready-made coordinate functional on `lp` (there is no `lp.proj`),
so `coordL` / `coordCLM` are built here from `lp.norm_apply_le_norm`.

### Part C — stretch

| item | relevant Mathlib API | assessment | statement-level concerns |
|---|---|---|---|
| C1 `closure_span_inter_block` | `Submodule.topologicalClosure`, `Submodule.topologicalClosure_minimal`, `Submodule.isClosed_topologicalClosure`, `ContinuousLinearMap.isClosed_ker`, `Submodule.starProjection`, `Submodule.sub_starProjection_mem_orthogonal`, `Submodule.starProjection_apply_mem`, `IsClosed.completeSpace_coe`, `inner_self_eq_zero` | moderate–hard | proved in the contract (closed-span) form; the weakening allowed by the work order was **not** needed |
| C2 `noblock` | `lp.single`, `lp.single_apply`, `lp.inner_single_left`, `lp.ext`, `Submodule.span_empty`, `Ultrafilter.compl_mem_iff_notMem` + A1, A4, C1 | moderate | none |

---

## 2. Restatements (Part A universes only)

The contract writes the partition index `ι` in `Type` while `κ : Type*`.

* **A2** (`sigmaQ_of_partition_selectors`). Here `ι` occurs in a *hypothesis*,
  and the partition the proof must feed to that hypothesis is the fiber
  partition of `g : κ → κ`, indexed by `↥(Set.range g) : Type u`. With `ι`
  pinned to `Type` and `κ` arbitrary, the hypothesis is simply never applicable
  to the object the proof needs, so the statement is proved with the hypothesis
  quantified over `ι : Type u`, `u` the universe of `κ`. For `κ : Type` this is
  verbatim the contract statement, and that instance is recorded separately as
  `sigmaQ_of_partition_selectors₀` (proved, with the contract's `∀ {ι : Type}`
  hypothesis). Nothing else about the statement changed.
* **A2′** (`partition_selectors_of_sigmaQ`) and **A3** (`minima_mem_of_fodor`).
  Here `ι` is universally quantified in the *conclusion* direction (it is an
  implicit argument of the theorem), so raising `Type` to `Type*` is a free
  strengthening; it is what makes A3′ available for `κ : Type*`. The contract
  statements are the `Type`-instances of these.

No other statement in the artifact deviates from the contract; a textual diff
of the theorem signatures against `PlufWO1.lean` as shipped shows differences
only in the three lines described above (plus the `def`s B1a/B1b, which the
contract left as `sorry` to be supplied).

---

## 3. Item-by-item report

### A1 — `not_mem_union_of_not_mem` — **proved**
`Ultrafilter.union_mem_iff` is in Mathlib; one line.

### A2 — `sigmaQ_of_partition_selectors` (+ `sigmaQ_of_partition_selectors₀`) — **proved with noted restatement (universe only)**
Apply the hypothesis to the fiber partition indexed by `↥(Set.range g)`;
disjointness, countability, nonemptiness and covering are immediate, and the
selector property of `S` is exactly `Set.InjOn g S`.

### A2′ — `partition_selectors_of_sigmaQ` — **proved** (`ι` lifted to `Type*`)
Via the shared construction `exists_piece_min_fun`: a choice function
`idx : κ → ι` picking a piece containing `x` (unique by disjointness) and
`g x = min (P (idx x))` given by well-foundedness of `<`. `g` is
countable-to-one (a nonempty fiber sits inside a single piece), so σ-Q-ness
gives `S ∈ U` on which `g` is injective; `g` is constant on pieces, hence `S`
meets each piece at most once.

### A3 — `minima_mem_of_fodor` — **proved** (`ι` lifted to `Type*`)
The paper argument, verbatim: with `g` as above, `M = {x | g x = x}` is the set
of piece-minima. If `M ∉ U` then `Mᶜ ∈ U` and `g` is regressive there
(`g x ≤ x` always, `≠` off `M`), so Fodor yields `y` with `{x | g x = y} ∈ U`;
that set is countable, contradicting `hcc`. And `M` is a partial selector,
since on a piece `g` is constant.

### A3′ — `sigmaQ_of_fodor` — **proved**
A3 supplies the hypothesis of A2.

### A4 — `exists_transversal_not_mem` — **proved**
Choose `a i ≠ b i` in `σ i`. `range a` and `range b` are transversals and are
disjoint (within a piece by `a i ≠ b i`, across pieces by disjointness of the
`σ i`), so they cannot both lie in `U`. The `LinearOrder`/`WellFoundedLT`
instances on `κ` are unused and are `omit`ted.

### B1a — `constraintVec`, `constraintVec_apply`, `constraintVec_ne_zero` — **proved**
`constraintVec A` is the `lp` element with underlying function
`Set.indicator A (fun n => (2 ^ (n+1))⁻¹)`; membership is `memℓp_gen` plus the
comparison `‖·‖² ≤ (1/4)^(n+1) ≤ (1/4)^n` against the geometric series
(`memlp_constraint`). `constraintVec_apply` is the contract's `if`-form.

### B1b — `block`, `mem_block_iff` / `W`, `mem_W_iff` — **proved**
`block S = ⨅ n ∈ Sᶜ, LinearMap.ker (coordL n)`, an intersection of kernels of
coordinate functionals, as suggested; the membership characterization is the
contract's. `mem_W_iff` is `Submodule.mem_iInf` plus `real_inner_comm` (the
contract states the inner product in the order `⟪x, constraintVec (A k)⟫`,
`W` is defined via `innerSL ℝ (constraintVec (A k))`).

### B1c — `isClosed_block` — **proved**
The coordinate functionals are continuous (`coordCLM`, bound `1` from
`lp.norm_apply_le_norm`), and `block S` is the corresponding intersection of
closed sets.

### B1d — `inner_constraintVec_eq_zero_of_disjoint` — **proved**
`lp.inner_eq_tsum` and termwise vanishing.

### B2 — `thin` — **proved**
On `R ⊓ block (A k)` the functional `x ↦ ⟪constraintVec (A k), x⟫` is injective:
an element of its kernel is orthogonal to `constraintVec (A j)` for every `j`
(for `j = k` by assumption, for `j ≠ k` by B1d and disjointness of the pieces),
hence lies in `R ⊓ W A = ⊥`. `LinearMap.rank_le_of_injective` then bounds the
rank by `Module.rank ℝ ℝ = 1`.

### C1 — `closure_span_inter_block` — **proved in the contract (closed-span) form**
Two ingredients.

1. *Coordinate rigidity* (`coord_smul_eq_inner_smul`): for `n ∈ supp (ρ i)`, the
   continuous functional `z ↦ ‖ρ i‖² zₙ − (ρ i)ₙ ⟪z, ρ i⟫` kills every `ρ j`
   (for `j = i` trivially, for `j ≠ i` because `(ρ j)ₙ = 0` and `ρ j ⊥ ρ i`),
   hence kills the closed span. This replaces the orthonormal-expansion route
   suggested in the work order and avoids Hilbert-space series API entirely.
2. *Projection*: for `x` in the closed span and in `block S`, rigidity forces
   `⟪x, ρ i⟫ = 0` whenever `supp (ρ i) ⊄ S`. Writing `K` for the right-hand
   side (a closed, hence complete, subspace) and `y = x − starProjection K x`,
   the vector `y` is orthogonal to *every* `ρ i` — to the good ones because
   `y ∈ Kᗮ`, to the bad ones because both `x` and `starProjection K x` are —
   while `y` lies in the closed span; so `⟪y, y⟫ = 0` and `x = starProjection K x ∈ K`.

The reverse inclusion is `Submodule.topologicalClosure_minimal` twice.
The permitted algebraic-span weakening was not used.

### C2 — `noblock` — **proved**
Exactly the sketched assembly. Vectors with singleton support are nonzero
multiples of basis vectors (`eq_smul_evec_of_supp_singleton`), so if two points
`n ≠ m` of one piece `A k` carried singleton supports, then
`v = 2^{n+1}·eₙ − 2^{m+1}·eₘ` would be a nonzero element of `R ⊓ W A`
(orthogonal to `constraintVec (A k)` by the explicit weights, to the other
`constraintVec (A l)` because `n, m ∉ A l`) — contradiction. Hence the
singleton-support points `D_s` form a partial selector and `D_s ∉ U`. The
remaining generators have at least two support points, so A4 gives a
transversal `D₁ ∉ U`; `D = D_s ∪ D₁ ∉ U` by A1 meets every support, so
`S = Dᶜ ∈ U` contains no support, the generator set of C1's right-hand side is
empty, and C1 gives `R ⊓ block S = ⊥`.

Two contract hypotheses turned out to be unnecessary and were kept anyway
(reported here, not repaired): `hneA` and `hcover`. Likewise `hρ` is
unnecessary in C1.
