# WO-2 report — pluf project (Feldman–Wilce), Parts D, E, F

Artifact: `RequestProject/PlufWO2.lean` (namespace `PlufWO2`), built on top of the
WO-1 project (`RequestProject/PartA.lean`, `PartB.lean`, `PartC.lean`,
`PlufWO1.lean`), all four of which are included unmodified.

Status: **all required items proved**. No `sorry`, `admit`, `axiom` or
`native_decide` anywhere in the artifact. Every contract theorem's
`#print axioms` output is `[propext, Classical.choice, Quot.sound]` (whitelist).
WO-1's sixteen theorems are green, verbatim, with their audit unchanged.

## 1. Census (Mathlib API, feasibility, statement concerns)

| Item | Needed API | Present in the pinned Mathlib? | Feasibility |
|---|---|---|---|
| D1 | `Memℓp`/`memℓp_gen_iff`, `Summable.countable_support` | yes | routine |
| D2 | `LinearMap.mkContinuous`, `lp.norm_apply_le_norm` | yes | routine (WO-1's proof transports verbatim) |
| D3 | `Submodule.mem_iInf`, `LinearMap.ker`, `isClosed_biInter` | yes | routine |
| D4 | `lp.single_apply` | yes | routine |
| E1 | `ContinuousLinearMap.adjoint` (needs `CompleteSpace (lp _ 2)`, available), `adjoint_inner_right`, `lp.inner_single_right` | yes | moderate |
| F2 | `Submodule.starProjection` and its API (`starProjection_apply_mem`, `sub_starProjection_mem_orthogonal`, `starProjection_apply_eq_zero_iff`, `orthogonal_orthogonal`), `lp.hasSum_single`, `ContinuousLinearMap.hasSum`, `IsClosed.mem_of_tendsto` | yes | moderate; the one analytic point is `lp.hasSum_single`, which supplies the ℓ²-expansion directly |
| F3 | — | — | immediate from F2 |

Statement concerns (report-rather-than-repair): **none**. Every statement in the
contract file `PlufWO2.lean` is true as written and is proved exactly as stated,
with the two binder adjustments recorded in §3 below (both explicitly licensed by
the work order). In particular the strict-order diagonal intersection in `DiagInt`
is exactly what E1 needs, and symmetrizing over `α < β` and `β < α` via the
adjoint works as the docstring predicts.

## 2. Item-by-item

* **D1 `countable_supp`** — `Memℓp x 2` unfolds (via `memℓp_gen_iff`) to
  summability of `α ↦ ‖x α‖ ^ (2:ℝ)`; `supp x` is literally the support of that
  function, and `Summable.countable_support` finishes.
* **D2 `coordCLM` / `coordCLM_apply`** — coordinate evaluation as a linear map
  `coordL`, made continuous with bound `1` from `lp.norm_apply_le_norm`;
  `coordCLM_apply` is `rfl`.
* **D3 `block`, `mem_block_iff`, `isClosed_block`** — `block S` is the infimum of
  the kernels of `coordL α` for `α ∉ S`; closedness is a `biInter` of preimages of
  `{0}` under the continuous functionals.
* **D4 `evec_mem_block`** — glue, plus the converse `evec_mem_block_iff`
  (`evec α ∈ block S ↔ α ∈ S`) and monotonicity `block_mono`, both stated for
  reuse in Part F.
* **E1 `exact_paving`** — as in the docstring: `c α = supp (T (evec α)) ∪
  supp (Tᵃᵈʲ (evec α))` is countable by D1, so `(c α)ᶜ ∈ U` by `CountableSmall`;
  `S = {β | ∀ α < β, β ∈ (c α)ᶜ}` lies in `U` by `DiagInt`. For `α, β ∈ S` with
  `α ≠ β`: if `α < β` then `β ∉ supp (T (evec α))` gives
  `⟪T (evec α), evec β⟫ = (T (evec α)) β = 0`; if `β < α` then
  `⟪T (evec α), evec β⟫ = ⟪evec α, Tᵃᵈʲ (evec β)⟫ = (Tᵃᵈʲ (evec β)) α = 0`.
* **F1** — inlined, as the work order permits, in the form of the
  coordinate-rigidity lemma `inner_eq_coord_mul`.
* **F2 `exact_dichotomy`** — route taken: **the coordinate-rigidity functional**
  (WO-1's C1 style), *not* the `tsum`-of-squared-norms computation. Concretely,
  `hasSum_coord_smul` pushes the ℓ²-expansion `x = ∑' β, x β • evec β`
  (`lp.hasSum_single`) through a continuous functional; applying it to
  `f = ⟪P (evec α), ·⟫` for `x ∈ block S₀` leaves a single surviving term, giving
  `⟪P (evec α), x⟫ = x α * ⟪P (evec α), evec α⟫` (lemma `inner_eq_coord_mul`).
  With `P = P_{Wᗮ}` and `S₀ ∈ U` from E1, put `S₁ = {α ∈ S₀ | evec α ∈ W}`.
  If `S₁ ∈ U` then `block S₁ ≤ W` by `block_le_of_evec_mem` (the ℓ²-expansion
  again, with partial sums in `W` and `W` closed). Otherwise `S₀ \ S₁ ∈ U`, and
  for `x ∈ W ⊓ block (S₀ \ S₁)` the left side vanishes (`P (evec α) ∈ Wᗮ`) while
  `⟪P (evec α), evec α⟫ = ‖P (evec α)‖² ≠ 0` (as `evec α ∉ W = Wᗮᗮ`, using
  closedness of `W`), so every coordinate of `x` is `0`, i.e. `x = 0`.
  No norm computation and no cross-term bookkeeping is needed.
* **F3 `block_filter_decides`** — immediate repackaging of F2.

## 3. D2/D3 refactoring decision, and binder decisions

* **Refactoring choice (required report):** *fresh κ-versions in `PlufWO2`*;
  WO-1's Part B is left byte-for-byte untouched. Rationale: `PlufWO1.block` and
  `PlufWO1.coordCLM` are consumed by Part B's `thin` and by all of Part C
  (`closure_span_inter_block`, `noblock`), where the ℕ-specific
  `constraintVec` machinery is interleaved with them; generalizing the index type
  in place would have meant re-elaborating those proofs against a new signature
  for no mathematical gain, whereas the κ-versions here are four short
  definitions and three short proofs. The two notions agree definitionally at
  `κ = ℕ` (same infimum-of-coordinate-kernels presentation), so nothing is lost
  if a later WO wishes to unify them.
* **`[WellFoundedLT κ]`** is unused throughout Part D–F (only the linear order
  enters, through the strict order in `DiagInt`), so it is dropped from the
  section variables, as the work order licenses ("omit freely, as in WO-1's A4").
* **`[LinearOrder κ]`** is omitted (`omit ... in`) from the order-free Part D
  items, and retained where `evec` needs decidable equality on `κ` or where the
  order is actually used.

## 4. Axiom audit

`RequestProject/PlufWO2.lean` imports `RequestProject.PlufWO1`, so it is now the
root file and building it re-runs both audits. The WO-2 block prints

```
PlufWO2.countable_supp        -- D1
PlufWO2.coordCLM_apply        -- D2
PlufWO2.mem_block_iff         -- D3
PlufWO2.isClosed_block        -- D3
PlufWO2.evec_mem_block        -- D4
PlufWO2.exact_paving          -- E1
PlufWO2.exact_dichotomy       -- F2
PlufWO2.block_filter_decides  -- F3
```

each with `depends on axioms: [propext, Classical.choice, Quot.sound]`.
