# WO-3 report — pluf project (Feldman–Wilce), Parts G, H, I

Artifact: `RequestProject/PlufWO3.lean` (root file; imports the WO-2 chain, so one
build re-runs the WO-1 and WO-2 audits as well).
Toolchain: `leanprover/lean4:v4.28.0`, Mathlib as pinned in the repository.

No `sorry`, `admit`, `axiom` or `native_decide` occurs anywhere in the artifact.
`#print axioms` for all 14 WO-3 contract theorems (and for the extra
counterexample theorem) reports only the whitelist
`propext, Classical.choice, Quot.sound`; the 24 prior theorems of WO-1 and WO-2
remain green with the same whitelist.

## Census

Carried over unchanged from the WO-2 artifact (`base/` of the tarball, copied
into `RequestProject/`): `PartA.lean`, `PartB.lean`, `PartC.lean`,
`PlufWO1.lean`, `PlufWO2.lean`, `Main.lean`. Nothing in them was edited.

Reused, not duplicated, from those files:

* `PlufWO2.Hk`, `evec`, `evec_apply`, `evec_mem_block`, `supp`, `block`,
  `mem_block_iff`, `block_mono`, `countable_supp`, `inner_evec_right`,
  `hasSum_coord_smul`, `inner_eq_coord_mul`, `exact_paving`,
  `block_filter_decides`, `DiagInt`, `CountableSmall`;
* `PlufWO1.IsPartialSelector`, and (as a template only) WO-1's Part B
  constraint-vector summability estimate `memlp_constraint` and its C2
  two-point witness technique, both transplanted to `κ`.

New in `PlufWO3.lean`: `CountablyComplete`, `PhiU`, `kConstraintVec`, `Wk`, the
14 contract theorems, four small specification lemmas for the constraint vector
(`kConstraintVec_apply`, `kConstraintVec_pos`, `kConstraintVec_eq_zero` and the
two directional halves of I3), one private construction (`cIdx`, the injection
into ℕ, with `cIdx_injOn` and `memlp_kConstraint`), and one report theorem
(`Wk_inf_block_eq_bot_iff_counterexample`).

Bookkeeping note (idiom, reported and free): several statements are proved under
`omit [LinearOrder κ]`, as the contract requires, while the reused WO-2 lemmas
`evec_apply`, `evec_mem_block`, `hasSum_coord_smul`, `inner_eq_coord_mul` carry
the order instance. Rather than duplicating those lemmas at a weaker typeclass,
their proofs are invoked under a locally introduced well-order
(`IsWellOrder.linearOrder WellOrderingRel`); the statements themselves mention no
order, so nothing about the contract statements changes and no extra hypothesis
is added.

## Item-by-item

**G1 `exists_ulim` — proved.** Route report: the bisection route of the docstring
is not needed, and neither is countable completeness. The ultralimit is produced
as `L = sSup {t | {α | t ≤ f α} ∈ U}`, which is nonempty (`-C` belongs) and
bounded above by `C`; for `ε > 0`, `{α | L - ε ≤ f α} ∈ U` because some `t > L-ε`
lies in the (downward closed) set, and `{α | f α < L + ε} ∈ U` because the
complementary set is not a member. **The hypothesis `hcc` is therefore unused**;
it is retained because the contract asks for it (this is the source of the
`unused variable hcc` warning).

**G2 `quadratic_flat` — proved.** Summability route (as requested): the set is
`S₀ ∩ {α | |d α − L| ≤ ε}` with `S₀` from `exact_paving` and
`d α = ⟪T (evec α), evec α⟫`. For `x` in the block:

* `hasSum_coord_smul` applied to the functional `⟪·, x⟫ ∘ T` gives
  `HasSum (fun β => x β * ⟪T (evec β), x⟫) ⟪T x, x⟫`; `inner_eq_coord_mul` with
  `P := T` on `S₀` turns each term into `(x β)² * d β` (off `S₀` the coordinate
  `x β` vanishes, so the identification is global);
* `lp.hasSum_norm` gives `HasSum (fun β => (x β)²) ‖x‖²`;
* the termwise bound `|(x β)²(d β − L)| ≤ ε (x β)²` (trivial where `x β = 0`,
  and from `|d β − L| ≤ ε` otherwise) plus `hasSum_le` in both directions gives
  the conclusion.

No operator-norm API is used and **no self-adjointness hypothesis is needed**.

**H1 `PhiU_upward`, `inf_mem_PhiU`, `bot_notMem_PhiU` — proved.** Properness uses
only nonemptiness of members of `U` together with `evec_mem_block`.

**H2 `iInf_mem_PhiU` — proved,** generically in the index type `ι`, exactly as
stated; choosing `S i ∈ U` with `block (S i) ≤ M i` and intersecting.

**H3 `PhiU_nonprincipal` — proved:** `(supp x)ᶜ ∈ U` by D1 plus `CountableSmall`,
and `block ((supp x)ᶜ)` is then a member of `Φ(U)` excluding every nonzero
vector.

**H4 `PhiU_decides` — proved** by unfolding `block_filter_decides`.

**I1 `kConstraintVec`, `supp_kConstraintVec`, `kConstraintVec_nonneg`,
`mem_Wk_iff`, `isClosed_Wk` — proved.** The injection `g : P₀ → ℕ` comes from
`countable_iff_exists_injOn`; the coordinates are `2^{-(g α + 1)}` on `P₀` and `0`
off it, `Memℓp` by comparison of the squared coordinates with the geometric
series `∑ 4^{-(n+1)}` composed with the injection
(`summable_subtype_iff_indicator` plus `Summable.comp_injective`). **I1c needed no
restatement**: with this normalization the coordinates are nonnegative — indeed
strictly positive exactly on `P₀`, which is recorded separately as
`kConstraintVec_pos` and used for the two-point witness.

**I2 `not_block_le_Wk`, `Wk_notMem_PhiU` — proved** as sketched.

**I3 — the contract statement is FALSE as written; repaired and reported.**
Without a covering hypothesis, direction (⇐) fails. Counterexample, formalized as
`Wk_inf_block_eq_bot_iff_counterexample`: take `κ = ℕ`, `ι = Unit`, `P _ = {0}`
(countable, nonempty, trivially pairwise disjoint) and `S = {1}`. Then
`S ∩ P i = ∅` is a subsingleton, so `S` is a partial selector, yet `evec 1` is a
nonzero vector of both `block S` and `Wk P h` (its only nonzero coordinate sits
off `P i`), so `Wk P h ⊓ block S ≠ ⊥`.

The repair adds `(hcover : (⋃ i, P i) = univ)`, which is available at every use
site (in particular in I4); the original statement is quoted verbatim in a
comment above the repaired theorem. Both directions are also available
separately:

* `selector_of_Wk_inf_block_eq_bot` (⇒, no cover needed): the two-point witness
  `c β • evec α − c α • evec β` for `α ≠ β` in `S ∩ P i`;
* `Wk_inf_block_eq_bot_of_selector` (⇐, cover needed): the single surviving term
  `x α * c α ≠ 0` of the constraint of the piece containing a nonzero coordinate,
  obtained as a `hasSum_single` in the WO-2 style.

With the cover present, the nonemptiness hypothesis `hne` is not used by either
direction; it is retained because the contract asks for it (second `unused
variable hne` warning).

**I4 `kappa_witness` — proved,** by assembling I2 and I3(⇒) with `PhiU`
membership. Here too `hne` is unused and retained.

## Remaining warnings

Only three `unused variable` warnings in `PlufWO3.lean` (`hcc` in G1, `hne` in I3
and I4), each a contract hypothesis kept deliberately and documented in the
corresponding docstring, plus three pre-existing warnings in the untouched
`PartC.lean` of the base artifact.
