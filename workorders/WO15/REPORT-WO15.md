# Report — Work Order 15 (pluf project, Feldman–Wilce)

**Scope.** Paper I, Theorem 5.7 (under CH, a nonprincipal pluf every member of
which is ample — hence no round slices for `T`) and Proposition 5.9 (the set of
`φ(T)` over the state face is the whole interval `[1/16, 1]`). Contract file:
`RequestProject/PlufWO15.lean`.

**Verdict: the commission closes.** Every contracted item is delivered and
proved. One contracted statement, A2, is **false as printed** and was repaired
by the marked minimal repair (`[Nonempty ι]`); the printed form is preserved
verbatim in a comment and its refutation is machine-checked
(`admissible_iUnion_counterexample`). Everything else is proved exactly as
printed. There is no `sorry`, `admit`, `axiom` or `native_decide` in the new
material; CH appears only as a hypothesis. `#print axioms` for every contract
theorem reports exactly `[propext, Classical.choice, Quot.sound]`. The base
tree is untouched — `diff -r` against the supplied `base/RequestProject`
reports only the two new entries `PlufWO15.lean` and `PlufWO15/` — so all 233
prior theorems remain green and `PlufWO7a.lean` was neither edited nor deleted.
Full-project build: `Build completed successfully (8084 jobs)`.

## Census

| Item | Contract statement | Verdict |
|---|---|---|
| A1 `exists_admissible_decides` | TRUE as printed | proved |
| A2 `admissible_iUnion` | **FALSE as printed** (empty index) | repaired (`[Nonempty ι]`) and proved; refutation recorded |
| B1 `exists_admissible_chain` | TRUE as printed | proved |
| C1 `exists_pluf_all_ample` | TRUE as printed | proved |
| C2 `not_rsp_of_all_ample` | TRUE as printed | proved |
| C2′ `radii_of_all_ample` | (docstring clause, not printed) | proved as a separate statement |
| D1 `face_apply_mem_Icc` | TRUE as printed | proved |
| D2 `exists_face_state_apply_eq` | TRUE as printed | proved |
| D3 `face_values_eq_Icc` | TRUE as printed | proved |

Unused binders kept only because the contract prints them: `hσ` and `hne` in
C2 (the constant-gap argument needs neither), and the `hM : IsClosed …`
binders inside the face conditions of D1–D3, which are part of the contracted
shape of "state of the face".

## Files

New material lives in `RequestProject/PlufWO15/`:

* `Basic.lean` — the two contracted definitions `Admissible` and `Decides`
  (docstrings verbatim), plus `admissible_singleton_top` and
  `admissible_adjoin`, the common shape of Cases II and III.
* `PartA.lean` — A1, the A2 refutation, and A2.
* `PartB.lean` — the history `AccFam`, the stage predicate `StageOK`, the
  admissibility of the history, and B1.
* `PartC.lean` — the room lemma `inf_orthogonal_singleton_ne_bot`, C1 and C2.
* `PartD.lean` — the Rayleigh calculus for `k • T` along an all-ample family,
  D1, D2 and D3.

`RequestProject/PlufWO15.lean` is the contract file: it keeps the contracted
statements and docstrings and discharges them from the part files. As in
WO-12, the duplicate `abbrev H` is dropped (it comes from
`PlufWO15/Basic.lean`), the two contracted definitions live in
`PlufWO15/Basic.lean` so that the part files can be phrased in terms of them,
and `include hCH` is placed before B1 so that CH really appears in its
signature — it does.

## The `Admissible` / `⊤` packaging decision (requested)

`⊤ ∈ F` is **carried as a side hypothesis**, not added as a field of
`Admissible`. Reason: the only place it is needed is the observation that
`p = ⊤ ⊓ p` (Case II) and `R = ⊤ ⊓ R` (Case III) join the new family, and the
recursion maintains it for free because the history is
`{⊤} ∪ ⋯`. Keeping `Admissible` at the four contracted fields also keeps A2's
hypotheses in the printed shape. The adjoining step is factored once:

```lean
admissible_adjoin (hF : Admissible F) (htop : ⊤ ∈ F) (X) (hX : ∀ g ∈ F, Ample (g ⊓ X)) :
  Admissible (F ∪ (fun g => g ⊓ X) '' F) ∧ ⊤ ∈ … ∧ F ⊆ … ∧ X ∈ …
```

Case II instantiates it at `X = p` (case hypothesis supplies `hX`), Case III at
`X = R` (clause (ii) of the blocking lemma supplies `hX`, modulo `inf_comm`).
Meet-closure of the enlarged family is the three associativity computations
`M ⊓ (h ⊓ X) = (M ⊓ h) ⊓ X`, `(g ⊓ X) ⊓ N = (g ⊓ N) ⊓ X`,
`(g ⊓ X) ⊓ (h ⊓ X) = (g ⊓ h) ⊓ X`. Case III's call to
`PlufWO14.blocking_lemma` supplies `hGN` — the negation of Case I — as the
contract requires, even though WO-14 flags it unused; directedness is
`P = M ⊓ M'` from meet-closure.

## The A2 form (requested), and the repair

**Form chosen:** a countable *and nonempty* index type with the contracted
directedness hypothesis, i.e. exactly the printed statement plus
`[Nonempty ι]`. Part B consumes it at `ι = Option {p // p < a}`: the `none`
branch contributes `{⊤}`, which makes the index nonempty at stage `0` and at
every limit stage, and directedness among the `some` branches is monotonicity
of the chain at `max p q`.

**Why the repair is forced.** For `ι` empty, `⋃ i, F i = ∅`: the three
hypotheses hold vacuously, but `∅` fails the `nonempty` field of `Admissible`
and does not contain `⊤`. This is machine-checked as
`PlufWO15.admissible_iUnion_counterexample`.

## B1: the recursion as implemented (requested)

WO-12's pattern is followed **with no divergence** in structure:

```lean
set Φ : (a : Ordinal.{u}) → ((p : Ordinal.{u}) → p < a → Set (Submodule ℝ H)) → …
  fun a ih => if hex : ∃ F, StageOK ({⊤} ∪ {M | ∃ p, ∃ hp : p < a, M ∈ ih p hp}) (sub a) F
              then hex.choose else {⊤}
set c := (inferInstanceAs (WellFoundedLT Ordinal.{u})).wf.fix Φ
have hceq : ∀ a, c a = Φ a (fun p _ => c p) := fun a => WellFounded.fix_eq _ Φ a
```

with the stage invariant `∀ a < ω₁, StageOK (AccFam c a) (sub a) (c a)` proved
afterwards by `Ordinal.induction`; no successor/limit split. `AccFam` (the
history, `{⊤} ∪ {M | ∃ p < a, M ∈ c p}`) and `StageOK` are top-level
definitions, so identifying `c a` with the chosen witness is `dif_pos`.
`sub a` is the `a`-th closed subspace from `PlufWO11.exists_enum_closedSubspaces`
(with `⊤` outside `ω₁`, so that closedness of the stage datum is unconditional).

**One divergence, in the universe discipline.** WO-12 pins `Ordinal.{0}`. That
does not work here, because the contract's B1 *states* a family indexed by
`Ordinal` and therefore auto-binds its own universe parameter `u`; pinning the
proof at `0` leaves the goal's `Ordinal.{u}` unsolved. The recursion is
therefore run at a *declared* universe variable `u`
(`universe u` + `Ordinal.{u}`/`aleph.{u}` annotations throughout), which is
legitimate because `PlufWO11.exists_enum_closedSubspaces` is polymorphic in the
ordinal universe (it takes CH in an independent universe). The work order's
practical point stands unchanged: annotate, or the universe of `(aleph 1).ord`
is left as a metavariable — only the annotation is `.{u}` rather than `.{0}`.

## Part C

`σ` is the upward closure among closed subspaces of `⋃ {c a : a < ω₁}`:

```lean
σ = {M | IsClosed (M : Set H) ∧ ∃ N ∈ U, N ≤ M},  U = {N | ∃ a < ω₁, N ∈ c a}
```

`PlufWO6.isPluf_of_criterion` is fed with: closedness and upward closure by
construction; meet-closure from monotonicity of the chain (two members dominate
members of the common stage `max a b`, which is meet-closed); properness from
`Ample N → N ≠ ⊥`; the decision clause directly from B1. Ampleness of every
member is `PlufWO13.ample_of_ample_le`.

**Nonprincipality (route reported).** Not via
`PlufWO6.principal_iff_sInf_ne_bot`, but directly, and by a **finite-codimension**
room argument as the work order requires — no countable-set escape. Given
`v ≠ 0`, apply the decision property to the hyperplane `(ℝ ∙ v)ᗮ`. If it is a
member, it is a member missing `v`. Otherwise some ample `g` has
`g ⊓ (ℝ ∙ v)ᗮ = ⊥`, whence `x ↦ ⟪v, x⟫` is injective on `g` and `g` embeds in
the line `ℝ` — contradicting `PlufWO13.infinite_dimensional_of_ample`. This is
recorded as `inf_orthogonal_singleton_ne_bot`.

C2 is the constant gap: `upper T M = 1` and `lower T M = 1/16` for every member
(WO-13's `upper_eq_one_of_ample`, `lower_eq_sixteenth_of_ample`), so
`ε = 15/16` defeats RSP. The radius clauses are WO-13's B1′ applied memberwise
(`radii_of_all_ample`).

## D2: the route (reported)

The paper builds `ψ(aI + bT) = a + bc` on `span {I, T}` and dominates it by
`limπ`. The formalization takes the shorter road that WO-6 already paved:
`PlufWO6.exists_state_with_value` is precisely Hahn–Banach dominated extension
**along the ray through a single operator** against the sublinear functional
`PlufWO6.plimsup σ A = sInf (upper A '' σ)` on all of `B(H)`, and it returns a
state *of the face* directly. So the only thing to supply is the paper's
two-case computation, at `T₁ = T` and `a = c`:

* `0 ≤ k` : `upper (k • T) M = k · upper T M = k` for every member, so
  `plimsup σ (k • T) = k ≥ k·c` since `c ≤ 1`;
* `k ≤ 0` : `k • T = -((-k) • T)`, so
  `upper (k • T) M = -lower ((-k) • T) M = k · lower T M = k/16`, and
  `plimsup σ (k • T) = k/16 ≥ k·c` since `c ≥ 1/16`.

(The auxiliary `lower_smul_of_nonneg`, `lower (d • A) M = d · lower A M` for
`d ≥ 0`, is derived from WO-6's `upper_smul`/`upper_neg`; it was not in the
WO-6 API.) The normalization `φ(I) = 1` is part of `IsState` and is supplied by
WO-6, so **no two-dimensional domain and no linear-independence lemma for
`{I, T}` are needed**; the contract's conclusion is unchanged.

D1 is WO-6's sandwich characterization `PlufWO6.face_iff_sandwich` at the
self-adjoint `T` with `upper T '' σ = {1}` and `lower T '' σ = {1/16}`; D3
combines C1, D1 and D2, the face being nonempty as `σ` is (`IsPluf.top_mem`).

## Axiom audit

```
PlufWO15.exists_admissible_decides            [propext, Classical.choice, Quot.sound]
PlufWO15.admissible_iUnion                    [propext, Classical.choice, Quot.sound]
PlufWO15.admissible_iUnion_counterexample     [propext, Classical.choice, Quot.sound]
PlufWO15.exists_admissible_chain              [propext, Classical.choice, Quot.sound]
PlufWO15.exists_pluf_all_ample                [propext, Classical.choice, Quot.sound]
PlufWO15.not_rsp_of_all_ample                 [propext, Classical.choice, Quot.sound]
PlufWO15.radii_of_all_ample                   [propext, Classical.choice, Quot.sound]
PlufWO15.face_apply_mem_Icc                   [propext, Classical.choice, Quot.sound]
PlufWO15.exists_face_state_apply_eq           [propext, Classical.choice, Quot.sound]
PlufWO15.face_values_eq_Icc                   [propext, Classical.choice, Quot.sound]
```

CH is a hypothesis (`Cardinal.continuum = Cardinal.aleph 1`) throughout, never
an axiom, and appears only in B1, C1 and D3.
