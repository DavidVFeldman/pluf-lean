# Report — Work Order 12 (pluf project, Feldman–Wilce)

**Scope.** Paper II, Theorem 5.4: under CH, a nonprincipal pluf that is
diagonalizable via no orthonormal basis. Contract file: `RequestProject/PlufWO12.lean`.

**Verdict: the deviation route closed.** Every contracted statement is true as
printed and is proved as printed; no repairs, no quarantined hypotheses, no
fallback to the paper's three-case recursion. `#print axioms` for each of the
seven contract theorems reports exactly `[propext, Classical.choice, Quot.sound]`.
There is no `sorry`, `admit`, `axiom` or `native_decide` in the new material, and
the whole tree (all prior theorems, `PlufWO7a.lean` untouched) builds green.

## Census

| Item | Contract statement | Verdict |
|---|---|---|
| A1 `exists_constrained_notMem` | TRUE as printed | proved |
| A2 `exists_two_nonzero_coords` | TRUE as printed | proved |
| A3 `exists_nonIntimate_blocking` | TRUE as printed | proved |
| B1 `exists_enum_vectors` | TRUE as printed | proved |
| B2 `exists_decreasing_cofinal` | TRUE as printed | proved |
| B3 `exists_witness_family` | TRUE as printed | proved |
| C1 `exists_nonprincipal_nondiagonalizable` | TRUE as printed | proved |

Two contracted hypotheses turn out not to be needed by the proofs and are kept
only because the contract prints them: `hhc` (closedness of `h 0`) in A1, and
`hNcl` (closedness of `N`) in A3 — see "A3 route" below for why the latter
disappears. They are the only unused binders in the artifact.

## Files

New material lives in `RequestProject/PlufWO12/`:

* `Basic.lean` — dimension/topology infrastructure: infinite-dimensionality is
  inherited upwards; the room principle
  (`not_finiteDimensional_inf_orthogonal`: if `M` is infinite-dimensional and
  `W` finite-dimensional then `M ⊓ Wᗮ` is infinite-dimensional, proved by
  rank–nullity for the compression `M → W` by the orthogonal projection); an
  infinite orthonormal family certifies infinite dimension; finite meets of
  closed subspaces are closed.
* `PartA.lean` — Fourier expansion along an orthonormal family inside its closed
  span, A2, the one-step stage lemma, the ℕ-indexed stage recursion, and A3.
* `PartB.lean` — B2, the stage step, the ordinal bookkeeping, B1 and B3.

`RequestProject/PlufWO12.lean` is the contract file: it keeps the contracted
statements and docstrings verbatim and discharges them from the part files.
Two purely mechanical edits were made to it: the duplicate `abbrev H` was
dropped (the abbreviation now comes from the imported `PlufWO12/Basic.lean`),
and `include hCH in` was placed before B1 and B3 so that CH really appears in
their signatures — it does (`Cardinal.continuum = Cardinal.aleph 1 → …`), while
B2 stays CH-free.

## The A3 route, and the one adjustment to the constraint bookkeeping

The stage recursion is as contracted: unit vectors `w n ∈ h n` and thresholds
`k 0 < p 0 < q 0 = k 1 < p 1 < q 1 = k 2 < ⋯` with

* `b.repr (w n) i = 0` for all `i ≤ k n`;
* `w n ⊥ w j` for `j < n`;
* `b.repr (w n) (p n) ≠ 0 ≠ b.repr (w n) (q n)`, both indices automatically
  `> k n`;

`R` is the closed span of the `w n` and `A = Set.range p`. Each stage is a
finite set of orthogonality constraints, i.e. an intersection `h n ⊓ Wᗮ` with
`W` finite-dimensional, which is infinite-dimensional by the room principle;
A2 then supplies the two nonzero coordinates, and normalising gives `w n`.
Non-intimacy is the paper's least-index argument, run against the Fourier
expansion `x = ∑ ⟪w n, x⟫ • w n` valid for `x` in the closed span of an
orthonormal family: if `L` is least with `⟪w L, x⟫ ≠ 0` then the `p L` and
`q L` coordinates of `x` are both nonzero, and the interval bookkeeping
`p n < q n = k (n+1) ≤ k m < p m` (`n < m`) gives `p L ∈ A`, `q L ∉ A`.
Infinite dimension inside each `h j` comes from the orthonormal tail
`{w n : n ≥ j} ⊆ R ⊓ h j`.

**The adjustment.** The paper blocks `N` by keeping the projections
`P_{Nᗮ}(w n)` pairwise orthogonal and nonzero and then arguing that `P_{Nᗮ}` is
injective on `R`. That is unnecessary here. Since `R ≤ h 0` and hence
`R ⊓ N ≤ h 0 ⊓ N =: D`, and `D` is finite-dimensional by hypothesis, it
suffices to add `w n ⊥ D` to the (already finite) constraint list at every
stage: then `R ≤ Dᗮ`, so `R ⊓ N ≤ D ⊓ Dᗮ = ⊥`. This removes the projection
argument, the constraints `w n ⊥ P_{Nᗮ}(w j)`, the requirement `w n ∉ N`, and
the hypothesis that `N` be closed (`hNcl`, kept in the statement but unused).

## B3: the packaging decision

As the work order permits, **the delivered family is the set of all finite
intersections** of the subspaces produced by the recursion:

```
Rset = {M | ∃ s : Finset Ordinal, (∀ p ∈ s, p < ω₁) ∧ M = s.inf c}
```

It is downward directed by construction (`Finset.inf_union`), nonempty (`s = ∅`
gives `⊤`), consists of closed subspaces, and has the same finite-intersection
property as the raw range. Handling arbitrary `Finset (Submodule ℝ H)` subsets
of `Rset` is done by a cover lemma (`exists_finset_ordinal_le`): every finite
subfamily dominates `s.inf c` for a single finite set `s` of ordinals, and such
finite meets are infinite-dimensional by a *max-element* argument — no induction
on the finite set is needed, only the stage property at `s.max'`.

## The recursion combinator: verdict, and the pattern for WO-15

**`PlufWO9.exists_omega1_chain` does not fit**, and was not used. Its step map
`β → β` cannot see the stage index, whereas each stage here consumes the `o`-th
basis and the `o`-th vector, and needs the *whole set* of earlier values (not
just a supremum) to state its infinite-dimensionality obligation.

The pattern actually used — recommended for WO-15 — is a plain well-founded
recursion on `Ordinal` with the stage choice hidden in a `dite`:

```lean
set Φ : (a : Ordinal) → ((p : Ordinal) → p < a → Submodule ℝ H) → Submodule ℝ H :=
  fun a ih =>
    if hex : ∃ R, StageGood {M | ∃ p, ∃ hp : p < a, ih p hp = M} (bas a) (vec a) R
    then hex.choose else ⊤
set c : Ordinal → Submodule ℝ H := (inferInstanceAs (WellFoundedLT Ordinal)).wf.fix Φ
have hceq : ∀ a, c a = Φ a (fun p _ => c p) := fun a => WellFounded.fix_eq _ Φ a
```

with the stage invariant proved *afterwards* by `Ordinal.induction`: assuming
every earlier stage is good, the accumulated family `Prev c a = c '' Set.Iio a`
is countable (`PlufWO11.countable_Iio_of_lt_omega1`), consists of closed
subspaces, and has the finite-intersection property, so the stage existence
lemma applies and `hceq` together with `dif_pos` identifies `c a` with the
chosen witness. No `Ordinal.limitRecOn`, no separate limit case, no
successor/limit split at all: the "history" formulation absorbs both. Two
practical notes for WO-15: (i) the recursion must be run at a fixed universe
(`Ordinal.{0}` annotations inside the proof), otherwise the universe of
`(aleph 1).ord` is left as a metavariable; (ii) keeping `Prev` and the stage
predicate as top-level definitions makes the `dite` rewriting a one-liner.

Stage `o` uses WO-11's enumerations: `PlufWO11.exists_enum_hilbertBases` for the
`o`-th basis, and B1 (`PlufWO11.enumShift hCH PlufWO11.mk_H`) for the `o`-th
vector; the blocking subspace is the line `ℝ ∙ (o-th vector)`, so A3's
finite-dimensionality hypothesis on `h n ⊓ N` is automatic.

## Part C

One application of `PlufWO10.one_witness_reduction` to the B3 family: it
supplies a pluf extending the family, its nonprincipality (from `sInf R = ⊥`)
and its non-diagonalizability at every orthonormal basis (from the non-intimate
member).

## Axiom audit

```
PlufWO12.exists_constrained_notMem            [propext, Classical.choice, Quot.sound]
PlufWO12.exists_two_nonzero_coords            [propext, Classical.choice, Quot.sound]
PlufWO12.exists_nonIntimate_blocking          [propext, Classical.choice, Quot.sound]
PlufWO12.exists_enum_vectors                  [propext, Classical.choice, Quot.sound]
PlufWO12.exists_decreasing_cofinal            [propext, Classical.choice, Quot.sound]
PlufWO12.exists_witness_family                [propext, Classical.choice, Quot.sound]
PlufWO12.exists_nonprincipal_nondiagonalizable [propext, Classical.choice, Quot.sound]
```

CH is a hypothesis throughout (`Cardinal.continuum = Cardinal.aleph 1`), never an
axiom, and appears only in B1, B3 and C1.
