# REPORT — Work Order 17 (pluf project, Paper V, Sections 4–6)

Artifact: `RequestProject/PlufWO17.lean` (contract roll-up) with the
mathematics in `RequestProject/PlufWO17/{Basic,PartA,PartB,PartC}.lean`.
Toolchain `leanprover/lean4:v4.28.0`, Mathlib as pinned in the repo.

**Bottom line.** All nine contract items are delivered in the printed shape.
No `sorry`, `admit`, `axiom` or `native_decide` occurs in the artifact, and
`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
every contract theorem. The whole base tree (all prior work orders) builds
green alongside it; `PlufWO7a.lean` is untouched. The counterexample license
was not invoked: no contracted statement was found false.

---

## 1. Census

Carried out before any proof was written, against the pinned Mathlib and the
base tree.

**Vocabulary (Part A).** As instructed, nothing was imported from
`Mathlib.Data.Matroid` and no `Matroid` instance was built. The four
predicates `IsCircuitFamily`, `IndepOf`, `HasSM`, `IsScrawlFamily` are defined
from scratch in `PlufWO17/Basic.lean`, verbatim from the contract, and they
sufficed: A1 and A2 speak only of `suppFamily`, B3 quotes `IsScrawlFamily`
through `AroKaHyp`, and C3 needs only the `nonempty`, `ne_empty` and
`antichain` fields of `IsCircuitFamily`. Finding: **the vocabulary as printed
is adequate; no amendment was needed.**

**The coordinate map (Part B1).** The contract names `PlufWO16.toFun`. The
base tree exports no such map: `PlufWO16`, `PlufWO2` and `PlufWO1` always write
the `lp` coercion `(x : ∀ _ : ℕ, ℝ)` inline. It is therefore **introduced
here** (see §3).

**Closedness (Part B3).** `Submodule.closed_of_finiteDimensional` is present
and applies in the form needed (see §5).

**Rolle (Part C1).** `exists_hasDerivAt_eq_zero` is present in the form
needed. Mathlib has no counting version — "`k` zeros of `f` give `k − 1` zeros
of `f'`" — so one was built (`PlufWO17.exists_deriv_zeros`, §6).

**Vandermonde.** As the WO-16 census reported, generalized Vandermonde
positivity is absent from Mathlib. The rewritten Example 6.2 does not need it,
and the formalization here uses none: the only analytic input to Part C is
Rolle's theorem, and the only linear-algebra input is the rank inequality
`LinearMap.finrank_le_finrank_of_injective`.

---

## 2. Part A — findings

* **A1** is derived from WO-16's `PlufWO16.exists_supp_sUnion`, applied to the
  set of vectors of `M` whose support lies in `G`; it is a citation, not a
  reproof, as directed.

* **A2** is the finite correction `y = x − ∑_{p ∈ X} (x_p / (u_p)_p) · u_p`,
  computed coordinatewise through `PlufWO16.toFun`. **Reportable: the
  hypothesis `hXw : ↑X ⊆ supp x` is not used.** The coefficients are well
  defined because `hsupp` forces `(u_p)_p ≠ 0`; whether or not `x_p ≠ 0` is
  irrelevant (if `x_p = 0` the coefficient is simply `0`). The hypothesis is
  retained verbatim, as contracted. This is the same phenomenon WO-16 recorded
  for A4.

---

## 3. Part B1 — the coercion used

```lean
noncomputable def PlufWO16.toFun : H →ₗ[ℝ] (ℕ → ℝ) where
  toFun x := (x : ∀ _ : ℕ, ℝ)
  map_add' := lp.coeFn_add
  map_smul' := lp.coeFn_smul
```

declared in `PlufWO17/Basic.lean` inside `namespace PlufWO16` (the base files
are not edited). Its underlying function is the `lp` coercion definitionally
(`PlufWO16.toFun_apply` is `rfl`), so `supp x = {n | toFun x n ≠ 0}` needs no
transport, and it is injective by `lp.ext` (`PlufWO16.toFun_injective`). With
it, B1 is immediate in both directions, and it is also the convenient way to
compute coordinates of finite sums in A2, B2 and C2.

---

## 4. Part B2 — the rescaling

Given `W` finite-dimensional, take a finite generating set `t : Finset (ℕ → ℝ)`
of `W` (`Module.Finite.iff_fg`) and put

```lean
weight t n = (1 / 2) ^ n / (1 + ∑ v ∈ t, |v n|).
```

Then `weight t n > 0` — so multiplication by it preserves supports — and
`|weight t n * v n| ≤ 2⁻ⁿ` for every generator `v ∈ t`, whence
`Memℓp (fun n => weight t n * v n) 2` by comparison with `∑ 4⁻ⁿ`.

The realization is the submodule

```lean
realization t W = {x : H | ∃ f ∈ W, ∀ n, toFun x n = weight t n * f n},
```

which is visibly support-preserving, and equals the span of the finitely many
rescaled generators — the inclusion `⊆` uses that a member of `W` is a
combination of `t` and that `toFun` is injective — hence is finite-dimensional.

Note the weights depend on the chosen generating set, not on a basis; no basis,
and no orthogonality, is needed.

---

## 5. Part B3 — closedness

**Finding: yes, Mathlib supplies it in the form needed.**
`Submodule.closed_of_finiteDimensional` applies to a submodule of `H` verbatim;
`Module.Finite ℝ ↥M` *is* the `FiniteDimensional ℝ ↥M` instance it asks for, so
the bridge is a `haveI`. Recorded as

```lean
theorem PlufWO17.isClosed_of_finite (M : Submodule ℝ H) (hfin : Module.Finite ℝ ↥M) :
    IsClosed (M : Set H)
```

B3 itself is the assembly of B1 with `AroKaHyp` applied to `M.map toFun`:
the image is finitely generated (`Submodule.FG.map`) and nonzero (injectivity
of `toFun`). Closedness is not needed for the statement as contracted, but the
lemma above records that it is available for free.

---

## 6. Part C1 — the form actually proved

**Reportable, as requested.** The induction is run in the *cardinality* form

```lean
theorem expSum_card_zeros_lt (n : ℕ) : ∀ (s : Finset ℝ) (a : ℝ → ℝ),
    s.card = n → s.Nonempty → (∀ mu ∈ s, a mu ≠ 0) →
    ∀ Z : Finset ℝ, (∀ x ∈ Z, expSum s a x = 0) → Z.card < n
```

where `expSum s a x = ∑ mu ∈ s, a mu * exp (mu * x)`. Finsets on both sides are
what the induction step wants: it erases an exponent and discards a vanishing
coefficient, and both are Finset operations. Fixing any `mu₁ ∈ s`, the
translated sum `expSum s' a'` with `s' = (· − mu₁) '' s` has the same zeros as
`expSum s a` (they differ by the nonvanishing factor `exp (−mu₁ x)`), and its
derivative is `expSum (s'.erase 0) b` with `b ν = a' ν · ν`, an exponential sum
with one exponent fewer and still-nonzero coefficients.

The Rolle step is packaged as

```lean
theorem exists_deriv_zeros (f f' : ℝ → ℝ) (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (Z : Finset ℝ) (hZ : ∀ z ∈ Z, f z = 0) :
    ∃ Z' : Finset ℝ, Z.card ≤ Z'.card + 1 ∧ ∀ z ∈ Z', f' z = 0
```

proved by enumerating `Z` in order (`Finset.orderEmbOfFin`), applying
`exists_hasDerivAt_eq_zero` on each of the `#Z − 1` consecutive intervals, and
observing that the chosen interior points are strictly increasing, hence
distinct. The `+ 1` phrasing avoids truncated subtraction.

The contracted negative form `expSum_zeros_lt` is then derived: discard the
indices with vanishing coefficients, transport the coefficient function along
`Function.invFun μ`, and read off `m ≤ #Z < #s ≤ m`. **C2 consumes only the
contracted form.**

---

## 7. Part C2 — the model space

`geom lam` is `⟨fun n => lam ^ n, _⟩` when `|lam| < 1` and `0` otherwise; the
contract's `geom_apply` is the positive case. For `S : Finset ℕ` and
`m = #S + 1`, evaluation at the points of `S`,

```lean
L : (Fin m → ℝ) →ₗ[ℝ] (↥S → ℝ),   L a s = ∑ i, a i * lam i ^ (s : ℕ),
```

cannot be injective, since `finrank (Fin m → ℝ) = m > #S = finrank (↥S → ℝ)`;
a nonzero `a` in its kernel gives `x = ∑ i, a i • geom (lam i)` in the span,
vanishing on `S`. If `x` also vanished at some `n ∉ S`, then with
`μ i = log (lam i)` — distinct, since the `lam i` are distinct and positive —
the `m` points of `insert n S` would be `m` distinct real zeros of an
exponential sum with nonzero coefficient vector, contradicting C1. Hence
`supp x = ↑Sᶜ` exactly. The witness lies in the span itself, a fortiori in its
topological closure. As the contract notes, the summability of `∑ (1 − λₖ)`
plays no part.

---

## 8. Part C3 — the argument formalized

**Reportable: the proof is shorter than the printed chain, and uses neither
`hM` nor the (SM) clause.** Suppose `suppFamily M` were the scrawl family of a
circuit family `C`. Any `c ∈ C` is a member of the family (take `D = {c}`),
hence a support; it is nonempty, so by `hcof` it is cofinite. Then `c \ {p}`
for `p ∈ c` is cofinite too, so by `hall` it is again a member, i.e. a union of
members of `C`; being nonempty (its complement is finite and `ℕ` is infinite)
that union has a term `d ∈ C` with `d ⊆ c \ {p} ⊆ c`. The antichain axiom
forces `d = c`, and then `p ∈ d ⊆ c \ {p}` — a contradiction.

The paper's route (no minimal nonempty member; the independent sets are the
coinfinite sets; these have no maximal element; so (SM) fails) is the
motivation, but the antichain axiom alone already refutes the existence of `C`.
Both `hM` and the (SM) clause are retained verbatim in the contracted
statement, as printed.

---

## 9. Residue

Exactly the two items the work order anticipates:

* `AroKaHyp` — the theorem of Aroca, Bossinger, Falkensteiner, Garay López,
  González-Ramírez and Valencia Negrete, quarantined as a named hypothesis and
  never discharged;
* the hypothesis `hcof` of C3, which is Paper V's open Question 9.3, supplied
  as a hypothesis and not proved.

Nothing else in Sections 4–6 is left open.
