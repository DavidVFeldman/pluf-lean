# REPORT-WO6 — census, gate verdicts, and item-by-item report

Work Order WO-6 (pluf project, Feldman–Wilce; Paper I §§2–4 plus the
discharge of WO-5's `PlufPackage`).

Contract file: `RequestProject/PlufWO6.lean` (roll-up: item statuses,
verbatim contract statements where the returned form differs, and the
`#print axioms` audit). Mathematics: `RequestProject/PlufWO6/*.lean`.

---

## 0. Summary

* All eighteen contract items are returned. Nine are proved exactly as
  contracted (A2, A3, A4, D1, E2, E3, F1, G1, G2); eight carry a **marked
  minimal repair** licensed by a formalized counterexample to the
  contracted form (A1, A5, B1, C1, C2, D2, E1, E4); one (F2) is returned
  with a repaired hypothesis, its contracted shape being underivable
  without the quarantined Marcus–Spielman–Srivastava theorem.
* **Both census gates PASS.** Part C's topological packaging is cheap in
  Mathlib and is delivered in full, including all four clauses of
  Proposition 2.4. Part E's state theory is within reach of Mathlib's
  Hahn–Banach and projection calculus and is delivered in full.
* The Part D "separate item" (the ellipsoid phrasing of Lemma 3.1) is
  **also** delivered, in addition to the contracted Rayleigh form, with a
  proof that the two phrasings of the round-slice property agree.
* The artifact compiles under `leanprover/lean4:v4.28.0` with the pinned
  Mathlib. No `sorry`, `admit`, `axiom` or `native_decide` occurs
  anywhere. Every completed contract theorem is audited with
  `#print axioms` and depends only on `propext`, `Classical.choice`,
  `Quot.sound`. All prior work orders' modules (WO-1 – WO-5, the 82
  prior theorems) build unchanged.
* The paper's Proposition 3.3 is completed beyond the contract: the face
  of states is also shown convex and weak-\* compact.
* WO-6 adds 12 modules, 152 theorems/instances and 24 definitions.

---

## 1. Census

### 1.1 What was available and used

| Need | Mathlib support | Verdict |
|---|---|---|
| Lattice of closed subspaces | `Submodule ℝ E` + `IsClosed (M : Set E)`; `Submodule.topologicalClosure` for joins | adequate; the contracted `IsPluf` shape is kept |
| Finite-dimensional subspace calculus | `Submodule.finrank_mono`, `Submodule.eq_of_le_of_finrank_eq`, `Submodule.closed_of_finiteDimensional`, `finrank_span_singleton` | complete; A3/A4 are routine |
| Orthogonal complements, projections | `Submodule.orthogonalProjection`, `Submodule.starProjection`, `isSelfAdjoint_starProjection`, `Submodule.inner_starProjection_left_eq_right`, `Submodule.orthogonal_orthogonal` | complete; used in A5 and throughout Part E |
| Generated topologies | `TopologicalSpace.generateFrom`, `IsTopologicalBasis.mk`, `IsTopologicalBasis.dense_iff` | cheap — see the Part C gate |
| Hahn–Banach, dominated extension | `exists_extension_of_le_sublinear`, `LinearPMap.mkSpanSingleton'`, `LinearMap.mkContinuous` | exactly the right shape — see the Part E gate |
| Adjoints | `ContinuousLinearMap.adjoint`, `ContinuousLinearMap.adjoint_adjoint` | complete |
| Ultrafilter limits of bounded sequences | `Ultrafilter.map`, `IsCompact.ultrafilter_le_nhds` on `Set.Icc` | complete (`exists_ultrafilter_limit`) |
| Suprema/infima through antitone maps | `Antitone.map_csSup_of_continuousAt`, `Antitone.map_csInf_of_continuousAt` | complete; used for the ellipsoid radii |
| `lp 2` coordinate calculus | WO-1 – WO-5 project infrastructure (`PlufWO1.evec`, `PlufWO5.block`, `PlufWO5.summable_sq`, …) | reused, not rebuilt |

### 1.2 What is absent

* **No state theory applicable here.** Mathlib has no `State` structure
  for operator algebras; its C\*-algebra order theory is developed for
  `StarOrderedRing`s over `ℂ`, and none of it applies verbatim to
  `E →L[ℝ] E` for a *real* Hilbert space `E`. There is likewise no API
  for "a continuous linear functional positive on the positive cone".
  Consequence: the contracted `IsState` rendering is retained (§3).
* **No GNS machinery over ℝ**; Paper I §3's closing remark about the GNS
  representation of a state in `S_π` is therefore out of scope here.
* **No essential-spectrum / `HilbertBasis` infrastructure** of the kind
  WO-5's census already flagged for WO-7. Nothing in WO-6 needed it.

---

## 2. GATE VERDICT — Part C (topology packaging): **PASSED**

Mathlib's generated-topology API makes the packaging cheap: the three
obligations of `TopologicalSpace.IsTopologicalBasis.mk` are exactly the
set-level lemmas the contract asks for. `PartCTop.lean` therefore
delivers, on the type `PlufSpace E` of plufs of a nonzero `E`:

* `isTopologicalBasis_plufBasis` — the sets `M̂ = {π | M ∈ π}`, for `M`
  closed, form a basis of the generated topology;
* `t2Space` — Hausdorff (Proposition 2.4, clause 1), separated by A1;
* `isClopen_hat` — each `M̂` is clopen, so the space is
  zero-dimensional in the sense of having a clopen basis (clause 2);
* `hat_line_eq_singleton`, `isOpen_singleton_principal` — the principal
  plufs are isolated points, and `dense_principal` — they are dense
  (clause 3);
* `not_compactSpace` — non-compactness (clause 4), by the paper's
  argument: for a plane `M = span {u, v}`, `M̂` is a clopen, hence
  compact, subspace covered by the pairwise disjoint open sets attached
  to the lines of `M`, of which there are continuum many.

Cost: 365 lines, of which the mathematics (the identification of `M̂` for
a plane with the set of lines of that plane) dominates; the `Mathlib`
packaging itself was a few dozen lines.

---

## 3. GATE VERDICT — Part E (states): **PASSED**

This was expected to be the pivotal finding; the finding is positive.

**What the paper needs, and what Mathlib supplies.**

1. *A state space.* Mathlib supplies nothing usable (§1.2). The
   contracted `IsState` shape — a continuous linear `φ : (E →L[ℝ] E) →L[ℝ] ℝ`
   with `φ A ≥ 0` whenever the quadratic form of `A` is nonnegative, and
   `φ id = 1` — is therefore **retained verbatim** (`States.lean`).
   *Assessment of the rendering:* it is the right one for this project.
   Positivity is phrased through the quadratic form rather than through
   `StarOrderedRing`'s positive cone, which for `B(H)` over `ℝ` is the
   same cone but with no Mathlib API attached; and it is strong enough to
   derive everything the paper uses: monotonicity for the quadratic-form
   order (`IsState.mono`), adjoint invariance (`IsState.adjoint`),
   Cauchy–Schwarz for `(A, B) ↦ φ (A* B)` (`IsState.cauchy_schwarz`),
   the compression identity `φ A = φ (P A P)` at a projection of value 1
   (`IsState.compress`), and `φ P ≤ 1` for projections
   (`IsState.starProjection_le_one`). Nothing in Part E had to be
   weakened to fit the rendering.
2. *Hahn–Banach from a sublinear functional.* `exists_extension_of_le_sublinear`
   is exactly the paper's tool. It is applied to
   `plimsup π T = sInf (upper T '' π)`, which is shown sublinear
   (`plimsup_smul`, `plimsup_add_le`) on **all** of `B(E)`, not merely on
   the self-adjoint part: the Rayleigh form sees only the symmetric part
   of an operator, so no restriction to self-adjoints is needed and the
   extension problem is a plain one. Positivity and normalization of the
   extension are then automatic (`isState_of_le_plimsup`), and membership
   in the face is automatic too (`mem_face_of_le_plimsup`).
3. *Banach–Alaoglu.* Available (`WeakDual.isCompact_polar`,
   `WeakDual.isCompact_closedBall`) and not needed for the contracted
   items: E1's nonemptiness comes from Hahn–Banach directly, E3's face
   property is elementary, and E4 is obtained by producing two states
   with prescribed values at a single operator
   (`exists_state_with_value`). The convexity and weak-\* compactness
   clauses of the paper's Proposition 3.3, which the contract does not
   ask for, are nevertheless delivered in `PartECompact.lean`: the face
   `stateFace π` is convex (`convex_stateFace`), is closed for the
   topology of pointwise convergence (`isClosed_stateFace`, the face
   being an intersection of conditions on evaluations), and every state
   has dual norm at most one (`IsState.norm_le_one`), so Alaoglu gives
   weak-\* compactness (`isCompact_stateFace`).

**Consequence for WO-8.** With the weak-\* clauses now in hand, the only
state-side infrastructure Paper III §§4–5 would need beyond WO-6 is — if
pure states and GNS are genuinely required — real GNS theory, which
Mathlib does not have and which is a substantial build. The verdict of
this gate is therefore: **commission WO-8**, but scope it on the understanding that "state" means the `IsState` rendering
of `States.lean`, and budget separately for anything needing GNS or
purity.

---

## 4. Item-by-item report

Throughout, *repair* means the codified licence: contracted statement
preserved verbatim in a comment, counterexample formalized, minimal
repair marked and proved.

### Part A

* **A1 `maximality_criterion` — repaired: `[Nontrivial E]`.**
  Counterexample `isPluf_empty_zero_space`: over the zero space every
  submodule is `⊥`, so the empty family satisfies all five clauses of
  `IsPluf` (the maximality clause vacuously, a proper family of subspaces
  of the zero space being empty), while for `M = ⊥` neither disjunct
  holds. `E ≠ 0` is the paper's standing hypothesis on `H`. With it the
  paper's argument goes through verbatim: `π ∪ {M ⊓ N : N ∈ π}` is a
  proper meet-closed family containing `π`, so maximality returns it into
  `π`.
* **A2 `isPluf_of_criterion` — as contracted.**
* **A3 `principal_of_finiteDimensional` — as contracted.** The care the
  work order asks for is in the closedness bookkeeping: a member of least
  finite dimension is contained in every member (via
  `Submodule.eq_of_le_of_finrank_eq`), and a line inside it is closed
  because it is finite-dimensional, so maximality applies to it. The
  `d ≥ 2` case is closed exactly as printed.
* **A4 `principal_iff_sInf_ne_bot` — as contracted.**
* **A5 `finCodim_mem_of_nonprincipal` — repaired: `[Nontrivial E]`**
  (same counterexample). The argument is the printed one: a member
  meeting `V` trivially injects into `Vᗮ` under the orthogonal
  projection, hence is finite-dimensional, hence forces principality by
  A3.

### Part B — the outcome the work order asked to be reported

Two findings.

1. **The contracted statement is false as printed.** The *empty* family
   satisfies all five hypotheses over a space of rank 3 and is prime,
   vacuously: `empty_filter_is_prime`. Minimal repair: `π.Nonempty`
   (equivalently `⊤ ∈ π`), which is what "filter" tacitly means.
2. **The printed three-lines argument does not survive formalization.**
   As printed it produces a line in the filter and then requires the
   plane spanned by two of the three lines to be in the filter; primeness
   does not supply this unless the plane is already known to be a member,
   and the plane is a member only if the ambient space is spanned by it.
   The parenthetical hedging in the paper is, on this reading, hedging a
   real gap.
   What survives is the same idea with the three lines of a plane
   replaced by a triple of closed subspaces that pairwise meet trivially
   and whose pairwise closed joins are everything: `not_prime_of_triple`.
   Such a triple exists in the paper's `H` — the even coordinates, the
   odd coordinates, and the diagonal subspace `x_{2n} = x_{2n+1}` — so
   Proposition 2.3 holds there, and that is what `no_prime_filter`
   returns.
   **Caveat, reported rather than concealed:** a triple of this kind
   cannot exist in *odd finite* dimension. If `A ⊕ B = A ⊕ C = B ⊕ C =`
   the whole space, then `dim A + dim B = dim A + dim C = dim B + dim C =
   n`, forcing `dim A = dim B = dim C = n/2`. So the returned B1 covers
   `H` (and, by the same triple construction, any even or infinite
   dimension), but the contracted "rank ≥ 3" generality is **not**
   established for odd finite dimension by this route. For that case the
   conceptual backstop is Kochen–Specker, which the work order excludes
   from this commission. This is the honest state of Part B.

### Part C

* **C1 `pluf_sets_inter` — repaired: `IsClosed M`, `IsClosed N`.**
  Counterexample `pluf_sets_inter_counterexample`: with `M` the span of
  the standard basis vectors of `H` (not closed — `not_isClosed_spanEvec`)
  and `N = ℝ ∙ evec 0`, the left-hand side is empty (no pluf has a
  non-closed member) while the right-hand side contains the principal
  pluf of `evec 0`. The repair is exactly the paper's `M, N ∈ P(H)`.
* **C2 `pluf_compl_eq_iUnion` — repaired: `[Nontrivial E]`**
  (counterexample `isPluf_empty_zero_space`; the proof is A1).
* Topological packaging: see the gate verdict in §2.

### Part D

* **D1 `lower_le_upper` — as contracted.**
* **D2 `rsp_iff_sup_eq_inf` — repaired: `[Nontrivial E]`.** Over the zero
  space `π = ∅` is a pluf, both sides of the equation are `sSup ∅ =
  sInf ∅ = 0`, and `RSP ∅ T` is false. The contracted positivity
  hypothesis `hpos` is retained as contracted; `rsp_iff_sup_eq_inf'`
  records that it is not needed — boundedness of `T` alone bounds the
  Rayleigh set on both sides.
* **D-form decision.** The contract is honoured in the Rayleigh form, and
  the paper's ellipsoid phrasing is delivered **in addition**, in
  `PartDEllipsoid.lean`, so that nothing is substituted:
  for a coercive positive `T` (the paper's "positive with bounded
  inverse": `c * ‖x‖² ≤ ⟨T x, x⟩` with `c > 0`) and a nonzero closed `M`,
  * `minorRadius_eq`: `m(E_T ∩ M) = uT(M)^{-1/2}`,
  * `majorRadius_eq`: `M(E_T ∩ M) = lT(M)^{-1/2}`,
  * `eccentricity_eq`: `r(E_T ∩ M) = sqrt (uT(M) / lT(M))`,
  which is Lemma 3.1 verbatim, and
  * `rsp_iff_rspEcc`: for such `T`, the contracted `RSP` and the paper's
    eccentricity form `RSPEcc π T : ∀ ε > 0, ∃ M ∈ π, r(E_T ∩ M) < 1 + ε`
    are equivalent.
  The mechanism is that the norms of the points of `E_T ∩ M` are exactly
  the inverse square roots of the Rayleigh values on `M`
  (`norm_image_ellipsoidSlice`), and `q ↦ q^{-1/2}` is antitone and
  continuous on `[c, ∞)`.

### Part E

Beyond the contract, `PartECompact.lean` completes the paper's
Proposition 3.3: `convex_stateFace` (the face is convex),
`isClosed_stateFace` (weak-* closed) and `isCompact_stateFace` (weak-*
compact, by Banach–Alaoglu together with `IsState.norm_le_one`).

* **E1 `face_nonempty` — repaired: `[Nontrivial E]`** (over the zero
  space `id = 0`, so no functional is normalized and no state exists).
  Proof: Hahn–Banach against `plimsup π`, as in §3.
* **E2 `face_iff_sandwich` — as contracted**, with no hypothesis on `E`:
  over the zero space the statement is vacuous, `IsState φ` being
  unsatisfiable there. The forward direction is the paper's
  `φ A = φ (P A P)` and `ℓ_T(M) P ≤ P T P ≤ u_T(M) P` sandwich; the
  converse is the paper's `ℓ_{P_M}(M) = 1`.
* **E3 `face_isFace` — as contracted.** The contracted hypothesis `hπ` is
  retained although the proof does not use it: the face property holds
  for the set of states equal to 1 on any family of projections.
* **E4 `rsp_all_iff_face_subsingleton` — repaired: `[Nontrivial E]`**
  (over the zero space the right side is vacuously true and the left side
  false). Forward: E2 plus D2. Backward: if some self-adjoint `T₀` fails
  RSP then `pliminf π T₀ < plimsup π T₀`, and `exists_state_with_value`
  produces two states of the face separating them.

### Part F

* **F1 `rsp_of_ks` — as contracted**, from the quarantined `KSHyp`. The
  contracted hypothesis `IsSelfAdjoint T` is retained but unused: the
  paving hypothesis already controls the Rayleigh quotient, which sees
  only the symmetric part of `T`.
* **F2 `ks_of_rsp_all` — hypothesis repair, `ks_of_blockRSP`.** The
  contracted hypothesis gives, for each `ε`, *some* member of a pluf with
  small Rayleigh oscillation; the paving conclusion needs a member of the
  special form `block S` with `S ∈ U`. Nothing in `RSP` identifies the
  witness with a block, and bridging that gap is precisely the ellipsoid/
  paving reduction plus, ultimately, Marcus–Spielman–Srivastava, which is
  quarantined. F2 is *true* — both sides are theorems of ZFC — but not
  derivable in the contracted shape here.
  What the elementary argument does give, and what is returned, is
  `ks_of_blockRSP`: if for every operator some **block** of `U` has
  arbitrarily small Rayleigh oscillation (`BlockRSP`), then `KSHyp U`
  holds. On such a block, the Rayleigh quotient of a unit vector and the
  diagonal sum — a convex combination of diagonal entries, each of which
  is itself a Rayleigh value of the block — both lie within the
  oscillation of the lower Rayleigh value. This is the honest content of
  Remark 4.2's converse direction.

### Part G — the payoff item

* **G1 `plufPackage_of_isPluf` — as contracted.** The five fields of
  `PlufWO5.PlufPackage` come from `IsPluf` (closedness, upward closure,
  meets, properness), from A5 (`finCodim_mem`) and from A1 (`decides`).
* **G2 `diagonalizable_iff_intimate_pluf` — as contracted.** With G1,
  WO-5's `diagonalizable_iff_intimate` becomes Paper II's Theorem 5.1 as
  printed, for genuine maximal filters. The retroactive upgrade of WO-5's
  Part E that the work order asked for is thereby in place.

---

## 5. Audit and build

* `lake build` is clean for the whole project (WO-1 – WO-6); warnings are
  confined to Mathlib's `unusedSectionVars`/`unusedVariables` linters,
  chiefly on contracted-but-unused hypotheses that are retained
  deliberately (`hpos` in D2, `hπ` in E3, `hT` in F1).
* `RequestProject/PlufWO6.lean` runs `#print axioms` on every completed
  contract theorem, on the three counterexamples, on the four ellipsoid
  results and on the five Part C packaging results. Every line reports
  `[propext, Classical.choice, Quot.sound]`.
* `rg -n "sorry|admit|native_decide|^axiom" RequestProject/` returns no
  declaration-level hit.

## 6. Recommendations

* **WO-8** (Paper III §§4–5): commissionable on the strength of the Part
  E verdict, with the `IsState` rendering as the state notion. Budget
  separately for GNS/pure states (absent from Mathlib; substantial).
* **Part B residue**: Proposition 2.3 in odd finite dimension is not
  established here and needs the Kochen–Specker route; it is a
  self-contained item if wanted.
* **WO-7**: nothing in WO-6 changes the WO-5 census finding that the
  transfinite recursions need essential-spectrum and `HilbertBasis`
  infrastructure that Mathlib does not provide.
