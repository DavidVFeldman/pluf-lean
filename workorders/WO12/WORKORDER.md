# Work Order WO-12 — pluf project (Feldman–Wilce)

**Paper II, Theorem 5.4**: under CH, a nonprincipal pluf diagonalizable via no
orthonormal basis. The first of the campaign's two transfinite targets, and
the cheaper one (the census budgeted ~2–2.5 commissions; the route below
should come in under that).

**Ground truth:** this tarball (`pluf-wo12.tar.gz`). Contract:
`PlufWO12.lean`. Paper source: `paper2.pdf`, Theorem 5.4 and its proof —
read it, since the stage construction (A3) is contracted directly from it.
`REPORT-WO9.md`, `REPORT-WO10.md`, `REPORT-WO11.md`, `REPORT-WO13.md` are
included: their signature tables are the API this commission is built on.

**Base:** the merged tree after WO-11 and WO-13 (216 theorems; CI runs
#1–#12; full project under `base/`). `PlufWO12.lean` imports
`RequestProject.PlufWO13`. All prior theorems must remain green;
`PlufWO7a.lean` is the census record and is not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-11, WO-13)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment + marked
minimal repair; ratification at audit). No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` per contract theorem; whitelist `propext`,
`Classical.choice`, `Quot.sound`. CH is a hypothesis, never an axiom, and
appears only in Parts B–C. Partial order: A → B → C.

## The deliberate deviation from the paper's proof

The paper proves Theorem 5.4 by running the three-case recursion of
[FWI, Theorem 5.6] directly — maintaining a pluf-in-progress and handling
membership, blocking and the basis task at every stage. **This commission
does not do that**, because Proposition 5.5 (the one-witness reduction) is
already verified as `PlufWO10.one_witness_reduction`. It suffices to build a
downward directed family with all finite intersections infinite-dimensional,
with trivial intersection, defeating every basis; Proposition 5.5 supplies
the pluf, its nonprincipality, and its non-diagonalizability.

Two simplifications follow, and they are the reason for the route:

1. No three-case split, no membership case, no maximality argument inside
   the recursion — all of that now lives in already-verified results.
2. **The blocking subspace `N` is always a LINE.** Blocking the line spanned
   by the `o`-th vector at stage `o` is precisely what delivers
   Proposition 5.5's `sInf R = ⊥` hypothesis, and it makes A3's requirement
   that `h n ⊓ N` be finite-dimensional automatic.

**If this route is blocked** — most plausibly because directedness cannot be
maintained in the exact shape `one_witness_reduction` expects — REPORT
rather than silently reverting to the paper's recursion. The fallback exists
but costs the three-case split, and we would rather know.

## Item notes

**Part A — the stage construction, and the substance of the commission.**
A1 and A2 are the two "room" lemmas: finitely many linear constraints leave
an infinite-dimensional subspace, and a subspace of dimension ≥ 2 contains a
vector with two nonzero coordinates (the paper's `u`, `v`, `u+v` argument).
A3 is the construction itself; its proof is written out in the paper and
restated in the docstring. Note the ordinary ℕ-indexed recursion inside A3
does **not** need the ω₁ combinator — that is Part B.

The three conclusions of A3 correspond to the paper's three claims: the
least-index argument for non-intimacy, injectivity of `P_{Nᗮ}` on `R` for the
blocking, and tails for the invariant.

**Part B — the recursion.** B1 is a further instantiation of WO-9's E1
(cite WO-11's exports rather than reproving). B2 is the standard
countable-directed-family-has-a-decreasing-cofinal-chain argument. B3 is the
assembly; its stage bookkeeping is `PlufWO11.countable_Iio_of_lt_omega1`.

**On the packaging of the family in B3:** taking the family to *be* the set
of finite intersections is directed by construction and satisfies the same
finite-intersection property; that is likely easier than proving directedness
of the raw range. Either is acceptable — report which.

**On the recursion combinator:** use `PlufWO9.exists_omega1_chain` if its
shape fits; if a direct `Ordinal.limitRecOn` is easier here, do that and
**report the pattern**, since WO-15 will reuse whichever proves workable and
its shape is worth recording once.

**Part C.** One application of `PlufWO10.one_witness_reduction`.

## Deliverables

Census; compiling artifact with all 216 prior theorems green;
`#print axioms` for every contract theorem; report with: the A3 route and any
adjustments to the constraint bookkeeping, the B3 packaging decision, the
recursion-combinator verdict (with the final pattern recorded for WO-15), and
confirmation that the deviation route closed — or, if it did not, a precise
statement of where it failed.

## Context

Remaining after this commission: **WO-14** (Paper I's blocking lemma,
Lemma 5.6 — the hardest item in the campaign, drafted against WO-13's now-final
`escape` interface, with a standing recommendation to quarantine it as a named
hypothesis if the budget binds) and **WO-15** (Paper I Theorem 5.7 and
Proposition 5.9, the CH recursion, consuming WO-11's enumerations and WO-14).
WO-12 and WO-14 are independent and may run in parallel. Note for WO-15:
WO-11's C3 came back FALSE in its contracted forms and was repaired to an
**algebraic (Baire) escape** statement — WO-15 must not be written against an
orthogonality-based C3.
