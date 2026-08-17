# Work Order WO-13 — pluf project (Feldman–Wilce)

**Paper I, Section 5: the ZFC lemmas.** Everything in §5 that precedes the
blocking lemma (WO-14) and the CH recursion (WO-15): the fixed operator, the
definition of ampleness with its dimension consequence, upward inheritance,
the finite-codimension lemma, and the escape lemma.

**Ground truth:** this tarball (`pluf-wo13.tar.gz`). Contract:
`PlufWO13.lean`. Paper source: `paper1.pdf`, §5 — note the numbering:
ample radii **Lemma 5.2**, upward inheritance **5.3**, finite codimension
**5.4**, escape **5.5**, the blocking lemma **5.6** (NOT in this
commission), the CH theorem **5.7**, the interval statement **Proposition
5.9**. `REPORT-WO9.md` and `REPORT-WO10.md` are included; the WO-9
signature table (Parts B and C) is the API this commission is built on.

**Base:** the WO-10 artifact (181 theorems; CI runs #1–#10; full project
under `base/`). `PlufWO13.lean` imports `RequestProject.PlufWO10`.
**WO-11 is running in parallel and is NOT a dependency** — nothing here
needs cardinal arithmetic or CH. All prior theorems must remain green;
`PlufWO7a.lean` is the census record and is not to be edited.

**Toolchain:** `leanprover/lean4:v4.28.0`, Mathlib pinned as included.

## Protocol (binding; as WO-1–WO-10)

Census first. Report-rather-than-repair with the codified license (false
contract ⇒ formalized counterexample + verbatim contract in comment +
marked minimal repair; ratification at audit). No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` per contract theorem; whitelist `propext`,
`Classical.choice`, `Quot.sound`. Partial order: A → B → C → D.

## The central substitution, and the interface decision

Paper I §5 is written with the **Borel functional calculus**: the escape
lemma produces the spectral subspace `K^ε_λ(V) = 1_{[λ-ε,λ+ε]}(T_V) V`.
Mathlib has no Borel functional calculus and the WO-7a census recommended
against building one. WO-9 proved the substitute — orthonormal approximate
eigenvectors with caller-chosen summable defects, and the closed span's
**homogeneous** bound `∀ x ∈ K, ‖T x − λ·x‖ ≤ (∑' n, ε n)·‖x‖` together
with `¬ FiniteDimensional`.

Part D is contracted against that API rather than against spectral
projections. **This is the interface decision of the commission**, because
WO-14's blocking recursion is written against whatever D1 delivers. That
recursion needs, at each stage: an infinite-dimensional escaping subspace, a
Rayleigh estimate for its unit vectors, and room to impose finitely many
linear constraints while staying off `N`. D1's three clauses plus D2's
quadratic corollary are intended to supply exactly that.

**If any further clause is needed to make WO-14 workable, add it to D1 and
report.** Changing this interface after WO-14 is drafted is expensive; the
WO-9/WO-10 experience (where a harvested statement turned out inapplicable
at its first call site) is the cautionary precedent.

## Item notes

**Part A.** `T = diag(1, 1/16, 1, 1/16, …)`. A2's two-sided bound is what
the ampleness arguments actually use — no spectral statement is required.
A3 supplies both essential-spectrum memberships from exact eigensequences
(the even and odd basis vectors), which is as elementary as it looks.

**Part B.** The paper's Lemma 5.2 is stated through the ellipsoid radii
`m = 1`, `M = 4`, `r = 4`; WO-6 verified the radii lemma in both the
Rayleigh and ellipsoid forms, so either route is available. The contracted
clause is infinite-dimensionality, which is what §5 consumes; prove the
radii clauses too if cheap on the WO-6 API, and report.

**Part C.** C1's `λ = 1/16` case is handled in the paper by rescaling
`1 − T`; if that is awkward in Lean, prove both cases directly and report —
the estimate is symmetric. C2 should reuse WO-9's `essSpec_le_of_finCodim`
for one inclusion; report which parts are new.

**Part D.** See above. Note D1's clause (iii) is contracted as infinite
codimension of `K ⊓ N` in `K`, matching the paper; D3 is the corollary the
paper draws.

## Deliverables

Census; compiling artifact with all 181 prior theorems green;
`#print axioms` for every contract theorem; report with the `compress`
reconciliation against WO-9, the C1 rescaling verdict, and — most
importantly — **an explicit statement of D1's final signature**, since
WO-14 will be drafted from it.

## Context

Remaining after this commission: **WO-14** (the blocking lemma, Lemma 5.6 —
the hardest item in the campaign, with a standing recommendation to
quarantine it as a named hypothesis if the budget binds), and **WO-15** (the
CH recursion assembling Theorem 5.7 and Proposition 5.9, consuming WO-11's
enumerations and WO-14). WO-11, running in parallel with this commission,
supplies the cardinal infrastructure for WO-15 and needs nothing from here.
