# pluf-lean

Lean 4 / Mathlib verification artifacts for the **pluf project**
(D. Feldman, A. Wilce): maximal filters in the projection lattice of a
Hilbert space, as the linearization of "bounded sequences converge along
ultrafilters."

**Status: private working repository.** Contents are machine-checked
fragments of a three-paper series, not the papers' full mathematics; see the
status table in `CLAUDE.md` for exactly what is and is not verified. Public
release, tagging, and Zenodo archival happen only when the project is judged
finished.

## Contents (WO-1)

- `RequestProject/PartA.lean` — σ-Q-point combinatorics for ultrafilters on a
  well-ordered type: partition/function equivalence, transversal escape, and
  *normal ⇒ σ-Q* via the piece-minima/Fodor argument (Paper III, Lemma 5.2).
- `RequestProject/PartB.lean` — the witness subspace `W` of a partition in
  ℓ²(ℕ), block subspaces, and the **thinness lemma**: a subspace meeting `W`
  trivially meets every piece-block in rank ≤ 1 (Paper II, Lemma 3.6).
- `RequestProject/PartC.lean` — the block-intersection identity for closed
  spans of disjointly supported families, and the **no-disjointly-supported-
  blocker** proposition (Paper II, Prop. 3.7).
- `RequestProject/PlufWO1.lean` — root; runs `#print axioms` on all sixteen
  contract theorems.
- `RequestProject/PlufWO2.lean` — WO-2 (root file; imports the WO-1 root, so
  building it runs both audits): ℓ²(κ) infrastructure for an arbitrary index
  type, **exact paving** along a diagonal-intersection-closed ultrafilter
  (Paper III, Thm 2.1), and the **exact dichotomy** with its
  maximality-shaped corollary (Paper III, Thm 3.1 / Cor 3.2).
- `RequestProject/PlufWO3.lean` — WO-3 (root file; imports the chain, so one
  build runs all three audits): ultrafilter limits of bounded functions,
  **diagonal flattening** (Paper III, Cor 2.2, certified without
  self-adjointness), the **block filter Φ(U) as a filter** (proper, upward
  closed, intersection-closed, generically complete, nonprincipal, deciding),
  and the **κ-witness** (Paper III, Prop 5.3, Hilbert half), including a
  formalized counterexample showing the covering hypothesis of the blocking
  characterization is necessary.
- `RequestProject/PlufWO4.lean` + `RequestProject/PlufWO4/` — WO-4
  (Paper IV): the twelve-pattern homogeneity analysis and **injectivity on a
  square** (`Homog`), the Fubini product with the **full-selector
  non-isomorphism** package (`Fubini`), the **exact-paving property** with
  its proof for the self-product and the EPP-parametrized transfer of the
  WO-2/WO-3 theory (`EPP`), and the **blocker constraints** at ω —
  generalized thinness, support, Baire piece-spread (`Blockers`).
- `RequestProject/PlufWO5.lean` + `RequestProject/PlufWO5/` — WO-5
  (Paper II, §§2–5 minus Thm 5.4): the **gliding-hump dichotomy** and its
  relativization, the block filter at ω with the **membership/addability
  criteria**, **Theorem 3.4** (necessity in full; sufficiency
  Mathias-parametrized), **Gowers's intimate subspace** with the dimension
  bound by the pair-sum route, and **diagonalizable ⟺ intimate** against
  the `PlufPackage` of companion-paper facts (to be discharged in WO-6),
  including a formalized obstruction showing the naive extension
  formulation requires the closed-subspace quantifier.
- `RequestProject/PlufWO6.lean` + `RequestProject/PlufWO6/` — WO-6 (Paper I
  §§2–4): the maximality criterion and its converse, the finite-dimension and
  principality lemmas, no prime filters (for H; see the paper's Prop. 2.3), the
  topology on the space of plufs, ellipsoid radii and the gap criterion, the
  state face with Banach–Alaoglu compactness, Kadison–Singer parametrized by a
  paving hypothesis, and the discharge of WO-5's `PlufPackage`.
- `RequestProject/PlufWO8.lean` + `RequestProject/PlufWO8/` — WO-8 (Paper III
  §§4–5, Paper I §6): the ultrafilter-limit state, its singularity (through the
  compact operators), countable and generic-index additivity, purity derived
  from the face machinery, Theorem 4.2 parametrized by a Blecher–Weaver
  excision package, and the identification of its 1-set with the block filter.
- `workorders/WO1/` … `workorders/WO8/` — the commission trails: work-order
  input tarballs, Aristotle's census/reports and summaries.

Formalization executed by **Aristotle** (Harmonic) against work order WO-1;
source-audited by hand; independently compiled by the CI in this repo.

## Building locally (optional)

With [elan](https://github.com/leanprover/elan) installed:

    lake exe cache get
    lake build

Toolchain is pinned (`lean-toolchain`: v4.28.0); first cache fetch downloads
several GB. On Windows, run the above in CMD or PowerShell from the repo
root.

## CI

Every push builds the project on the pinned toolchain and runs
`scripts/check_axioms.py`, which fails unless each contract theorem's axiom
line is present in the build log and confined to
`propext`, `Classical.choice`, `Quot.sound`, and unless the sources are free
of `sorry`/`admit`/`axiom`/`native_decide`. The build log is uploaded as an
artifact on every run.
