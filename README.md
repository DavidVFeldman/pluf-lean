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
- `workorders/WO1/` — the commission trail: work-order input tarball,
  Aristotle's census/report and summary.

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
