# pluf-lean

[![DOI](https://zenodo.org/badge/1336315599.svg)](https://doi.org/10.5281/zenodo.21987888)

A Lean 4 / Mathlib verification of the theorems of a five-paper series on
**maximal filters in the projection lattice of a Hilbert space** — *plufs*, the
lattice-theoretic linearization of "bounded sequences converge along
ultrafilters."

**272 audited theorems.** Every one carries a `#print axioms` line reporting
exactly `propext`, `Classical.choice`, `Quot.sound`. The sources contain no
`sorry`, `admit`, `axiom` or `native_decide`. Both facts are enforced by CI on
every push rather than asserted here: `scripts/check_axioms.py` parses the
build log and fails unless each audited name's axiom line is present and
confined to the whitelist.

## The papers

Sources and PDFs are in `papers/`.

| | Title |
|---|---|
| I | Ultrafilter limits in the projection lattice of a Hilbert space |
| II | Intimate subspaces, block filters, and the diagonalization of maximal projection filters |
| III | Projection-lattice ultrafilters at a measurable cardinal |
| IV | Exact paving for Fubini products of normal measures, with an application to maximal projection filters |
| V | Support families of closed subspaces of $\ell^2$, with an application to diagonalizable projection filters |

**[`PAPERS.md`](PAPERS.md) is the index for a reader checking a paper.** It maps
each printed numbered assertion to the Lean name that proves it and the file it
lives in, paper by paper, and states for each paper what is *not* covered.

## What is and is not proved here

Four results from the literature are used and **never discharged**. Each enters
only as a named hypothesis on the statements that consume it, so every
mechanized statement is a theorem of ZFC:

| Input | Hypothesis |
|---|---|
| Mathias, happy families | `PlufWO5.MathiasHyp` |
| Marcus–Spielman–Srivastava (Kadison–Singer) | `PlufWO6.KSHyp` |
| Blecher–Weaver excision and regularity | `PlufWO8.BWPackage` |
| Rowbottom homogeneity; Fodor | `PlufWO4.RowbottomFor`, `PlufWO1.FodorProperty` |
| Aroca et al. (supports of finite-dimensional spaces) | `PlufWO17.AroKaHyp` |

The continuum hypothesis is likewise a hypothesis
(`Cardinal.continuum = Cardinal.aleph 1`), never an axiom, on the two
statements that use it.

Mathlib has no essential spectrum, Calkin algebra, Fredholm theory or Borel
functional calculus. The first is defined here by Weyl sequences; the last is
circumvented rather than built, spectral subspaces being replaced by closed
spans of approximate eigenvectors with summable defects
(`PlufWO9.approx_eigen_span_spec`).

**Scalars.** The development is over ℝ. The lattice-level results are
field-blind and the explicit constructions have real coefficients; the
state-theoretic sections would need the standard complexification to be read
over ℂ.

## Why one repository and not four

The five papers share a dependency chain. Paper II's diagonalization theorem is
stated against a package of lattice facts that Paper I discharges
(`PlufWO6.plufPackage_of_isPluf`); Paper IV's transfer theorem consumes Paper
III's mechanization; Papers I and II share the Hilbert-basis block API
(`PlufWO9.blockB`) and the cardinal infrastructure (`PlufWO11`). Splitting the
artifact would either duplicate that infrastructure — and let the copies
drift — or introduce cross-repository version pinning. One CI over the whole
chain is also what has caught defects: every commission was run under the
requirement that all previously proved theorems stay green.

## Building

With [elan](https://github.com/leanprover/elan):

```
lake exe cache get
lake build
```

The toolchain is pinned (`lean-toolchain`: `leanprover/lean4:v4.28.0`) and
Mathlib is pinned by `lake-manifest.json`. The first cache fetch downloads
several gigabytes.

## Layout

```
RequestProject/       Lean sources; see PAPERS.md for the map to the papers
papers/               the four papers, LaTeX sources and PDFs
scripts/              check_axioms.py, the axiom and forbidden-token audit
workorders/           provenance: one directory per commission, each with the
                      work order, the input tarball, and the returned census
                      and report
.github/workflows/    CI: build on the pinned toolchain, run the audit, upload
                      the build log as an artifact
```

The `workorders/` trail is kept deliberately. The development was produced by a
sequence of commissions against written contracts, and the reports record what
was found: eight contract statements that turned out to be false, each with a
formalized counterexample; a defective printed proof of Proposition 2.3 of
Paper I, replaced by the argument now in the paper; and several places where
the mechanized proof is shorter or stronger than the printed one. These are
itemized in `CLAUDE.md`, which also records the working protocol.

## Licensing

Lean sources, scripts and workflows: Apache-2.0 (`LICENSE-CODE`).
Papers: CC BY 4.0 (`LICENSE`).
