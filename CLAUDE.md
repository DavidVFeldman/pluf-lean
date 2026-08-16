# CLAUDE.md — pluf-lean

Lean 4 verification repository for the **pluf project** (Feldman–Wilce):
maximal filters in the projection lattice of a Hilbert space. This file
encodes the working protocol so any Claude session (or collaborator) can
continue without re-deriving conventions.

## Pipeline

Claude drafts mathematics and Lean work orders → **Aristotle** (Harmonic)
executes the formalization → this repo + CI provide the independent compile →
GitHub release tag → Zenodo archival.

- Aristotle requires **Lean v4.28.0** exactly; `lean-toolchain` and
  `lake-manifest.json` pin the toolchain and Mathlib. Do not bump either
  except as part of a deliberate migration WO.
- Work-order inputs to Aristotle are **tar.gz**; archives for David's own
  use are **zip**. The WO input tarball is the ground truth for each
  commission and is preserved under `workorders/WOn/`.

## Protocol constants (binding)

1. **Tarball as ground truth.** Each `workorders/WOn/` keeps the exact WO
   input archive, the WORKORDER, Aristotle's REPORT and SUMMARY.
2. **Census-first.** Every WO instructs Aristotle to return an item-by-item
   census (Mathlib API, feasibility) before or with the proofs.
3. **Report-rather-than-repair.** Renaming/idiom changes fine; changes to
   mathematical content are not — obstructions are reported, never silently
   patched. False-looking statements come back as reports.
4. **Closure discipline.** No `sorry`, `admit`, `axiom`, `native_decide`.
   Every contract theorem carries `#print axioms`; whitelist:
   `propext`, `Classical.choice`, `Quot.sound`. **No closure claim in any
   paper until this repo's CI is green on the relevant artifact** — the
   claimed axiom lines must appear in an independent build log, not only in
   Aristotle's report.
5. `scripts/check_axioms.py` is the machine form of (4); it must list every
   contract theorem of every merged WO. Extend the list when merging a WO.

## Repo conventions

- Two-component version tags (`v1.0`, `v1.1`, …), tagged only on green CI.
- Zenodo: cite **concept DOIs**, not version DOIs.
- Paper front matter and metadata email: `dvfinnh@gmail.com`.
- David works on Windows 10 (GitHub Desktop, CMD/PowerShell): give
  Windows-native commands in instructions; CI itself runs Linux.

## Layout

    RequestProject/      Lean sources (PartA/PartB/PartC + PlufWO1 root
                         which runs the axiom audit; Main.lean is
                         Aristotle's options file, harmless)
    workorders/WOn/      per-commission trail (input tarball, WORKORDER,
                         REPORT, SUMMARY)
    scripts/             CI audit tooling
    .github/workflows/   CI

## Verification status (update on every merge)

| Result (paper) | Lean name | WO | Status |
|---|---|---|---|
| Paper II Lemma 3.6 (thinness) | `PlufWO1.thin` | WO-1 | awaiting first CI run |
| Paper II Prop 3.7 (no disjointly supported blocker) | `PlufWO1.noblock` | WO-1 | awaiting first CI run |
| Paper III Lemma 5.2 (normal ⇒ σ-Q, minima form) | `PlufWO1.minima_mem_of_fodor` (+ `sigmaQ_of_fodor`) | WO-1 | awaiting first CI run |
| supporting: σ-Q equivalences, transversal escape, W/block infrastructure, C1 | Part A/B/C | WO-1 | awaiting first CI run |

Everything else in Papers I–III is **hand-checked only**. In particular:
nothing of Paper I; Theorems A, C (both directions; sufficiency consumes
Mathias's theorem, absent from Mathlib — WO-era statements must be
hypothesis-parametrized), D, E, the blocking lemma and Theorem CH; at κ,
Theorems F, G, Corollary H, MSS-free existence, Theorem J. WO-2 target of
choice: Theorems F/G at κ (diagonal intersections + countable support; low
analytic risk).

## Known mathematical debts (do not lose)

- **Rigidity Conjecture** (Paper II, Conj. 3.8): every pluf extension of
  Φ(U) contains the witness W. WO-1 verifies the two partial theorems.
- **σ-Q sufficiency** (Paper III, Q 5.5): is σ-Q equivalent to maximality
  of the block filter at κ? Test case D⊗D.
- An earlier draft of Paper II claimed incompatible maximalizations for
  non-selective U; **withdrawn** (quantifier error). Any circulating draft
  or the first-edition lecture notes carrying that remark needs the fix.
