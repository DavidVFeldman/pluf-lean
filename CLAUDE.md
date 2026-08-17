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
| Paper II Lemma 3.6 (thinness) | `PlufWO1.thin` | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |
| Paper II Prop 3.7 (no disjointly supported blocker) | `PlufWO1.noblock` | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |
| Paper III Lemma 5.2 (normal ⇒ σ-Q, minima form) | `PlufWO1.minima_mem_of_fodor` (+ `sigmaQ_of_fodor`) | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |
| supporting: σ-Q equivalences, transversal escape, W/block infrastructure, C1 | Part A/B/C | WO-1 | **verified** (CI #1, commit `1be8bac`, 2026-08-16) |

Axiom footprint of every WO-1 and WO-2 theorem (24 in all): `propext`,
`Classical.choice`, `Quot.sound` (build-log artifacts of CI runs #1 and #2).

| Paper III Cor 2.2 (diagonal flattening; certified w/o self-adjointness) | `PlufWO3.quadratic_flat` (+`exists_ulim`) | WO-3 | awaiting CI run #3 |
| Paper III Cor 3.2, filter half (Φ(U): proper, upward, ∩-closed, generically complete, nonprincipal, decides) | `PlufWO3` Part H | WO-3 | awaiting CI run #3 |
| Paper III Prop 5.3, Hilbert half (κ-witness) | `PlufWO3.kappa_witness` (+Part I) | WO-3 | awaiting CI run #3 |

**WO-3 ratified repair:** contracted I3 (`Wk_inf_block_eq_bot_iff`) was FALSE
without a covering hypothesis; Aristotle formalized the counterexample
(`Wk_inf_block_eq_bot_iff_counterexample`), preserved the contract in a
comment, and repaired with `hcover` (present at all use sites). Ratified
2026-08-16; the paper is unaffected (its partition covers κ). Unused
contract hypotheses flagged and retained: `hcc` in G1 (boundedness suffices),
`hne` in I3/I4. G2 certified without self-adjointness.

**Protocol codification (from the WO-3 precedent):** future work orders
license the following on a false contract statement: formalize a
counterexample where feasible, preserve the contract verbatim in a comment,
and MAY supply a minimally repaired statement clearly marked as such —
subject to commissioner ratification at audit.

| Paper III Thm 2.1 (exact paving) | `PlufWO2.exact_paving` | WO-2 | **verified** (CI #2, 2026-08-16) |
| Paper III Thm 3.1 (exact dichotomy) | `PlufWO2.exact_dichotomy` | WO-2 | **verified** (CI #2, 2026-08-16) |
| Paper III Cor 3.2, lattice half | `PlufWO2.block_filter_decides` | WO-2 | **verified** (CI #2, 2026-08-16) |
| supporting: κ-infrastructure (countable supports, blocks, coordCLM at κ) | `PlufWO2` Part D | WO-2 | **verified** (CI #2, 2026-08-16) |

Everything else in Papers I–III is **hand-checked only**. In particular:
nothing of Paper I; Theorems A, C (both directions; sufficiency consumes
Mathias's theorem, absent from Mathlib — WO-era statements must be
hypothesis-parametrized), D, E, the blocking lemma and Theorem CH; at κ,
MSS-free existence and Theorem J (state-theoretic; consume Blecher–Weaver
excision, out of scope until that theory exists in Mathlib). Paper III's
lattice level is now fully covered by WO-1–WO-3. Next WO candidate:
Paper II's Theorem C necessity witness at ω (requires the finite-codimension
membership calculus of lem:criteria).

## Known mathematical debts (do not lose)

- **Rigidity Conjecture** (Paper II, Conj. 3.8): every pluf extension of
  Φ(U) contains the witness W. WO-1 verifies the two partial theorems.
- **σ-Q sufficiency** (Paper III, Q 5.5): is σ-Q equivalent to maximality
  of the block filter at κ? Test case D⊗D.
- An earlier draft of Paper II claimed incompatible maximalizations for
  non-selective U; **withdrawn** (quantifier error). Any circulating draft
  or the first-edition lecture notes carrying that remark needs the fix.
