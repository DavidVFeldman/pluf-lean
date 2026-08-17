# Verification campaign — pluf papers I–IV

**Target ("totally verified"):** every assertion of the authors in Papers
I–IV machine-checked as a ZFC theorem, with each classical import isolated
as a named hypothesis discharged by citation. The quarantined imports, fixed
once and for all: **Mathias** (happy families / Ramsey for analytic sets),
**Marcus–Spielman–Srivastava** (paving), **Blecher–Weaver** (excision and
the regularity theory), **Rowbottom** (homogeneity for normal measures),
**Fodor** (pressing-down for normal measures). Nothing else may be assumed.

Status after WO-1–WO-3 (CI green, 39 theorems): Paper III's lattice level
complete; Paper II's rigidity pair complete.

## The commissions

**WO-4 (this tarball).** Paper IV in full, hypothesis-parametrized
(Rowbottom, Fodor, pivots), plus its ω-lemmas D1–D3. On completion: Paper
IV totally verified; Papers II–III gain the D-lemmas and the EPP
re-parametrization.

**WO-5 — Paper II, sections 2–5 (minus Theorem 5.4).** The membership and
addability criteria (Lemma 3.2: finite-codimension calculus in blocks);
Theorem 3.4 necessity in full (the dimension/codimension computations of
the witness); Theorem 3.4 sufficiency **parametrized by a Mathias
hypothesis** (the dichotomy conclusion for the analytic family, stated as
a hypothesis on the ultrafilter); Theorem 2.1 (the gliding hump, with the
explicit 1/48 estimate); Corollary 2.2; Gowers's construction (Theorem
4.1: explicit vectors, the duplication identity, the echelon rank bound);
Proposition 4.2; Theorem 5.1 (diagonalizable ⟺ intimate) and Corollary
5.2; Propositions 5.5–5.6 (one-witness reduction; coordinatization of
chains via orthomodular decomposition). Assessment: no new analytic
infrastructure; largest items are the gliding hump (series estimates) and
chain coordinatization (Hilbert-sum bookkeeping).

**WO-6 — Paper I, sections 2–4.** The maximality criterion and
finite-dimension lemmas; no-prime-filters (finite-dimensional
Kochen–Specker-style geometry); the pluf-space topology; radii/gap/slice
formulas; the face S_p (states as positive normalized functionals on
bounded operators, weak-* compactness via Banach–Alaoglu, RSP ⟺
singleton); Theorem 4.1 **parametrized by a paving hypothesis** (the MSS
conclusion), including the Anderson-style equivalence with (⋆); the
interval proposition. Assessment: the state-theoretic packaging is the
work; Mathlib's weak-* and dual-space API should carry it, but the census
must confirm what exists for states on B(H) before proofs are attempted.

**WO-7 — the transfinite constructions.** Paper I, section 5 (ample
subspaces, upward inheritance, escape, the blocking lemma, Theorem 5.6
under CH, the interval corollary) and Paper II, Theorem 5.4. Assessment:
the campaign's long pole, for two reasons to be resolved in this order:
(i) essential-spectrum infrastructure (Weyl sequences, invariance under
finite-codimension passage, two-sided accumulation criteria) is not
expected in Mathlib and must be either built or hypothesis-parametrized —
a scoping census is the first deliverable, possibly as its own
mini-commission WO-7a; (ii) the ω₁-recursions themselves (CH as a
hypothesis giving enumerations; countable elementary bookkeeping at limit
stages). Nothing here is conceptually beyond the existing artifacts, but
the volume is largest.

**WO-8 — Paper III, sections 4–5, and Paper I, section 6 residue.**
MSS-free existence; Theorem 4.2 (the 1-set of a countably additive pure
state is a pluf) **parametrized by an excision hypothesis** and the
Blecher–Weaver regularity facts as hypotheses; the coincidence
corollaries; Paper I's thm:meas restated against the now-verified
Paper III/IV results. Assessment: small once WO-6's state infrastructure
exists; sequence after WO-6.

## Sequencing and invariants

Order: WO-4, WO-5, WO-6, WO-8, WO-7 (WO-7a census may run any time after
WO-4). Every commission: census-first; report-rather-than-repair with the
WO-3 codified license; the full prior theorem set stays green; the audit
script extends with each merge; papers learn of results only after CI.
Endgame: when WO-7 lands green, the series is totally verified in the
campaign's sense; only then do public release, two-component tagging, and
Zenodo archival (concept DOI) proceed, per the project's standing rule
that GitHub-as-publication waits for the finish.
