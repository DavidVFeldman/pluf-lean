# Which Lean theorem proves which printed assertion

This repository holds a single Lean 4 development covering all five papers of
the pluf series. The papers share a dependency chain — Paper II's
diagonalization theorem is stated against a package of lattice facts that
Paper I discharges, Paper IV's transfer theorem consumes Paper III's
mechanization, and Papers I and II share the Hilbert-basis block API and the
cardinal infrastructure — so the artifact is not separable into four. This
file is the index a reader checking one paper needs.

**How to check a claim.** Find the printed assertion below, note the Lean
name, and locate it in the listed file. Every name in the tables is audited:
the CI runs `scripts/check_axioms.py` against the build log, which fails
unless each name's `#print axioms` line is present and confined to
`propext`, `Classical.choice`, `Quot.sound`, and unless the sources are free
of `sorry`, `admit`, `axiom`, and `native_decide`. The build log is uploaded
as an artifact of every CI run.

**Quarantined classical inputs.** Four results from the literature are used
and never discharged; each enters only as a named hypothesis on the
statements that consume it, so every mechanized statement is a theorem of
ZFC:

| Input | Where it enters | Hypothesis form |
|---|---|---|
| Mathias, happy families | Paper II, Thm 3.4 sufficiency | `PlufWO5.MathiasHyp` |
| Marcus–Spielman–Srivastava (Kadison–Singer) | Paper I, Thm 4.1 | `PlufWO6.KSHyp` |
| Blecher–Weaver excision and regularity | Paper III, Thm 4.2 | `PlufWO8.BWPackage` (in `PlufWO8/BW.lean`) |
| Rowbottom homogeneity; Fodor | Paper IV, §§2–4; Paper III, Lemma 5.2 | `PlufWO4.RowbottomFor`, `PlufWO1.FodorProperty` |
| Aroca et al., supports of finite-dimensional spaces | Paper V, Thm 5.2 | `PlufWO17.AroKaHyp` |

The continuum hypothesis is likewise a hypothesis
(`Cardinal.continuum = Cardinal.aleph 1`), never an axiom, on the two
statements that use it.

---

## Paper I — *Ultrafilter limits in the projection lattice of a Hilbert space*

| Printed assertion | Lean name | File |
|---|---|---|
| Lemma 2.1 (maximality criterion) | `PlufWO6.maximality_criterion` | `PlufWO6/PartA.lean` |
| Lemma 2.1, converse | `PlufWO6.isPluf_of_criterion` | `PlufWO6/PartA.lean` |
| Lemma 2.2 (finite-dimensional ⇒ principal) | `PlufWO6.principal_of_finiteDimensional` | `PlufWO6/PartA.lean` |
| Lemma 2.2 (principal ⟺ nonzero intersection) | `PlufWO6.principal_iff_sInf_ne_bot` | `PlufWO6/PartA.lean` |
| Lemma 2.2 (nonprincipal ⊇ finite codimension) | `PlufWO6.finCodim_mem_of_nonprincipal` | `PlufWO6/PartA.lean` |
| Prop. 2.3 (no prime filters), in `H` | `PlufWO6.no_prime_filter` | `PlufWO6/PartB.lean` |
| Prop. 2.3, finite dimension ≥ 2 | `PlufWO9.no_prime_filter_finrank` | `PlufWO9.lean` |
| Prop. 2.3, any infinite orthonormal basis | `PlufWO9.no_prime_filter_paper` | `PlufWO9.lean` |
| Prop. 2.4 (topology of the pluf space) | `PlufWO6.PlufSpace.*` | `PlufWO6/PartCTop.lean` |
| Lemma 3.1 (radii of a slice) | `PlufWO6` Part D | `PlufWO6/PartD.lean`, `PlufWO6/PartDEllipsoid.lean` |
| Prop. 3.2 (gap criterion for RSP) | `PlufWO6.rsp_iff_sup_eq_inf` | `PlufWO6/PartD.lean` |
| Prop. 3.4 (the state face) | `PlufWO6` Part E | `PlufWO6/PartE.lean`, `PlufWO6/PartECompact.lean` |
| Thm. 4.1 (Kadison–Singer as RSP) | `PlufWO6.rsp_of_ks` | `PlufWO6/PartF.lean` |
| Remark 4.2 (converse half) | `PlufWO6.ks_of_blockRSP` | `PlufWO6/PartF.lean` |
| §5: the operator `T`, ampleness | `PlufWO13.T`, `PlufWO13.Ample` | `PlufWO13.lean` |
| Lemma 5.2 (radii of an ample slice) | `PlufWO13.minorRadius_of_ample` etc. | `PlufWO13.lean` |
| Lemma 5.3 (upward inheritance) | `PlufWO13.essSpec_compress_mono` | `PlufWO13.lean` |
| Lemma 5.4 (finite codimension) | `PlufWO13.essSpec_compress_eq_of_finCodim` | `PlufWO13.lean` |
| Lemma 5.5 (escape) | `PlufWO13.escape` | `PlufWO13.lean` |
| Remark 5.6 (functional-calculus-free form) | `PlufWO9.approx_eigen_span_spec` | `PlufWO9.lean` |
| **Lemma 5.6 (blocking lemma)** | `PlufWO14.blocking_lemma` | `PlufWO14.lean` |
| Thm. 5.7 (CH: all members ample) | `PlufWO15.exists_pluf_all_ample` | `PlufWO15.lean` |
| Thm. 5.7, failure of RSP | `PlufWO15.not_rsp_of_all_ample` | `PlufWO15.lean` |
| Prop. 5.9 (limits fill `[1/16, 1]`) | `PlufWO15.face_values_eq_Icc` | `PlufWO15.lean` |

Not mechanized: §6 (a summary of Paper III, verified there) and §7 (the
model-theoretic coda, which states no theorems).

---

## Paper II — *Intimate subspaces, block filters, and the diagonalization of maximal projection filters*

| Printed assertion | Lean name | File |
|---|---|---|
| Thm. 2.1 (Galvin's question; gliding hump) | `PlufWO5.gliding_hump` | `PlufWO5/PartA.lean` |
| Cor. 2.2 (relativized dichotomy) | `PlufWO5.relativized_dichotomy` | `PlufWO5/PartA.lean` |
| Lemma 3.2(a) (membership criterion) | `PlufWO5.phiOmega_iff_finCodim` | `PlufWO5/PartB.lean` |
| Lemma 3.2(b) (addability criterion) | `PlufWO5.addable_iff_infDim` | `PlufWO5/PartB.lean` |
| Thm. 3.4, necessity | `PlufWO5.necessity` | `PlufWO5/PartC.lean` |
| Thm. 3.4, sufficiency (Mathias-parametrized) | `PlufWO5.decides_of_mathias` | `PlufWO5/PartC.lean` |
| Lemma 3.6 (blockers are thin) | `PlufWO1.thin` | `PartB.lean` |
| Prop. 3.7 (no disjointly supported blocker) | `PlufWO1.noblock` | `PartC.lean` |
| Thm. 4.2 (Gowers's intimate subspace) | `PlufWO5.gowersX_intimate` | `PlufWO5/PartD.lean` |
| Thm. 4.2, dimension bound | `PlufWO5.gowersX_dim_bound` | `PlufWO5/PartD.lean` |
| Remark 4.4 (the finitely supported part) | `PlufWO5.gowersX_pairSum_eq_zero` | `PlufWO5/PartD.lean` |
| Prop. 4.6 (shape of nontrivial intimacy) | `PlufWO5.dense_zero_set` | `PlufWO5/PartA.lean` |
| Thm. 5.2 (diagonalizable ⟺ intimate) | `PlufWO5.diagonalizable_iff_intimate` | `PlufWO5/PartE.lean` |
| Thm. 5.2, for genuine plufs | `PlufWO6.diagonalizable_iff_intimate_pluf` | `PlufWO6/PartG.lean` |
| Thm. 5.2, at an arbitrary basis (Remark 5.3) | `PlufWO10.diagonalizableB_iff_intimateB` | `PlufWO10.lean` |
| Prop. 5.5 (one-witness reduction) | `PlufWO10.one_witness_reduction` | `PlufWO10.lean` |
| **Thm. 5.4 (CH: no basis diagonalizes)** | `PlufWO12.exists_nonprincipal_nondiagonalizable` | `PlufWO12.lean` |
| Prop. 6.1 (chains never suffice) | `PlufWO10.chains_never_suffice` | `PlufWO10.lean` |

The package of lattice facts against which Thm. 5.2 is stated
(`PlufWO5.PlufPackage`) is discharged for every nonprincipal pluf by
`PlufWO6.plufPackage_of_isPluf`, which is what makes the printed statement
about maximal filters a theorem rather than a conditional.

---

## Paper III — *Projection-lattice ultrafilters at a measurable cardinal*

| Printed assertion | Lean name | File |
|---|---|---|
| Thm. 2.1 (exact paving) | `PlufWO2.exact_paving` | `PlufWO2.lean` |
| Cor. 2.2 (flattening, quadratic form) | `PlufWO3.quadratic_flat` | `PlufWO3.lean` |
| Ultrafilter limits of bounded functions | `PlufWO3.exists_ulim` | `PlufWO3.lean` |
| Thm. 3.1 (exact dichotomy) | `PlufWO2.exact_dichotomy` | `PlufWO2.lean` |
| Cor. 3.2, lattice half | `PlufWO2.block_filter_decides` | `PlufWO2.lean` |
| Cor. 3.2, filter half | `PlufWO3.PhiU_*` | `PlufWO3.lean` |
| Thm. 4.1 (φ_U is a state) | `PlufWO8.isState_phiLim` | `PlufWO8.lean` |
| Thm. 4.1, singularity | `PlufWO8.phiLim_compact_eq_zero` | `PlufWO8.lean` |
| Thm. 4.1, countable additivity | `PlufWO8.phiLim_iSup` | `PlufWO8.lean` |
| Thm. 4.1, `<κ`-additivity (generic index) | `PlufWO8.phiLim_iSup_eq_zero_generic` | `PlufWO8.lean` |
| Thm. 4.1, purity | `PlufWO8.phiLim_pure` | `PlufWO8.lean` |
| **Thm. 4.2 (countably additive pure ⇒ pluf)** | `PlufWO8.isPluf_oneSet` | `PlufWO8.lean` |
| Cor. 4.4 (`F_φ = Φ(U)`) | `PlufWO8.oneSet_phiLim_eq_PhiU` | `PlufWO8.lean` |
| Lemma 5.2 (normal ⇒ σ-Q-point) | `PlufWO1.minima_mem_of_fodor` | `PartA.lean` |
| σ-Q-point equivalences | `PlufWO1.sigmaQ_of_partition_selectors` etc. | `PartA.lean` |
| Prop. 5.3 (κ-witness), combinatorial half | `PlufWO1.exists_transversal_not_mem` | `PartA.lean` |
| Prop. 5.3 (κ-witness), Hilbert half | `PlufWO3.kappa_witness` | `PlufWO3.lean` |

`PlufWO3.Wk_inf_block_eq_bot_iff` certifies that a block meets the witness
trivially exactly when its index set is a partial selector;
`PlufWO3.Wk_inf_block_eq_bot_iff_counterexample` certifies that the covering
hypothesis is necessary there.

---

## Paper IV — *Exact paving for Fubini products of normal measures*

| Printed assertion | Lean name | File |
|---|---|---|
| Lemma 2.2 (full selectors) | `PlufWO4.fullSelector_of_fodor` | `PlufWO4/Fubini.lean` |
| Prop. 2.3 (product ≇ normal) | `PlufWO4.fubini_not_iso_fodor` | `PlufWO4/Fubini.lean` |
| Thm. 3.1 (injectivity on a square) | `PlufWO4.inj_on_pairs` | `PlufWO4/Homog.lean` |
| Cor. 3.2 (product is σ-Q) | `PlufWO4.sigmaQ_fubini` | `PlufWO4/Fubini.lean` |
| **Thm. 4.1 (exact paving for the product)** | `PlufWO4.EPP_fubini` | `PlufWO4/EPP.lean` |
| Def. 5.1 (EPP) and EPP ⇒ σ-Q | `PlufWO4.EPP`, `PlufWO4.sigmaQ_of_EPP` | `PlufWO4/EPP.lean` |
| Thm. 5.2, operator paving | `PlufWO4.exact_paving_of_EPP` | `PlufWO4/EPP.lean` |
| Thm. 5.2, dichotomy and flattening | `PlufWO4.exact_dichotomy_of_EPP`, `quadratic_flat_of_EPP` | `PlufWO4/EPP.lean` |
| Cor. 5.3 (answer to Paper III, Q. 5.5) | `PlufWO4.product_decides` | `PlufWO4/EPP.lean` |
| Lemma 6.1 (generalized thinness) | `PlufWO4.gen_thin` | `PlufWO4/Blockers.lean` |
| Lemma 6.2 (support lemma) | `PlufWO4.support_mem` | `PlufWO4/Blockers.lean` |
| Lemma 6.3 (Baire piece-spread) | `PlufWO4.baire_spread` | `PlufWO4/Blockers.lean` |

Not mechanized: the finite-power remark of §4, and the state-theoretic
clauses of Thm. 5.2 (singleton face, round slices) — the face machinery is
verified for Paper I, but its transfer to ultrafilters given only by EPP is
not part of this development.

---

## Paper V — *Support families of closed subspaces of $\ell^2$*

| Printed assertion | Lean name | File |
|---|---|---|
| Lemma 2.1 (union of two supports) | `PlufWO16.exists_supp_union` | `PlufWO16/PartA.lean` |
| Prop. 2.2 (countable unions; where closedness enters) | `PlufWO16.exists_supp_iUnion` | `PlufWO16/PartA.lean` |
| Cor. 2.3 (arbitrary unions) | `PlufWO16.exists_supp_sUnion` | `PlufWO16/PartA.lean` |
| Prop. 3.2 (elimination; minimality not needed) | `PlufWO16.exists_supp_elimination` | `PlufWO16/PartA.lean` |
| Thm. 4.3 (S1) | `PlufWO17.suppFamily_sUnion_closed` | `PlufWO17/PartA.lean` |
| Thm. 4.3 (S2, finite deletions) | `PlufWO17.suppFamily_elimination_finite` | `PlufWO17/PartA.lean` |
| Thm. 5.1 (Aroca et al.) — **quarantined** | `PlufWO17.AroKaHyp` | `PlufWO17/Basic.lean` |
| Thm. 5.2 (finite-rank classification) | `PlufWO17.suppFamily_isScrawlFamily` | `PlufWO17/PartB.lean` |
| Thm. 5.2, the transfer into $\ell^2$ | `PlufWO17.exists_realization_in_lp` | `PlufWO17/PartB.lean` |
| Lemma 6.1 (zeros of an exponential sum) | `PlufWO17.expSum_zeros_lt` | `PlufWO17/PartC.lean` |
| Example 6.2 (every cofinite set is a support) | `PlufWO17.exists_supp_compl_finite` | `PlufWO17/PartC.lean` |
| §6 conditional (no scrawl family) | `PlufWO17.not_isScrawlFamily_of_cofiniteOnly` | `PlufWO17/PartC.lean` |
| Lemma 7.2 (meet nonzero ⟺ contains a support) | `PlufWO16.mem_cD_iff` | `PlufWO16/PartB.lean` |
| Prop. 7.3 (the trace formula) | `PlufWO16.trace_subset`, `mem_trace_of_forall_cD` | `PlufWO16/PartB.lean` |
| Prop. 7.5 (consistency ⟺ membership in a diagonalizable pluf) | `PlufWO16.diagonallyConsistent_iff` | `PlufWO16/PartB.lean` |
| **Thm. 7.6 (the covering criterion)** | `PlufWO16.diagonallyConsistent_iff_not_finiteCover` | `PlufWO16/PartB.lean` |
| Prop. 8.1 (intimate ⟺ no two-cover) | `PlufWO16.intimate_iff_no_two_cover` | `PlufWO16/PartC.lean` |
| Prop. 8.2 (the collapse) | `PlufWO16.diagonallyConsistent_of_mem_diagonalizable` | `PlufWO16/PartC.lean` |
| Cor. 8.3 (three equivalent conditions on a pluf) | `PlufWO16.diagonalizable_iff_all_diagonallyConsistent` | `PlufWO16/PartC.lean` |
| **Thm. 8.4 ($\chi$ of Gowers's subspace is 3)** | `PlufWO16.gowersX_threeCover` | `PlufWO16/PartC.lean` |
| Prop. 8.5 (addable blockers) | `PlufWO16.diagonallyConsistent_of_addableBlocker` | `PlufWO16/PartC.lean` |

The matroid vocabulary of §§4–5 — circuit families, independence, the
maximality axiom, scrawl families — is defined in `PlufWO17/Basic.lean` in
terms of families of subsets of ℕ. Nothing is imported from Mathlib's matroid
API, which has no constructor from a circuit family. Question 9.3 is open and
is supplied as a hypothesis to the §6 conditional.

---

## Infrastructure not tied to a single paper

`PlufWO7a` is a scoping census: probes establishing what Mathlib does and
does not provide (it has no essential spectrum, Calkin algebra, Fredholm
theory, or Borel functional calculus). `PlufWO9` harvests that material into
a stable API: the essential spectrum by Weyl sequences, the
approximate-eigenvector substitute for spectral subspaces, blocks relative to
an arbitrary Hilbert basis, and the ω₁ machinery. `PlufWO11` supplies the
cardinal arithmetic — the closed subspaces, the ℕ-indexed orthonormal bases
and the bounded operators each number the continuum — and the CH
enumerations the two transfinite constructions consume.
