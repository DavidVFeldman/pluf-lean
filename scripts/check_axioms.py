#!/usr/bin/env python3
"""Axiom audit for the pluf-lean CI.

Reads the `lake build` log and verifies that every contract theorem's
`#print axioms` line is present and uses only whitelisted axioms; also scans
the Lean sources for forbidden tokens outside comments.

Exit code 0 iff everything passes. Run from the repository root:
    python3 scripts/check_axioms.py build.log
"""
import re
import sys
from pathlib import Path

WHITELIST = {"propext", "Classical.choice", "Quot.sound"}

CONTRACT_THEOREMS = [
    # Part A
    "PlufWO1.not_mem_union_of_not_mem",
    "PlufWO1.sigmaQ_of_partition_selectors",
    "PlufWO1.sigmaQ_of_partition_selectors\u2080",
    "PlufWO1.partition_selectors_of_sigmaQ",
    "PlufWO1.minima_mem_of_fodor",
    "PlufWO1.sigmaQ_of_fodor",
    "PlufWO1.exists_transversal_not_mem",
    # Part B
    "PlufWO1.constraintVec_apply",
    "PlufWO1.constraintVec_ne_zero",
    "PlufWO1.mem_block_iff",
    "PlufWO1.isClosed_block",
    "PlufWO1.inner_constraintVec_eq_zero_of_disjoint",
    "PlufWO1.mem_W_iff",
    "PlufWO1.thin",
    # Part C
    "PlufWO1.closure_span_inter_block",
    "PlufWO1.noblock",
    # WO-2, Part D
    "PlufWO2.countable_supp",
    "PlufWO2.coordCLM_apply",
    "PlufWO2.mem_block_iff",
    "PlufWO2.isClosed_block",
    "PlufWO2.evec_mem_block",
    # WO-2, Parts E and F
    "PlufWO2.exact_paving",
    "PlufWO2.exact_dichotomy",
    "PlufWO2.block_filter_decides",
    # WO-3, Part G
    "PlufWO3.exists_ulim",
    "PlufWO3.quadratic_flat",
    # WO-3, Part H
    "PlufWO3.PhiU_upward",
    "PlufWO3.inf_mem_PhiU",
    "PlufWO3.bot_notMem_PhiU",
    "PlufWO3.iInf_mem_PhiU",
    "PlufWO3.PhiU_nonprincipal",
    "PlufWO3.PhiU_decides",
    # WO-3, Part I
    "PlufWO3.supp_kConstraintVec",
    "PlufWO3.mem_Wk_iff",
    "PlufWO3.isClosed_Wk",
    "PlufWO3.Wk_notMem_PhiU",
    "PlufWO3.Wk_inf_block_eq_bot_iff",
    "PlufWO3.kappa_witness",
    # WO-3, report item (formalized counterexample to the un-repaired I3)
    "PlufWO3.Wk_inf_block_eq_bot_iff_counterexample",
    # WO-4 (Paper IV): Parts A-D plus auxiliaries
    "PlufWO4.inj_on_pairs",
    "PlufWO4.mem_fubini_iff",
    "PlufWO4.triangle_mem_fubini",
    "PlufWO4.countableSmall_fubini",
    "PlufWO4.column_notMem_fubini",
    "PlufWO4.fullSelector_of_fodor",
    "PlufWO4.not_fullSelector_fubini",
    "PlufWO4.fullSelector_map_iff",
    "PlufWO4.fubini_not_iso_fodor",
    "PlufWO4.sigmaQ_fubini",
    "PlufWO4.sigmaQ_of_EPP",
    "PlufWO4.EPP_fubini",
    "PlufWO4.exact_paving_of_EPP",
    "PlufWO4.exact_dichotomy_of_EPP",
    "PlufWO4.quadratic_flat_of_EPP",
    "PlufWO4.PhiU_decides_of_EPP",
    "PlufWO4.product_decides",
    "PlufWO4.gen_thin",
    "PlufWO4.inter_infinite_iff_mem",
    "PlufWO4.rank_le_of_le_block_finite",
    "PlufWO4.support_mem",
    "PlufWO4.baire_spread",
    "PlufWO4.exists_avoiding_homog",
    "PlufWO4.fullSelectorAll_of_fodor",
    "PlufWO4.not_fullSelectorAll_fubini",
    "PlufWO4.fullSelectorAll_map_iff",
    # WO-5 (Paper II, Parts A-E) plus the formalized E2 obstruction
    "PlufWO5.gliding_hump",
    "PlufWO5.relativized_dichotomy",
    "PlufWO5.dense_zero_set",
    "PlufWO5.phiOmega_iff_finCodim",
    "PlufWO5.addable_iff_infDim",
    "PlufWO5.bot_not_phiOmega",
    "PlufWO5.witness_not_mem",
    "PlufWO5.witness_infDim",
    "PlufWO5.necessity",
    "PlufWO5.decides_of_mathias",
    "PlufWO5.isClosed_gowersX",
    "PlufWO5.gowersX_intimate",
    "PlufWO5.gowersX_dim_bound",
    "PlufWO5.gowersX_no_finCodim",
    "PlufWO5.diagonalizable_iff_intimate",
    "PlufWO5.diagonalizable_iff_extends_phiOmega",
    "PlufWO5.exists_phiOmega_not_isClosed",
    # WO-6 (Paper I §§2-4, package discharge) incl. counterexamples and extras
    "PlufWO6.maximality_criterion",
    "PlufWO6.isPluf_of_criterion",
    "PlufWO6.principal_of_finiteDimensional",
    "PlufWO6.principal_iff_sInf_ne_bot",
    "PlufWO6.finCodim_mem_of_nonprincipal",
    "PlufWO6.no_prime_filter",
    "PlufWO6.pluf_sets_inter",
    "PlufWO6.pluf_compl_eq_iUnion",
    "PlufWO6.lower_le_upper",
    "PlufWO6.rsp_iff_sup_eq_inf",
    "PlufWO6.face_nonempty",
    "PlufWO6.face_iff_sandwich",
    "PlufWO6.face_isFace",
    "PlufWO6.rsp_all_iff_face_subsingleton",
    "PlufWO6.rsp_of_ks",
    "PlufWO6.ks_of_blockRSP",
    "PlufWO6.plufPackage_of_isPluf",
    "PlufWO6.diagonalizable_iff_intimate_pluf",
    "PlufWO6.isPluf_empty_zero_space",
    "PlufWO6.empty_filter_is_prime",
    "PlufWO6.pluf_sets_inter_counterexample",
    "PlufWO6.convex_stateFace",
    "PlufWO6.isClosed_stateFace",
    "PlufWO6.isCompact_stateFace",
    "PlufWO6.minorRadius_eq",
    "PlufWO6.majorRadius_eq",
    "PlufWO6.eccentricity_eq",
    "PlufWO6.rsp_iff_rspEcc",
    "PlufWO6.PlufSpace.isTopologicalBasis_plufBasis",
    "PlufWO6.PlufSpace.isClopen_hat",
    "PlufWO6.PlufSpace.isOpen_singleton_principal",
    "PlufWO6.PlufSpace.dense_principal",
    "PlufWO6.PlufSpace.not_compactSpace",
    # WO-8 (Paper III §§4-5, Paper I §6): state theory, excision-parametrized
    "PlufWO8.phiLim_spec",
    "PlufWO8.isState_phiLim",
    "PlufWO8.phiLim_rankOne_eq_zero",
    "PlufWO8.phiLim_finiteDimensional_eq_zero",
    "PlufWO8.phiLim_iSup_eq_zero",
    "PlufWO8.phiLim_iSup",
    "PlufWO8.phiLim_iSup_eq_zero_generic",
    "PlufWO8.phiLim_mem_face",
    "PlufWO8.phiLim_pure",
    "PlufWO8.oneSet_upward",
    "PlufWO8.oneSet_inf",
    "PlufWO8.bot_notMem_oneSet",
    "PlufWO8.exists_oneSet_inf_eq_bot",
    "PlufWO8.isPluf_oneSet",
    "PlufWO8.oneSet_nonprincipal",
    "PlufWO8.oneSet_phiLim_eq_PhiU",
    "PlufWO8.phiLim_finiteRank_eq_zero",
    "PlufWO8.phiLim_compact_eq_zero",
    # WO-7a (scoping probes; incl. target (d) closed and the Q2 refutation)
    "PlufWO7a.tendsto_norm_proj_finiteDimensional_of_weaklyNull",
    "PlufWO7a.exists_weyl_sequence_in_orthogonal",
    "PlufWO7a.essSpec_le_of_finCodim",
    "PlufWO7a.tendsto_inner_of_orthonormal",
    "PlufWO7a.exists_orthonormal_approx_eigenvectors",
    "PlufWO7a.isClosed_essSpec",
    "PlufWO7a.countable_of_orthonormal",
    "PlufWO7a.hilbertBasis_nat_of_decomposition_false",
    "PlufWO7a.exists_countable_hilbertBasis_of_decomposition",
    "PlufWO7a.hilbertBasis_reindex",
    "PlufWO7a.mem_blockB_iff",
    "PlufWO7a.exists_enumeration_of_CH",
    "PlufWO7a.exists_omega1_chain",
    "PlufWO7a.exists_pair_sup_top_notMem",
    "PlufWO7a.no_prime_filter_of_finrank_ge_two",
    "PlufWO7a.no_prime_filter_odd_finrank",
    # WO-9 (harvest: Prop 2.3 paper-facing, essSpec, approx-eigen substitute, blockB, omega-1)
    "PlufWO9.no_prime_filter_finrank",
    "PlufWO9.no_prime_filter_paper",
    "PlufWO9.no_prime_filter_of_finrank_ge_two",
    "PlufWO9.no_prime_filter_of_infinite_hilbertBasis",
    "PlufWO9.exists_orthonormal_approx_eigenvectors_mem",
    "PlufWO9.mem_blockB_iff_inner",
    "PlufWO9.isClosed_essSpec",
    "PlufWO9.essSpec_le_of_finCodim",
    "PlufWO9.essSpec_subset_essSpec_compress",
    "PlufWO9.tendsto_norm_proj_finiteDimensional_of_weaklyNull",
    "PlufWO9.exists_orthonormal_approx_eigenvectors",
    "PlufWO9.approx_eigen_span_spec",
    "PlufWO9.mem_blockB_iff",
    "PlufWO9.isClosed_blockB",
    "PlufWO9.blockB_stdBasis_eq",
    "PlufWO9.hilbertBasis_reindex",
    "PlufWO9.exists_countable_hilbertBasis_of_decomposition",
    "PlufWO9.exists_enumeration_of_CH",
    "PlufWO9.exists_omega1_chain",
    # WO-10 (target (a) closed: Zorn extension, chain coordinatization, Props 5.5 & 6.1)
    "PlufWO10.exists_pluf_extension",
    "PlufWO10.exists_pluf_of_directed",
    "PlufWO10.chain_decomposition",
    "PlufWO10.exists_basis_blocks_of_chain",
    "PlufWO10.exists_basis_blocks_of_chain_false",
    "PlufWO10.blockB_inf_blockB",
    "PlufWO10.intimateB_blockB",
    "PlufWO10.intimateB_mono",
    "PlufWO10.intimateB_stdHilbertBasis_iff",
    "PlufWO10.chains_never_suffice",
    "PlufWO10.chains_never_suffice_false",
    "PlufWO10.diagonalizableB_iff_intimateB",
    "PlufWO10.one_witness_reduction",
    # WO-11 (cardinal infrastructure for the transfinite commissions)
    "PlufWO11.mk_closedSubspaces",
    "PlufWO11.mk_hilbertBases",
    "PlufWO11.mk_continuousLinearMaps",
    "PlufWO11.mk_selfAdjoint",
    "PlufWO11.exists_enum_closedSubspaces",
    "PlufWO11.exists_enum_hilbertBases",
    "PlufWO11.exists_enum_selfAdjoint",
    "PlufWO11.countable_Iio_of_lt_omega1",
    "PlufWO11.countable_iUnion_Iio",
    "PlufWO11.exists_orthogonal_of_countable",
    "PlufWO11.span_ne_top_of_countable",
    "PlufWO11.exists_notMem_of_countable_closed_proper",
    "PlufWO11.orthogonal_ne_bot_of_isClosed_ne_top",
    "PlufWO11.exists_orthogonal_of_countable_false",
    "PlufWO11.closedSpan_countable_eq_top_counterexample",
    "PlufWO11.orthogonal_finiteDimensional_counterexample",
    "PlufWO11.mk_eq_continuum_of_hilbertBasis",
    "PlufWO11.mk_continuousLinearMaps_of_hilbertBasis",
    # WO-13 (Paper I §5 ZFC lemmas: T, ampleness, inheritance, escape)
    "PlufWO13.T_evec",
    "PlufWO13.T_selfAdjoint",
    "PlufWO13.T_bounds",
    "PlufWO13.one_mem_essSpec",
    "PlufWO13.sixteenth_mem_essSpec",
    "PlufWO13.infinite_dimensional_of_ample",
    "PlufWO13.minorRadius_of_ample",
    "PlufWO13.majorRadius_of_ample",
    "PlufWO13.eccentricity_of_ample",
    "PlufWO13.ample_top",
    "PlufWO13.essSpec_compress_mono",
    "PlufWO13.ample_of_ample_le",
    "PlufWO13.essSpec_compress_eq_of_finCodim",
    "PlufWO13.ample_of_finCodim",
    "PlufWO13.escape",
    "PlufWO13.quadratic_estimate_of_bound",
    "PlufWO13.infinite_codim_of_escape",
    # WO-14 (Paper I Lemma 5.6, THE BLOCKING LEMMA - proved unconditionally)
    "PlufWO14.finCodim_of_constraints",
    "PlufWO14.exists_unit_constrained_rayleigh",
    "PlufWO14.exists_unit_constrained_rayleigh_notMem",
    "PlufWO14.exists_unit_constrained_rayleigh_notMem_other",
    "PlufWO14.perturb_unit",
    "PlufWO14.exists_decreasing_cofinal",
    "PlufWO14.exists_blocking_sequence",
    "PlufWO14.compress_exact_diagonal",
    "PlufWO14.blocking_lemma_of_sequence",
    "PlufWO14.blocking_lemma",
    # WO-12 (Paper II Thm 5.4: CH construction of a non-diagonalizable pluf)
    "PlufWO12.exists_constrained_notMem",
    "PlufWO12.exists_two_nonzero_coords",
    "PlufWO12.exists_nonIntimate_blocking",
    "PlufWO12.exists_enum_vectors",
    "PlufWO12.exists_decreasing_cofinal",
    "PlufWO12.exists_witness_family",
    "PlufWO12.exists_nonprincipal_nondiagonalizable",
    # WO-15 (FINAL: Paper I Thm 5.7 and Prop 5.9 - the CH construction)
    "PlufWO15.exists_admissible_decides",
    "PlufWO15.admissible_iUnion",
    "PlufWO15.admissible_iUnion_counterexample",
    "PlufWO15.exists_admissible_chain",
    "PlufWO15.exists_pluf_all_ample",
    "PlufWO15.not_rsp_of_all_ample",
    "PlufWO15.radii_of_all_ample",
    "PlufWO15.face_apply_mem_Icc",
    "PlufWO15.exists_face_state_apply_eq",
    "PlufWO15.face_values_eq_Icc",
    # WO-16 (Paper V: support families, covering criterion, series transfers)
    "PlufWO16.exists_supp_union",
    "PlufWO16.exists_supp_iUnion",
    "PlufWO16.exists_supp_sUnion",
    "PlufWO16.exists_supp_elimination",
    "PlufWO16.mem_cD_iff",
    "PlufWO16.cI_downward",
    "PlufWO16.trace_subset",
    "PlufWO16.mem_trace_of_forall_cD",
    "PlufWO16.diagonallyConsistent_iff",
    "PlufWO16.diagonallyConsistent_iff_not_finiteCover",
    "PlufWO16.intimate_iff_no_two_cover",
    "PlufWO16.diagonallyConsistent_of_mem_diagonalizable",
    "PlufWO16.diagonalizable_iff_all_diagonallyConsistent",
    "PlufWO16.gowersX_pairSum_rec",
    "PlufWO16.mem_gowersX_iff_pairSum_rec",
    "PlufWO16.mem_cI_gowersX_iff",
    "PlufWO16.gowersX_threeCover",
    "PlufWO16.diagonallyConsistent_of_addableBlocker",
]

FORBIDDEN = ["sorry", "admit", "native_decide"]

def strip_comments(src: str) -> str:
    """Remove Lean comments, honouring NESTED block comments.

    Lean's `/- ... -/` nests, and this project's files quote contract text
    (which itself contains `-/`) inside comments under the
    report-rather-than-repair protocol. A non-greedy regex terminates at the
    first inner `-/` and leaves real-looking code exposed, producing spurious
    forbidden-token hits. Hence the explicit scanner below.
    """
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif two == "--":
            j = src.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)

def main(logpath: str) -> int:
    ok = True
    log = Path(logpath).read_text(encoding="utf-8")

    # 1. Every contract theorem has an axiom line within the whitelist.
    for thm in CONTRACT_THEOREMS:
        pat = re.compile(re.escape(f"'{thm}'") + r"\s+depends on axioms:\s*\[([^\]]*)\]")
        m = pat.search(log)
        if not m:
            print(f"FAIL missing axiom line for {thm}")
            ok = False
            continue
        axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
        bad = axioms - WHITELIST
        if bad:
            print(f"FAIL {thm} uses non-whitelisted axioms: {sorted(bad)}")
            ok = False
        else:
            print(f"OK   {thm}: {sorted(axioms)}")

    # 2. Nothing in the log mentions sorryAx (belt and braces).
    if "sorryAx" in log:
        print("FAIL build log mentions sorryAx")
        ok = False

    # 3. Source scan for forbidden tokens outside comments; bare `axiom`
    #    declarations are forbidden too.
    for f in sorted(Path("RequestProject").glob("*.lean")):
        s = strip_comments(f.read_text(encoding="utf-8"))
        for tok in FORBIDDEN:
            if re.search(r"\b" + tok + r"\b", s):
                print(f"FAIL forbidden token '{tok}' in {f}")
                ok = False
        if re.search(r"^\s*axiom\b", s, flags=re.M):
            print(f"FAIL axiom declaration in {f}")
            ok = False

    print("AUDIT " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "build.log"))
