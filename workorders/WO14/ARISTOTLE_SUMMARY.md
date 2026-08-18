# Summary of changes for run 1568a3c6-acca-47b9-8da7-e1b4c180f62a
Work order WO-14 (Paper I, Lemma 5.6 — the blocking lemma) is complete.

**What was delivered**

`RequestProject/PlufWO14.lean` (~885 lines) contains all eight contracted items, with every contract statement kept verbatim:

- **S0** `finCodim_of_constraints` — finitely many continuous functionals cut a closed subspace to a closed subspace of finite codimension, in the quotient form required downstream.
- **S1** `exists_unit_constrained_rayleigh` — constrained unit vector with Rayleigh value near a point of the essential spectrum of the compression.
- **S2** `exists_unit_constrained_rayleigh_notMem` — the same, additionally off the closed subspace `N`, at a blocked value.
- **P1** `perturb_unit` — the two-vector perturbation lemma preserving all shared continuous linear constraints.
- **W0** `exists_decreasing_cofinal` — a decreasing cofinal sequence in a countable downward directed family.
- **W1** `exists_blocking_sequence` — the full recursion, proved unconditionally, keeping the contracted rate `1/(n+1)`.
- **W2** `compress_exact_diagonal` — exact diagonality of the compression on tail spans.
- **W3** `blocking_lemma` — the blocking lemma itself, proved unconditionally, together with the conditional form `blocking_lemma_of_sequence` permitted by the work order's fallback clause (here used as a stepping stone rather than a fallback).

One additional reusable lemma was added, `exists_unit_constrained_rayleigh_notMem_other` (the odd-stage selection step, obtained from S1, S2 and P1), so that the escape lemma is applied only at the blocked value.

**Verification**

- The whole project builds cleanly (`Build completed successfully`, 8074 jobs).
- No `sorry`, `admit`, `axiom`, or `native_decide` anywhere in the new file.
- `#print axioms` is emitted for all ten audited theorems; each reports exactly `[propext, Classical.choice, Quot.sound]`.
- The base tree was copied in unmodified — a recursive diff against the supplied base shows the only difference is the newly added `PlufWO14.lean`; `PlufWO7a.lean` is untouched.

**Report-rather-than-repair items** (documented in `REPORT-WO14.md`): two contracted hypotheses turn out to be unused by the proofs — `hN` in `perturb_unit` (staying off `N` is a purely algebraic two-candidate argument, needing no closedness) and `hGN` in `blocking_lemma`. Both are retained exactly as contracted and flagged; they are the only two build warnings in the new file.

`REPORT-WO14.md` at the project root carries the item-by-item census (including the S0 and essential-spectrum-membership-criterion verdicts), the W2 packaging choice, W1 constraint bookkeeping, the axiom audit, and notes for the next work order. All work is committed and pushed.