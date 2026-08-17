# Summary of changes for run 96a7f906-c08c-4058-a8d4-b66952688d55
WO-7a is complete. The commission was a scoping job, so the primary deliverable is the report, backed by a probe file that builds green.

**Deliverable 1 — `REPORT-WO7a.md`** (repo root). Eight sections: audit status; group-by-group findings for P (essential spectrum), Q (bases as objects) and R (transfinite recursion and CH), each listing what the library provides by name, which probes succeeded and at what line cost, which failed and why, and what remains to be built; the bonus group D; cost estimates for targets (a)–(d) in units of commissions comparable to WO-2…WO-8; a recommended decomposition into seven future work orders with a suggested order; the paper-numbering drift between the work order's references and the printed papers; and a summary of findings.

**Deliverable 2 — `RequestProject/PlufWO7a.lean`** (848 lines). All eleven probes resolved, ten proved outright. The file compiles with no errors, contains no `sorry`/`admit`/`axiom`/`native_decide` in live code, and all sixteen `#print axioms` lines report exactly `[propext, Classical.choice, Quot.sound]`. The full project (base artifact plus probes) builds successfully.

Principal findings recorded in the report:

- **P1 answered negatively.** The library has no essential spectrum, no Calkin algebra and no Fredholm theory (only a TODO comment), and — the more expensive gap — no Borel functional calculus. The Weyl-sequence definition was installed instead.
- **P3, the load-bearing probe, is cheap** (13 lines on a 66-line helper) and needs neither self-adjointness nor the finite-rank/Calkin argument the paper uses; P4 is cheaper still (23 lines).
- **A substitute for the missing Borel functional calculus** was identified and proved: closed spans of rapidly-decaying orthonormal approximate-eigenvector sequences serve the role of the spectral subspaces in Paper I's escape and blocking lemmas. This is the single largest cost saving found.
- **Probe Q2 is false as stated**, refuted by an explicit counterexample (ℝ with a trivial decomposition); the original statement is preserved commented-out with the diagnosis beside it, and a corrected form — separable space, countable index type — is proved and is what Paper II's "chains never suffice" requires.
- The Hilbert-basis API is adequate and the earlier census verdict of "absent" should be revised; the coordinate-block machinery generalises to arbitrary bases for free (Q4).
- CH has no library predicate; the friction in R1/R2 is universe lifting, and **ω₁-recursion needs no successor/limit case split**. The unmeasured cost is two cardinality computations shared by two targets.
- **Target (d) is closed by this commission, without Kochen–Specker**, via a least-dimension-member argument. The odd-dimension hypothesis of the paper's Proposition 2.3 is unnecessary: dimension at least two suffices, and parity plays no role.

Estimates: (d) already done; (a) ≈ 0.5 commission; (c) ≈ 2–2.5; (b) ≈ 3–4, with an explicit, narrowly-scoped honest negative recommending that the blocking lemma alone be quarantined as a named hypothesis if the budget binds, and recommending against formalising Borel functional calculus.

The base artifact was not modified and remains green. All work is committed and pushed.