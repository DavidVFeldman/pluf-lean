# Summary of changes for run 46680ea4-4b6c-4647-b763-3335f36b558e
All items of the pluf Work Order 1 (`pluf-wo1.tar.gz` / `WORKORDER.md`) are formalized and proved in Lean 4.28.0 + Mathlib. The artifact builds cleanly and contains no `sorry`, `admit`, `axiom`, or `native_decide`; `#print axioms` for every contract theorem reports exactly `[propext, Classical.choice, Quot.sound]`.

Files (a small file set with a root import, as permitted):
- `RequestProject/PlufWO1.lean` — root: imports everything and runs the axiom audit for all 16 contract theorems.
- `RequestProject/PartA.lean` — A1 `not_mem_union_of_not_mem`, A2 `sigmaQ_of_partition_selectors` (+ `sigmaQ_of_partition_selectors₀`), A2′ `partition_selectors_of_sigmaQ`, A3 `minima_mem_of_fodor`, A3′ `sigmaQ_of_fodor`, A4 `exists_transversal_not_mem`.
- `RequestProject/PartB.lean` — B1a `constraintVec` (+ `constraintVec_apply`, `constraintVec_ne_zero`), B1b `block`/`mem_block_iff` and `W`/`mem_W_iff`, B1c `isClosed_block`, B1d `inner_constraintVec_eq_zero_of_disjoint`, B2 `thin`.
- `RequestProject/PartC.lean` — C1 `closure_span_inter_block`, C2 `noblock`.
- `REPORT.md` — the required census (item-by-item, with Mathlib citations and assessments) and the item-by-item outcome report.

Status per item: A1, A2, A2′, A3, A3′, A4, B1a–B1d, B2, C1, C2 all **proved**. C1 is proved in the contract's closed-span form; the permitted algebraic-span weakening was not needed.

Statement-level deviations (all reported, none mathematical):
- A2: the index type of the partition hypothesis had to be taken in the same universe as the ground type, since the proof applies that hypothesis to the fiber partition of `g`, whose index type is a subtype of the ground type. With the index type pinned to `Type` and an arbitrary ground type, the hypothesis is never applicable to the needed object. The verbatim contract statement (ground type in `Type`) is proved separately as `sigmaQ_of_partition_selectors₀`.
- A2′ and A3: the partition index type is lifted from `Type` to `Type*` — a free strengthening; the contract statements are the `Type`-instances.
Three contract hypotheses turned out to be unnecessary and were kept as stated, with a note in the docstrings: `hρ` in C1, and `hneA`/`hcover` in C2.

Two supporting facts worth flagging: Mathlib has no coordinate functional on `lp` (no `lp.proj`), so `coordL`/`coordCLM` were built from `lp.norm_apply_le_norm`; and C1's forward inclusion is proved by a coordinate-rigidity functional plus an orthogonal-projection argument, avoiding orthonormal series expansions entirely.

The original tarball is left untouched in the project.