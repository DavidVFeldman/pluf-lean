# WO-4 report — pluf project (Feldman–Wilce), Paper IV

Artifact: `RequestProject/PlufWO4.lean` (root, with the axiom audit) and the
four modules `RequestProject/PlufWO4/{Homog,Fubini,EPP,Blockers}.lean`.
Base (`PlufWO1`–`PlufWO3`) untouched; all 39 prior theorems green, their
audits re-run through the import chain.

**Status: complete.** All 22 contract items are proved, with no
`sorry`/`admit`/`axiom`/`native_decide` anywhere. `#print axioms` for each of
the 22 (plus four auxiliaries) reports exactly
`[propext, Classical.choice, Quot.sound]`.

Two contract statements are restated under the codified licence (A1, B5);
both are documented below and at the theorem, with the contract statement
preserved verbatim in a comment beside it. No other statement changed.

## Census (what was already available)

* `PlufWO1`: `SigmaQPoint`, `IsPartialSelector`, `FodorProperty`,
  `minima_mem_of_fodor` (countable-piece form; its helper
  `exists_piece_min_fun` is `private`, so the piece-minimum construction is
  redone here without countability), `H`, `block`, `mem_block_iff`,
  `isClosed_block`, `coordL`, `constraintVec`, `W`, `mem_W_iff`,
  `inner_constraintVec_eq_zero_of_disjoint`, `thin`.
* `PlufWO2`: `Hk`, `evec`, `supp`, `countable_supp`, `block`,
  `mem_block_iff`, `isClosed_block`, `block_mono`, `inner_evec_right`,
  `hasSum_coord_smul`, `hasSum_evec_smul`, `inner_eq_coord_mul`,
  `block_le_of_evec_mem`, `exact_paving`, `exact_dichotomy`.
* `PlufWO3`: `PhiU` and the filter axioms, `PhiU_decides`, `quadratic_flat`,
  `Wk` and the κ-witness package.
* Mathlib: **no** `Ultrafilter.prod`/Fubini product object exists; the
  monadic `Ultrafilter.bind` does, and `fubini` is its instance along
  `β ↦ (γ, β)`, with `mem_fubini_iff` as the bridging lemma (it holds by
  `Iff.rfl`). Also used: `Set.MapsTo.countable_of_injOn`,
  `Submodule.eq_top_of_nonempty_interior'`,
  `nonempty_interior_of_iUnion_of_closed` with
  `BaireSpace.of_completelyPseudoMetrizable`, `LinearMap.rank_le_of_injective`,
  `rank_fun'`, `Submodule.rank_mono`.

## Item-by-item

**A1 `inj_on_pairs` — proved, RESTATED (one added hypothesis).**
Proved with the extra hypothesis `htail : ∀ γ, {β | γ < β} ∈ D`. This is the
paper's "H has order type κ, so pass to a tail of H" step, used by every
pattern whose free coordinate varies *upward*; `UncountablePivots` gives only
the downward direction and does not by itself make members of `D` unbounded.
`htail` is already a contract hypothesis of B1, B8 and C2, so nothing
downstream changes. (Whether the contract form is provable without `htail` is
not settled here: a counterexample would need an ultrafilter with uncountable
Rowbottom-homogeneous sets, so it cannot be built in ZFC; a proof would need,
at least, a Sierpiński-style colouring argument to rule out the case in which
every point of every `D`-large set has only countably many `D`-large-set
points above it.)

The conclusion is stated on ordered coordinates, as in the contract; `V` lives
in an arbitrary universe.

**Shared core.** A1 and C2 are both instances of one lemma,
`exists_avoiding_homog`: for any assignment of countable sets `c a b` of pairs
to increasing pairs, some `H ∈ D` has its increasing pairs mutually avoiding
`c`. A1 takes `c a b` to be the `g`-fiber through `(a,b)`; C2 takes it to be
the EPP data restricted to the triangle.

**PATTERN-ANALYSIS FINDING (A1/C2).** The paper enumerates placement patterns
as unordered pairs of positions and then splits into two regimes ("y owns the
top position", "x owns the top position"). Mechanization needs the ordered
enumeration: three splittings of a four-element set into two disjoint pairs
and three pairs from a three-element set, each with **both** role assignments
— twelve patterns (`pattern₁`–`pattern₁₂`). All twelve are refutable, so both
theorems stand exactly as claimed. But two of them —
`x = (h₁,h₃), y = (h₁,h₂)` and `x = (h₃,h₄), y = (h₁,h₂)`, where the free
coordinate of `y` must be produced *between* two fixed coordinates of `x` —
are not covered by either regime as literally stated: freeing a coordinate
below a pivot is not enough, because the pivot has to be chosen *above* an
already-fixed coordinate of `x`. The repair is one lemma, `exists_mid`: apply
`UncountablePivots` to the tail `H ∩ (γ, →)` (itself in `D`) rather than to
`H`, obtaining uncountably many points of `H` strictly between `γ` and the
pivot. Two further patterns (`x = (h₁,h₄), y = (h₂,h₃)` and
`x = (h₁,h₃), y = (h₂,h₃)`) use the same device. This is the paper's
parenthetical "together, when the pattern permits, with a region between x's
coordinates, which only helps" made into an actual step: for these patterns
that region is not a bonus but the only source of the large family.

**B0 `fubini`, `mem_fubini_iff` — proved.** Constructed as
`D₁.bind fun γ => Ultrafilter.map (fun β => (γ, β)) D₂`; the section-largeness
characterization of the contract holds definitionally.

**B1 `triangle_mem_fubini`, B2 `countableSmall_fubini`,
B3 `column_notMem_fubini` — proved**, verbatim.

**B4 `fullSelector_of_fodor` — proved**, verbatim; proved via the
universe-polymorphic `fullSelectorAll_of_fodor` (`FullSelectorAll`, the same
property with the index type in an arbitrary universe). WO-1's piece-minimum
construction is redone here without countability of the pieces and without
assuming them nonempty (a piece containing no point is never selected).

**B5 `not_fullSelector_fubini` — proved, RESTATED (universe).** The contract
`FullSelector` quantifies over `ι : Type 0`, while the refuting partition is
the column partition, indexed by `κ` itself; the contract statement is
therefore proved at `κ : Type`. For arbitrary `κ` the same refutation is
`not_fullSelectorAll_fubini`, and B7 — which is what Proposition 2.3 exists
for — is proved verbatim for every `κ`.

**B6 `fullSelector_map_iff` — proved**, verbatim (and in the
universe-polymorphic form), by transporting partitions along the equivalence.

**B7 `fubini_not_iso_fodor` — proved**, verbatim, at arbitrary `κ`, by
combining B4, B6 and B5 in their universe-polymorphic forms.

**B8 `sigmaQ_fubini` — proved**, verbatim: A1 applied to
`(a,b) ↦ g (a,b)`, with the selector the triangle of the homogeneous set.

**C1 `sigmaQ_of_EPP` — proved**, verbatim.

**C2 `EPP_fubini` — proved**, verbatim (the centerpiece); see the shared core
and the pattern-analysis finding above.

**C3 `exact_paving_of_EPP` — proved**, verbatim. Route report: the adjoint of
`T` is not needed. WO-2's diagonal intersection was one-sided, so the `α < β`
half had to be complemented through `T*`; EPP is symmetric in `x` and `y`, so
the single family `c α = supp (T (evec α))` serves both halves.

**C4–C6 `exact_dichotomy_of_EPP`, `quadratic_flat_of_EPP`,
`PhiU_decides_of_EPP` — proved**, verbatim. **REFACTORING DECISION: option
(ii)** — the EPP versions are proved fresh in namespace `PlufWO4`, reusing the
WO-2/WO-3 auxiliary lemmas (`inner_eq_coord_mul`, `hasSum_coord_smul`,
`block_le_of_evec_mem`, `block_mono`, …) unchanged and replacing only the
paving input. The WO-2/WO-3 sources are untouched, so the 39 prior theorems
remain green verbatim rather than being re-derived as instances. The
proofs are the WO-2/WO-3 arguments line for line with `exact_paving_of_EPP`
substituted for `exact_paving`, which is itself the evidence the paper claims
("consumes normality only through the paving conclusion").

Note on hypotheses: `hsmall` in C4/C6 is retained exactly as contracted but is
not used — in WO-2 it was consumed only inside `exact_paving`.

**C7 `product_decides` — proved**, verbatim. Instance note: `PlufWO2.evec`
carries the `LinearOrder` of its index type, so C3–C6 are stated over a
linearly ordered index set; at `X = κ × κ` any linear order does (no part of
the statement depends on it) and the lexicographic one is supplied in the
proof.

**D1 `gen_thin` — proved**, verbatim: the `F.card` inner-product functionals,
as a single injective linear map into `F → ℝ`.

**D2a `inter_infinite_iff_mem`, D2b `rank_le_of_le_block_finite`,
D2 `support_mem` — proved**, verbatim, with `Module.rank` as contracted (no
restatement was needed). D2 is proved by the sharper contrapositive: for
`T ∉ U` the witness `S = Tᶜ` gives `R ⊓ block S = ⊥` outright, so neither D2a
nor D2b is consumed, and the contract hypothesis `hcof` of D2 is retained but
unused. D2a and D2b are proved independently, as contracted.

**D3 `baire_spread` — proved**, verbatim: inside the complete space
`R ⊓ block S`, the vectors of piece-spread inside a fixed finite `F` form the
closed subspace cut out by `block (⋃ k ∈ F, A k)`, proper because its rank is
at most `F.card` by D1 while `R ⊓ block S` has infinite rank, hence of empty
interior (`Submodule.eq_top_of_nonempty_interior'`); Baire category over
`Finset ℕ` then leaves a vector of infinite piece-spread. `hcover` is used, as
the contract anticipates, to see that a finite spread forces support inside
the corresponding finite union of pieces.
