/-
  PlufWO12.lean — Work Order 12 for the pluf project (Feldman–Wilce).

  Scope: Paper II, Theorem 5.4 — under CH, a nonprincipal pluf
  diagonalizable via no orthonormal basis:
    (A) the stage construction: given a decreasing chain of
        infinite-dimensional closed subspaces, a Hilbert basis, and a
        subspace `N` meeting the chain finite-dimensionally, produce a
        closed `R` that is not intimate for the basis, misses `N`, and
        meets every chain member in infinite dimension;
    (B) the ω₁ recursion assembling the witness family;
    (C) Theorem 5.4 itself.

  A DELIBERATE DEVIATION FROM THE PAPER'S PROOF. The paper proves
  Theorem 5.4 by running the three-case recursion of [FWI, Theorem 5.6]
  directly, maintaining a pluf-in-progress and handling membership,
  blocking and the basis task at each stage. That is not necessary here,
  because Proposition 5.5 (the one-witness reduction) is already verified
  as `PlufWO10.one_witness_reduction`. It suffices to build a downward
  directed family with all finite intersections infinite-dimensional,
  with trivial intersection, defeating every basis; Proposition 5.5 then
  supplies the pluf, its nonprincipality and its non-diagonalizability.

  Consequences of the deviation, all simplifications:
    * no three-case split, no membership case, no maximality argument in
      the recursion — those live inside the already-verified
      Proposition 5.5 and the Zorn extension theorem;
    * the "blocking" subspace `N` is always a LINE `ℝ ∙ v`, so the
      hypothesis that `N` meets the chain finite-dimensionally is
      automatic; blocking every line in turn is exactly what forces the
      family's intersection to be trivial, which is Proposition 5.5's
      `sInf R = ⊥` hypothesis.

  If this route turns out to be blocked — for instance if directedness
  cannot be maintained in the shape Proposition 5.5 wants — REPORT rather
  than silently reverting to the paper's recursion; the fallback is
  available but costs the three-case split.

  Base: the WO-11 artifact together with WO-13 (216 theorems; CI runs
  #1–#12). WO-13 is not logically required here, but the base is the
  merged tree. All prior theorems must remain green; `PlufWO7a.lean` is
  the census record and is not to be edited.

  CH is a hypothesis (`Cardinal.continuum = Cardinal.aleph 1`), never an
  axiom.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.
-/
import RequestProject.PlufWO13
import RequestProject.PlufWO12.PartB

open Set Cardinal

namespace PlufWO12

-- `H` (an abbreviation for `PlufWO1.H`) is introduced in
-- `RequestProject.PlufWO12.Basic`, which this file imports.

/-! ### Part A: the stage construction

Fix a Hilbert basis `b : HilbertBasis ℕ ℝ H`, a decreasing sequence
`h : ℕ → Submodule ℝ H` of infinite-dimensional closed subspaces, and a
closed `N` with `h n ⊓ N` finite-dimensional for every `n`.

The paper's recursion chooses unit vectors `w n ∈ h n` and thresholds
`N₁ < N₂ < ⋯` in the basis index so that

  (a) `w n ⊥ b β` for all `β ≤ N n`;
  (b) `w n ⊥ w j` and `w n ⊥ P_{Nᗮ} (w j)` for `j < n`, and `w n ∉ N`;
  (c) `w n` has at least two nonzero `b`-coordinates `a n < c n`, and
      `N (n+1) > c n`.

Every constraint but the two nonvanishing ones is a finite set of linear
conditions, so it carves a finite-codimension subspace out of `h n`. -/

section Stage

variable (b : HilbertBasis ℕ ℝ H) (h : ℕ → Submodule ℝ H) (N : Submodule ℝ H)

/-- A1 (room to work). A finite-codimension subspace of an
    infinite-dimensional closed subspace is infinite-dimensional, and
    remains so after removing a finite-dimensional part. State the form
    the stage recursion cites: given `h n` infinite-dimensional closed,
    finitely many continuous functionals, and `h n ⊓ N`
    finite-dimensional, the set of vectors of `h n` annihilated by the
    functionals and outside `N` is nonempty. -/
theorem exists_constrained_notMem
    (hh : ¬ FiniteDimensional ℝ ↥(h 0)) (hhc : IsClosed ((h 0 : Submodule ℝ H) : Set H))
    (hN : FiniteDimensional ℝ ↥(h 0 ⊓ N))
    (F : Finset (H →L[ℝ] ℝ)) :
    ∃ x ∈ h 0, x ∉ N ∧ ∀ f ∈ F, f x = 0 := by
  classical
  -- represent the functionals by vectors (Riesz) and cut by their orthogonal complement
  set rep : (H →L[ℝ] ℝ) → H := fun f => (InnerProductSpace.toDual ℝ H).symm f with hrep
  have hrepapp : ∀ (f : H →L[ℝ] ℝ) (x : H), f x = inner ℝ (rep f) x := by
    intro f x
    conv_lhs => rw [← (InnerProductSpace.toDual ℝ H).apply_symm_apply f]
    rw [hrep, InnerProductSpace.toDual_apply_apply]
  set W : Submodule ℝ H := Submodule.span ℝ (rep '' (F : Set (H →L[ℝ] ℝ))) with hW
  haveI hWfin : FiniteDimensional ℝ ↥W :=
    FiniteDimensional.span_of_finite ℝ (F.finite_toSet.image rep)
  have hMinf : ¬ FiniteDimensional ℝ ↥(h 0 ⊓ Wᗮ) := not_finiteDimensional_inf_orthogonal hh hWfin
  have hnotle : ¬ (h 0 ⊓ Wᗮ) ≤ N := by
    intro hle
    refine hMinf (Submodule.finiteDimensional_of_le (S₂ := h 0 ⊓ N) ?_)
    exact le_inf inf_le_left hle
  obtain ⟨x, hxM, hxN⟩ : ∃ x ∈ h 0 ⊓ Wᗮ, x ∉ N := by
    by_contra hc
    push_neg at hc
    exact hnotle hc
  refine ⟨x, hxM.1, hxN, ?_⟩
  intro f hf
  rw [hrepapp f x]
  exact (Submodule.mem_orthogonal W x).mp hxM.2 (rep f)
    (Submodule.subset_span ⟨f, by simpa using hf, rfl⟩)

/-- A2 (two nonzero coordinates). A subspace of `H` of dimension at least
    two contains a vector with at least two nonzero `b`-coordinates.
    (Paper: a subspace all of whose vectors are multiples of single basis
    vectors has dimension at most one; given independent `u, v`, one of
    `u`, `v`, `u + v` has two nonzero coordinates.) State it for the
    constrained subspace the recursion works in, i.e. together with the
    `N`-avoidance if that is convenient; report the packaging. -/
theorem exists_two_nonzero_coords {M : Submodule ℝ H}
    (hM : ¬ FiniteDimensional ℝ ↥M) :
    ∃ x ∈ M, ∃ i j : ℕ, i ≠ j ∧ b.repr x i ≠ 0 ∧ b.repr x j ≠ 0 :=
  exists_two_nonzero_coords_aux b hM

/-- A3 (the stage construction). The heart of the commission.

    Given the data above, there are a closed subspace `R` and a set
    `A ⊆ ℕ` with
      (i)   `R ⊓ PlufWO9.blockB b A = ⊥` and
            `R ⊓ PlufWO9.blockB b Aᶜ = ⊥` — so `R` is not `b`-intimate;
      (ii)  `R ⊓ N = ⊥`;
      (iii) `¬ FiniteDimensional ℝ ↥(R ⊓ h j)` for every `j`.

    Construction (paper): choose `w n` and thresholds as in (a)–(c) above,
    put `A = {a n : n}` and `R = closed span {w n}`. For (i): the `w n`
    are orthonormal, so `x ∈ R` expands as `∑ c n • w n`; if `L` is least
    with `c L ≠ 0` then, because `w m` vanishes on coordinates `≤ N m` and
    `a L, c L ≤ N (L+1) ≤ N m` for `m > L`, the coordinates of `x` at
    `a L` and at `c L` are both nonzero — one in `A`, one outside. For
    (ii): `y n = P_{Nᗮ} (w n)` are pairwise orthogonal and nonzero by (b),
    so `P_{Nᗮ}` is injective on `R`. For (iii): the closed span of
    `{w n : n ≥ j}` lies in `R ⊓ h j`.

    The recursion itself is ordinary (ℕ-indexed, with a finite constraint
    set at each step); the WO-9 ω₁ combinator is NOT needed here — it is
    needed in Part B. -/
theorem exists_nonIntimate_blocking
    (hmono : ∀ n, h (n+1) ≤ h n)
    (hcl : ∀ n, IsClosed ((h n : Submodule ℝ H) : Set H))
    (hinf : ∀ n, ¬ FiniteDimensional ℝ ↥(h n))
    (hNcl : IsClosed (N : Set H))
    (hNfin : ∀ n, FiniteDimensional ℝ ↥(h n ⊓ N)) :
    ∃ R : Submodule ℝ H, IsClosed (R : Set H) ∧
      ¬ PlufWO10.IntimateB b R ∧
      R ⊓ N = ⊥ ∧
      ∀ j, ¬ FiniteDimensional ℝ ↥(R ⊓ h j) :=
  exists_nonIntimate_blocking_aux b h N hmono hcl hinf hNfin

end Stage

/-! ### Part B: the ω₁ recursion -/

section Recursion

variable (hCH : continuum = aleph 1)

include hCH in
/-- B1 (the vector enumeration). Under CH, the nonzero vectors of `H` are
    enumerated by the countable ordinals. This is a further instantiation
    of WO-9's E1 alongside WO-11's B1–B3, using `PlufWO11.mk_H`; if WO-11
    already exports a suitable form, cite it rather than reproving. -/
theorem exists_enum_vectors :
    ∃ f : {o : Ordinal // o < (aleph 1).ord} → H, ∀ v : H, v ≠ 0 → ∃ o, f o = v :=
  exists_enum_vectors_aux hCH

/-- B2 (chain extraction). A countable downward directed family of closed
    subspaces admits a decreasing cofinal sequence: enumerate it and take
    finite meets. This is what feeds Part A at each stage. -/
theorem exists_decreasing_cofinal {G : Set (Submodule ℝ H)}
    (hctble : G.Countable) (hne : G.Nonempty)
    (hdir : ∀ M ∈ G, ∀ M' ∈ G, ∃ P ∈ G, P ≤ M ⊓ M') :
    ∃ h : ℕ → Submodule ℝ H, (∀ n, h n ∈ G) ∧ (∀ n, h (n+1) ≤ h n) ∧
      ∀ M ∈ G, ∃ n, h n ≤ M :=
  exists_decreasing_cofinal_aux hctble hne hdir

include hCH in
/-- B3 (the recursion). Under CH there is a family `R : {o // o < ω₁} →
    Submodule ℝ H` of closed subspaces such that, writing `Rset` for its
    range:
      * every finite intersection of members is infinite-dimensional;
      * `Rset` is downward directed — or, if it is more convenient, take
        the family to BE the set of finite intersections, which is
        directed by construction and has the same finite-intersection
        property; report which packaging was used;
      * `sInf Rset = ⊥`, because stage `o` blocks the line spanned by the
        `o`-th nonzero vector;
      * for every Hilbert basis `b` some member is not `b`-intimate,
        because stage `o` defeats the `o`-th basis.

    At stage `o`: the members already built are indexed by `{p // p < o}`,
    countable by `PlufWO11.countable_Iio_of_lt_omega1`, so their finite
    intersections form a countable directed family; extract a decreasing
    cofinal chain (B2), and apply A3 with that chain, the `o`-th basis
    (WO-11 B2) and `N` the line spanned by the `o`-th vector (B1). The
    hypothesis of A3 that `h n ⊓ N` is finite-dimensional is automatic
    because `N` is one-dimensional.

    Use WO-9's ω₁ combinator (`PlufWO9.exists_omega1_chain`) if its shape
    fits; if the bookkeeping here is easier with a direct
    `Ordinal.limitRecOn`, do that and REPORT — WO-15 will reuse whichever
    pattern proves workable, so its shape is worth recording. -/
theorem exists_witness_family :
    ∃ R : Set (Submodule ℝ H),
      R.Nonempty ∧
      (∀ M ∈ R, IsClosed (M : Set H)) ∧
      (∀ M ∈ R, ∀ M' ∈ R, ∃ P ∈ R, P ≤ M ⊓ M') ∧
      (∀ F : Finset (Submodule ℝ H), ↑F ⊆ R → ¬ Module.Finite ℝ ↥(F.inf id)) ∧
      sInf R = ⊥ ∧
      (∀ b : HilbertBasis ℕ ℝ H, ∃ M ∈ R, ¬ PlufWO10.IntimateB b M) :=
  exists_witness_family_aux hCH

end Recursion

/-! ### Part C: Theorem 5.4 -/

/-- C1 (Paper II, Theorem 5.4). Assume CH. There is a nonprincipal pluf
    diagonalizable via no orthonormal basis.

    Immediate from B3 and `PlufWO10.one_witness_reduction`. Deliver the
    conclusion in the paper's own terms: a `PlufWO6.IsPluf` family that is
    nonprincipal (no nonzero vector lies in every member) and for which no
    basis diagonalizes (no ultrafilter traces it through `blockB b`). -/
theorem exists_nonprincipal_nondiagonalizable (hCH : continuum = aleph 1) :
    ∃ σ : Set (Submodule ℝ H), PlufWO6.IsPluf σ ∧
      (∀ v : H, v ≠ 0 → ∃ M ∈ σ, v ∉ M) ∧
      ∀ b : HilbertBasis ℕ ℝ H,
        ¬ ∃ V : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ V ↔ PlufWO9.blockB b S ∈ σ := by
  obtain ⟨R, hne, hcl, hdir, hFIP, hsInf, hwit⟩ := exists_witness_family hCH
  obtain ⟨⟨σ, hσ, hRσ⟩, hprops⟩ :=
    PlufWO10.one_witness_reduction R hne hcl hdir hFIP hsInf hwit
  exact ⟨σ, hσ, (hprops σ hσ hRσ).1, (hprops σ hσ hRσ).2⟩

/-! ### Axiom audit -/

#print axioms exists_constrained_notMem
#print axioms exists_two_nonzero_coords
#print axioms exists_nonIntimate_blocking
#print axioms exists_enum_vectors
#print axioms exists_decreasing_cofinal
#print axioms exists_witness_family
#print axioms exists_nonprincipal_nondiagonalizable

end PlufWO12
