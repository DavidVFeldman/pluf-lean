/-
  PlufWO6/PartB.lean — Work Order 6, Part B: no prime filters
  (Paper I, Proposition 2.3).

  Two findings, both reported under the codified licence.

  (1) The contracted statement is false as printed: the *empty* family
      satisfies every hypothesis (it is closed under meets, upward closed
      and proper, all vacuously) and is prime, again vacuously. See
      `empty_filter_is_prime`. The marked minimal repair adds `π.Nonempty`
      — equivalently `⊤ ∈ π`, which the paper's "filter" tacitly means.

  (2) The paper's printed three-lines argument does not survive
      formalization in the form printed: it produces a *line* in `F`, and
      then needs `Π₀ = L₂ ∨ L₃` to lie in `F`, which primeness does not
      supply unless the plane `Π₀` is already known to be in `F`; and the
      plane is in `F` only if the ambient space is spanned by it. What
      does survive, and is what we prove, is the same idea applied to a
      triple of closed subspaces that pairwise meet trivially and whose
      pairwise (closed) joins are everything: `not_prime_of_triple`. In a
      separable infinite-dimensional Hilbert space such a triple exists —
      the even coordinates, the odd coordinates, and the "diagonal"
      subspace `x_{2n} = x_{2n+1}` — so Proposition 2.3 holds there
      (`no_prime_filter`). A triple of this kind cannot exist in odd
      finite dimension (dimension counting forbids it); the finite
      dimensional case is discussed in `REPORT-WO6.md`.
-/
import RequestProject.PlufWO6.PartA

open Set
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The counterexample to the contracted statement -/

/-- The empty family is a proper, upward closed, meet-closed family of
    closed subspaces, and it is prime: the contracted form of B1 is false
    for it, over any space, in particular over one of rank `≥ 3`. -/
theorem empty_filter_is_prime :
    (∀ M ∈ (∅ : Set (Submodule ℝ (EuclideanSpace ℝ (Fin 3)))),
        IsClosed (M : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ M ∈ (∅ : Set (Submodule ℝ (EuclideanSpace ℝ (Fin 3)))),
        ∀ N : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
          IsClosed (N : Set (EuclideanSpace ℝ (Fin 3))) → M ≤ N → N ∈ (∅ : Set _)) ∧
      (∀ M ∈ (∅ : Set (Submodule ℝ (EuclideanSpace ℝ (Fin 3)))),
        ∀ N ∈ (∅ : Set (Submodule ℝ (EuclideanSpace ℝ (Fin 3)))), M ⊓ N ∈ (∅ : Set _)) ∧
      ((⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ∉ (∅ : Set _)) ∧
      (3 ≤ Module.rank ℝ (EuclideanSpace ℝ (Fin 3))) ∧
      (∀ M N : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
        IsClosed (M : Set (EuclideanSpace ℝ (Fin 3))) →
        IsClosed (N : Set (EuclideanSpace ℝ (Fin 3))) →
        (M ⊔ N).topologicalClosure ∈ (∅ : Set _) → M ∈ (∅ : Set _) ∨ N ∈ (∅ : Set _)) := by
  refine ⟨by simp, by simp, by simp, by simp, ?_, by simp⟩
  have h : Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    rw [← Module.finrank_eq_rank]
    simp
  rw [h]

/-! ### The general obstruction to primeness -/

/-- A proper filter of closed subspaces admitting a triple of closed
    subspaces that pairwise meet trivially and whose pairwise closed joins
    are everything is not prime. (This is the paper's three-lines argument,
    with the three lines of a plane replaced by a triple that spans the
    ambient space in pairs; see the file header.) -/
theorem not_prime_of_triple (π : Set (Submodule ℝ E))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ E) ∉ π)
    (hne : π.Nonempty)
    (A B C : Submodule ℝ E)
    (hA : IsClosed (A : Set E)) (hB : IsClosed (B : Set E)) (hC : IsClosed (C : Set E))
    (hAB : A ⊓ B = ⊥) (hAC : A ⊓ C = ⊥) (hBC : B ⊓ C = ⊥)
    (hABtop : (A ⊔ B).topologicalClosure = ⊤)
    (hACtop : (A ⊔ C).topologicalClosure = ⊤)
    (hBCtop : (B ⊔ C).topologicalClosure = ⊤) :
    ¬ (∀ M N : Submodule ℝ E, IsClosed (M : Set E) → IsClosed (N : Set E) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π) := by
  intro hprime
  obtain ⟨M₀, hM₀⟩ := hne
  have htop : (⊤ : Submodule ℝ E) ∈ π := by
    refine hup M₀ hM₀ ⊤ ?_ le_top
    simp only [Submodule.top_coe]
    exact isClosed_univ
  have hclash : ∀ X ∈ π, ∀ Y ∈ π, X ⊓ Y = ⊥ → False := by
    intro X hX Y hY hXY
    exact hbot (hXY ▸ hinf X hX Y hY)
  have h1 : A ∈ π ∨ B ∈ π := hprime A B hA hB (hABtop ▸ htop)
  have h2 : A ∈ π ∨ C ∈ π := hprime A C hA hC (hACtop ▸ htop)
  have h3 : B ∈ π ∨ C ∈ π := hprime B C hB hC (hBCtop ▸ htop)
  by_cases hAπ : A ∈ π
  · rcases h3 with hBπ | hCπ
    · exact hclash A hAπ B hBπ hAB
    · exact hclash A hAπ C hCπ hAC
  · exact hclash B (h1.resolve_left hAπ) C (h2.resolve_left hAπ) hBC

/-! ### The triple in `PlufWO1.H` -/

section Concrete

open PlufWO1

/-- The "diagonal" subspace of `H`: the vectors whose `2n`-th and
    `(2n+1)`-st coordinates agree. -/
noncomputable def diagSub : Submodule ℝ H where
  carrier := {x : H | ∀ n : ℕ, (x : ∀ _ : ℕ, ℝ) (2 * n) = (x : ∀ _ : ℕ, ℝ) (2 * n + 1)}
  add_mem' := by
    intro x y hx hy n
    simp only [Set.mem_setOf_eq] at hx hy
    show (x : ∀ _ : ℕ, ℝ) (2 * n) + (y : ∀ _ : ℕ, ℝ) (2 * n)
      = (x : ∀ _ : ℕ, ℝ) (2 * n + 1) + (y : ∀ _ : ℕ, ℝ) (2 * n + 1)
    rw [hx n, hy n]
  zero_mem' := by intro n; rfl
  smul_mem' := by
    intro c x hx n
    simp only [Set.mem_setOf_eq] at hx
    show c * (x : ∀ _ : ℕ, ℝ) (2 * n) = c * (x : ∀ _ : ℕ, ℝ) (2 * n + 1)
    rw [hx n]

theorem mem_diagSub {x : H} :
    x ∈ diagSub ↔ ∀ n : ℕ, (x : ∀ _ : ℕ, ℝ) (2 * n) = (x : ∀ _ : ℕ, ℝ) (2 * n + 1) :=
  Iff.rfl

theorem isClosed_diagSub : IsClosed (diagSub : Set H) := by
  have h : (diagSub : Set H)
      = ⋂ n : ℕ, {x : H | coordCLM (2 * n) x = coordCLM (2 * n + 1) x} := by
    ext x
    simp [mem_diagSub]
  rw [h]
  exact isClosed_iInter fun n => isClosed_eq (coordCLM _).continuous (coordCLM _).continuous

/-- A subspace containing every standard basis vector is dense. -/
theorem topologicalClosure_eq_top_of_evec_mem (K : Submodule ℝ H)
    (h : ∀ n : ℕ, evec n ∈ K) : K.topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro z hz
  refine lp.ext (funext fun n => ?_)
  have := hz (evec n) (h n)
  rwa [PlufWO5.inner_evec_left] at this

/-- The sum of two consecutive basis vectors lies in the diagonal
    subspace. -/
theorem evec_add_evec_mem_diagSub (k : ℕ) : evec (2 * k) + evec (2 * k + 1) ∈ diagSub := by
  intro n
  show (evec (2 * k) : ∀ _ : ℕ, ℝ) (2 * n) + (evec (2 * k + 1) : ∀ _ : ℕ, ℝ) (2 * n)
    = (evec (2 * k) : ∀ _ : ℕ, ℝ) (2 * n + 1) + (evec (2 * k + 1) : ∀ _ : ℕ, ℝ) (2 * n + 1)
  simp only [evec_apply]
  by_cases h : n = k
  · subst h; simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem block_even_inf_diagSub : block {n : ℕ | Even n} ⊓ diagSub = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [SetLike.mem_coe, mem_block_iff] at hx1
  replace hx2 : ∀ n : ℕ, (x : ∀ _ : ℕ, ℝ) (2 * n) = (x : ∀ _ : ℕ, ℝ) (2 * n + 1) := hx2
  refine lp.ext (funext fun n => ?_)
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hk2 : n = 2 * k := by omega
    subst hk2
    rw [hx2 k]
    exact hx1 (2 * k + 1) (by simp [parity_simps])
  · exact hx1 n (by simpa [Nat.not_even_iff_odd] using ho)

theorem block_odd_inf_diagSub : block {n : ℕ | ¬ Even n} ⊓ diagSub = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [SetLike.mem_coe, mem_block_iff] at hx1
  replace hx2 : ∀ n : ℕ, (x : ∀ _ : ℕ, ℝ) (2 * n) = (x : ∀ _ : ℕ, ℝ) (2 * n + 1) := hx2
  refine lp.ext (funext fun n => ?_)
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hk2 : n = 2 * k := by omega
    subst hk2
    exact hx1 (2 * k) (by simp [parity_simps])
  · obtain ⟨k, hk⟩ := ho
    have hk2 : n = 2 * k + 1 := by omega
    subst hk2
    rw [← hx2 k]
    exact hx1 (2 * k) (by simp [parity_simps])

theorem block_even_inf_block_odd : block {n : ℕ | Even n} ⊓ block {n : ℕ | ¬ Even n} = ⊥ := by
  rw [← PlufWO5.block_inter]
  have : ({n : ℕ | Even n} ∩ {n : ℕ | ¬ Even n}) = (∅ : Set ℕ) := by
    ext n; simp
  rw [this, PlufWO5.block_empty]

/-  B1, contract statement, preserved verbatim:

theorem no_prime_filter (π : Set (Submodule ℝ E))
    (hcl : ∀ M ∈ π, IsClosed (M : Set E))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ E) ∉ π)
    (hdim : 3 ≤ Module.rank ℝ E) :
    ¬ (∀ M N : Submodule ℝ E, IsClosed (M : Set E) → IsClosed (N : Set E) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π)

    False as printed: `π = ∅` satisfies all five hypotheses over a space
    of rank `3` and is vacuously prime (`empty_filter_is_prime`). The
    marked minimal repair adds `π.Nonempty`; the argument then runs, in
    the paper's separable infinite-dimensional `H`, through the triple
    (even coordinates, odd coordinates, diagonal) of `not_prime_of_triple`
    rather than through the printed three-lines argument, which is
    defective as printed (see the file header and `REPORT-WO6.md`). -/

/-- B1 (Proposition 2.3), minimal repair: `π` nonempty, and the ambient
    space is the paper's separable infinite-dimensional `H`. `P(H)` has no
    prime filters: no nonempty proper filter `π` satisfies
    `M ∨ N ∈ π ⇒ M ∈ π or N ∈ π`. -/
theorem no_prime_filter (π : Set (Submodule ℝ H))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ H, IsClosed (N : Set H) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ H) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ H, IsClosed (M : Set H) → IsClosed (N : Set H) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π) := by
  refine not_prime_of_triple π hup hinf hbot hne
    (block {n : ℕ | Even n}) (block {n : ℕ | ¬ Even n}) diagSub
    (isClosed_block _) (isClosed_block _) isClosed_diagSub
    block_even_inf_block_odd block_even_inf_diagSub block_odd_inf_diagSub ?_ ?_ ?_
  · refine topologicalClosure_eq_top_of_evec_mem _ (fun n => ?_)
    by_cases h : Even n
    · exact Submodule.mem_sup_left (PlufWO5.evec_mem_block h)
    · exact Submodule.mem_sup_right (PlufWO5.evec_mem_block h)
  · refine topologicalClosure_eq_top_of_evec_mem _ (fun n => ?_)
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, hk⟩ := he
      exact Submodule.mem_sup_left (PlufWO5.evec_mem_block (by simp [hk, parity_simps]))
    · obtain ⟨k, hk⟩ := ho
      have hk2 : n = 2 * k + 1 := by omega
      subst hk2
      have h1 : evec (2 * k) + evec (2 * k + 1) ∈
          block {n : ℕ | Even n} ⊔ diagSub :=
        Submodule.mem_sup_right (evec_add_evec_mem_diagSub k)
      have h2 : evec (2 * k) ∈ block {n : ℕ | Even n} ⊔ diagSub :=
        Submodule.mem_sup_left (PlufWO5.evec_mem_block ⟨k, by omega⟩)
      simpa using sub_mem h1 h2
  · refine topologicalClosure_eq_top_of_evec_mem _ (fun n => ?_)
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, hk⟩ := he
      have hk2 : n = 2 * k := by omega
      subst hk2
      have h1 : evec (2 * k) + evec (2 * k + 1) ∈
          block {n : ℕ | ¬ Even n} ⊔ diagSub :=
        Submodule.mem_sup_right (evec_add_evec_mem_diagSub k)
      have h2 : evec (2 * k + 1) ∈ block {n : ℕ | ¬ Even n} ⊔ diagSub :=
        Submodule.mem_sup_left (PlufWO5.evec_mem_block (by simp [parity_simps]))
      simpa using sub_mem h1 h2
    · exact Submodule.mem_sup_left (PlufWO5.evec_mem_block (by simpa [Nat.not_even_iff_odd] using ho))

end Concrete

end PlufWO6
