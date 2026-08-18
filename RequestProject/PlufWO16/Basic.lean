/-
  PlufWO16/Basic.lean — Work Order 16, shared infrastructure.

  The contracted definitions of the work order (`supp`, `cD`, `cI`,
  `DiagonallyConsistent`, `HasFiniteCover`, `pair`), verbatim, together with
  the elementary dictionary between supports, blocks and the two families
  `cD`/`cI`.
-/
import RequestProject.PlufWO15

open Set

namespace PlufWO16

abbrev H := PlufWO1.H

/-! ### Supports -/

/-- The support of a vector of `ℓ²(ℕ)`. -/
def supp (x : H) : Set ℕ := {n | (x : ∀ _ : ℕ, ℝ) n ≠ 0}

/-- REPORT (census, item A/`supp`). `PlufWO2.supp` is stated for `Hk κ`, and
    `H = PlufWO2.Hk ℕ` reducibly, so at the standard space the two agree
    definitionally: the contract's `supp` is `PlufWO2.supp`, and is introduced
    only because the contract names it. -/
theorem supp_eq_plufWO2_supp (x : H) : supp x = PlufWO2.supp x := rfl

@[simp] theorem mem_supp_iff (x : H) (n : ℕ) :
    n ∈ supp x ↔ (x : ∀ _ : ℕ, ℝ) n ≠ 0 := Iff.rfl

/-- A vector lies in the block of `S` exactly when its support is inside `S`. -/
theorem mem_block_iff_supp_subset (S : Set ℕ) (x : H) :
    x ∈ PlufWO1.block S ↔ supp x ⊆ S := by
  rw [PlufWO1.mem_block_iff]
  constructor
  · intro h n hn
    by_contra hnS
    exact hn (h n hnS)
  · intro h n hn
    by_contra hx
    exact hn (h hx)

@[simp] theorem supp_zero : supp (0 : H) = ∅ := by
  ext n
  simp only [mem_supp_iff, mem_empty_iff_false, iff_false, not_not]
  rfl

theorem supp_eq_empty_iff (x : H) : supp x = ∅ ↔ x = 0 := by
  constructor
  · intro h
    refine lp.ext (funext fun n => ?_)
    by_contra hn
    have : n ∈ supp x := hn
    rw [h] at this
    exact this
  · rintro rfl; exact supp_zero

theorem supp_nonempty_iff (x : H) : (supp x).Nonempty ↔ x ≠ 0 := by
  rw [nonempty_iff_ne_empty, ne_eq, supp_eq_empty_iff]

/-! ### The two families of the diagonal block -/

/-- The sets meeting `M` nontrivially through their block. -/
def cD (M : Submodule ℝ H) : Set (Set ℕ) := {S | M ⊓ PlufWO1.block S ≠ ⊥}

/-- The sets meeting `M` trivially through their block. -/
def cI (M : Submodule ℝ H) : Set (Set ℕ) := {S | M ⊓ PlufWO1.block S = ⊥}

theorem mem_cI_iff_notMem_cD (M : Submodule ℝ H) (S : Set ℕ) :
    S ∈ cI M ↔ S ∉ cD M := by
  simp only [cI, cD, mem_setOf_eq, not_not]

theorem mem_cD_iff_notMem_cI (M : Submodule ℝ H) (S : Set ℕ) :
    S ∈ cD M ↔ S ∉ cI M := by
  simp only [cI, cD, mem_setOf_eq, ne_eq]

/-- Diagonal consistency: some ultrafilter is contained in `cD M`. -/
def DiagonallyConsistent (M : Submodule ℝ H) : Prop :=
  ∃ U : Ultrafilter ℕ, ∀ S ∈ U, S ∈ cD M

/-- ℕ admits a finite cover by members of `cI M`. -/
def HasFiniteCover (M : Submodule ℝ H) : Prop :=
  ∃ F : Finset (Set ℕ), (∀ S ∈ F, S ∈ cI M) ∧ (⋃ S ∈ F, S) = univ

/-! ### The coordinate pairs of Gowers's example -/

/-- The `k`-th coordinate pair, in the development's 0-indexing. -/
def pair (k : ℕ) : Set ℕ := {2 * k, 2 * k + 1}

theorem mem_pair_iff (k n : ℕ) : n ∈ pair k ↔ n = 2 * k ∨ n = 2 * k + 1 := Iff.rfl

/-- The pair sum of a vector at the `k`-th pair. -/
def pairSum (x : H) (k : ℕ) : ℝ :=
  (x : ∀ _ : ℕ, ℝ) (2 * k) + (x : ∀ _ : ℕ, ℝ) (2 * k + 1)

end PlufWO16
