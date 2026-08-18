/-
  PlufWO17/PartA.lean — Work Order 17, Part A.

  A1: the support family of a closed submodule is closed under arbitrary
      unions (Paper V, Theorem 4.3, axiom (S1)); WO-16's `exists_supp_sUnion`
      restated in the scrawl vocabulary.
  A2: scrawl elimination for finite deleted sets (axiom (S2), finite case).
-/
import RequestProject.PlufWO17.Basic

open Set

namespace PlufWO17

open PlufWO16 (supp toFun)

/-- A1 (Paper V, Theorem 4.3, axiom (S1)). The support family of a closed
    submodule is closed under arbitrary unions. This is WO-16's
    `exists_supp_sUnion` restated in the vocabulary above; cite rather than
    reprove. -/
theorem suppFamily_sUnion_closed (M : Submodule ℝ H) (hM : IsClosed (M : Set H))
    (G : Set (Set ℕ)) (hG : G ⊆ suppFamily M) :
    (⋃ S ∈ G, S) ∈ suppFamily M := by
  classical
  obtain ⟨z, hzM, hz⟩ :=
    PlufWO16.exists_supp_sUnion M hM {x : H | x ∈ M ∧ supp x ∈ G} (fun _ hx => hx.1)
  refine ⟨z, hzM, ?_⟩
  rw [hz]
  apply Subset.antisymm
  · simp only [iUnion_subset_iff]
    rintro x ⟨-, hxG⟩
    exact fun n hn => mem_biUnion hxG hn
  · simp only [iUnion_subset_iff]
    intro S hS
    obtain ⟨x, hxM, rfl⟩ := hG hS
    exact fun n hn => mem_biUnion (show x ∈ {x : H | x ∈ M ∧ supp x ∈ G} from ⟨hxM, hS⟩) hn

/-- A2 (Paper V, Theorem 4.3, axiom (S2) for finite deleted sets). Let
    `w = supp x` with `x ∈ M`, let `X ⊆ w` be finite, and for `p ∈ X` let
    `u p ∈ M` have support `w p` with `p ∈ w q ↔ p = q`. Then for every
    `z ∈ w \ ⋃ p, w p` some `y ∈ M` has
    `z ∈ supp y ⊆ (w ∪ ⋃ p, w p) \ X`.

    (The correction `y = x - ∑_{p ∈ X} (x p / u p p) • u p` is a finite sum,
    hence in `M`; it kills each `p ∈ X` and does not touch `z`.) -/
theorem suppFamily_elimination_finite (M : Submodule ℝ H) (x : H) (hx : x ∈ M)
    (X : Finset ℕ) (hXw : ↑X ⊆ supp x) (u : ℕ → H) (hu : ∀ p ∈ X, u p ∈ M)
    (hsupp : ∀ p ∈ X, ∀ q ∈ X, p ∈ supp (u q) ↔ p = q)
    {z : ℕ} (hz : z ∈ supp x) (hznot : ∀ p ∈ X, z ∉ supp (u p)) :
    ∃ y ∈ M, z ∈ supp y ∧
      supp y ⊆ (supp x ∪ ⋃ p ∈ X, supp (u p)) \ ↑X := by
  classical
  set c : ℕ → ℝ := fun p => toFun x p / toFun (u p) p with hc
  set y : H := x - ∑ p ∈ X, c p • u p with hy
  have hyM : y ∈ M :=
    M.sub_mem hx (Submodule.sum_mem _ fun p hp => M.smul_mem _ (hu p hp))
  have hcoord : ∀ n, toFun y n = toFun x n - ∑ p ∈ X, c p * toFun (u p) n := by
    intro n
    simp [hy, Finset.sum_apply]
  -- the corrected vector vanishes on `X`
  have hkill : ∀ q ∈ X, toFun y q = 0 := by
    intro q hq
    have hsum : ∑ p ∈ X, c p * toFun (u p) q = toFun x q := by
      rw [Finset.sum_eq_single q]
      · have hne : toFun (u q) q ≠ 0 := (hsupp q hq q hq).2 rfl
        show toFun x q / toFun (u q) q * toFun (u q) q = toFun x q
        exact div_mul_cancel₀ _ hne
      · intro p hp hpq
        have : q ∉ supp (u p) := fun hmem => hpq ((hsupp q hq p hp).1 hmem).symm
        have : toFun (u p) q = 0 := by
          simpa [PlufWO16.mem_supp_iff] using this
        rw [this, mul_zero]
      · intro hq'
        exact absurd hq hq'
    rw [hcoord q, hsum, sub_self]
  -- and it does not touch `z`
  have hyz : toFun y z = toFun x z := by
    rw [hcoord z, Finset.sum_eq_zero, sub_zero]
    intro p hp
    have : toFun (u p) z = 0 := by
      simpa [PlufWO16.mem_supp_iff] using hznot p hp
    rw [this, mul_zero]
  refine ⟨y, hyM, ?_, ?_⟩
  · show toFun y z ≠ 0
    rw [hyz]
    exact hz
  · intro n hn
    have hn' : toFun y n ≠ 0 := hn
    constructor
    · by_cases hxn : toFun x n ≠ 0
      · exact Or.inl hxn
      · rw [not_not] at hxn
        refine Or.inr ?_
        by_contra hcon
        have hterm : ∀ p ∈ X, c p * toFun (u p) n = 0 := by
          intro p hp
          have hup0 : toFun (u p) n = 0 := by
            by_contra hup
            exact hcon (mem_biUnion hp hup)
          rw [hup0, mul_zero]
        exact hn' (by rw [hcoord n, hxn, Finset.sum_eq_zero hterm, sub_zero])
    · intro hnX
      exact hn' (hkill n hnX)

end PlufWO17
