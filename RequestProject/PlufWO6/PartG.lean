/-
  PlufWO6/PartG.lean — Work Order 6, Part G: the discharge of WO-5's
  package. A1 and A5 supply the two clauses of `PlufWO5.PlufPackage`
  that were consumed from Paper I, so WO-5's diagonalization theorem
  becomes a statement about genuine maximal filters.
-/
import RequestProject.PlufWO6.PartA

open Set
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO6

/-- `PlufWO1.H` is nonzero. -/
theorem nontrivial_H : Nontrivial PlufWO1.H :=
  ⟨⟨PlufWO1.evec 0, 0, PlufWO1.evec_ne_zero 0⟩⟩

/-- G1. Every nonprincipal pluf of `PlufWO1.H` satisfies WO-5's
    `PlufPackage`. With this, `PlufWO5.diagonalizable_iff_intimate` and the
    repaired `PlufWO5.diagonalizable_iff_extends_phiOmega` become
    statements about genuine maximal filters, as printed in Paper II —
    which is the point of this work order. (Fields: closedness and the
    lattice axioms from `IsPluf`; `finCodim_mem` from A5; `decides` from
    A1.) -/
theorem plufPackage_of_isPluf (π : Set (Submodule ℝ PlufWO1.H)) (hπ : IsPluf π)
    (hnp : ∀ v : PlufWO1.H, v ≠ 0 → ∃ M ∈ π, v ∉ M) :
    PlufWO5.PlufPackage π := by
  haveI := nontrivial_H
  exact
    { mem_closed := hπ.mem_closed
      upward := hπ.upward
      inf_mem := hπ.inf_mem
      proper := hπ.proper
      finCodim_mem := fun M hM hfc => finCodim_mem_of_nonprincipal π hπ hnp M hM hfc
      decides := maximality_criterion π hπ }

/-- G2 (Paper II, Theorem 5.1, as printed). A nonprincipal pluf is
    diagonalizable over the standard basis iff every member is intimate. -/
theorem diagonalizable_iff_intimate_pluf (π : Set (Submodule ℝ PlufWO1.H))
    (hπ : IsPluf π) (hnp : ∀ v : PlufWO1.H, v ≠ 0 → ∃ M ∈ π, v ∉ M) :
    (∃ V : Ultrafilter ℕ, ∀ S : Set ℕ, S ∈ V ↔ PlufWO1.block S ∈ π) ↔
      (∀ M ∈ π, PlufWO5.Intimate M) :=
  PlufWO5.diagonalizable_iff_intimate π (plufPackage_of_isPluf π hπ hnp)

end PlufWO6
