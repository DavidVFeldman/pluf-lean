/-
  PlufWO17/Basic.lean — Work Order 17, shared vocabulary.

  The contracted definitions of the work order (`IsCircuitFamily`, `IndepOf`,
  `HasSM`, `IsScrawlFamily`, `suppFamily`, `AroKaHyp`, `geom`), verbatim, the
  coordinate map `PlufWO16.toFun` that B1 needs (see the REPORT note below),
  and the elementary dictionary they require.

  ON VOCABULARY. As the work order directs, nothing is imported from
  `Mathlib.Data.Matroid`: the three predicates are defined from scratch, and no
  `Matroid` instance is built.
-/
import RequestProject.PlufWO16

open Set

namespace PlufWO16

/-- REPORT (work order, Part B1: "B1 will need whatever coercion `PlufWO16`
    uses from `H` to `ℕ → ℝ`; if no such map is exported, introduce one and
    report it"). FINDING: `PlufWO16` exports no such map — the development
    always writes the `lp` coercion `(x : ∀ _ : ℕ, ℝ)` inline. It is introduced
    here, in the `PlufWO16` namespace, as the ℝ-linear map given by that very
    coercion; it is injective (`PlufWO16.toFun_injective`) and its underlying
    function is the coercion definitionally (`PlufWO16.toFun_apply` is `rfl`). -/
noncomputable def toFun : H →ₗ[ℝ] (ℕ → ℝ) where
  toFun x := (x : ∀ _ : ℕ, ℝ)
  map_add' := lp.coeFn_add
  map_smul' := lp.coeFn_smul

@[simp] theorem toFun_apply (x : H) (n : ℕ) :
    toFun x n = (x : ∀ _ : ℕ, ℝ) n := rfl

theorem toFun_injective : Function.Injective (toFun : H → (ℕ → ℝ)) :=
  fun _ _ h => lp.ext h

end PlufWO16

namespace PlufWO17

abbrev H := PlufWO1.H
open PlufWO16 (supp)

/-! ### Part A: scrawls, and the two axioms the support family satisfies -/

/-- A family of subsets of `ι` is a *circuit family* if it is a nonempty
    antichain of nonempty sets satisfying circuit elimination. -/
structure IsCircuitFamily {ι : Type*} (C : Set (Set ι)) : Prop where
  nonempty : C.Nonempty
  ne_empty : ∀ c ∈ C, c.Nonempty
  antichain : ∀ c ∈ C, ∀ c' ∈ C, c ⊆ c' → c = c'
  elimination : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ∀ p ∈ c ∩ c',
    ∃ c'' ∈ C, c'' ⊆ (c ∪ c') \ {p}

/-- The sets containing no member of `C`. -/
def IndepOf {ι : Type*} (C : Set (Set ι)) : Set (Set ι) :=
  {S | ∀ c ∈ C, ¬ c ⊆ S}

/-- The maximality axiom (SM) of Bruhn–Diestel–Kriesell–Pendavingh–Wollan. -/
def HasSM {ι : Type*} (C : Set (Set ι)) : Prop :=
  ∀ X : Set ι, ∀ I ∈ IndepOf C, I ⊆ X →
    ∃ J ∈ IndepOf C, I ⊆ J ∧ J ⊆ X ∧ ∀ K ∈ IndepOf C, J ⊆ K → K ⊆ X → K = J

/-- `F` is the scrawl family of a matroid: the unions of members of some
    circuit family satisfying (SM), together with the empty set. -/
def IsScrawlFamily {ι : Type*} (F : Set (Set ι)) : Prop :=
  ∃ C, IsCircuitFamily C ∧ HasSM C ∧
    F = {S | ∃ D ⊆ C, S = ⋃ c ∈ D, c}

/-- The support family of a submodule. -/
def suppFamily (M : Submodule ℝ H) : Set (Set ℕ) := {S | ∃ x ∈ M, supp x = S}

theorem mem_suppFamily_of_mem {M : Submodule ℝ H} {x : H} (hx : x ∈ M) :
    supp x ∈ suppFamily M := ⟨x, hx, rfl⟩

/-! ### Part B: the quarantined hypothesis -/

/-- The Aroca–Bossinger–Falkensteiner–Garay López–González-Ramírez–Valencia
    Negrete theorem, quarantined as a hypothesis exactly as Mathias, MSS and
    Blecher–Weaver are elsewhere in this development. For a nonzero
    finite-dimensional `W ⊆ (ι → ℝ)` with `ι` countable, the supports of
    members of `W` form the scrawl family of a circuit family, namely the
    minimal nonempty supports.

    State it about `T(W)` as the source does, NOT about the support family of a
    closed subspace of `ℓ²`; the transfer between the two is the content of B2
    and B3 and must not be smuggled into the hypothesis. -/
def AroKaHyp : Prop :=
  ∀ (W : Submodule ℝ (ℕ → ℝ)), W ≠ ⊥ → Module.Finite ℝ ↥W →
    IsScrawlFamily {S : Set ℕ | ∃ f ∈ W, {n | f n ≠ 0} = S}

/-! ### Part C: the geometric vectors -/

theorem memℓp_geom {lam : ℝ} (h : |lam| < 1) :
    Memℓp (fun n : ℕ => lam ^ n) 2 := by
  apply memℓp_gen
  have h2 : ‖lam ^ 2‖ < 1 := by
    rw [norm_pow, Real.norm_eq_abs]
    nlinarith [abs_nonneg lam]
  have hs := summable_geometric_of_norm_lt_one h2
  refine hs.congr fun n => ?_
  have h2' : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2', Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  ring

/-- The geometric vectors of the example. -/
noncomputable def geom (lam : ℝ) : H :=
  if h : |lam| < 1 then ⟨fun n : ℕ => lam ^ n, memℓp_geom h⟩ else 0

theorem geom_apply' {lam : ℝ} (h : |lam| < 1) (n : ℕ) :
    (geom lam : ∀ _ : ℕ, ℝ) n = lam ^ n := by
  rw [geom, dif_pos h]

end PlufWO17
