/-
  PlufWO8/BW.lean — Work Order 8, Part E: countably additive pure states
  give plufs (Paper III, Theorem 4.2), parametrized by the Blecher–Weaver
  package.

  The Blecher–Weaver regularity/excision theory enters ONLY through the
  `BWPackage` structure below, as named hypotheses; every theorem of this
  file is therefore a ZFC statement. Marcus–Spielman–Srivastava does not
  appear.
-/
import RequestProject.PlufWO8.Proj

open Set PlufWO6

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO8

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-  Contract statement of `oneSet`, preserved verbatim:

def oneSet (φ : (E →L[ℝ] E) →L[ℝ] ℝ) : Set (Submodule ℝ E) :=
  {M | IsClosed (M : Set E) ∧ φ M.starProjection = 1}

    This does not elaborate: `Submodule.starProjection` takes an instance
    argument `[M.HasOrthogonalProjection]`, which for a general submodule
    of a complete space is available only *after* closedness of `M` is in
    context. The marked minimal repair replaces the conjunction by the
    (propositionally equivalent) dependent pair, so that the closedness
    clause is in scope where the projection is formed. -/

/-- The 1-set of a state, as a family of closed subspaces (minimal repair
    of the contracted conjunction; see the comment above). -/
def oneSet (φ : (E →L[ℝ] E) →L[ℝ] ℝ) : Set (Submodule ℝ E) :=
  {M | ∃ _hc : IsClosed (M : Set E), φ M.starProjection = 1}

variable {φ : (E →L[ℝ] E) →L[ℝ] ℝ} {M N : Submodule ℝ E}

/-- Members of the 1-set are closed. -/
theorem isClosed_of_mem_oneSet (hM : M ∈ oneSet φ) : IsClosed (M : Set E) := hM.choose

/-- Members of the 1-set have projection of value `1`. -/
theorem starProjection_eq_one_of_mem_oneSet [M.HasOrthogonalProjection]
    (hM : M ∈ oneSet φ) : φ M.starProjection = 1 := hM.choose_spec

/-- Membership in the 1-set. -/
theorem mem_oneSet [M.HasOrthogonalProjection] (hc : IsClosed (M : Set E))
    (h1 : φ M.starProjection = 1) : M ∈ oneSet φ := ⟨hc, h1⟩

/-  Contract statement of `BWPackage.excision`, preserved verbatim:

  excision : ∀ x : E →L[ℝ] E, ∃ M ∈ oneSet φ,
    M.starProjection.comp (x.comp M.starProjection)
      = (φ x) • M.starProjection

    As for `oneSet`, the bounded-existential form leaves no closedness
    hypothesis in scope at the point where `M.starProjection` is formed,
    so it does not elaborate; the marked minimal repair spells out the
    membership as the pair (closedness, value one). -/

/-- The Blecher–Weaver package for a countably additive pure state,
    supplied as named hypotheses:
    * `sigma_filter`: the 1-set is closed under countable meets;
    * `excision`: every operator admits an excising projection in the
      1-set, `p x p = φ(x) p`. -/
structure BWPackage (φ : (E →L[ℝ] E) →L[ℝ] ℝ) : Prop where
  sigma_filter : ∀ M : ℕ → Submodule ℝ E, (∀ n, M n ∈ oneSet φ) →
    ∃ N ∈ oneSet φ, ∀ n, N ≤ M n
  excision : ∀ x : E →L[ℝ] E, ∃ M : Submodule ℝ E, ∃ _hc : IsClosed (M : Set E),
    φ M.starProjection = 1 ∧
      M.starProjection.comp (x.comp M.starProjection) = (φ x) • M.starProjection

namespace Internal

/-- E1 (upward closure). -/
theorem oneSet_upward (hφ : IsState φ) (hM : M ∈ oneSet φ)
    (hN : IsClosed (N : Set E)) (hMN : M ≤ N) : N ∈ oneSet φ := by
  haveI hiM : M.HasOrthogonalProjection :=
    hasOrthogonalProjection_of_isClosed (isClosed_of_mem_oneSet hM)
  haveI hiN : N.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hN
  have h1 : φ M.starProjection = 1 := starProjection_eq_one_of_mem_oneSet hM
  have hmono : φ M.starProjection ≤ φ N.starProjection :=
    state_starProjection_mono hφ hMN
  have hle : φ N.starProjection ≤ 1 := hφ.starProjection_le_one N
  exact mem_oneSet hN (by linarith)

/-- E1 (binary meets), from the σ-filtration clause of the package. -/
theorem oneSet_inf (hφ : IsState φ) (hBW : BWPackage φ) (hM : M ∈ oneSet φ)
    (hN : N ∈ oneSet φ) : M ⊓ N ∈ oneSet φ := by
  classical
  obtain ⟨L, hL, hLle⟩ := hBW.sigma_filter (fun n => if n = 0 then M else N)
    (fun n => by by_cases h : n = 0 <;> simp [h, hM, hN])
  have hLM : L ≤ M := by simpa using hLle 0
  have hLN : L ≤ N := by simpa using hLle 1
  exact oneSet_upward hφ hL
    (isClosed_inf (isClosed_of_mem_oneSet hM) (isClosed_of_mem_oneSet hN))
    (le_inf hLM hLN)

/-- E1 (properness). -/
theorem bot_notMem_oneSet : (⊥ : Submodule ℝ E) ∉ oneSet φ := by
  intro hbot
  have h1 : φ (⊥ : Submodule ℝ E).starProjection = 1 :=
    starProjection_eq_one_of_mem_oneSet hbot
  rw [Submodule.starProjection_bot, map_zero] at h1
  exact zero_ne_one h1

/-- E2 (the excision step; Paper III, Theorem 4.2, maximality). A closed
    subspace outside the 1-set is met trivially by a member of it. -/
theorem exists_oneSet_inf_eq_bot (hBW : BWPackage φ) (hMc : IsClosed (M : Set E))
    (hM : M ∉ oneSet φ) : ∃ N ∈ oneSet φ, M ⊓ N = ⊥ := by
  haveI hiM : M.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hMc
  obtain ⟨N, hNc, hN1, hexc⟩ := hBW.excision M.starProjection
  haveI hiN : N.HasOrthogonalProjection := hasOrthogonalProjection_of_isClosed hNc
  refine ⟨N, mem_oneSet hNc hN1, ?_⟩
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hvM, hvN⟩
  by_contra hv0
  have hPM : M.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hvM
  have hPN : N.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hvN
  have happ := congrArg (fun S : E →L[ℝ] E => S v) hexc
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, hPN, hPM] at happ
  have hval : (1 : ℝ) = φ M.starProjection := by
    have hsmul : v = φ M.starProjection • v := by simpa [hPN] using happ
    have hzero : (1 - φ M.starProjection) • v = 0 := by
      rw [sub_smul, one_smul, ← hsmul]
      simp
    rcases smul_eq_zero.mp hzero with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h hv0
  exact hM (mem_oneSet hMc hval.symm)

/-- E3 (Theorem 4.2). The 1-set of a state satisfying the package is a
    pluf. -/
theorem isPluf_oneSet (hφ : IsState φ) (hBW : BWPackage φ) [Nontrivial E] :
    PlufWO6.IsPluf (oneSet φ) := by
  refine PlufWO6.isPluf_of_criterion (oneSet φ)
    (fun M hM => isClosed_of_mem_oneSet hM)
    (fun M hM N hNc hMN => oneSet_upward hφ hM hNc hMN)
    (fun M hM N hN => oneSet_inf hφ hBW hM hN)
    bot_notMem_oneSet ?_
  intro M hMc
  by_cases hM : M ∈ oneSet φ
  · exact Or.inl hM
  · exact Or.inr (exists_oneSet_inf_eq_bot hBW hMc hM)

/-- E4 (nonprincipality for singular states). -/
theorem oneSet_nonprincipal (hBW : BWPackage φ)
    (hsing : ∀ (M : Submodule ℝ E) (_hM : Module.Finite ℝ ↥M), φ M.starProjection = 0) :
    ∀ v : E, v ≠ 0 → ∃ N ∈ oneSet φ, v ∉ N := by
  intro v hv
  have hfin : Module.Finite ℝ ↥(ℝ ∙ v) := inferInstance
  haveI : FiniteDimensional ℝ ↥(ℝ ∙ v) := hfin
  have hc : IsClosed ((ℝ ∙ v : Submodule ℝ E) : Set E) :=
    Submodule.closed_of_finiteDimensional (ℝ ∙ v)
  have h0 : φ (ℝ ∙ v : Submodule ℝ E).starProjection = 0 := hsing _ hfin
  have hnot : (ℝ ∙ v : Submodule ℝ E) ∉ oneSet φ := by
    intro hmem
    have := starProjection_eq_one_of_mem_oneSet hmem
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨N, hN, hbot⟩ := exists_oneSet_inf_eq_bot hBW hc hnot
  refine ⟨N, hN, ?_⟩
  intro hvN
  have hmem : v ∈ (ℝ ∙ v : Submodule ℝ E) ⊓ N :=
    ⟨Submodule.mem_span_singleton_self v, hvN⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv hmem

end Internal

end PlufWO8
