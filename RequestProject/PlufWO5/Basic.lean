/-
  PlufWO5/Basic.lean — Work Order 5, shared infrastructure.

  Coordinate-level machinery in `H = lp (fun _ : ℕ => ℝ) 2`: square
  summability of the coordinates, restriction of a vector to a set of
  coordinates, tail estimates, elementary block lemmas, dimension
  criteria, and the rendering of relative codimension (`FinCodimIn`)
  together with its orthogonal-complement bridge.
-/
import RequestProject.PlufWO4

open Set

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO5

open PlufWO1

noncomputable section

/-! ### Coordinates and square summability -/

theorem summable_sq (x : H) : Summable (fun n => ((x : ∀ _ : ℕ, ℝ) n) ^ 2) := by
  have h := (lp.memℓp x).summable (p := 2) (by norm_num)
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2] at h
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem norm_sq_eq_tsum (x : H) : ‖x‖ ^ 2 = ∑' n, ((x : ∀ _ : ℕ, ℝ) n) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2] at h
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem inner_evec_left (n : ℕ) (x : H) :
    inner (𝕜 := ℝ) (evec n) x = (x : ∀ _ : ℕ, ℝ) n := by
  rw [evec, lp.inner_single_left]; simp

theorem orthonormal_evec : Orthonormal ℝ (fun n : ℕ => evec n) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp [inner_evec_left, evec_apply]

/-! ### Restriction of a vector to a set of coordinates -/

/-- The restriction of `x` to the coordinates in `T`: the vector agreeing
    with `x` on `T` and vanishing off `T`. -/
def restr (T : Set ℕ) (x : H) : H :=
  ⟨fun n => Set.indicator T (fun n => (x : ∀ _ : ℕ, ℝ) n) n, by
    apply memℓp_gen
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    rw [h2]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((lp.memℓp x).summable (p := 2) (by norm_num) |>.congr (fun n => by rw [h2]))
    by_cases h : n ∈ T
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
      positivity⟩

theorem restr_apply_of_mem {T : Set ℕ} {n : ℕ} (x : H) (h : n ∈ T) :
    (restr T x : ∀ _ : ℕ, ℝ) n = (x : ∀ _ : ℕ, ℝ) n := by
  show Set.indicator T _ n = _
  rw [Set.indicator_of_mem h]

theorem restr_apply_of_notMem {T : Set ℕ} {n : ℕ} (x : H) (h : n ∉ T) :
    (restr T x : ∀ _ : ℕ, ℝ) n = 0 := by
  show Set.indicator T _ n = _
  rw [Set.indicator_of_notMem h]

theorem restr_mem_block (T : Set ℕ) (x : H) : restr T x ∈ block T := by
  rw [mem_block_iff]
  intro n hn
  exact restr_apply_of_notMem x hn

theorem norm_restr_le (T : Set ℕ) (x : H) : ‖restr T x‖ ≤ ‖x‖ := by
  have hle : ‖restr T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    refine Summable.tsum_mono (summable_sq _) (summable_sq _) (fun n => ?_)
    by_cases h : n ∈ T
    · rw [restr_apply_of_mem x h]
    · rw [restr_apply_of_notMem x h]; simpa using sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hle

theorem inner_eq_inner_restr {T : Set ℕ} {y : H}
    (hy : ∀ m ∉ T, (y : ∀ _ : ℕ, ℝ) m = 0) (u : H) :
    inner (𝕜 := ℝ) y u = inner (𝕜 := ℝ) y (restr T u) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  by_cases h : n ∈ T
  · rw [restr_apply_of_mem u h]
  · rw [restr_apply_of_notMem u h, hy n h]
    simp

theorem norm_sq_restr_gt (x : H) (N : ℕ) :
    ‖restr {m | N < m} x‖ ^ 2 = ∑' i : ℕ, ((x : ∀ _ : ℕ, ℝ) (i + (N + 1))) ^ 2 := by
  rw [norm_sq_eq_tsum]
  have hs : Summable (fun n => ((restr {m | N < m} x : ∀ _ : ℕ, ℝ) n) ^ 2) := summable_sq _
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  rw [← hsplit]
  have h1 : ∑ i ∈ Finset.range (N + 1), ((restr {m | N < m} x : ∀ _ : ℕ, ℝ) i) ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [restr_apply_of_notMem x (by simp at hi ⊢; omega)]
    ring
  rw [h1, zero_add]
  refine tsum_congr (fun i => ?_)
  rw [restr_apply_of_mem x (by simp; omega)]

/-- The ℓ²-tails of a vector are eventually small. -/
theorem exists_tail_norm_le (u : H) {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N, N₀ < N ∧ ‖restr {m | N < m} u‖ ≤ ε := by
  have htend := tendsto_sum_nat_add (fun n => ((u : ∀ _ : ℕ, ℝ) n) ^ 2)
  have hev : ∀ᶠ i in Filter.atTop, ∑' k : ℕ, ((u : ∀ _ : ℕ, ℝ) (k + i)) ^ 2 < ε ^ 2 :=
    htend.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨M, hM⟩ := (hev.and (Filter.eventually_gt_atTop (N₀ + 1))).exists
  refine ⟨M - 1, by omega, ?_⟩
  have hM1 : M - 1 + 1 = M := by omega
  have hnorm := norm_sq_restr_gt u (M - 1)
  rw [hM1] at hnorm
  nlinarith [norm_nonneg (restr {m | M - 1 < m} u), hM.1, hnorm]

/-! ### Elementary block lemmas -/

theorem block_univ : block (univ : Set ℕ) = ⊤ := by
  ext x; simp [mem_block_iff]

theorem block_empty : block (∅ : Set ℕ) = ⊥ := by
  ext x
  simp only [mem_block_iff, Submodule.mem_bot, mem_empty_iff_false, not_false_iff,
    forall_true_left]
  constructor
  · intro h; exact lp.ext (funext (fun n => by simpa using h n))
  · rintro rfl; intro n; rfl

theorem block_mono {S T : Set ℕ} (h : S ⊆ T) : block S ≤ block T := by
  intro x hx
  rw [mem_block_iff] at hx ⊢
  exact fun n hn => hx n (fun hs => hn (h hs))

theorem block_inter (S T : Set ℕ) : block (S ∩ T) = block S ⊓ block T := by
  ext x
  simp only [mem_block_iff, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun n hn => h n (fun hc => hn hc.1), fun n hn => h n (fun hc => hn hc.2)⟩
  · rintro ⟨h1, h2⟩ n hn
    by_cases hS : n ∈ S
    · exact h2 n (fun hT => hn ⟨hS, hT⟩)
    · exact h1 n hS

theorem evec_mem_block {S : Set ℕ} {n : ℕ} (h : n ∈ S) : evec n ∈ block S := by
  rw [mem_block_iff]
  intro m hm
  rw [evec_apply, if_neg]
  rintro rfl; exact hm h

/-- Members of an ultrafilter containing the cofinite filter are infinite. -/
theorem infinite_of_mem (U : Ultrafilter ℕ) (hcof : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U)
    {S : Set ℕ} (hS : S ∈ U) : S.Infinite := by
  have h := (PlufWO4.inter_infinite_iff_mem U hcof S).mpr hS S hS
  simpa using h

/-- Intersections of closed subspaces are closed. -/
theorem isClosed_inf {M N : Submodule ℝ H} (hM : IsClosed (M : Set H))
    (hN : IsClosed (N : Set H)) : IsClosed ((M ⊓ N : Submodule ℝ H) : Set H) := by
  have : ((M ⊓ N : Submodule ℝ H) : Set H) = (M : Set H) ∩ (N : Set H) := rfl
  rw [this]
  exact hM.inter hN

/-! ### Finiteness criteria -/

/-- An infinite orthonormal family inside a submodule forbids finiteness. -/
theorem not_finite_of_orthonormal {ι : Type*} [Infinite ι] (v : ι → H)
    (hv : Orthonormal ℝ v) (P : Submodule ℝ H) (hmem : ∀ i, v i ∈ P) :
    ¬ Module.Finite ℝ ↥P := by
  intro hfin
  have hli : LinearIndependent ℝ (fun i => (⟨v i, hmem i⟩ : ↥P)) :=
    LinearIndependent.of_comp P.subtype (by simpa using hv.linearIndependent)
  have := hli.finite_of_isNoetherian (R := ℝ)
  exact not_finite ι

/-- An infinite family of nonzero pairwise-orthogonal vectors inside a
    submodule forbids finiteness. -/
theorem not_finite_of_orthogonal_family {ι : Type*} [Infinite ι] (v : ι → H)
    (hne : ∀ i, v i ≠ 0)
    (horth : Pairwise (fun i j => inner (𝕜 := ℝ) (v i) (v j) = 0))
    (P : Submodule ℝ H) (hmem : ∀ i, v i ∈ P) :
    ¬ Module.Finite ℝ ↥P := by
  classical
  set w : ι → H := fun i => (‖v i‖)⁻¹ • v i with hw
  have hnorm : ∀ i, ‖v i‖ ≠ 0 := fun i => by
    simpa [norm_ne_zero_iff] using hne i
  refine not_finite_of_orthonormal w ?_ P (fun i => P.smul_mem _ (hmem i))
  rw [orthonormal_iff_ite]
  intro i j
  simp only [hw]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_mul_norm]
    field_simp
    exact div_self (hnorm i)
  · rw [if_neg hij, real_inner_smul_left, real_inner_smul_right, horth hij,
      mul_zero, mul_zero]

/-- The block of an infinite set is infinite-dimensional. -/
theorem not_finite_block {S : Set ℕ} (hS : S.Infinite) :
    ¬ Module.Finite ℝ ↥(block S) := by
  have : Infinite ↥S := hS.to_subtype
  refine not_finite_of_orthonormal (fun n : ↥S => evec (n : ℕ)) ?_ _
    (fun n => evec_mem_block n.2)
  exact orthonormal_evec.comp _ Subtype.val_injective

/-- The block of a finite set is finite-dimensional. -/
theorem finite_block {C : Set ℕ} (hC : C.Finite) : Module.Finite ℝ ↥(block C) := by
  rw [← Module.rank_lt_aleph0_iff]
  exact lt_of_le_of_lt (PlufWO4.rank_le_of_le_block_finite hC _ le_rfl) (by simp)

theorem card_le_finrank_block (C : Finset ℕ) :
    C.card ≤ Module.finrank ℝ ↥(block (C : Set ℕ)) := by
  haveI : Module.Finite ℝ ↥(block (C : Set ℕ)) := finite_block C.finite_toSet
  have hli : LinearIndependent ℝ
      (fun n : (C : Set ℕ) => (⟨evec (n : ℕ), evec_mem_block n.2⟩ :
        ↥(block (C : Set ℕ)))) :=
    LinearIndependent.of_comp (block (C : Set ℕ)).subtype
      (by simpa using (orthonormal_evec.comp _ Subtype.val_injective).linearIndependent)
  have := hli.fintype_card_le_finrank
  simpa using this

/-- A subspace meeting a closed subspace of finite codimension only in `0`
    is itself finite-dimensional. -/
theorem finite_of_trivial_on_finite_codim (X V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (hVfin : Module.Finite ℝ ↥Vᗮ) (hXV : ∀ x ∈ X, x ∈ V → x = 0) :
    Module.Finite ℝ ↥X := by
  haveI : CompleteSpace V := hV.completeSpace_coe
  haveI : Module.Finite ℝ ↥Vᗮ := hVfin
  set f : ↥X →ₗ[ℝ] ↥Vᗮ :=
    (LinearMap.codRestrict Vᗮ
      (((Vᗮ).starProjection : H →L[ℝ] H).toLinearMap.comp X.subtype)
      (fun x => Submodule.starProjection_apply_mem _ _)) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have h0 : (Vᗮ).starProjection x = 0 := by
      have hz : f ⟨x, hx⟩ = 0 := hker
      simpa [hf] using congrArg Subtype.val hz
    have hxV : x ∈ V := by
      have hmem : x ∈ (Vᗮ)ᗮ := by
        have hsub : x - (Vᗮ).starProjection x ∈ (Vᗮ)ᗮ :=
          Submodule.sub_starProjection_mem_orthogonal x
        simpa [h0] using hsub
      rwa [Submodule.orthogonal_orthogonal] at hmem
    exact Subtype.ext (by simpa using hXV x hx hxV)
  exact Module.Finite.of_injective f hinj

/-- An infinite-dimensional subspace meets every closed subspace of finite
    codimension nontrivially. -/
theorem inf_ne_bot_of_not_finite (X V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (hVfin : Module.Finite ℝ ↥Vᗮ) (hX : ¬ Module.Finite ℝ ↥X) :
    X ⊓ V ≠ ⊥ := by
  intro hbot
  refine hX (finite_of_trivial_on_finite_codim X V hV hVfin (fun x hx hxV => ?_))
  have hmem2 : x ∈ X ⊓ V := ⟨hx, hxV⟩
  rw [hbot] at hmem2
  simpa using hmem2

/-! ### Relative codimension -/

/-- Finite codimension of `W` inside `V`, as finiteness of the quotient of
    `V` by the image of `W ⊓ V`. -/
def FinCodimIn (W V : Submodule ℝ H) : Prop :=
  Module.Finite ℝ (↥V ⧸ (W ⊓ V).comap V.subtype)

/-- The bridge: relative codimension is finite exactly when the relative
    orthocomplement of `W ⊓ V` in `V` is finite-dimensional. Only closedness
    of `W ⊓ V` is used. -/
theorem finCodimIn_iff_finite_orthocomplement (W V : Submodule ℝ H)
    (hWV : IsClosed ((W ⊓ V : Submodule ℝ H) : Set H)) :
    FinCodimIn W V ↔ Module.Finite ℝ ↥((W ⊓ V)ᗮ ⊓ V) := by
  classical
  haveI : CompleteSpace ↥(W ⊓ V) := hWV.completeSpace_coe
  set f : ↥((W ⊓ V)ᗮ ⊓ V) →ₗ[ℝ] (↥V ⧸ (W ⊓ V).comap V.subtype) :=
    ((W ⊓ V).comap V.subtype).mkQ.comp
      (Submodule.inclusion (fun x hx => hx.2)) with hf
  have hfapply : ∀ r : ↥((W ⊓ V)ᗮ ⊓ V),
      f r = Submodule.Quotient.mk ⟨(r : H), r.2.2⟩ := fun r => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxR⟩ hker
    have hx : (⟨x, hxR.2⟩ : ↥V) ∈ (W ⊓ V).comap V.subtype := by
      have hz : f ⟨x, hxR⟩ = 0 := hker
      rw [hfapply] at hz
      simpa [Submodule.Quotient.mk_eq_zero] using hz
    have hxK : x ∈ W ⊓ V := hx
    have hmem : x ∈ (W ⊓ V) ⊓ (W ⊓ V)ᗮ := ⟨hxK, hxR.1⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hpK : (W ⊓ V).starProjection (v : H) ∈ W ⊓ V :=
      Submodule.starProjection_apply_mem _ _
    have hpV : (W ⊓ V).starProjection (v : H) ∈ V := hpK.2
    have hrR : (v : H) - (W ⊓ V).starProjection (v : H) ∈ (W ⊓ V)ᗮ ⊓ V :=
      ⟨Submodule.sub_starProjection_mem_orthogonal _, Submodule.sub_mem _ v.2 hpV⟩
    refine ⟨⟨_, hrR⟩, ?_⟩
    rw [hfapply, Submodule.Quotient.eq, Submodule.mem_comap]
    have hval : (V.subtype) ((⟨(v : H) - (W ⊓ V).starProjection (v : H), hrR.2⟩ : ↥V) - v)
        = -((W ⊓ V).starProjection (v : H)) := by
      simp
    rw [hval]
    exact neg_mem hpK
  constructor
  · intro h
    haveI : Module.Finite ℝ (↥V ⧸ (W ⊓ V).comap V.subtype) := h
    exact Module.Finite.of_injective f hinj
  · intro h
    haveI : Module.Finite ℝ ↥((W ⊓ V)ᗮ ⊓ V) := h
    exact Module.Finite.of_surjective f hsurj

end

end PlufWO5
