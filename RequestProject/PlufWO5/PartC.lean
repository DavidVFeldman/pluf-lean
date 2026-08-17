/-
  PlufWO5/PartC.lean — Work Order 5, Part C: Theorem 3.4 — necessity in
  full (the witness subspace is unadded yet addable), and sufficiency
  parametrized by a Mathias hypothesis.
-/
import RequestProject.PlufWO5.PartA
import RequestProject.PlufWO5.PartB

open Set

set_option synthInstance.maxHeartbeats 1000000

namespace PlufWO5

open PlufWO1

noncomputable section

/-- The witness subspace of a partition is closed: it is an intersection of
    kernels of continuous functionals. -/
theorem isClosed_W (A : ℕ → Set ℕ) : IsClosed ((PlufWO1.W A : Submodule ℝ H) : Set H) := by
  have h : ((PlufWO1.W A : Submodule ℝ H) : Set H)
      = ⋂ k, {x : H | innerSL ℝ (constraintVec (A k)) x = 0} := by
    ext x
    simp only [SetLike.mem_coe, mem_W_iff, mem_iInter, mem_setOf_eq, innerSL_apply_apply]
    exact ⟨fun h k => by rw [real_inner_comm]; exact h k,
      fun h k => by rw [real_inner_comm]; exact h k⟩
  rw [h]
  exact isClosed_iInter fun k =>
    isClosed_eq (innerSL ℝ (constraintVec (A k))).continuous continuous_const

/-- A constraint vector is supported in its own index set. -/
theorem constraintVec_mem_block (T : Set ℕ) : constraintVec T ∈ block T := by
  rw [mem_block_iff]
  intro n hn
  rw [constraintVec_apply, if_neg hn]

/-- Against a vector supported in `S`, the constraint vector of `T` and that
    of `T ∩ S` are indistinguishable. -/
theorem inner_constraintVec_inter {S T : Set ℕ} {x : H} (hx : x ∈ block S) :
    inner (𝕜 := ℝ) x (constraintVec (T ∩ S)) = inner (𝕜 := ℝ) x (constraintVec T) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  by_cases hn : n ∈ S
  · by_cases hT : n ∈ T
    · rw [constraintVec_apply, constraintVec_apply, if_pos ⟨hT, hn⟩, if_pos hT]
    · rw [constraintVec_apply, constraintVec_apply, if_neg (fun h => hT h.1), if_neg hT]
  · rw [(mem_block_iff S x).mp hx n hn]
    simp

/-- Cofinal sets belong to an ultrafilter refining the cofinite filter. -/
theorem gt_mem (U : Ultrafilter ℕ) (hcof : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U) (N : ℕ) :
    {n : ℕ | N < n} ∈ U := by
  induction N with
  | zero =>
      have := hcof 0
      refine Filter.mem_of_superset this (fun n hn => ?_)
      simp only [mem_compl_iff, mem_singleton_iff] at hn
      simpa using Nat.pos_of_ne_zero hn
  | succ N ih =>
      have := Filter.inter_mem ih (hcof (N + 1))
      refine Filter.mem_of_superset this (fun n hn => ?_)
      obtain ⟨h1, h2⟩ := hn
      simp only [mem_setOf_eq] at h1 ⊢
      simp only [mem_compl_iff, mem_singleton_iff] at h2
      omega

/-- The two-point witness vector of a pair inside a single piece lies in the
    witness subspace. -/
theorem pairVec_mem_W (A : ℕ → Set ℕ) (hdisj : Pairwise (Function.onFun Disjoint A))
    {a b k : ℕ} (ha : a ∈ A k) (hb : b ∈ A k) :
    ((2 : ℝ) ^ (a + 1) • evec a - (2 : ℝ) ^ (b + 1) • evec b) ∈ PlufWO1.W A := by
  rw [mem_W_iff]
  intro j
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    inner_evec_left, inner_evec_left, constraintVec_apply, constraintVec_apply]
  rcases eq_or_ne j k with rfl | hjk
  · rw [if_pos ha, if_pos hb]
    field_simp
    ring
  · have hda := Set.disjoint_right.mp (hdisj hjk) ha
    have hdb := Set.disjoint_right.mp (hdisj hjk) hb
    rw [if_neg (fun h => hda h), if_neg (fun h => hdb h)]
    ring

section Necessity

variable (U : Ultrafilter ℕ) (A : ℕ → Set ℕ)
  (hdisj : Pairwise (Function.onFun Disjoint A))
  (hne : ∀ k, (A k).Nonempty) (hcover : (⋃ k, A k) = univ)
  (hcof : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U)
  (hpieces : ∀ k, A k ∉ U)
  (hsel : ∀ S ∈ U, ¬ PlufWO1.IsPartialSelector S A)

include hdisj hne hcover hcof hpieces hsel in
/-- C1 (necessity, unadded half). Every `U`-set touches infinitely many
    pieces (a `U`-set inside a finite union of pieces puts a piece in
    `U`), and the restricted constraint vectors of touched pieces are
    linearly independent members of the relative orthocomplement of
    `W ⊓ block S` in `block S`; so the relative codimension is infinite
    and, by B1, `W ∉ Φ(U)`.

    Note: the contract hypotheses `hne`, `hcof` and `hsel` are retained as
    stated but are not consumed here; the argument uses only pairwise
    disjointness, the covering property and `hpieces`. -/
theorem witness_not_mem : ¬ PhiOmega U (PlufWO1.W A) := by
  classical
  rw [phiOmega_iff_finCodim U _ (isClosed_W A)]
  push_neg
  intro S hSU hcodim
  set K : Set ℕ := {k | (A k ∩ S).Nonempty} with hKdef
  have hKinf : K.Infinite := by
    intro hfin
    have hsub : S ⊆ ⋃ k ∈ K, A k := by
      intro n hn
      have : n ∈ ⋃ k, A k := by rw [hcover]; trivial
      obtain ⟨_, ⟨k, rfl⟩, hnk⟩ := this
      exact mem_biUnion (show k ∈ K from ⟨n, hnk, hn⟩) hnk
    have hmem : (⋃ k ∈ K, A k) ∈ U := Filter.mem_of_superset hSU hsub
    obtain ⟨k, _, hk⟩ := (Ultrafilter.finite_biUnion_mem_iff hfin).mp hmem
    exact hpieces k hk
  have hWSclosed : IsClosed ((PlufWO1.W A ⊓ block S : Submodule ℝ H) : Set H) :=
    isClosed_inf (isClosed_W A) (isClosed_block S)
  rw [finCodimIn_iff_finite_orthocomplement _ _ hWSclosed] at hcodim
  haveI : Infinite ↥K := hKinf.to_subtype
  refine not_finite_of_orthogonal_family (fun k : ↥K => constraintVec (A (k : ℕ) ∩ S))
    (fun k => constraintVec_ne_zero k.2) ?_ _ ?_ hcodim
  · intro i j hij
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    refine inner_constraintVec_eq_zero_of_disjoint ?_ (constraintVec_mem_block _)
    exact ((hdisj hne').mono inter_subset_left inter_subset_left).symm
  · intro k
    refine ⟨?_, block_mono inter_subset_right (constraintVec_mem_block _)⟩
    refine (Submodule.mem_orthogonal _ _).mpr (fun u hu => ?_)
    rw [inner_constraintVec_inter hu.2]
    exact (mem_W_iff A u).mp hu.1 _

include hdisj hne hcover hcof hpieces hsel in
/-- C2 (necessity, addable half). For every `S ∈ U`, the space
    `W ⊓ block S` is infinite-dimensional: the two-point witness vectors
    (WO-3's C2 move at ω) supply an infinite orthogonal family.

    Pair organization (reported): the pairs are produced by a recursion
    that keeps them consecutive and separated — at stage `i` the tail
    `S ∩ {n | gᵢ < n}` is still in `U` (by `hcof`), so `hsel` yields two
    distinct points `aᵢ < bᵢ` of it inside one piece `A k`, and
    `gᵢ₊₁ := bᵢ`. Distinct pairs therefore have disjoint supports and the
    witnesses `2^(aᵢ+1) • e aᵢ − 2^(bᵢ+1) • e bᵢ` are pairwise orthogonal.

    Note: the contract hypotheses `hne`, `hcover` and `hpieces` are
    retained as stated but are not consumed here. -/
theorem witness_infDim : ∀ S ∈ U, ¬ Module.Finite ℝ ↥(PlufWO1.W A ⊓ block S) := by
  classical
  intro S hSU
  have hstep : ∀ N : ℕ, ∃ p : ℕ × ℕ,
      N < p.1 ∧ p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S ∧ ∃ k, p.1 ∈ A k ∧ p.2 ∈ A k := by
    intro N
    have hmem : S ∩ {n : ℕ | N < n} ∈ U := Filter.inter_mem hSU (gt_mem U hcof N)
    have hns := hsel _ hmem
    rw [PlufWO1.IsPartialSelector] at hns
    push_neg at hns
    obtain ⟨k, hk⟩ := hns
    obtain ⟨a, ha, b, hb, hab⟩ := hk
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨(a, b), ha.1.2, h, ha.1.1, hb.1.1, k, ha.2, hb.2⟩
    · exact ⟨(b, a), hb.1.2, h, hb.1.1, ha.1.1, k, hb.2, ha.2⟩
  choose f hf1 hf2 hf3 hf4 hf5 using hstep
  set g : ℕ → ℕ := fun i => Nat.rec 0 (fun _ n => (f n).2) i with hgdef
  have hgsucc : ∀ i, g (i + 1) = (f (g i)).2 := fun _ => rfl
  have hmono : StrictMono g := strictMono_nat_of_lt_succ (fun i => by
    rw [hgsucc]; exact lt_trans (hf1 (g i)) (hf2 (g i)))
  set a : ℕ → ℕ := fun i => (f (g i)).1 with hadef
  set b : ℕ → ℕ := fun i => (f (g i)).2 with hbdef
  have hab : ∀ i, g i < a i ∧ a i < b i ∧ b i = g (i + 1) := fun i =>
    ⟨hf1 (g i), hf2 (g i), (hgsucc i).symm⟩
  have hsep : ∀ i j, i < j → b i ≤ g j := by
    intro i j hij
    have := hmono.monotone (Nat.succ_le_of_lt hij)
    rw [(hab i).2.2]
    exact this
  set w : ℕ → H := fun i =>
    (2 : ℝ) ^ (a i + 1) • evec (a i) - (2 : ℝ) ^ (b i + 1) • evec (b i) with hwdef
  have hinner : ∀ i j, inner (𝕜 := ℝ) (w i) (w j)
      = (2 : ℝ) ^ (a i + 1) * (2 : ℝ) ^ (a j + 1) * (if a i = a j then 1 else 0)
        - (2 : ℝ) ^ (a i + 1) * (2 : ℝ) ^ (b j + 1) * (if a i = b j then 1 else 0)
        - (2 : ℝ) ^ (b i + 1) * (2 : ℝ) ^ (a j + 1) * (if b i = a j then 1 else 0)
        + (2 : ℝ) ^ (b i + 1) * (2 : ℝ) ^ (b j + 1) * (if b i = b j then 1 else 0) := by
    intro i j
    simp only [hwdef, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, inner_evec_left, evec_apply]
    ring
  refine not_finite_of_orthogonal_family w ?_ ?_ _ ?_
  · intro i hi
    have h0 : inner (𝕜 := ℝ) (w i) (w i) = 0 := by rw [hi]; simp
    rw [hinner i i, if_pos rfl, if_pos rfl,
      if_neg (Nat.ne_of_lt (hab i).2.1), if_neg (Nat.ne_of_gt (hab i).2.1)] at h0
    have hpa : (0 : ℝ) < (2 : ℝ) ^ (a i + 1) := by positivity
    have hpb : (0 : ℝ) < (2 : ℝ) ^ (b i + 1) := by positivity
    nlinarith [h0]
  · intro i j hij
    have hlt : ∀ {i j : ℕ}, i < j → a i < a j ∧ a i < b j ∧ b i < a j ∧ b i < b j := by
      intro i j h
      have h1 : b i ≤ g j := hsep i j h
      have h2 : g j < a j := (hab j).1
      have h3 : a j < b j := (hab j).2.1
      have h4 : a i < b i := (hab i).2.1
      exact ⟨by omega, by omega, by omega, by omega⟩
    rcases lt_or_gt_of_ne hij with h | h
    · obtain ⟨p1, p2, p3, p4⟩ := hlt h
      rw [hinner i j, if_neg (Nat.ne_of_lt p1), if_neg (Nat.ne_of_lt p2),
        if_neg (Nat.ne_of_lt p3), if_neg (Nat.ne_of_lt p4)]
      ring
    · obtain ⟨p1, p2, p3, p4⟩ := hlt h
      rw [hinner i j, if_neg (Nat.ne_of_gt p1), if_neg (Nat.ne_of_gt p3),
        if_neg (Nat.ne_of_gt p2), if_neg (Nat.ne_of_gt p4)]
      ring
  · intro i
    obtain ⟨k, hka, hkb⟩ := hf5 (g i)
    refine ⟨pairVec_mem_W A hdisj hka hkb, ?_⟩
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ (evec_mem_block (hf3 (g i))))
      (Submodule.smul_mem _ _ (evec_mem_block (hf4 (g i))))

include hdisj hne hcover hcof hpieces hsel in
/-- C3 (Theorem 3.4, necessity, packaged). The witness is unadded yet
    meets every member. -/
theorem necessity :
    ¬ PhiOmega U (PlufWO1.W A) ∧
      ∀ N : Submodule ℝ H, PhiOmega U N → PlufWO1.W A ⊓ N ≠ ⊥ := by
  refine ⟨witness_not_mem U A hdisj hne hcover hcof hpieces hsel, ?_⟩
  exact (addable_iff_infDim U hcof (PlufWO1.W A) (isClosed_W A)).mpr
    (witness_infDim U A hdisj hne hcover hcof hpieces hsel)

end Necessity

/-- The Mathias hypothesis for `U` at a closed subspace `W`: some `U`-set
    is homogeneous for the analytic family `{T : W ⊓ block T ≠ ⊥}`. -/
def MathiasHyp (U : Ultrafilter ℕ) (W : Submodule ℝ H) : Prop :=
  ∃ S ∈ U, (∀ T ⊆ S, T.Infinite → W ⊓ block T ≠ ⊥) ∨
    (∀ T ⊆ S, T.Infinite → W ⊓ block T = ⊥)

/-- C4 (Theorem 3.4, sufficiency, Mathias-parametrized). If the Mathias
    hypothesis holds at `W`, then `Φ(U)` decides `W`. -/
theorem decides_of_mathias (U : Ultrafilter ℕ)
    (hcof : ∀ n : ℕ, ({n}ᶜ : Set ℕ) ∈ U)
    (W : Submodule ℝ H) (hW : IsClosed (W : Set H))
    (hM : MathiasHyp U W) :
    PhiOmega U W ∨ ∃ N : Submodule ℝ H, PhiOmega U N ∧ W ⊓ N = ⊥ := by
  obtain ⟨S, hSU, hhom⟩ := hM
  have hSinf : S.Infinite := infinite_of_mem U hcof hSU
  have hblockS : PhiOmega U (block S) :=
    ⟨S, hSU, ⊤, by simp,
      by rw [Submodule.top_orthogonal_eq_bot]; infer_instance, by simp⟩
  rcases hhom with hpos | hneg
  · rcases relativized_dichotomy W hW hSinf with hcodim | ⟨T, hTS, hTinf, hTbot⟩
    · exact Or.inl ((phiOmega_iff_finCodim U W hW).mpr ⟨S, hSU, hcodim⟩)
    · exact absurd hTbot (hpos T hTS hTinf)
  · exact Or.inr ⟨block S, hblockS, hneg S subset_rfl hSinf⟩

end

end PlufWO5
