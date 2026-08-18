/-
  PlufWO12/PartA.lean — the stage construction of Work Order 12.

  Fix a Hilbert basis `b : HilbertBasis ℕ ℝ H`, a decreasing sequence `h`
  of infinite-dimensional closed subspaces, and a closed subspace `N` with
  `h n ⊓ N` finite-dimensional for each `n`.  We build a closed subspace
  `R` which
    * is not `b`-intimate,
    * meets `N` trivially,
    * meets every `h j` in infinite dimension.

  The construction chooses unit vectors `w n ∈ h n` and thresholds
  `k 0 < p 0 < q 0 = k 1 < p 1 < q 1 = k 2 < ⋯` in the basis index with

    (a) `b.repr (w n) i = 0` for `i ≤ k n`;
    (b) `w n ⊥ w j` for `j < n`, and `w n ⊥ (h 0 ⊓ N)`;
    (c) `b.repr (w n) (p n) ≠ 0 ≠ b.repr (w n) (q n)`.

  Then `R` is the closed span of the `w n` and `A = Set.range p`.
-/
import RequestProject.PlufWO12.Basic

open Set RealInnerProductSpace

namespace PlufWO12

/-! ### Expansions along an orthonormal family -/

section Expansion

/-- The closed span of a sequence of vectors. -/
noncomputable def closedSpan (w : ℕ → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range w)).topologicalClosure

theorem closedSpan_def (w : ℕ → H) :
    closedSpan w = (Submodule.span ℝ (Set.range w)).topologicalClosure := rfl

theorem isClosed_closedSpan (w : ℕ → H) : IsClosed ((closedSpan w : Submodule ℝ H) : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem mem_closedSpan (w : ℕ → H) (n : ℕ) : w n ∈ closedSpan w :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

theorem closedSpan_le {w : ℕ → H} {M : Submodule ℝ H}
    (hM : IsClosed ((M : Submodule ℝ H) : Set H)) (hmem : ∀ n, w n ∈ M) :
    closedSpan w ≤ M := by
  have hsub : (Set.range w) ⊆ (M : Set H) := by rintro _ ⟨n, rfl⟩; exact hmem n
  rw [closedSpan_def]
  exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hsub) hM

/-- A vector of the closed span orthogonal to every member of the family is zero. -/
theorem eq_zero_of_mem_closedSpan_of_inner_eq_zero {w : ℕ → H} {x : H} (hx : x ∈ closedSpan w)
    (h0 : ∀ n, ⟪w n, x⟫ = 0) : x = 0 := by
  have hxo : x ∈ (Submodule.span ℝ (Set.range w))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨n, rfl⟩ := hy; exact h0 n
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
    | smul c y _ hy => simp [inner_smul_left, hy]
  have hxo' : x ∈ (closedSpan w)ᗮ := by
    rw [closedSpan_def, Submodule.orthogonal_closure]
    exact hxo
  have hmem : x ∈ closedSpan w ⊓ (closedSpan w)ᗮ := ⟨hx, hxo'⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hmem
  simpa using hmem

/-- Every vector of the closed span of an orthonormal family is the sum of
    its Fourier series along the family. -/
theorem hasSum_of_mem_closedSpan {w : ℕ → H} (hw : Orthonormal ℝ w) {x : H}
    (hx : x ∈ closedSpan w) :
    HasSum (fun n => (⟪w n, x⟫ : ℝ) • w n) x := by
  classical
  set R := closedSpan w with hR
  have hRc : IsClosed ((R : Submodule ℝ H) : Set H) := isClosed_closedSpan w
  haveI : CompleteSpace ↥R := IsClosed.completeSpace_coe (hs := hRc)
  set e : ℕ → ↥R := fun n => ⟨w n, mem_closedSpan w n⟩ with he
  have hone : Orthonormal ℝ e := ⟨fun i => hw.1 i, fun {i j} hij => hw.2 hij⟩
  have hbot : (Submodule.span ℝ (Set.range e))ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro y hy
    have h0 : ∀ n, ⟪w n, (y : H)⟫ = 0 := fun n => hy (e n) (Submodule.subset_span ⟨n, rfl⟩)
    have hy0 : (y : H) = 0 := eq_zero_of_mem_closedSpan_of_inner_eq_zero y.2 h0
    rw [Submodule.mem_bot]
    exact Subtype.ext (by simpa using hy0)
  have hcoe : ⇑(HilbertBasis.mkOfOrthogonalEqBot hone hbot) = e :=
    HilbertBasis.coe_mkOfOrthogonalEqBot hone hbot
  set hb : HilbertBasis ℕ ℝ ↥R := HilbertBasis.mkOfOrthogonalEqBot hone hbot with hbdef
  have hsum := (hb.hasSum_repr ⟨x, hx⟩).mapL (R.subtypeL)
  have hfun : (fun n => (R.subtypeL) (hb.repr ⟨x, hx⟩ n • hb n))
      = fun n => (⟪w n, x⟫ : ℝ) • w n := by
    funext n
    have hr : hb.repr ⟨x, hx⟩ n = (⟪w n, x⟫ : ℝ) := by
      rw [HilbertBasis.repr_apply_apply, hcoe]
      rfl
    rw [hr]
    simp [hcoe, he]
  rw [hfun] at hsum
  simpa using hsum

/-- If `x` lies in the closed span of an orthonormal family, `L` is below
    the support of its coefficient sequence, and `v` is orthogonal to all
    members of the family after `L`, then `⟪v, x⟫` collapses to the single
    term `L`. -/
theorem inner_eq_of_least {w : ℕ → H} (hw : Orthonormal ℝ w) {x : H} (hx : x ∈ closedSpan w)
    (v : H) (L : ℕ) (hzero : ∀ n, n < L → ⟪w n, x⟫ = 0)
    (hvan : ∀ n, L < n → ⟪v, w n⟫ = 0) :
    ⟪v, x⟫ = ⟪w L, x⟫ * ⟪v, w L⟫ := by
  have hsum := (hasSum_of_mem_closedSpan hw hx).mapL (innerSL ℝ v)
  simp only [innerSL_apply_apply, real_inner_smul_right] at hsum
  have hsingle : HasSum (fun n => (⟪w n, x⟫ : ℝ) * ⟪v, w n⟫)
      ((⟪w L, x⟫ : ℝ) * ⟪v, w L⟫) := by
    refine hasSum_single (f := fun n => (⟪w n, x⟫ : ℝ) * ⟪v, w n⟫) L ?_
    intro n hn
    show (⟪w n, x⟫ : ℝ) * ⟪v, w n⟫ = 0
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · rw [hzero n hlt, zero_mul]
    · rw [hvan n hgt, mul_zero]
  exact hsum.unique hsingle

end Expansion

/-! ### A2: two nonzero coordinates -/

section Coords

variable (b : HilbertBasis ℕ ℝ H)

/-- A vector with at most one nonzero coordinate is a multiple of a basis
    vector. -/
theorem eq_smul_basis_of_unique_coord {x : H} {i : ℕ}
    (h : ∀ j, j ≠ i → b.repr x j = 0) : x = (b.repr x i) • b i := by
  have hzero : ∀ j, b.repr (x - (b.repr x i) • b i) j = 0 := by
    intro j
    rw [map_sub, map_smul]
    by_cases hj : j = i
    · subst hj
      simp [HilbertBasis.repr_self]
    · simp [h j hj, HilbertBasis.repr_self, Pi.single_eq_of_ne hj]
  exact sub_eq_zero.mp (PlufWO9.eq_zero_of_repr_eq_zero b hzero)

/-- A vector with no two nonzero coordinates is a multiple of a basis
    vector. -/
theorem exists_eq_smul_basis_of_not_two {x : H}
    (h : ¬ ∃ i j : ℕ, i ≠ j ∧ b.repr x i ≠ 0 ∧ b.repr x j ≠ 0) :
    ∃ i : ℕ, x = (b.repr x i) • b i := by
  classical
  by_cases hx0 : ∀ j, b.repr x j = 0
  · refine ⟨0, ?_⟩
    have hx : x = 0 := PlufWO9.eq_zero_of_repr_eq_zero b hx0
    simp [hx]
  · push_neg at hx0
    obtain ⟨i, hi⟩ := hx0
    refine ⟨i, eq_smul_basis_of_unique_coord b ?_⟩
    intro j hj
    by_contra hji
    exact h ⟨j, i, hj, hji, hi⟩

/-- The coordinates of a multiple of a basis vector. -/
theorem repr_smul_basis (c : ℝ) (i j : ℕ) (hij : j ≠ i) : b.repr (c • b i) j = 0 := by
  simp [HilbertBasis.repr_self, Pi.single_eq_of_ne hij]

/-- A2 (two nonzero coordinates). An infinite-dimensional subspace contains
    a vector with two nonzero `b`-coordinates. -/
theorem exists_two_nonzero_coords_aux {M : Submodule ℝ H}
    (hM : ¬ FiniteDimensional ℝ ↥M) :
    ∃ x ∈ M, ∃ i j : ℕ, i ≠ j ∧ b.repr x i ≠ 0 ∧ b.repr x j ≠ 0 := by
  classical
  have hMne : M ≠ ⊥ := by
    intro hbot
    exact hM (by rw [hbot]; infer_instance)
  obtain ⟨u, huM, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
  have hspan : ¬ M ≤ Submodule.span ℝ ({u} : Set H) := fun hle =>
    hM (Submodule.finiteDimensional_of_le hle)
  obtain ⟨v, hvM, hv⟩ : ∃ v ∈ M, v ∉ Submodule.span ℝ ({u} : Set H) := by
    by_contra hc
    push_neg at hc
    exact hspan hc
  by_cases hu2 : ∃ i j : ℕ, i ≠ j ∧ b.repr u i ≠ 0 ∧ b.repr u j ≠ 0
  · exact ⟨u, huM, hu2⟩
  by_cases hv2 : ∃ i j : ℕ, i ≠ j ∧ b.repr v i ≠ 0 ∧ b.repr v j ≠ 0
  · exact ⟨v, hvM, hv2⟩
  obtain ⟨i, hui⟩ := exists_eq_smul_basis_of_not_two b hu2
  obtain ⟨j, hvj⟩ := exists_eq_smul_basis_of_not_two b hv2
  have hc0 : b.repr u i ≠ 0 := by
    intro h0
    exact hu0 (by rw [hui, h0, zero_smul])
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; exact Submodule.zero_mem _)
  have hd0 : b.repr v j ≠ 0 := by
    intro h0
    exact hv0 (by rw [hvj, h0, zero_smul])
  obtain ⟨c, hcne, hueq⟩ : ∃ c : ℝ, c ≠ 0 ∧ u = c • b i := ⟨b.repr u i, hc0, hui⟩
  obtain ⟨d, hdne, hveq⟩ : ∃ d : ℝ, d ≠ 0 ∧ v = d • b j := ⟨b.repr v j, hd0, hvj⟩
  have hij : i ≠ j := by
    intro hji
    subst hji
    refine hv ?_
    have hvu : v = (d / c) • u := by
      rw [hueq, hveq, smul_smul, div_mul_cancel₀ _ hcne]
    rw [hvu]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hvi : b.repr v i = 0 := by
    rw [hveq]
    exact repr_smul_basis b _ j i hij
  have huj : b.repr u j = 0 := by
    rw [hueq]
    exact repr_smul_basis b _ i j (Ne.symm hij)
  refine ⟨u + v, M.add_mem huM hvM, i, j, hij, ?_, ?_⟩
  · rw [map_add]
    simpa [hvi] using hc0
  · rw [map_add]
    simpa [huj] using hd0

end Coords

/-! ### The stage vector: one step of the recursion -/

section Step

/-- One step of the stage recursion: inside an infinite-dimensional
    subspace `Mn`, and subject to finitely many orthogonality constraints
    (orthogonality to the previously chosen vectors `S`, to the
    finite-dimensional subspace `D`, and to the first `k` basis vectors),
    there is a unit vector with two nonzero coordinates, both beyond `k`. -/
theorem exists_stage_vector (b : HilbertBasis ℕ ℝ H) {Mn : Submodule ℝ H}
    (hMn : ¬ FiniteDimensional ℝ ↥Mn) {D : Submodule ℝ H} (hD : FiniteDimensional ℝ ↥D)
    (u : ℕ → H) (n : ℕ) (k : ℕ) :
    ∃ (w : H) (p q : ℕ), w ∈ Mn ∧ ‖w‖ = 1 ∧ (∀ j, j < n → ⟪u j, w⟫ = 0) ∧ w ∈ Dᗮ ∧
      (∀ i, i ≤ k → b.repr w i = 0) ∧ k < p ∧ p < q ∧
      b.repr w p ≠ 0 ∧ b.repr w q ≠ 0 := by
  classical
  set W : Submodule ℝ H := Submodule.span ℝ ((u '' Set.Iio n) ∪ (b '' Set.Iic k)) ⊔ D with hWdef
  haveI hspanfin :
      FiniteDimensional ℝ ↥(Submodule.span ℝ ((u '' Set.Iio n) ∪ (b '' Set.Iic k))) :=
    FiniteDimensional.span_of_finite ℝ
      (((Set.finite_Iio n).image u).union ((Set.finite_Iic k).image b))
  haveI hWfin : FiniteDimensional ℝ ↥W := Submodule.finiteDimensional_sup _ _
  have hinf : ¬ FiniteDimensional ℝ ↥(Mn ⊓ Wᗮ) := not_finiteDimensional_inf_orthogonal hMn hWfin
  obtain ⟨x, hxM, i, j, hij, hxi, hxj⟩ := exists_two_nonzero_coords_aux b hinf
  have hxMn : x ∈ Mn := hxM.1
  have hxW : x ∈ Wᗮ := hxM.2
  have horth : ∀ y ∈ W, ⟪y, x⟫ = 0 := (Submodule.mem_orthogonal W x).mp hxW
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx] at hxi
    simp at hxi
  set c : ℝ := ‖x‖⁻¹ with hc
  have hcne : c ≠ 0 := by
    simp [hc, norm_ne_zero_iff.mpr hx0]
  set w : H := c • x with hw
  have hreprw : ∀ m : ℕ, b.repr w m = c * b.repr x m := by
    intro m
    rw [hw, map_smul]
    simp
  have hvan : ∀ m, m ≤ k → b.repr w m = 0 := by
    intro m hm
    have hb : b m ∈ W := Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨m, hm, rfl⟩))
    have hzero : b.repr x m = 0 := by
      rw [HilbertBasis.repr_apply_apply]
      exact horth _ hb
    rw [hreprw, hzero, mul_zero]
  refine ⟨w, min i j, max i j, ?_, ?_, ?_, ?_, hvan, ?_, ?_, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ hxMn
  · rw [hw, hc, norm_smul]
    simp [norm_ne_zero_iff.mpr hx0]
  · intro jj hjj
    have hyW : u jj ∈ W :=
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨jj, hjj, rfl⟩))
    rw [hw, real_inner_smul_right, horth _ hyW, mul_zero]
  · have hDW : D ≤ W := le_sup_right
    have : x ∈ Dᗮ := Submodule.orthogonal_le hDW hxW
    exact Submodule.smul_mem _ _ this
  · -- k < min i j
    by_contra hk
    push_neg at hk
    have := hvan _ hk
    rcases min_choice i j with hmin | hmin <;> rw [hmin] at this <;>
      rw [hreprw] at this
    · exact hxi (by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hcne
        · exact h)
    · exact hxj (by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hcne
        · exact h)
  · exact min_lt_max.mpr hij
  · rw [hreprw]
    rcases min_choice i j with hmin | hmin <;> rw [hmin] <;>
      exact mul_ne_zero hcne (by assumption)
  · rw [hreprw]
    rcases max_choice i j with hmax | hmax <;> rw [hmax] <;>
      exact mul_ne_zero hcne (by assumption)

end Step

/-! ### The stage recursion -/

section Recursion

variable (F : ℕ → ℕ → (ℕ → H) → H × ℕ × ℕ)

/-- The state of the recursion after `n` steps: the vectors chosen so far
    (junk outside `Finset.range n`) together with the current threshold. -/
noncomputable def wState : ℕ → (ℕ → H) × ℕ
  | 0 => (fun _ => 0, 0)
  | n + 1 =>
      (Function.update (wState n).1 n (F n (wState n).2 (wState n).1).1,
        (F n (wState n).2 (wState n).1).2.2)

/-- The datum chosen at stage `n`. -/
noncomputable def wData (n : ℕ) : H × ℕ × ℕ :=
  F n (wState F n).2 (wState F n).1

/-- The vector chosen at stage `n`. -/
noncomputable def wSeq (n : ℕ) : H := (wData F n).1

/-- The first distinguished coordinate at stage `n`. -/
noncomputable def pSeq (n : ℕ) : ℕ := (wData F n).2.1

/-- The second distinguished coordinate at stage `n`. -/
noncomputable def qSeq (n : ℕ) : ℕ := (wData F n).2.2

/-- The threshold in force at stage `n`. -/
noncomputable def kSeq (n : ℕ) : ℕ := (wState F n).2

theorem kSeq_zero : kSeq F 0 = 0 := rfl

theorem kSeq_succ (n : ℕ) : kSeq F (n + 1) = qSeq F n := rfl

theorem wState_succ_fst (n : ℕ) :
    (wState F (n + 1)).1 = Function.update (wState F n).1 n (wSeq F n) := rfl

theorem wSeq_eq (n : ℕ) : wSeq F n = (F n (kSeq F n) (wState F n).1).1 := rfl

theorem pSeq_eq (n : ℕ) : pSeq F n = (F n (kSeq F n) (wState F n).1).2.1 := rfl

theorem qSeq_eq (n : ℕ) : qSeq F n = (F n (kSeq F n) (wState F n).1).2.2 := rfl

theorem wState_fst_apply : ∀ m n : ℕ, n < m → (wState F m).1 n = wSeq F n := by
  intro m
  induction m with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ m ih =>
      intro n hn
      rw [wState_succ_fst]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
      · rw [Function.update_of_ne (by omega) _ _]
        exact ih n hlt
      · subst heq
        simp

end Recursion

/-! ### A3: the stage construction -/

section Stage

/-- The family of vectors produced by the stage recursion, with all the
    properties the construction needs. -/
theorem exists_stage_family (b : HilbertBasis ℕ ℝ H) (h : ℕ → Submodule ℝ H)
    (hinf : ∀ n, ¬ FiniteDimensional ℝ ↥(h n)) {D : Submodule ℝ H}
    (hD : FiniteDimensional ℝ ↥D) :
    ∃ (w : ℕ → H) (p q : ℕ → ℕ),
      Orthonormal ℝ w ∧ (∀ n, w n ∈ h n) ∧ (∀ n, w n ∈ Dᗮ) ∧
      (∀ n, p n < q n) ∧ (∀ n m, n < m → q n < p m) ∧
      (∀ n, b.repr (w n) (p n) ≠ 0) ∧ (∀ n, b.repr (w n) (q n) ≠ 0) ∧
      (∀ n m, n < m → b.repr (w m) (p n) = 0 ∧ b.repr (w m) (q n) = 0) := by
  classical
  choose Fw Fp Fq hmem hnorm horth hDorth hvan hkp hpq hp0 hq0 using
    fun (n k : ℕ) (u : ℕ → H) => exists_stage_vector b (hinf n) hD u n k
  set F : ℕ → ℕ → (ℕ → H) → H × ℕ × ℕ := fun n k u => (Fw n k u, Fp n k u, Fq n k u) with hF
  set w : ℕ → H := wSeq F with hw
  set p : ℕ → ℕ := pSeq F with hp
  set q : ℕ → ℕ := qSeq F with hq
  set k : ℕ → ℕ := kSeq F with hk
  set u : ℕ → ℕ → H := fun n => (wState F n).1 with hu
  have hwn : ∀ n, w n = Fw n (k n) (u n) := fun n => rfl
  have hpn : ∀ n, p n = Fp n (k n) (u n) := fun n => rfl
  have hqn : ∀ n, q n = Fq n (k n) (u n) := fun n => rfl
  have hun : ∀ n j, j < n → u n j = w j := fun n j hj => wState_fst_apply F n j hj
  have hksucc : ∀ n, k (n + 1) = q n := fun n => rfl
  -- the basic stage properties
  have hmemn : ∀ n, w n ∈ h n := by intro n; rw [hwn]; exact hmem n (k n) (u n)
  have hnormn : ∀ n, ‖w n‖ = 1 := by intro n; rw [hwn]; exact hnorm n (k n) (u n)
  have horthn : ∀ n, ∀ j, j < n → ⟪w j, w n⟫ = 0 := by
    intro n j hj
    have := horth n (k n) (u n) j hj
    rwa [hun n j hj, ← hwn n] at this
  have hDorthn : ∀ n, w n ∈ Dᗮ := by intro n; rw [hwn]; exact hDorth n (k n) (u n)
  have hvann : ∀ n, ∀ i, i ≤ k n → b.repr (w n) i = 0 := by
    intro n i hi; rw [hwn]; exact hvan n (k n) (u n) i hi
  have hkpn : ∀ n, k n < p n := by intro n; rw [hpn]; exact hkp n (k n) (u n)
  have hpqn : ∀ n, p n < q n := by intro n; rw [hpn, hqn]; exact hpq n (k n) (u n)
  have hp0n : ∀ n, b.repr (w n) (p n) ≠ 0 := by
    intro n; rw [hwn, hpn]; exact hp0 n (k n) (u n)
  have hq0n : ∀ n, b.repr (w n) (q n) ≠ 0 := by
    intro n; rw [hwn, hqn]; exact hq0 n (k n) (u n)
  -- monotonicity of the thresholds
  have hkmono : Monotone k := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hksucc n]
    exact le_of_lt ((hkpn n).trans (hpqn n))
  -- separation of the distinguished coordinates
  have hsep : ∀ n m, n < m → q n < p m := by
    intro n m hnm
    have h1 : k (n + 1) ≤ k m := hkmono (Nat.succ_le_of_lt hnm)
    rw [hksucc n] at h1
    exact lt_of_le_of_lt h1 (hkpn m)
  -- late vectors vanish on early coordinates
  have hlate : ∀ n m, n < m → b.repr (w m) (p n) = 0 ∧ b.repr (w m) (q n) = 0 := by
    intro n m hnm
    have h1 : k (n + 1) ≤ k m := hkmono (Nat.succ_le_of_lt hnm)
    rw [hksucc n] at h1
    exact ⟨hvann m _ (le_of_lt (lt_of_lt_of_le (hpqn n) h1)), hvann m _ h1⟩
  -- orthonormality
  have hON : Orthonormal ℝ w := by
    refine ⟨hnormn, ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact horthn j i hlt
    · rw [real_inner_comm]
      exact horthn i j hgt
  exact ⟨w, p, q, hON, hmemn, hDorthn, hpqn, hsep, hp0n, hq0n, hlate⟩

/-- A3 (the stage construction). -/
theorem exists_nonIntimate_blocking_aux (b : HilbertBasis ℕ ℝ H) (h : ℕ → Submodule ℝ H)
    (N : Submodule ℝ H)
    (hmono : ∀ n, h (n + 1) ≤ h n)
    (hcl : ∀ n, IsClosed ((h n : Submodule ℝ H) : Set H))
    (hinf : ∀ n, ¬ FiniteDimensional ℝ ↥(h n))
    (hNfin : ∀ n, FiniteDimensional ℝ ↥(h n ⊓ N)) :
    ∃ R : Submodule ℝ H, IsClosed (R : Set H) ∧
      ¬ PlufWO10.IntimateB b R ∧
      R ⊓ N = ⊥ ∧
      ∀ j, ¬ FiniteDimensional ℝ ↥(R ⊓ h j) := by
  classical
  have hmonoAdd : ∀ n d : ℕ, h (n + d) ≤ h n := by
    intro n d
    induction d with
    | zero => simp
    | succ d ih => exact le_trans (hmono (n + d)) ih
  have hmono' : ∀ n m : ℕ, n ≤ m → h m ≤ h n := by
    intro n m hnm
    have hEq : m = n + (m - n) := by omega
    rw [hEq]
    exact hmonoAdd n (m - n)
  set D : Submodule ℝ H := h 0 ⊓ N with hD
  haveI hDfin : FiniteDimensional ℝ ↥D := hNfin 0
  obtain ⟨w, p, q, hON, hmem, hDorth, hpq, hsep, hp0, hq0, hlate⟩ :=
    exists_stage_family b h hinf hDfin
  set R : Submodule ℝ H := closedSpan w with hR
  set A : Set ℕ := Set.range p with hA
  have hRcl : IsClosed ((R : Submodule ℝ H) : Set H) := isClosed_closedSpan w
  -- the key coordinate computation
  have hkey : ∀ x ∈ R, x ≠ 0 → ∃ L : ℕ, b.repr x (p L) ≠ 0 ∧ b.repr x (q L) ≠ 0 := by
    intro x hx hx0
    have hex : ∃ n, ⟪w n, x⟫ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx0 (eq_zero_of_mem_closedSpan_of_inner_eq_zero hx hcon)
    set L := Nat.find hex with hL
    have hLne : ⟪w L, x⟫ ≠ 0 := Nat.find_spec hex
    have hLmin : ∀ n, n < L → ⟪w n, x⟫ = 0 := by
      intro n hn
      by_contra hne
      have hle : L ≤ n := by rw [hL]; exact Nat.find_le hne
      omega
    refine ⟨L, ?_, ?_⟩
    · have hval := inner_eq_of_least hON hx (b (p L)) L hLmin
        (fun n hn => by
          rw [← HilbertBasis.repr_apply_apply]
          exact (hlate L n hn).1)
      rw [HilbertBasis.repr_apply_apply, hval, ← HilbertBasis.repr_apply_apply]
      exact mul_ne_zero hLne (hp0 L)
    · have hval := inner_eq_of_least hON hx (b (q L)) L hLmin
        (fun n hn => by
          rw [← HilbertBasis.repr_apply_apply]
          exact (hlate L n hn).2)
      rw [HilbertBasis.repr_apply_apply, hval, ← HilbertBasis.repr_apply_apply]
      exact mul_ne_zero hLne (hq0 L)
  -- `q L` is never a member of `A`
  have hqA : ∀ L : ℕ, q L ∉ A := by
    intro L hmemA
    obtain ⟨n, hn⟩ := hmemA
    have h1 := hpq n
    have h2 := hpq L
    rcases lt_trichotomy n L with hlt | heq | hgt
    · have h3 : q n < p L := hsep n L hlt
      omega
    · subst heq
      omega
    · have h3 : q L < p n := hsep L n hgt
      omega
  refine ⟨R, hRcl, ?_, ?_, ?_⟩
  · -- non-intimacy
    intro hint
    rcases hint A with hne | hne
    · refine hne (le_antisymm ?_ bot_le)
      intro x hx
      by_contra hx0
      obtain ⟨L, -, hqL⟩ := hkey x hx.1 (by simpa using hx0)
      have := (PlufWO9.mem_blockB_iff b A x).mp hx.2 (q L) (hqA L)
      exact hqL this
    · refine hne (le_antisymm ?_ bot_le)
      intro x hx
      by_contra hx0
      obtain ⟨L, hpL, -⟩ := hkey x hx.1 (by simpa using hx0)
      have hmemc : p L ∉ (Aᶜ : Set ℕ) := by simp [hA]
      have := (PlufWO9.mem_blockB_iff b Aᶜ x).mp hx.2 (p L) hmemc
      exact hpL this
  · -- `R ⊓ N = ⊥`
    have hRh0 : R ≤ h 0 := closedSpan_le (hcl 0) (fun n => hmono' 0 n (Nat.zero_le n) (hmem n))
    have hRD : R ≤ Dᗮ := closedSpan_le (Submodule.isClosed_orthogonal D) hDorth
    refine le_antisymm ?_ bot_le
    intro x hx
    have h1 : x ∈ D := ⟨hRh0 hx.1, hx.2⟩
    have h2 : x ∈ Dᗮ := hRD hx.1
    have : x ∈ D ⊓ Dᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot] at this
  · -- infinite dimension in every `h j`
    intro j
    refine not_finiteDimensional_of_orthonormal (v := fun n => w (j + n))
      (hON.comp _ (fun a c hac => by omega)) (fun n => ?_)
    exact ⟨mem_closedSpan w (j + n), hmono' j (j + n) (Nat.le_add_right j n) (hmem (j + n))⟩

end Stage

end PlufWO12
