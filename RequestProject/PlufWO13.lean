/-
  PlufWO13.lean — Work Order 13 for the pluf project (Feldman–Wilce).

  Scope: the ZFC lemmas of Paper I, Section 5 — everything before the
  blocking lemma (WO-14) and the CH recursion (WO-15):
    (A) the fixed operator T = diag(1, 1/16, 1, 1/16, …), its spectrum,
        and its essential spectrum;
    (B) ampleness: the definition, the radii lemma (Lemma 5.2), and
        infinite-dimensionality of ample subspaces;
    (C) upward inheritance (Lemma 5.3) and the finite-codimension lemma
        (Lemma 5.4);
    (D) the escape lemma (Lemma 5.5), in the approximate-eigenvector
        formulation that replaces the spectral subspace.

  THE CENTRAL SUBSTITUTION. Paper I §5 is written with the Borel
  functional calculus: the escape lemma produces the spectral subspace
  K^ε_λ(V) = 1_{[λ-ε,λ+ε]}(T_V) V. Mathlib has no Borel functional
  calculus, and the WO-7a census recommended against building one. The
  substitute, proved in WO-9, is the closed span of an orthonormal
  sequence of approximate eigenvectors with summable defects:

    PlufWO9.exists_orthonormal_approx_eigenvectors
    PlufWO9.approx_eigen_span_spec

  whose tolerance clause is homogeneous:
    ∀ x ∈ K, ‖T x - lam • x‖ ≤ (∑' n, ε n) * ‖x‖,
  with infinite-dimensionality delivered as ¬ FiniteDimensional.

  Part D is therefore contracted against that API, not against spectral
  projections. The escaping subspace is an `approxEigenSpan`; the clause
  "λ ∈ σ_ess(T_K)" becomes the homogeneous bound; and "K ∩ N has infinite
  codimension in K" is contracted directly. If the substitution forces a
  change in what the downstream arguments can assume, REPORT it — WO-14
  and WO-15 are written against whatever this commission fixes, and this
  is the interface decision of the commission.

  Base: the WO-10 artifact (181 theorems; CI runs #1–#10). WO-11 runs in
  parallel and is NOT a dependency: nothing here needs cardinal
  arithmetic or CH. All prior theorems must remain green; `PlufWO7a.lean`
  is the census record and is not to be edited.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  DELIVERY NOTE (WO-13).  Operator-free infrastructure (elementary
  identities for orthogonal projections, emptiness of the essential
  spectrum in finite dimensions, and the finite-codimension bookkeeping)
  is in `RequestProject/PlufWO13/Basic.lean`, namespace `PlufWO13.Aux`;
  everything that mentions `T` is here.
-/
import RequestProject.PlufWO13.Basic

open Set

namespace PlufWO13

abbrev H := PlufWO1.H

/-! ### Part A: the operator T -/

/-- A1. The fixed diagonal operator `T = diag(1, 1/16, 1, 1/16, …)`:
    coordinate `n` is scaled by `1` if `n` is even and `1/16` if `n` is
    odd. Contract the operator and its two basic bounds; the diagonal
    entries are `tEntry`. -/
noncomputable def tEntry (n : ℕ) : ℝ := if Even n then 1 else 1/16

/-- The closed subspace of vectors supported on the even coordinates. -/
noncomputable def evenBlock : Submodule ℝ H := PlufWO1.block {n : ℕ | Even n}

theorem isClosed_evenBlock : IsClosed (evenBlock : Set H) :=
  PlufWO1.isClosed_block _

instance instCompleteSpaceEvenBlock : CompleteSpace ↥evenBlock :=
  isClosed_evenBlock.completeSpace_coe

/-- `T = (1/16) • id + (15/16) • P`, with `P` the orthogonal projection onto
    the even block: the diagonal operator with entries `tEntry`. -/
noncomputable def T : H →L[ℝ] H :=
  (1/16 : ℝ) • ContinuousLinearMap.id ℝ H + (15/16 : ℝ) • evenBlock.starProjection

theorem T_apply (x : H) :
    T x = (1/16 : ℝ) • x + (15/16 : ℝ) • evenBlock.starProjection x := rfl

theorem evec_mem_evenBlock {n : ℕ} (hn : Even n) : PlufWO1.evec n ∈ evenBlock := by
  rw [evenBlock, PlufWO1.mem_block_iff]
  intro m hm
  rw [PlufWO1.evec_apply]
  have hmn : m ≠ n := by rintro rfl; exact hm hn
  simp [hmn]

theorem evec_mem_evenBlock_orthogonal {n : ℕ} (hn : ¬ Even n) :
    PlufWO1.evec n ∈ evenBlockᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hun : (u : ∀ _ : ℕ, ℝ) n = 0 := by
    rw [evenBlock, PlufWO1.mem_block_iff] at hu
    exact hu n hn
  have : inner (𝕜 := ℝ) u (PlufWO1.evec n) = (u : ∀ _ : ℕ, ℝ) n := by
    rw [PlufWO1.evec, lp.inner_single_right]
    simp
  rw [this, hun]

@[simp] theorem T_evec (n : ℕ) : T (PlufWO1.evec n) = tEntry n • PlufWO1.evec n := by
  rcases Nat.even_or_odd n with he | ho
  · rw [T_apply, (Submodule.starProjection_eq_self_iff).mpr (evec_mem_evenBlock he),
      tEntry, if_pos he]
    module
  · have hne : ¬ Even n := Nat.not_even_iff_odd.mpr ho
    rw [T_apply, (evenBlock.starProjection_apply_eq_zero_iff).mpr
      (evec_mem_evenBlock_orthogonal hne), tEntry, if_neg hne]
    module

theorem T_inner_symm (x y : H) : inner (𝕜 := ℝ) (T x) y = inner (𝕜 := ℝ) x (T y) := by
  rw [T_apply, T_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
    evenBlock.inner_starProjection_left_eq_right x y]

theorem T_selfAdjoint : IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  exact T_inner_symm x y

/-! #### The two defect identities -/

theorem inner_T_self (y : H) :
    inner (𝕜 := ℝ) (T y) y
      = (1/16 : ℝ) * ‖y‖ ^ 2 + (15/16 : ℝ) * ‖evenBlock.starProjection y‖ ^ 2 := by
  rw [T_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, Aux.inner_starProjection_self]

theorem T_sub_one_smul (y : H) :
    T y - y = -(15/16 : ℝ) • (y - evenBlock.starProjection y) := by
  rw [T_apply]; module

theorem T_sub_sixteenth_smul (y : H) :
    T y - (1/16 : ℝ) • y = (15/16 : ℝ) • evenBlock.starProjection y := by
  rw [T_apply]; module

theorem norm_T_sub_one_sq (y : H) :
    ‖T y - y‖ ^ 2 = (15/16 : ℝ) * (‖y‖ ^ 2 - inner (𝕜 := ℝ) (T y) y) := by
  rw [T_sub_one_smul, norm_smul, inner_T_self]
  have h := Aux.norm_sub_starProjection_sq evenBlock y
  simp only [norm_neg, Real.norm_eq_abs]
  rw [mul_pow, h]
  norm_num
  ring

theorem norm_T_sub_sixteenth_sq (y : H) :
    ‖T y - (1/16 : ℝ) • y‖ ^ 2
      = (15/16 : ℝ) * (inner (𝕜 := ℝ) (T y) y - (1/16 : ℝ) * ‖y‖ ^ 2) := by
  rw [T_sub_sixteenth_smul, norm_smul, inner_T_self]
  simp only [Real.norm_eq_abs]
  rw [mul_pow]
  norm_num
  ring

/-- A2. The two-sided bound `1/16 ≤ ⟪T x, x⟫ ≤ ‖x‖²`, which is what the
    ampleness arguments use (rather than any spectral statement). State
    in whichever of the quadratic-form or operator-order forms Mathlib
    supports cleanly; report the choice. -/
theorem T_bounds (x : H) :
    (1/16 : ℝ) * ‖x‖^2 ≤ inner (𝕜 := ℝ) (T x) x ∧
      inner (𝕜 := ℝ) (T x) x ≤ ‖x‖^2 := by
  constructor
  · nlinarith [norm_T_sub_sixteenth_sq x, sq_nonneg ‖T x - (1/16 : ℝ) • x‖]
  · nlinarith [norm_T_sub_one_sq x, sq_nonneg ‖T x - x‖]

/-- The unified defect estimate at the two relevant points of the spectrum:
    the squared defect is controlled by the deviation of the quadratic form.
    This replaces the paper's use of `1/16 ≤ T ≤ 1` in Lemmas 5.3 and 5.5. -/
theorem norm_T_sub_lam_sq_le {lam : ℝ} (hlam : lam = 1 ∨ lam = 1/16) (y : H) :
    ‖T y - lam • y‖ ^ 2 ≤ |inner (𝕜 := ℝ) (T y) y - lam * ‖y‖ ^ 2| := by
  rcases hlam with rfl | rfl
  · have h := norm_T_sub_one_sq y
    have hb := (T_bounds y).2
    rw [one_smul] at *
    rw [h, abs_of_nonpos (by linarith)]
    linarith
  · have h := norm_T_sub_sixteenth_sq y
    have hb := (T_bounds y).1
    rw [h, abs_of_nonneg (by linarith)]
    linarith

/-! #### A3: the two essential-spectrum memberships -/

theorem orthonormal_evec : Orthonormal ℝ PlufWO1.evec := by
  rw [orthonormal_iff_ite]
  intro i j
  have : inner (𝕜 := ℝ) (PlufWO1.evec i) (PlufWO1.evec j)
      = (PlufWO1.evec j : ∀ _ : ℕ, ℝ) i := by
    rw [PlufWO1.evec, lp.inner_single_left]
    simp
  rw [this, PlufWO1.evec_apply]

/-- An exact eigensequence of `T` at `lam` built from basis vectors along an
    injective index sequence exhibits `lam` in the essential spectrum. -/
theorem mem_essSpec_of_evec_seq {lam : ℝ} (f : ℕ → ℕ) (hf : Function.Injective f)
    (hval : ∀ n, tEntry (f n) = lam) : lam ∈ PlufWO9.essSpec T := by
  refine ⟨fun n => PlufWO1.evec (f n), fun n => ?_, ?_, ?_⟩
  · simpa using (orthonormal_evec.1 (f n))
  · exact fun y => PlufWO9.tendsto_inner_of_orthonormal (orthonormal_evec.comp f hf) y
  · have : ∀ n, ‖T (PlufWO1.evec (f n)) - lam • PlufWO1.evec (f n)‖ = 0 := by
      intro n
      rw [T_evec, hval n, sub_self, norm_zero]
    simp only [this]
    exact tendsto_const_nhds

/-- A3. Both `1` and `1/16` lie in the essential spectrum of `T`: the even
    (resp. odd) basis vectors form an orthonormal, hence weakly null,
    exact eigensequence. (Uses `PlufWO9.essSpec`.) -/
theorem one_mem_essSpec : (1 : ℝ) ∈ PlufWO9.essSpec T := by
  refine mem_essSpec_of_evec_seq (fun n => 2 * n) (fun a b h => by dsimp only at h; omega) ?_
  intro n
  rw [tEntry, if_pos ⟨n, by ring⟩]

theorem sixteenth_mem_essSpec : (1/16 : ℝ) ∈ PlufWO9.essSpec T := by
  refine mem_essSpec_of_evec_seq (fun n => 2 * n + 1)
    (fun a b h => by dsimp only at h; omega) ?_
  intro n
  rw [tEntry, if_neg (by simp [parity_simps])]

/-! ### Part B: ampleness -/

open Classical in
/-- The compression of `T` to a closed subspace. Contract whichever
    rendering WO-9's `essSpec` API consumes — WO-9 supplied an operator
    form `essSpec T ⊆ essSpec (compress T V)`; reuse its `compress` if it
    exists rather than defining a second one, and REPORT.

    DELIVERED: WO-9's `PlufWO9.compress` is reused verbatim. Its
    completeness instance `[CompleteSpace ↥V]` is not available for a
    general `V` (the contract's `compress` takes no closedness
    hypothesis), so the definition branches on it; `compress_eq` says the
    two agree whenever `V` is complete — in particular whenever `V` is
    closed, which every consumer in §5 assumes. -/
noncomputable def compress (V : Submodule ℝ H) : ↥V →L[ℝ] ↥V :=
  if h : CompleteSpace ↥V then (haveI := h; PlufWO9.compress T V) else 0

theorem compress_eq (V : Submodule ℝ H) [inst : CompleteSpace ↥V] :
    compress V = PlufWO9.compress T V := by
  classical
  simp only [compress, dif_pos inst]

theorem compress_coe (V : Submodule ℝ H) [CompleteSpace ↥V] (x : ↥V) :
    ((compress V x : ↥V) : H) = V.starProjection (T (x : H)) := by
  rw [compress_eq, Submodule.starProjection_apply]
  rfl

theorem norm_compress_sub (V : Submodule ℝ H) [CompleteSpace ↥V] (lam : ℝ) (x : ↥V) :
    ‖compress V x - lam • x‖ = ‖V.starProjection (T (x : H)) - lam • (x : H)‖ := by
  have h : ((compress V x - lam • x : ↥V) : H)
      = V.starProjection (T (x : H)) - lam • (x : H) := by
    push_cast [compress_coe]
    rfl
  rw [← h]
  rfl

/-- A nonzero closed subspace is *ample* if both `1` and `1/16` lie in the
    essential spectrum of the compression of `T` to it. -/
def Ample (M : Submodule ℝ H) : Prop :=
  M ≠ ⊥ ∧ IsClosed (M : Set H) ∧
    (1 : ℝ) ∈ PlufWO9.essSpec (compress M) ∧ (1/16 : ℝ) ∈ PlufWO9.essSpec (compress M)

/-! #### The sequence interface for `essSpec (compress V)` -/

/-- The compression's defect pairs with a vector of `V` exactly as the
    ambient quadratic form does. -/
theorem inner_proj_sub (V : Submodule ℝ H) [CompleteSpace ↥V] (lam : ℝ) {y : H} (hy : y ∈ V) :
    inner (𝕜 := ℝ) (V.starProjection (T y) - lam • y) y
      = inner (𝕜 := ℝ) (T y) y - lam * ‖y‖ ^ 2 := by
  rw [inner_sub_left, real_inner_smul_left, V.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).mpr hy, real_inner_self_eq_norm_sq]

/-- Insertion, in the form with the compression's own defect. -/
theorem mem_essSpec_compress_of_seq_proj (V : Submodule ℝ H) [CompleteSpace ↥V] {lam : ℝ}
    (y : ℕ → H) (hmem : ∀ n, y n ∈ V) (hnorm : ∀ n, ‖y n‖ = 1)
    (hweak : ∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0))
    (hdef : Filter.Tendsto (fun n => ‖V.starProjection (T (y n)) - lam • y n‖)
      Filter.atTop (nhds 0)) :
    lam ∈ PlufWO9.essSpec (compress V) := by
  refine ⟨fun n => ⟨y n, hmem n⟩, fun n => hnorm n, ?_, ?_⟩
  · intro z
    have h := hweak (z : H)
    simpa [Submodule.coe_inner] using h
  · simpa only [norm_compress_sub] using hdef

/-- Insertion, in the form with the ambient defect. -/
theorem mem_essSpec_compress_of_seq (V : Submodule ℝ H) [CompleteSpace ↥V] {lam : ℝ}
    (y : ℕ → H) (hmem : ∀ n, y n ∈ V) (hnorm : ∀ n, ‖y n‖ = 1)
    (hweak : ∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0))
    (hdef : Filter.Tendsto (fun n => ‖T (y n) - lam • y n‖) Filter.atTop (nhds 0)) :
    lam ∈ PlufWO9.essSpec (compress V) := by
  refine mem_essSpec_compress_of_seq_proj V y hmem hnorm hweak ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hdef
  have hproj : V.starProjection (T (y n) - lam • y n)
      = V.starProjection (T (y n)) - lam • y n := by
    rw [map_sub, map_smul, (Submodule.starProjection_eq_self_iff).mpr (hmem n)]
  rw [← hproj]
  exact Aux.norm_starProjection_le V _

/-- Extraction, in the form with the compression's own defect. -/
theorem exists_seq_of_mem_essSpec_compress_proj (V : Submodule ℝ H) [CompleteSpace ↥V]
    {lam : ℝ} (h : lam ∈ PlufWO9.essSpec (compress V)) :
    ∃ y : ℕ → H, (∀ n, y n ∈ V) ∧ (∀ n, ‖y n‖ = 1) ∧
      (∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0)) ∧
      Filter.Tendsto (fun n => ‖V.starProjection (T (y n)) - lam • y n‖)
        Filter.atTop (nhds 0) := by
  obtain ⟨x, hx1, hxw, hxd⟩ := h
  refine ⟨fun n => ((x n : ↥V) : H), fun n => (x n).2, fun n => hx1 n, ?_, ?_⟩
  · intro z
    have h := hxw (V.orthogonalProjection z)
    have hz : ∀ n, inner (𝕜 := ℝ) ((x n : ↥V) : H) z
        = inner (𝕜 := ℝ) (x n) (V.orthogonalProjection z) := by
      intro n
      have h1 : inner (𝕜 := ℝ) ((x n : ↥V) : H) z
          = inner (𝕜 := ℝ) (V.starProjection ((x n : ↥V) : H)) z := by
        rw [(Submodule.starProjection_eq_self_iff).mpr (x n).2]
      rw [h1, V.inner_starProjection_left_eq_right, Submodule.starProjection_apply]
      rfl
    simpa only [hz] using h
  · simpa only [norm_compress_sub] using hxd

/-- Extraction, in the quadratic-form shape used by the inheritance
    arguments: the Rayleigh quotients converge to `lam`. -/
theorem exists_seq_of_mem_essSpec_compress (V : Submodule ℝ H) [CompleteSpace ↥V]
    {lam : ℝ} (h : lam ∈ PlufWO9.essSpec (compress V)) :
    ∃ y : ℕ → H, (∀ n, y n ∈ V) ∧ (∀ n, ‖y n‖ = 1) ∧
      (∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0)) ∧
      Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) (y n)) Filter.atTop (nhds lam) := by
  obtain ⟨y, hmem, hnorm, hweak, hdef⟩ := exists_seq_of_mem_essSpec_compress_proj V h
  refine ⟨y, hmem, hnorm, hweak, ?_⟩
  have key : ∀ n, |inner (𝕜 := ℝ) (T (y n)) (y n) - lam|
      ≤ ‖V.starProjection (T (y n)) - lam • y n‖ := by
    intro n
    have hy : inner (𝕜 := ℝ) (V.starProjection (T (y n)) - lam • y n) (y n)
        = inner (𝕜 := ℝ) (T (y n)) (y n) - lam := by
      rw [inner_sub_left, real_inner_smul_left, V.inner_starProjection_left_eq_right,
        (Submodule.starProjection_eq_self_iff).mpr (hmem n), real_inner_self_eq_norm_sq,
        hnorm n]
      ring
    have hcs := abs_real_inner_le_norm (V.starProjection (T (y n)) - lam • y n) (y n)
    rw [hy, hnorm n, mul_one] at hcs
    exact hcs
  have h0 : Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) (y n) - lam)
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using key n) hdef
  simpa using h0.add (tendsto_const_nhds (x := lam))

/-- The compression to the zero subspace has empty essential spectrum:
    there are no unit vectors at all. -/
theorem notMem_essSpec_compress_bot (lam : ℝ) :
    lam ∉ PlufWO9.essSpec (compress (⊥ : Submodule ℝ H)) := by
  rintro ⟨x, hx1, -, -⟩
  have hx0 : ((x 0 : ↥(⊥ : Submodule ℝ H)) : H) = 0 := (Submodule.mem_bot ℝ).mp (x 0).2
  have hn := hx1 0
  rw [show ‖x 0‖ = ‖((x 0 : ↥(⊥ : Submodule ℝ H)) : H)‖ from rfl, hx0, norm_zero] at hn
  norm_num at hn

theorem not_ample_bot : ¬ Ample (⊥ : Submodule ℝ H) := fun h => h.1 rfl

/-- Missing one of the two points of the essential spectrum already
    contradicts ampleness; this is why D1's contracted hypothesis
    `¬ Ample (V ⊓ N)` is redundant. -/
theorem not_ample_of_notMem_essSpec {M : Submodule ℝ H} {lam : ℝ}
    (hlam : lam = 1 ∨ lam = 1/16) (h : lam ∉ PlufWO9.essSpec (compress M)) :
    ¬ Ample M := by
  rintro ⟨-, -, h1, h16⟩
  rcases hlam with rfl | rfl
  · exact h h1
  · exact h h16

/-- B1 (Lemma 5.2, the consequence actually used). Ample subspaces are
    infinite-dimensional.

    The paper states Lemma 5.2 in terms of the ellipsoid radii
    `m(E ∩ M) = 1`, `M(E ∩ M) = 4`, `r(E ∩ M) = 4`, deducing
    infinite-dimensionality. WO-6 verified the radii lemma
    (`PlufWO6` Part D, both the Rayleigh and ellipsoid forms), so both
    routes are available. Contract the infinite-dimensionality clause,
    which is what §5 consumes; if the radii clauses are cheap on top of
    the WO-6 API, prove them too as B1' and report. -/
theorem infinite_dimensional_of_ample {M : Submodule ℝ H} (hM : Ample M) :
    ¬ FiniteDimensional ℝ ↥M := by
  intro hfd
  haveI : CompleteSpace ↥M := hM.2.1.completeSpace_coe
  haveI : FiniteDimensional ℝ ↥M := hfd
  have hempty := Aux.essSpec_eq_empty_of_finiteDimensional (compress M)
  have h1 := hM.2.2.1
  rw [hempty] at h1
  exact h1

/-! #### B1' : the radii clauses of Lemma 5.2, on the WO-6 ellipsoid API -/

/-- `T` is coercive with constant `1/16`, which is what the WO-6 radii
    lemmas require. -/
theorem T_coercive (x : H) : (1/16 : ℝ) * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) (T x) x :=
  (T_bounds x).1

/-- On an ample subspace the upper Rayleigh value is `1`. -/
theorem upper_eq_one_of_ample {M : Submodule ℝ H} (hM : Ample M) :
    PlufWO6.upper T M = 1 := by
  obtain ⟨hne, hcl, h1, -⟩ := hM
  haveI : CompleteSpace ↥M := hcl.completeSpace_coe
  obtain ⟨y, hmem, hnorm, -, hray⟩ := exists_seq_of_mem_essSpec_compress M h1
  rw [PlufWO6.upper_eq]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (PlufWO6.rayleighSet_nonempty hne)
    ?_ ?_
  · rintro q ⟨x, ⟨-, hx1⟩, rfl⟩
    have := (T_bounds x).2
    rwa [hx1, one_pow] at this
  · intro w hw
    obtain ⟨n, hn⟩ := (hray.eventually (eventually_gt_nhds hw)).exists
    exact ⟨inner (𝕜 := ℝ) (T (y n)) (y n), ⟨y n, ⟨hmem n, hnorm n⟩, rfl⟩, hn⟩

/-- On an ample subspace the lower Rayleigh value is `1/16`. -/
theorem lower_eq_sixteenth_of_ample {M : Submodule ℝ H} (hM : Ample M) :
    PlufWO6.lower T M = 1/16 := by
  obtain ⟨hne, hcl, -, h16⟩ := hM
  haveI : CompleteSpace ↥M := hcl.completeSpace_coe
  obtain ⟨y, hmem, hnorm, -, hray⟩ := exists_seq_of_mem_essSpec_compress M h16
  rw [PlufWO6.lower_eq]
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt (PlufWO6.rayleighSet_nonempty hne)
    ?_ ?_
  · rintro q ⟨x, ⟨-, hx1⟩, rfl⟩
    have := (T_bounds x).1
    rwa [hx1, one_pow, mul_one] at this
  · intro w hw
    obtain ⟨n, hn⟩ := (hray.eventually (eventually_lt_nhds hw)).exists
    exact ⟨inner (𝕜 := ℝ) (T (y n)) (y n), ⟨y n, ⟨hmem n, hnorm n⟩, rfl⟩, hn⟩

/-- B1' (Lemma 5.2 as printed, minor radius): `m(E ∩ M) = 1`. -/
theorem minorRadius_of_ample {M : Submodule ℝ H} (hM : Ample M) :
    PlufWO6.minorRadius T M = 1 := by
  rw [PlufWO6.minorRadius_eq (by norm_num : (0:ℝ) < 1/16) T_coercive hM.1,
    upper_eq_one_of_ample hM]
  simp

/-- B1' (Lemma 5.2 as printed, major radius): `M(E ∩ M) = 4`. -/
theorem majorRadius_of_ample {M : Submodule ℝ H} (hM : Ample M) :
    PlufWO6.majorRadius T M = 4 := by
  rw [PlufWO6.majorRadius_eq (by norm_num : (0:ℝ) < 1/16) T_coercive hM.1,
    lower_eq_sixteenth_of_ample hM]
  rw [show (1/16 : ℝ) = (1/4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- B1' (Lemma 5.2 as printed, eccentricity): `r(E ∩ M) = 4`. -/
theorem eccentricity_of_ample {M : Submodule ℝ H} (hM : Ample M) :
    PlufWO6.eccentricity T M = 4 := by
  rw [PlufWO6.eccentricity_eq (by norm_num : (0:ℝ) < 1/16) T_coercive hM.1,
    upper_eq_one_of_ample hM, lower_eq_sixteenth_of_ample hM]
  rw [show (1 : ℝ) / (1/16) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! #### Ampleness is not vacuous: the whole space is ample -/

/-- The ambient space itself is ample; in particular the hypotheses of the
    escape lemma are satisfiable. -/
theorem ample_top : Ample (⊤ : Submodule ℝ H) := by
  have htopcl : IsClosed ((⊤ : Submodule ℝ H) : Set H) := by simp
  haveI : CompleteSpace ↥(⊤ : Submodule ℝ H) := htopcl.completeSpace_coe
  have key : ∀ (lam : ℝ) (f : ℕ → ℕ), Function.Injective f → (∀ n, tEntry (f n) = lam) →
      lam ∈ PlufWO9.essSpec (compress (⊤ : Submodule ℝ H)) := by
    intro lam f hf hval
    refine mem_essSpec_compress_of_seq ⊤ (fun n => PlufWO1.evec (f n))
      (fun n => Submodule.mem_top) (fun n => by simpa using orthonormal_evec.1 (f n))
      (fun z => PlufWO9.tendsto_inner_of_orthonormal (orthonormal_evec.comp f hf) z) ?_
    have hzero : ∀ n, ‖T (PlufWO1.evec (f n)) - lam • PlufWO1.evec (f n)‖ = 0 := by
      intro n
      rw [T_evec, hval n, sub_self, norm_zero]
    simp only [hzero]
    exact tendsto_const_nhds
  refine ⟨?_, htopcl, ?_, ?_⟩
  · intro hbot
    have h0 : PlufWO1.evec 0 ∈ (⊥ : Submodule ℝ H) := hbot ▸ Submodule.mem_top
    exact PlufWO1.evec_ne_zero 0 ((Submodule.mem_bot ℝ).mp h0)
  · exact key 1 (fun n => 2 * n) (fun a b h => by dsimp only at h; omega)
      (fun n => by rw [tEntry, if_pos ⟨n, by ring⟩])
  · exact key (1/16) (fun n => 2 * n + 1) (fun a b h => by dsimp only at h; omega)
      (fun n => by rw [tEntry, if_neg (by simp [parity_simps])])

/-! ### Part C: inheritance -/

/-- C1 (Lemma 5.3, upward inheritance). For `λ ∈ {1, 1/16}` and closed
    `W ≤ V`: if `λ ∈ σ_ess(T_W)` then `λ ∈ σ_ess(T_V)`. Hence ampleness
    passes upward and its failure passes downward.

    Proof (paper): for `λ = 1`, a weakly null orthonormal `(x k)` in `W`
    with `⟪T x k, x k⟫ → 1` satisfies
    `‖T x k − x k‖² ≤ 2 − 2⟪T x k, x k⟫ → 0` by `0 ≤ T ≤ 1`, so
    `‖T_V x k − x k‖ = ‖P_V (T x k − x k)‖ → 0`. The case `λ = 1/16`
    follows by applying the argument to a rescaled `1 − T`; if that
    rescaling is awkward in Lean, prove the two cases directly — the
    estimate is symmetric — and REPORT. -/
theorem essSpec_compress_mono {W V : Submodule ℝ H}
    (hW : IsClosed (W : Set H)) (hV : IsClosed (V : Set H)) (hWV : W ≤ V)
    {lam : ℝ} (hlam : lam = 1 ∨ lam = 1/16)
    (h : lam ∈ PlufWO9.essSpec (compress W)) :
    lam ∈ PlufWO9.essSpec (compress V) := by
  haveI : CompleteSpace ↥W := hW.completeSpace_coe
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  obtain ⟨y, hmem, hnorm, hweak, hray⟩ := exists_seq_of_mem_essSpec_compress W h
  refine mem_essSpec_compress_of_seq V y (fun n => hWV (hmem n)) hnorm hweak ?_
  -- the defect tends to `0` by the unified defect estimate
  have hsq : Filter.Tendsto (fun n => ‖T (y n) - lam • y n‖ ^ 2) Filter.atTop (nhds 0) := by
    have hbound : ∀ n, ‖T (y n) - lam • y n‖ ^ 2
        ≤ |inner (𝕜 := ℝ) (T (y n)) (y n) - lam| := by
      intro n
      have := norm_T_sub_lam_sq_le hlam (y n)
      rwa [hnorm n, one_pow, mul_one] at this
    refine squeeze_zero (fun n => sq_nonneg _) hbound ?_
    have h0 : Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) (y n) - lam)
        Filter.atTop (nhds 0) := by
      simpa using hray.sub (tendsto_const_nhds (x := lam))
    simpa [Real.norm_eq_abs] using h0.norm
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem ample_of_ample_le {W V : Submodule ℝ H} (hW : Ample W)
    (hV : IsClosed (V : Set H)) (hWV : W ≤ V) : Ample V := by
  obtain ⟨hne, hWcl, h1, h2⟩ := hW
  refine ⟨?_, hV, essSpec_compress_mono hWcl hV hWV (Or.inl rfl) h1,
    essSpec_compress_mono hWcl hV hWV (Or.inr rfl) h2⟩
  intro hVbot
  exact hne (le_bot_iff.mp (hVbot ▸ hWV))

/-- C2 (Lemma 5.4, finite codimension). If `W ≤ V` has finite codimension
    in `V` then the compressions have the same essential spectrum; in
    particular ampleness is inherited by finite-codimension subspaces.

    Paper's proof: `P_V − P_W` has finite rank, so the compressions differ
    by a finite-rank operator. WO-9's B2
    (`essSpec_le_of_finCodim`) supplies one inclusion with minimal
    hypotheses; the other should follow from C1. Report which parts came
    from WO-9 and which are new. -/
theorem essSpec_compress_eq_of_finCodim {W V : Submodule ℝ H}
    (hW : IsClosed (W : Set H)) (hV : IsClosed (V : Set H)) (hWV : W ≤ V)
    (hfc : Module.Finite ℝ (↥V ⧸ (W.comap V.subtype))) :
    PlufWO9.essSpec (compress W) = PlufWO9.essSpec (compress V) := by
  haveI : CompleteSpace ↥W := hW.completeSpace_coe
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  have hfinF : Module.Finite ℝ ↥(V ⊓ Wᗮ) := Aux.finite_inf_orthogonal hW hV hWV hfc
  apply Set.eq_of_subset_of_subset
  · -- upward: the compressions differ by a finite-rank piece
    intro lam hlam
    obtain ⟨y, hmem, hnorm, hweak, hdef⟩ := exists_seq_of_mem_essSpec_compress_proj W hlam
    refine mem_essSpec_compress_of_seq_proj V y (fun n => hWV (hmem n)) hnorm hweak ?_
    have hTweak : ∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) z)
        Filter.atTop (nhds 0) := by
      intro z
      have := hweak (T z)
      simpa only [T_inner_symm] using this
    set d : ℕ → H := fun n => V.starProjection (T (y n)) - W.starProjection (T (y n)) with hd
    have hdmem : ∀ n, d n ∈ V ⊓ Wᗮ := fun n =>
      Aux.sub_starProjection_mem_inf_orthogonal hWV (T (y n))
    have hdweak : ∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (d n) z)
        Filter.atTop (nhds 0) := by
      intro z
      have h1 := hTweak (V.starProjection z)
      have h2 := hTweak (W.starProjection z)
      have hz : ∀ n, inner (𝕜 := ℝ) (d n) z
          = inner (𝕜 := ℝ) (T (y n)) (V.starProjection z)
            - inner (𝕜 := ℝ) (T (y n)) (W.starProjection z) := by
        intro n
        rw [hd]
        simp only [inner_sub_left]
        rw [V.inner_starProjection_left_eq_right, W.inner_starProjection_left_eq_right]
      simpa only [hz, sub_zero] using h1.sub h2
    haveI : FiniteDimensional ℝ ↥(V ⊓ Wᗮ) := hfinF
    haveI : CompleteSpace ↥(V ⊓ Wᗮ) := FiniteDimensional.complete ℝ ↥(V ⊓ Wᗮ)
    have hdnorm : Filter.Tendsto (fun n => ‖d n‖) Filter.atTop (nhds 0) := by
      have h := PlufWO9.tendsto_norm_proj_finiteDimensional_of_weaklyNull
        (V ⊓ Wᗮ) hfinF d hdweak
      have hfix : ∀ n, (V ⊓ Wᗮ).starProjection (d n) = d n := fun n =>
        (Submodule.starProjection_eq_self_iff).mpr (hdmem n)
      simpa only [hfix] using h
    have hsplit : ∀ n, V.starProjection (T (y n)) - lam • y n
        = (W.starProjection (T (y n)) - lam • y n) + d n := by
      intro n; simp only [hd]; abel
    have hsum0 : Filter.Tendsto
        (fun n => ‖W.starProjection (T (y n)) - lam • y n‖ + ‖d n‖) Filter.atTop (nhds 0) := by
      have h := hdef.add hdnorm
      rwa [add_zero] at h
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum0
    rw [hsplit n]
    exact norm_add_le _ _
  · -- downward: WO-9's B2 inside `↥V`
    intro lam hlam
    have hfin' : Module.Finite ℝ ↥((W.comap V.subtype)ᗮ) :=
      Aux.finite_orthogonal_comap hW hV hfc
    have hcl : IsClosed ((W.comap V.subtype : Submodule ℝ ↥V) : Set ↥V) := by
      have hpre : ((W.comap V.subtype : Submodule ℝ ↥V) : Set ↥V) = V.subtype ⁻¹' (W : Set H) :=
        rfl
      rw [hpre]
      exact hW.preimage continuous_subtype_val
    obtain ⟨u, hu, huW, hut⟩ :=
      PlufWO9.essSpec_le_of_finCodim (compress V) (W.comap V.subtype) hcl hfin' lam hlam
    set y : ℕ → H := fun n => ((u n : ↥V) : H) with hy
    have hmemW : ∀ n, y n ∈ W := fun n => huW n
    have hnorm : ∀ n, ‖y n‖ = 1 := fun n => by simpa using hu.1 n
    have horth : Orthonormal ℝ y := by
      rw [orthonormal_iff_ite]
      intro i j
      have := (orthonormal_iff_ite.mp hu) i j
      simpa [hy, Submodule.coe_inner] using this
    refine mem_essSpec_compress_of_seq_proj W y hmemW hnorm
      (fun z => PlufWO9.tendsto_inner_of_orthonormal horth z) ?_
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hut
    have hstep : W.starProjection (T (y n)) - lam • y n
        = W.starProjection (V.starProjection (T (y n)) - lam • y n) := by
      rw [map_sub, map_smul, Aux.starProjection_starProjection_of_le hWV,
        (Submodule.starProjection_eq_self_iff).mpr (hmemW n)]
    rw [hstep]
    refine le_trans (Aux.norm_starProjection_le W _) ?_
    rw [← norm_compress_sub V lam (u n)]

theorem ample_of_finCodim {W V : Submodule ℝ H} (hV : Ample V)
    (hW : IsClosed (W : Set H)) (hWV : W ≤ V)
    (hfc : Module.Finite ℝ (↥V ⧸ (W.comap V.subtype))) : Ample W := by
  obtain ⟨hne, hVcl, h1, h2⟩ := hV
  have heq := essSpec_compress_eq_of_finCodim hW hVcl hWV hfc
  have h1' : (1 : ℝ) ∈ PlufWO9.essSpec (compress W) := by rw [heq]; exact h1
  have h2' : (1/16 : ℝ) ∈ PlufWO9.essSpec (compress W) := by rw [heq]; exact h2
  refine ⟨?_, hW, h1', h2'⟩
  intro hbot
  subst hbot
  exact notMem_essSpec_compress_bot 1 h1'

/-! ### Part D: escape, in the approximate-eigenvector formulation -/

/-- D1 (Lemma 5.5, escape). Let `V` be ample, `N` closed, `V ⊓ N` not
    ample, and `λ ∈ {1, 1/16}` with `λ ∉ σ_ess(T_{V ⊓ N})`. Then for every
    tolerance `δ > 0` there is a closed subspace `K ≤ V` with:
      (i)   `K` infinite-dimensional;
      (ii)  the homogeneous bound `∀ x ∈ K, ‖T x − λ • x‖ ≤ δ * ‖x‖`;
      (iii) `K ⊓ N` of infinite codimension in `K`.

    This replaces the paper's spectral subspace `K^ε_λ(V)` by a WO-9
    `approxEigenSpan`: obtain a weakly null orthonormal approximate
    eigensequence in `V` at `λ` with summable defects of total mass `≤ δ`
    (WO-9 C1, whose decay rate is a caller parameter — take
    `ε n = δ / 2^(n+1)`), and let `K` be its closed span (WO-9 C2 gives
    (i) and (ii)). For (iii): if `K ⊓ N` had finite codimension in `K`,
    then C2 and C1 would put `λ ∈ σ_ess(T_{V ⊓ N})`, contrary to
    hypothesis.

    THE INTERFACE DECISION. WO-14's blocking-lemma recursion works inside
    `K` and needs, at each stage: an infinite-dimensional subspace, a
    quadratic-form estimate for unit vectors of `K`, and enough room to
    impose finitely many linear constraints while staying off `N`. Clause
    (ii) in homogeneous form yields the quadratic-form estimate
    `|⟪T x, x⟫ − λ‖x‖²| ≤ δ‖x‖²` by Cauchy–Schwarz; supply that corollary
    explicitly as D2, since it is what the recursion cites. If any further
    clause is needed to make WO-14 workable, ADD IT HERE and report —
    changing this interface later is expensive.

    REPORTED: the contracted hypothesis `hVN : ¬ Ample (V ⊓ N)` turns out
    not to be needed — `hnot` alone drives the argument, and `hVN` is in
    any case implied by it (a subspace whose compression misses `λ` from
    its essential spectrum is not ample). It is retained because the
    contract prescribes it. -/
theorem escape {V N : Submodule ℝ H} (hV : Ample V)
    (hN : IsClosed (N : Set H)) (hVN : ¬ Ample (V ⊓ N))
    {lam : ℝ} (hlam : lam = 1 ∨ lam = 1/16)
    (hnot : lam ∉ PlufWO9.essSpec (compress (V ⊓ N)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Submodule ℝ H, K ≤ V ∧ IsClosed (K : Set H) ∧
      ¬ FiniteDimensional ℝ ↥K ∧
      (∀ x ∈ K, ‖T x - lam • x‖ ≤ δ * ‖x‖) ∧
      ¬ Module.Finite ℝ (↥K ⧸ ((K ⊓ N).comap K.subtype)) := by
  classical
  obtain ⟨hVne, hVcl, hV1, hV16⟩ := hV
  haveI : CompleteSpace ↥V := hVcl.completeSpace_coe
  have hlamV : lam ∈ PlufWO9.essSpec (compress V) := by
    rcases hlam with rfl | rfl
    · exact hV1
    · exact hV16
  -- WO-9's engine inside `↥V`, with tolerances chosen so that the *ambient*
  -- defects are summable with total mass `δ`.
  have hepspos : ∀ n : ℕ, 0 < (δ / 4 / 2 ^ n) ^ 2 := fun n => by positivity
  obtain ⟨u, hu, hut⟩ :=
    PlufWO9.exists_orthonormal_approx_eigenvectors (compress V) lam hlamV
      (fun n => (δ / 4 / 2 ^ n) ^ 2) hepspos
  set y : ℕ → H := fun n => ((u n : ↥V) : H) with hy
  have hyV : ∀ n, y n ∈ V := fun n => (u n).2
  have hynorm : ∀ n, ‖y n‖ = 1 := fun n => hu.1 n
  have horth : Orthonormal ℝ y := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := (orthonormal_iff_ite.mp hu) i j
    simpa [hy, Submodule.coe_inner] using h
  -- the ambient defect is controlled by the compression's defect
  have hdef : ∀ n, ‖T (y n) - lam • y n‖ < δ / 2 / 2 ^ n := by
    intro n
    have h1 : ‖V.starProjection (T (y n)) - lam • y n‖ < (δ / 4 / 2 ^ n) ^ 2 := by
      have h := hut n
      rwa [norm_compress_sub] at h
    have h2 : ‖T (y n) - lam • y n‖ ^ 2
        ≤ ‖V.starProjection (T (y n)) - lam • y n‖ := by
      refine (norm_T_sub_lam_sq_le hlam (y n)).trans ?_
      rw [← inner_proj_sub V lam (hyV n)]
      have hcs := abs_real_inner_le_norm (V.starProjection (T (y n)) - lam • y n) (y n)
      rwa [hynorm n, mul_one] at hcs
    have h3 : ‖T (y n) - lam • y n‖ ^ 2 < (δ / 4 / 2 ^ n) ^ 2 := lt_of_le_of_lt h2 h1
    have h4 : (0 : ℝ) < δ / 4 / 2 ^ n := by positivity
    have h5 : ‖T (y n) - lam • y n‖ < δ / 4 / 2 ^ n := by
      nlinarith [norm_nonneg (T (y n) - lam • y n)]
    have h6 : δ / 4 / 2 ^ n < δ / 2 / 2 ^ n := by
      have hpow : (0 : ℝ) < 2 ^ n := by positivity
      rw [div_div, div_div]
      exact div_lt_div_of_pos_left hδ (by positivity) (by linarith)
    linarith
  have hsum : Summable (fun n : ℕ => δ / 2 / 2 ^ n) := summable_geometric_two' δ
  have htsum : (∑' n : ℕ, δ / 2 / 2 ^ n) = δ := tsum_geometric_two' δ
  obtain ⟨hmemK, hinfK, hboundK⟩ :=
    PlufWO9.approx_eigen_span_spec T lam y horth (fun n => δ / 2 / 2 ^ n) hdef hsum
  refine ⟨PlufWO9.approxEigenSpan y, ?_, PlufWO9.isClosed_approxEigenSpan y, hinfK, ?_, ?_⟩
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hVcl
    rintro z ⟨n, rfl⟩
    exact hyV n
  · intro x hx
    have h := hboundK x hx
    rwa [htsum] at h
  · -- (iii): infinite codimension of `K ⊓ N` in `K`
    intro hfinq
    set K : Submodule ℝ H := PlufWO9.approxEigenSpan y with hK
    have hKcl : IsClosed (K : Set H) := PlufWO9.isClosed_approxEigenSpan y
    haveI : CompleteSpace ↥K := hKcl.completeSpace_coe
    have hdef0 : Filter.Tendsto (fun n => ‖T (y n) - lam • y n‖) Filter.atTop (nhds 0) :=
      squeeze_zero (fun n => norm_nonneg _) (fun n => (hdef n).le) hsum.tendsto_atTop_zero
    have hlamK : lam ∈ PlufWO9.essSpec (compress K) :=
      mem_essSpec_compress_of_seq K y hmemK hynorm
        (fun z => PlufWO9.tendsto_inner_of_orthonormal horth z) hdef0
    have hKNcl : IsClosed ((K ⊓ N : Submodule ℝ H) : Set H) := by
      simpa using hKcl.inter hN
    have hVNcl : IsClosed ((V ⊓ N : Submodule ℝ H) : Set H) := by
      simpa using hVcl.inter hN
    have hKV : K ≤ V := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hVcl
      rintro z ⟨n, rfl⟩
      exact hyV n
    have heq := essSpec_compress_eq_of_finCodim hKNcl hKcl inf_le_left hfinq
    have hKN : lam ∈ PlufWO9.essSpec (compress (K ⊓ N)) := by rw [heq]; exact hlamK
    exact hnot (essSpec_compress_mono hKNcl hVNcl (inf_le_inf hKV le_rfl) hlam hKN)

/-- D2 (the quadratic-form corollary, for WO-14). On such a `K`,
    `|⟪T x, x⟫ − λ * ‖x‖²| ≤ δ * ‖x‖²`; in particular every unit vector of
    `K` has Rayleigh quotient within `δ` of `λ`. -/
theorem quadratic_estimate_of_bound {K : Submodule ℝ H} {lam δ : ℝ}
    (h : ∀ x ∈ K, ‖T x - lam • x‖ ≤ δ * ‖x‖) (x : H) (hx : x ∈ K) :
    |inner (𝕜 := ℝ) (T x) x - lam * ‖x‖^2| ≤ δ * ‖x‖^2 := by
  have hid : inner (𝕜 := ℝ) (T x - lam • x) x
      = inner (𝕜 := ℝ) (T x) x - lam * ‖x‖ ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hcs := abs_real_inner_le_norm (T x - lam • x) x
  rw [hid] at hcs
  refine hcs.trans ?_
  have := h x hx
  nlinarith [norm_nonneg x, norm_nonneg (T x - lam • x)]

/-- D3 (the corollary the paper draws). Under the hypotheses of D1, `N`
    has infinite codimension in `H`. -/
theorem infinite_codim_of_escape {V N : Submodule ℝ H} (hV : Ample V)
    (hN : IsClosed (N : Set H)) (hVN : ¬ Ample (V ⊓ N))
    {lam : ℝ} (hlam : lam = 1 ∨ lam = 1/16)
    (hnot : lam ∉ PlufWO9.essSpec (compress (V ⊓ N))) :
    ¬ Module.Finite ℝ (H ⧸ N) := by
  intro hfin
  obtain ⟨K, -, -, -, -, hKN⟩ := escape hV hN hVN hlam hnot (δ := 1) one_pos
  exact hKN (Aux.finite_quotient_of_finite_quotient hfin)

/-! ### Axiom audit -/

#print axioms T_evec
#print axioms T_selfAdjoint
#print axioms T_bounds
#print axioms one_mem_essSpec
#print axioms sixteenth_mem_essSpec
#print axioms infinite_dimensional_of_ample
#print axioms minorRadius_of_ample
#print axioms majorRadius_of_ample
#print axioms eccentricity_of_ample
#print axioms ample_top
#print axioms essSpec_compress_mono
#print axioms ample_of_ample_le
#print axioms essSpec_compress_eq_of_finCodim
#print axioms ample_of_finCodim
#print axioms escape
#print axioms quadratic_estimate_of_bound
#print axioms infinite_codim_of_escape

end PlufWO13
