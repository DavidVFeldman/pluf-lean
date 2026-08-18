/-
  PlufWO14.lean — Work Order 14 for the pluf project (Feldman–Wilce).

  Scope: Paper I, Lemma 5.6 — the BLOCKING LEMMA, the technical heart of
  the paper and the hardest single item of this campaign. Decomposed as:
    (S) the selection lemmas — the recursion's inner loop, consuming
        WO-13's interface exactly as its report prescribes;
    (P) the perturbation lemma — the odd-stage algebra that replaces the
        orthogonal decomposition non-distributivity forbids;
    (W) the recursion, the exact-diagonality lemma, and the assembly.

  QUARANTINE FALLBACK (per the standing WO-7a recommendation). If the
  recursion W1 cannot be closed, DO NOT abandon the commission: deliver
  S0–S3, P1, W2, and W3 in the conditional form
  `blocking_lemma_of_sequence` (W3 with W1's conclusion as a hypothesis),
  and report precisely where W1 failed. That converts the blocking lemma
  into a named quarantined hypothesis with its entire consumption
  machine-checked, which is the sanctioned fallback. W3 as contracted
  below is the unconditional composition and is the primary target.

  DESIGN NOTES BOUND INTO THE CONTRACTS (read before the census):

  1. THE RAYLEIGH-ONLY DISCIPLINE. The selection lemmas conclude with the
     Rayleigh estimate `|⟪T w, w⟫ − λ| ≤ ε`, NOT with a defect-norm bound
     `‖T w − λ w‖ ≤ ε` in H. This is deliberate: S1's proof routes
     through the compression to a finite-codimension cut, and Rayleigh
     values transfer exactly through compressions
     (`⟪(compress C) u, u⟫ = ⟪T u, u⟫`) while defect norms do not. The
     recursion's clause (a) consumes only Rayleigh, so nothing is lost.
     Do not strengthen S1's conclusion to a defect bound: it is not
     provable by this route and is not needed.

  2. WHERE ESCAPE IS AND IS NOT AVAILABLE. The blocked value λ₀ (the one
     with `λ₀ ∉ essSpec (compress (q ⊓ N))`) supports the full
     escape-based selection S2; the OTHER value λ₁ does not — nothing
     excludes `λ₁ ∈ essSpec (compress (h ⊓ N))` — and the odd stage must
     go through P1's perturbation instead. A draft that applies S2 at λ₁
     is wrong even if it elaborates.

  3. THE UNUSED HYPOTHESIS. The paper's statement carries
     "g ⊓ N ≠ ⊥ for all g ∈ G". It is contracted for fidelity and is
     expected to be flagged unused: the proof never consumes it, and even
     the degenerate `q ⊓ N = ⊥` needs nothing extra, since
     `PlufWO13.notMem_essSpec_compress_bot` makes BOTH values missing
     there. Retain and flag, per protocol.

  4. KNOWN DUPLICATION. W0 (decreasing cofinal chains in a countable
     directed family) is also contracted as WO-12's B2, running in
     parallel. The duplication is accepted and will be reconciled at
     merge; do not import from WO-12.

  Base: the merged tree after WO-13 (216 theorems; CI runs #1–#12).
  `PlufWO14.lean` imports `RequestProject.PlufWO13`. All prior theorems
  must remain green; `PlufWO7a.lean` is the census record, not to be
  edited.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  DELIVERY NOTES (WO-14).

  * All eight contract statements are delivered verbatim and proved; the
    quarantine fallback was NOT needed (W1 is unconditional), but
    `blocking_lemma_of_sequence` is delivered as well, since it is a
    cheap corollary of the same assembly and was explicitly requested as
    the audited fallback shape.
  * Support material added here: a generic index-dependent recursion
    principle (`exists_seq_of_step`), the Hilbert-space substitute for
    Hahn–Banach used to see that P1's perturbed vector stays in the span
    of its two inputs (`mem_of_forall_annihilating_functional`,
    `mem_span_pair_of_functional_vanishing`), and the bookkeeping lemmas
    for the constraint subspace `V ⊓ ⨅ f ∈ F, ker f`.
-/
import RequestProject.PlufWO13

open Set PlufWO13

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PlufWO14

abbrev H := PlufWO1.H

/-! ### Part 0: support material -/

/-- An index-dependent recursion principle. If at every stage `n`, given
    any candidate history `u`, a vector `y` with `P n u y` exists, and if
    `P n u y` depends on `u` only through its values below `n`, then a
    single sequence `f` exists with `P n f (f n)` for every `n`. This is
    the gadget the blocking recursion W1 runs on: its stage predicate
    refers to the finitely many previously chosen vectors. -/
theorem exists_seq_of_step {α : Type*} [Nonempty α] (P : ℕ → (ℕ → α) → α → Prop)
    (hdep : ∀ (n : ℕ) (u v : ℕ → α) (y : α), (∀ j, j < n → u j = v j) → P n u y → P n v y)
    (hex : ∀ (n : ℕ) (u : ℕ → α), ∃ y, P n u y) :
    ∃ f : ℕ → α, ∀ n, P n f (f n) := by
  classical
  let d : α := Classical.arbitrary α
  let g : ℕ → (ℕ → α) := fun n => Nat.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun k gk => Function.update gk k (Classical.choose (hex k gk))) n
  have hg0 : g 0 = fun _ => d := rfl
  have hgs : ∀ k, g (k + 1) = Function.update (g k) k (Classical.choose (hex k (g k))) :=
    fun k => rfl
  set f : ℕ → α := fun n => g (n + 1) n with hf
  -- values below the update index are unchanged
  have hstep : ∀ k j, j < k → g (k + 1) j = g k j := by
    intro k j hj
    rw [hgs k]
    exact Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hstable : ∀ m n, n ≤ m → ∀ j, j < n → g m j = g n j := by
    intro m
    induction m with
    | zero => intro n hn j hj; omega
    | succ k ih =>
      intro n hn j hj
      rcases Nat.lt_or_ge n (k + 1) with hlt | hge
      · have hnk : n ≤ k := by omega
        have h1 : g (k + 1) j = g k j := hstep k j (lt_of_lt_of_le hj hnk)
        rw [h1]
        exact ih n hnk j hj
      · have : n = k + 1 := le_antisymm hn hge
        subst this
        rfl
  refine ⟨f, fun n => ?_⟩
  have hbelow : ∀ j, j < n → g n j = f j := fun j hj =>
    hstable n (j + 1) (by omega) j (by omega)
  have hchoose := Classical.choose_spec (hex n (g n))
  have hfn : f n = Classical.choose (hex n (g n)) := by
    rw [hf]
    simp [hgs n]
  rw [hfn]
  exact hdep n (g n) f _ hbelow hchoose

/-- Hilbert-space substitute for the Hahn–Banach separation used in P1:
    a vector annihilated by every continuous functional that annihilates
    a closed subspace lies in that subspace. -/
theorem mem_of_forall_annihilating_functional (S : Submodule ℝ H)
    [S.HasOrthogonalProjection] (w : H)
    (hw : ∀ f : H →L[ℝ] ℝ, (∀ s ∈ S, f s = 0) → f w = 0) : w ∈ S := by
  set u : H := w - S.starProjection w with hu
  have humem : u ∈ Sᗮ := S.sub_starProjection_mem_orthogonal w
  have hf : ∀ s ∈ S, (innerSL ℝ u) s = 0 := by
    intro s hs
    have := (Submodule.mem_orthogonal S u).mp humem s hs
    simpa [real_inner_comm] using this
  have h0 : inner (𝕜 := ℝ) u w = 0 := by simpa using hw (innerSL ℝ u) hf
  have hsplit : inner (𝕜 := ℝ) u w = ‖u‖ ^ 2 := by
    have h1 : inner (𝕜 := ℝ) u (S.starProjection w) = 0 := by
      have := (Submodule.mem_orthogonal S u).mp humem _ (S.starProjection_apply_mem w)
      simpa [real_inner_comm] using this
    have hw' : w = u + S.starProjection w := by rw [hu]; abel
    rw [hw', inner_add_right, h1, real_inner_self_eq_norm_sq]
    ring
  have hu0 : u = 0 := by
    have h2 : ‖u‖ ^ 2 = 0 := by rw [← hsplit, h0]
    have : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
    simpa using this
  have hwp : w = S.starProjection w := sub_eq_zero.mp (hu ▸ hu0)
  rw [hwp]
  exact S.starProjection_apply_mem w

/-- Membership in the constraint subspace `V ⊓ ⨅ f ∈ F, ker f`, unfolded. -/
theorem mem_constraint_inf_iff (V : Submodule ℝ H) (F : Finset (H →L[ℝ] ℝ)) (x : H) :
    x ∈ (V ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ) : Submodule ℝ H)
      ↔ x ∈ V ∧ ∀ f ∈ F, f x = 0 := by
  simp [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

/-! ### Part S: the selection lemmas (the inner loop) -/

/-- S0 (constraint cutting, quotient form). Finitely many continuous
    linear functionals cut a closed subspace down to a closed subspace of
    finite codimension, in the exact quotient shape WO-13's C2 consumes:
    `Module.Finite ℝ (↥V ⧸ (C.comap V.subtype))`. The census should first
    check `PlufWO13/Basic.lean`, whose finiteness-transfer lemmas may
    already contain this; if so, cite rather than reprove, and report. -/
theorem finCodim_of_constraints (V : Submodule ℝ H)
    (hV : IsClosed (V : Set H)) (F : Finset (H →L[ℝ] ℝ)) :
    IsClosed ((V ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ) : Submodule ℝ H) : Set H) ∧
    Module.Finite ℝ
      (↥V ⧸ ((V ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ)).comap V.subtype)) := by
  constructor
  · have hset : ((V ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ) : Submodule ℝ H) : Set H)
        = (V : Set H) ∩ ⋂ f ∈ F, {x : H | f x = 0} := by
      ext x
      simp
    rw [hset]
    exact hV.inter (isClosed_biInter fun f _ => isClosed_eq f.continuous continuous_const)
  · set φ : ↥V →ₗ[ℝ] ({x // x ∈ F} → ℝ) :=
      LinearMap.pi (fun f : {x // x ∈ F} => ((f : H →L[ℝ] ℝ) : H →ₗ[ℝ] ℝ) ∘ₗ V.subtype) with hφ
    have hker : LinearMap.ker φ
        = ((V ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ)).comap V.subtype) := by
      ext v
      simp only [LinearMap.mem_ker, hφ, LinearMap.pi_apply, funext_iff, Submodule.mem_comap,
        Submodule.subtype_apply, LinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe, Pi.zero_apply]
      rw [mem_constraint_inf_iff]
      constructor
      · intro h
        exact ⟨v.2, fun f hf => h ⟨f, hf⟩⟩
      · rintro ⟨-, h⟩ f
        exact h f f.2
    rw [← hker]
    haveI : FiniteDimensional ℝ ({x // x ∈ F} → ℝ) := inferInstance
    haveI : Module.Finite ℝ (LinearMap.range φ) :=
      Module.Finite.of_injective (LinearMap.range φ).subtype Subtype.val_injective
    exact Module.Finite.equiv (φ.quotKerEquivRange).symm

/-- S1 (constrained selection at an essential-spectrum value). If
    `λ ∈ essSpec (compress V)` for closed `V`, then inside `V`, subject to
    finitely many linear constraints, there is a unit vector with Rayleigh
    value within `ε` of `λ`. -/
theorem exists_unit_constrained_rayleigh (V : Submodule ℝ H)
    (hV : IsClosed (V : Set H)) {lam : ℝ}
    (hlam : lam ∈ PlufWO9.essSpec (compress V))
    (F : Finset (H →L[ℝ] ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : H, w ∈ V ∧ ‖w‖ = 1 ∧ (∀ f ∈ F, f w = 0) ∧
      |inner (𝕜 := ℝ) (T w) w - lam| ≤ ε := by
  obtain ⟨hCcl, hfin⟩ := finCodim_of_constraints V hV F
  set C := (V ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ) : Submodule ℝ H) with hC
  haveI : CompleteSpace ↥C := hCcl.completeSpace_coe
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  have hCV : C ≤ V := inf_le_left
  have hlamC : lam ∈ PlufWO9.essSpec (compress C) := by
    rw [essSpec_compress_eq_of_finCodim hCcl hV hCV hfin]
    exact hlam
  obtain ⟨y, hmem, hnorm, -, hray⟩ := exists_seq_of_mem_essSpec_compress C hlamC
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hray ε hε
  have hMM := hM M le_rfl
  rw [Real.dist_eq] at hMM
  obtain ⟨hyV, hyF⟩ := (mem_constraint_inf_iff V F (y M)).mp (hmem M)
  exact ⟨y M, hyV, hnorm M, hyF, hMM.le⟩

/-- S2 (constrained selection off `N`, at the blocked value). -/
theorem exists_unit_constrained_rayleigh_notMem (V N : Submodule ℝ H)
    (hV : Ample V) (hN : IsClosed (N : Set H)) {lam : ℝ}
    (hlam : lam = 1 ∨ lam = 1/16)
    (hnot : lam ∉ PlufWO9.essSpec (compress (V ⊓ N)))
    (F : Finset (H →L[ℝ] ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : H, w ∈ V ∧ ‖w‖ = 1 ∧ (∀ f ∈ F, f w = 0) ∧ w ∉ N ∧
      |inner (𝕜 := ℝ) (T w) w - lam| ≤ ε := by
  have hVN : ¬ Ample (V ⊓ N) := not_ample_of_notMem_essSpec hlam hnot
  obtain ⟨K, hKV, hKcl, hKinf, hKbound, hKcodim⟩ := escape hV hN hVN hlam hnot hε
  obtain ⟨hCcl, hfin⟩ := finCodim_of_constraints K hKcl F
  set C := (K ⊓ ⨅ f ∈ F, LinearMap.ker (f : H →ₗ[ℝ] ℝ) : Submodule ℝ H) with hC
  have hCK : C ≤ K := inf_le_left
  have hCN : ¬ (C ≤ N) := by
    intro hle
    apply hKcodim
    have hle2 : C.comap K.subtype ≤ (K ⊓ N).comap K.subtype := fun v hv => ⟨v.2, hle hv⟩
    refine Module.Finite.of_surjective (Submodule.mapQ _ _ LinearMap.id hle2) ?_
    intro y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  obtain ⟨x, hxC, hxN⟩ := SetLike.not_le_iff_exists.mp hCN
  have hx0 : x ≠ 0 := fun h => hxN (h ▸ N.zero_mem)
  refine ⟨‖x‖⁻¹ • x, hKV (hCK (C.smul_mem _ hxC)), norm_smul_inv_norm hx0, ?_, ?_, ?_⟩
  · intro f hf
    have := ((mem_constraint_inf_iff K F x).mp hxC).2 f hf
    simp [this]
  · intro hmem
    apply hxN
    have hx : x = ‖x‖ • (‖x‖⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
    rw [hx]
    exact N.smul_mem _ hmem
  · have hw1 : ‖‖x‖⁻¹ • x‖ = 1 := norm_smul_inv_norm hx0
    have hq := quadratic_estimate_of_bound hKbound (‖x‖⁻¹ • x) (hCK (C.smul_mem _ hxC))
    rw [hw1] at hq
    simpa using hq

/-! ### Part P: the perturbation lemma (the odd stage) -/

/-- The algebra of the odd-stage perturbation, at a fixed `η > 0`: the
    normalized vector `(1 + η²)^(-1/2) • (w' + η • z)` is a unit vector
    whose Rayleigh value differs from that of `w'` by at most `η²`. Over
    `ℝ`, self-adjointness of `T` turns `⟪T w', z⟫ = 0` into the vanishing
    of both cross terms, so `⟪T w, w⟫ = (⟪T w', w'⟫ + η²⟪T z, z⟫)/(1+η²)`,
    and `PlufWO13.T_bounds` bounds the two Rayleigh values in `[1/16, 1]`. -/
theorem perturb_key (w' z : H) (hw' : ‖w'‖ = 1) (hz : ‖z‖ = 1)
    (horth : inner (𝕜 := ℝ) w' z = 0)
    (hTorth : inner (𝕜 := ℝ) (T w') z = 0) (η : ℝ) (hη : 0 < η) :
    ‖(Real.sqrt (1 + η^2))⁻¹ • (w' + η • z)‖ = 1 ∧
      |inner (𝕜 := ℝ) (T ((Real.sqrt (1 + η^2))⁻¹ • (w' + η • z)))
        ((Real.sqrt (1 + η^2))⁻¹ • (w' + η • z)) - inner (𝕜 := ℝ) (T w') w'| ≤ η^2 := by
  set s : ℝ := Real.sqrt (1 + η^2) with hs
  have hpos : (0:ℝ) < 1 + η^2 := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s^2 = 1 + η^2 := Real.sq_sqrt hpos.le
  set v : H := w' + η • z with hv
  have hnv : ‖v‖^2 = 1 + η^2 := by
    rw [hv, norm_add_sq_real, real_inner_smul_right, horth, norm_smul]
    simp [hw', hz, abs_of_pos hη]
  have hnv' : ‖v‖ = s := by
    have h : ‖v‖^2 = s^2 := by rw [hnv, hs2]
    nlinarith [norm_nonneg v, hs0]
  have hnorm : ‖s⁻¹ • v‖ = 1 := by
    rw [norm_smul, hnv', norm_inv, Real.norm_eq_abs, abs_of_pos hs0,
      inv_mul_cancel₀ (ne_of_gt hs0)]
  refine ⟨hnorm, ?_⟩
  set a : ℝ := inner (𝕜 := ℝ) (T w') w' with ha
  set b : ℝ := inner (𝕜 := ℝ) (T z) z with hb
  have hcross : inner (𝕜 := ℝ) (T z) w' = 0 := by
    rw [T_inner_symm z w', real_inner_comm]
    exact hTorth
  have hTv : inner (𝕜 := ℝ) (T v) v = a + η^2 * b := by
    rw [hv]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hTorth, hcross, ← ha, ← hb]
    ring
  have hmain : inner (𝕜 := ℝ) (T (s⁻¹ • v)) (s⁻¹ • v) = (a + η^2 * b) / (1 + η^2) := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, hTv, ← hs2]
    field_simp
  rw [hmain]
  have hab := T_bounds w'
  have hbb := T_bounds z
  rw [hw'] at hab
  rw [hz] at hbb
  simp only [one_pow, mul_one] at hab hbb
  rw [← ha] at hab
  rw [← hb] at hbb
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, div_eq_mul_inv, ← sub_nonneg]
    have h1 : (a + η ^ 2 * b) * (1+η^2)⁻¹ - (-η ^ 2 + a)
        = (η^2 * (b - a) + η^2 * (1 + η^2)) * (1+η^2)⁻¹ := by
      field_simp
      ring
    rw [h1]
    have : 0 ≤ η^2 * (b - a) + η^2 * (1 + η^2) := by nlinarith [sq_nonneg η]
    positivity
  · rw [sub_le_iff_le_add, ← sub_nonneg]
    have h1 : η ^ 2 + a - (a + η ^ 2 * b) / (1 + η^2)
        = (η^2 * (a - b) + η^2 * (1 + η^2)) / (1+η^2) := by
      field_simp
      ring
    rw [h1]
    have : 0 ≤ η^2 * (a - b) + η^2 * (1 + η^2) := by nlinarith [sq_nonneg η]
    positivity

theorem perturb_unit (w' z : H) (hw' : ‖w'‖ = 1) (hz : ‖z‖ = 1)
    (horth : inner (𝕜 := ℝ) w' z = 0)
    (hTorth : inner (𝕜 := ℝ) (T w') z = 0)
    (N : Submodule ℝ H) (hN : IsClosed (N : Set H)) (hzN : z ∉ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : H, ‖w‖ = 1 ∧
      (∀ f : H →L[ℝ] ℝ, f w' = 0 → f z = 0 → f w = 0) ∧
      w ∉ N ∧
      |inner (𝕜 := ℝ) (T w) w - inner (𝕜 := ℝ) (T w') w'| ≤ ε := by
  classical
  set W : ℝ → H := fun η => (Real.sqrt (1 + η^2))⁻¹ • (w' + η • z) with hW
  set t : ℝ := min 1 ε with ht
  have ht0 : 0 < t := lt_min one_pos hε
  have ht1 : t ≤ 1 := min_le_left _ _
  have htε : t ≤ ε := min_le_right _ _
  have hmemiff : ∀ η : ℝ, W η ∈ N → w' + η • z ∈ N := by
    intro η hmem
    have hpos : (0:ℝ) < Real.sqrt (1 + η^2) := Real.sqrt_pos.mpr (by positivity)
    have heq : w' + η • z = (Real.sqrt (1 + η^2)) • W η := by
      rw [hW]
      simp only
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
    rw [heq]
    exact N.smul_mem _ hmem
  have hnotboth : ¬ (W t ∈ N ∧ W (t/2) ∈ N) := by
    rintro ⟨h1, h2⟩
    have k1 := hmemiff t h1
    have k2 := hmemiff (t/2) h2
    have hd : (t/2) • z ∈ N := by
      have hsub := N.sub_mem k1 k2
      have heq : (w' + t • z) - (w' + (t/2) • z) = (t/2) • z := by module
      rwa [heq] at hsub
    apply hzN
    have heq2 : z = (t/2)⁻¹ • ((t/2) • z) := by
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [heq2]
    exact N.smul_mem _ hd
  have hchoice : ∃ η : ℝ, 0 < η ∧ η ≤ t ∧ W η ∉ N := by
    by_cases h : W t ∈ N
    · exact ⟨t/2, by positivity, by linarith, fun hc => hnotboth ⟨h, hc⟩⟩
    · exact ⟨t, ht0, le_rfl, h⟩
  obtain ⟨η, hη0, hηt, hηN⟩ := hchoice
  obtain ⟨hnorm, hray⟩ := perturb_key w' z hw' hz horth hTorth η hη0
  refine ⟨W η, hnorm, ?_, hηN, ?_⟩
  · intro f h1 h2
    rw [hW]
    simp [h1, h2]
  · refine hray.trans ?_
    nlinarith

/-- S3 (the odd-stage selection, the composite of S1, S2 and P1). At the
    unblocked value `lam₁` — for which no escape is available (design
    note 2) — a constrained unit vector off `N` is still obtainable: S1
    supplies `w' ∈ V` with Rayleigh value within `ε/2` of `lam₁`, S2 at
    the blocked value `lam₀` supplies `z ∈ V \ N` orthogonal to both `w'`
    and `T w'`, and P1 perturbs `w'` towards `z`. Membership `w ∈ V` is
    recovered from P1's shared-constraint clause: the perturbed vector is
    annihilated by every functional killing `w'` and `z`, hence lies in
    `span {w', z} ≤ V` by `mem_of_forall_annihilating_functional`. -/
theorem exists_unit_constrained_rayleigh_notMem_other (V N : Submodule ℝ H)
    (hV : Ample V) (hN : IsClosed (N : Set H)) {lam₀ lam₁ : ℝ}
    (hlam₀ : lam₀ = 1 ∨ lam₀ = 1/16)
    (hnot : lam₀ ∉ PlufWO9.essSpec (compress (V ⊓ N)))
    (hlam₁ : lam₁ ∈ PlufWO9.essSpec (compress V))
    (F : Finset (H →L[ℝ] ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : H, w ∈ V ∧ ‖w‖ = 1 ∧ (∀ f ∈ F, f w = 0) ∧ w ∉ N ∧
      |inner (𝕜 := ℝ) (T w) w - lam₁| ≤ ε := by
  classical
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨w', hw'V, hw'1, hw'F, hw'ray⟩ :=
    exists_unit_constrained_rayleigh V hV.2.1 hlam₁ F hhalf
  set F' : Finset (H →L[ℝ] ℝ) := insert (innerSL ℝ w') (insert (innerSL ℝ (T w')) F) with hF'
  obtain ⟨z, hzV, hz1, hzF, hzN, -⟩ :=
    exists_unit_constrained_rayleigh_notMem V N hV hN hlam₀ hnot F' hε
  have horth : inner (𝕜 := ℝ) w' z = 0 := by
    have := hzF (innerSL ℝ w') (by simp [hF'])
    simpa using this
  have hTorth : inner (𝕜 := ℝ) (T w') z = 0 := by
    have := hzF (innerSL ℝ (T w')) (by simp [hF'])
    simpa using this
  obtain ⟨w, hw1, hwf, hwN, hwray⟩ :=
    perturb_unit w' z hw'1 hz1 horth hTorth N hN hzN hhalf
  have hsub : ({w', z} : Set H) ⊆ (V : Set H) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hw'V
    · exact hzV
  have hspanle : Submodule.span ℝ ({w', z} : Set H) ≤ V := Submodule.span_le.mpr hsub
  haveI : FiniteDimensional ℝ ↥(Submodule.span ℝ ({w', z} : Set H)) :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  have hwspan : w ∈ Submodule.span ℝ ({w', z} : Set H) := by
    refine mem_of_forall_annihilating_functional _ w ?_
    intro f hf
    exact hwf f (hf w' (Submodule.subset_span (by simp))) (hf z (Submodule.subset_span (by simp)))
  refine ⟨w, hspanle hwspan, hw1, ?_, hwN, ?_⟩
  · intro f hf
    exact hwf f (hw'F f hf) (hzF f (by simp [hF', hf]))
  · have htri : |inner (𝕜 := ℝ) (T w) w - lam₁|
        ≤ |inner (𝕜 := ℝ) (T w) w - inner (𝕜 := ℝ) (T w') w'|
          + |inner (𝕜 := ℝ) (T w') w' - lam₁| := by
      calc |inner (𝕜 := ℝ) (T w) w - lam₁|
          = |(inner (𝕜 := ℝ) (T w) w - inner (𝕜 := ℝ) (T w') w')
              + (inner (𝕜 := ℝ) (T w') w' - lam₁)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith

/-! ### Part W: the recursion and the assembly -/

theorem exists_decreasing_cofinal {G : Set (Submodule ℝ H)}
    (hctble : G.Countable) {q : Submodule ℝ H} (hq : q ∈ G)
    (hdir : ∀ M ∈ G, ∀ M' ∈ G, ∃ P ∈ G, P ≤ M ⊓ M') :
    ∃ h : ℕ → Submodule ℝ H, (∀ n, h n ∈ G) ∧ (∀ n, h (n+1) ≤ h n) ∧
      h 0 ≤ q ∧ ∀ M ∈ G, ∃ n, h n ≤ M := by
  classical
  obtain ⟨e, he⟩ := hctble.exists_eq_range ⟨q, hq⟩
  have hmem : ∀ n, e n ∈ G := fun n => by rw [he]; exact ⟨n, rfl⟩
  let step : {M : Submodule ℝ H // M ∈ G} → ℕ → {M : Submodule ℝ H // M ∈ G} := fun M n =>
    ⟨(hdir M.1 M.2 (e n) (hmem n)).choose, (hdir M.1 M.2 (e n) (hmem n)).choose_spec.1⟩
  let f : ℕ → {M : Submodule ℝ H // M ∈ G} := fun n =>
    Nat.rec (motive := fun _ => {M : Submodule ℝ H // M ∈ G}) ⟨q, hq⟩ (fun k Mk => step Mk k) n
  have hstep : ∀ n, (f (n+1)).1 ≤ (f n).1 ⊓ e n := fun n =>
    (hdir (f n).1 (f n).2 (e n) (hmem n)).choose_spec.2
  refine ⟨fun n => (f n).1, fun n => (f n).2, fun n => le_trans (hstep n) inf_le_left, le_rfl, ?_⟩
  intro M hM
  rw [he] at hM
  obtain ⟨k, hk⟩ := hM
  exact ⟨k+1, hk ▸ le_trans (hstep k) inf_le_right⟩

theorem exists_blocking_sequence (h : ℕ → Submodule ℝ H)
    (hmono : ∀ n, h (n+1) ≤ h n) (hamp : ∀ n, Ample (h n))
    (N : Submodule ℝ H) (hN : IsClosed (N : Set H))
    {lam₀ lam₁ : ℝ}
    (hpair : (lam₀ = 1 ∧ lam₁ = 1/16) ∨ (lam₀ = 1/16 ∧ lam₁ = 1))
    (hnot : lam₀ ∉ PlufWO9.essSpec (compress (h 0 ⊓ N))) :
    ∃ w : ℕ → H,
      (∀ n, w n ∈ h n) ∧
      Orthonormal ℝ w ∧
      (∀ m n, m ≠ n → inner (𝕜 := ℝ) (T (w m)) (w n) = 0) ∧
      (∀ n, w n ∉ N) ∧
      (∀ m n, m ≠ n →
        inner (𝕜 := ℝ) ((Nᗮ).starProjection (w m)) ((Nᗮ).starProjection (w n)) = 0) ∧
      (∀ n, |inner (𝕜 := ℝ) (T (w n)) (w n) - (if Even n then lam₀ else lam₁)|
        ≤ 1 / (n + 1)) := by
  classical
  have hlam₀ : lam₀ = 1 ∨ lam₀ = 1/16 := by
    rcases hpair with ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inl e
    · exact Or.inr e
  have hcl : ∀ n, IsClosed ((h n : Set H)) := fun n => (hamp n).2.1
  have hdec : ∀ m n, m ≤ n → h n ≤ h m := by
    intro m n hmn
    induction n with
    | zero =>
      have : m = 0 := by omega
      subst this; exact le_rfl
    | succ k ih =>
      rcases Nat.lt_or_ge m (k+1) with hlt | hge
      · exact le_trans (hmono k) (ih (by omega))
      · have : m = k+1 := le_antisymm hmn hge
        subst this; exact le_rfl
  have hclinf : ∀ n, IsClosed (((h n ⊓ N : Submodule ℝ H)) : Set H) := by
    intro n
    have hset : ((h n ⊓ N : Submodule ℝ H) : Set H) = (h n : Set H) ∩ (N : Set H) := rfl
    rw [hset]
    exact (hcl n).inter hN
  have hnotn : ∀ n, lam₀ ∉ PlufWO9.essSpec (compress (h n ⊓ N)) := by
    intro n hmem
    exact hnot (essSpec_compress_mono (hclinf n) (hclinf 0)
      (inf_le_inf_right N (hdec 0 n (Nat.zero_le n))) hlam₀ hmem)
  have hlam₁mem : ∀ n, lam₁ ∈ PlufWO9.essSpec (compress (h n)) := by
    intro n
    rcases hpair with ⟨-, e⟩ | ⟨-, e⟩
    · rw [e]; exact (hamp n).2.2.2
    · rw [e]; exact (hamp n).2.2.1
  set P : ℕ → (ℕ → H) → H → Prop := fun n u y =>
    y ∈ h n ∧ ‖y‖ = 1 ∧
      (∀ j, j < n → inner (𝕜 := ℝ) (u j) y = 0 ∧ inner (𝕜 := ℝ) (T (u j)) y = 0 ∧
        inner (𝕜 := ℝ) ((Nᗮ).starProjection (u j)) y = 0) ∧
      y ∉ N ∧ |inner (𝕜 := ℝ) (T y) y - (if Even n then lam₀ else lam₁)| ≤ 1 / ((n:ℝ) + 1)
    with hP
  have hdep : ∀ (n : ℕ) (u v : ℕ → H) (y : H), (∀ j, j < n → u j = v j) → P n u y → P n v y := by
    intro n u v y huv hPy
    obtain ⟨k1, k2, k3, k4, k5⟩ := hPy
    exact ⟨k1, k2, fun j hj => by rw [← huv j hj]; exact k3 j hj, k4, k5⟩
  have hex : ∀ (n : ℕ) (u : ℕ → H), ∃ y, P n u y := by
    intro n u
    set F : Finset (H →L[ℝ] ℝ) := (Finset.range n).biUnion (fun j =>
      {innerSL ℝ (u j), innerSL ℝ (T (u j)), innerSL ℝ ((Nᗮ).starProjection (u j))}) with hF
    have hεpos : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
    have hconstr : ∀ y : H, (∀ f ∈ F, f y = 0) → ∀ j, j < n →
        inner (𝕜 := ℝ) (u j) y = 0 ∧ inner (𝕜 := ℝ) (T (u j)) y = 0 ∧
          inner (𝕜 := ℝ) ((Nᗮ).starProjection (u j)) y = 0 := by
      intro y hy j hj
      have h1 := hy (innerSL ℝ (u j)) (by
        rw [hF]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, by simp⟩)
      have h2 := hy (innerSL ℝ (T (u j))) (by
        rw [hF]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, by simp⟩)
      have h3 := hy (innerSL ℝ ((Nᗮ).starProjection (u j))) (by
        rw [hF]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, by simp⟩)
      simp only [innerSL_apply_apply] at h1 h2 h3
      exact ⟨h1, h2, h3⟩
    by_cases hpar : Even n
    · obtain ⟨y, hyV, hy1, hyF, hyN, hyray⟩ :=
        exists_unit_constrained_rayleigh_notMem (h n) N (hamp n) hN hlam₀ (hnotn n) F hεpos
      exact ⟨y, hyV, hy1, hconstr y hyF, hyN, by simpa [hpar] using hyray⟩
    · obtain ⟨y, hyV, hy1, hyF, hyN, hyray⟩ :=
        exists_unit_constrained_rayleigh_notMem_other (h n) N (hamp n) hN hlam₀ (hnotn n)
          (hlam₁mem n) F hεpos
      exact ⟨y, hyV, hy1, hconstr y hyF, hyN, by simpa [hpar] using hyray⟩
  obtain ⟨w, hw⟩ := exists_seq_of_step P hdep hex
  have hmemh : ∀ n, w n ∈ h n := fun n => (hw n).1
  have hnorm : ∀ n, ‖w n‖ = 1 := fun n => (hw n).2.1
  have hcon : ∀ n j, j < n → inner (𝕜 := ℝ) (w j) (w n) = 0 ∧
      inner (𝕜 := ℝ) (T (w j)) (w n) = 0 ∧
      inner (𝕜 := ℝ) ((Nᗮ).starProjection (w j)) (w n) = 0 := fun n => (hw n).2.2.1
  have hnotN : ∀ n, w n ∉ N := fun n => (hw n).2.2.2.1
  have hray : ∀ n, |inner (𝕜 := ℝ) (T (w n)) (w n) - (if Even n then lam₀ else lam₁)|
      ≤ 1 / ((n:ℝ) + 1) := fun n => (hw n).2.2.2.2
  have horth : Orthonormal ℝ w := by
    refine ⟨hnorm, ?_⟩
    intro i j hij
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact (hcon j i hlt).1
    · have hlt' : j < i := by omega
      have hkey := (hcon i j hlt').1
      rw [real_inner_comm]
      exact hkey
  refine ⟨w, hmemh, horth, ?_, hnotN, ?_, hray⟩
  · intro m n hmn
    rcases Nat.lt_or_ge m n with hlt | hge
    · exact (hcon n m hlt).2.1
    · have hlt' : n < m := by omega
      have hkey := (hcon m n hlt').2.1
      rw [T_inner_symm (w m) (w n), real_inner_comm]
      exact hkey
  · intro m n hmn
    have hidem : ∀ a b : H, inner (𝕜 := ℝ) ((Nᗮ).starProjection a) ((Nᗮ).starProjection b)
        = inner (𝕜 := ℝ) ((Nᗮ).starProjection a) b := by
      intro a b
      rw [← Submodule.inner_starProjection_left_eq_right]
      congr 1
      exact Submodule.starProjection_eq_self_iff.mpr ((Nᗮ).starProjection_apply_mem a)
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [hidem]
      exact (hcon n m hlt).2.2
    · have hlt' : n < m := by omega
      rw [real_inner_comm, hidem]
      exact (hcon m n hlt').2.2

theorem compress_exact_diagonal (w : ℕ → H) (hw : Orthonormal ℝ w)
    (hT : ∀ m n, m ≠ n → inner (𝕜 := ℝ) (T (w m)) (w n) = 0) (j m : ℕ)
    (hm : j ≤ m) :
    ((Submodule.span ℝ (Set.range fun n : {n // j ≤ n} => w n)).topologicalClosure).starProjection
        (T (w m))
      = (inner (𝕜 := ℝ) (T (w m)) (w m)) • w m := by
  set d : ℝ := inner (𝕜 := ℝ) (T (w m)) (w m) with hd
  set S : Submodule ℝ H := Submodule.span ℝ (Set.range fun n : {n // j ≤ n} => w n) with hS
  set R : Submodule ℝ H := S.topologicalClosure with hR
  have hwmem : ∀ n : ℕ, j ≤ n → w n ∈ R :=
    fun n hn => Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩)
  have hself : inner (𝕜 := ℝ) (w m) (w m) = 1 := by
    rw [real_inner_self_eq_norm_sq, hw.1 m]; norm_num
  set v : H := T (w m) - d • w m with hv
  have hker : R ≤ LinearMap.ker ((innerSL ℝ v : H →L[ℝ] ℝ) : H →ₗ[ℝ] ℝ) := by
    rw [hR]
    refine S.topologicalClosure_minimal ?_ (ContinuousLinearMap.isClosed_ker (innerSL ℝ v))
    rw [hS]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨n, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    rw [hv, inner_sub_left, real_inner_smul_left]
    rcases eq_or_ne (n : ℕ) m with h | h
    · rw [h, hself, hd]; ring
    · rw [hT m n (Ne.symm h), hw.2 (Ne.symm h)]; ring
  refine Submodule.eq_starProjection_of_mem_orthogonal (R.smul_mem _ (hwmem m hm)) ?_
  rw [Submodule.mem_orthogonal']
  intro u hu
  have h3 : inner (𝕜 := ℝ) (T (w m)) u - d * inner (𝕜 := ℝ) (w m) u = 0 := by
    simpa [hv, inner_sub_left, real_inner_smul_left] using LinearMap.mem_ker.mp (hker hu)
  rw [inner_sub_left, real_inner_smul_left]
  exact h3

/-! #### Support for the assembly: tail spans and their ampleness -/

/-- If the squares of a nonnegative sequence are dominated by a null
    sequence, the sequence is null. -/
theorem tendsto_zero_of_sq_le (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hle : ∀ n, (f n)^2 ≤ g n)
    (hg : Filter.Tendsto g Filter.atTop (nhds 0)) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hsqrt : Filter.Tendsto (fun n => Real.sqrt (g n)) Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hg
    simpa using this
  refine squeeze_zero hf (fun n => ?_) hsqrt
  have h1 : f n = Real.sqrt ((f n)^2) := (Real.sqrt_sq (hf n)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt (hle n)

/-- The essential-spectrum membership criterion in the Rayleigh-only form
    the recursion produces: at `lam ∈ {1, 1/16}` the WO-13 defect identity
    `norm_T_sub_lam_sq_le` upgrades Rayleigh convergence to defect
    convergence, so a weakly null sequence of unit vectors of `V` whose
    Rayleigh values converge to `lam` witnesses
    `lam ∈ essSpec (compress V)`. -/
theorem mem_essSpec_compress_of_rayleigh_seq (V : Submodule ℝ H) [CompleteSpace ↥V] {lam : ℝ}
    (hlam : lam = 1 ∨ lam = 1/16) (y : ℕ → H) (hmem : ∀ n, y n ∈ V) (hnorm : ∀ n, ‖y n‖ = 1)
    (hweak : ∀ z : H, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (y n) z) Filter.atTop (nhds 0))
    (hray : Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) (y n)) Filter.atTop (nhds lam)) :
    lam ∈ PlufWO9.essSpec (compress V) := by
  refine mem_essSpec_compress_of_seq V y hmem hnorm hweak ?_
  refine tendsto_zero_of_sq_le _ (fun n => |inner (𝕜 := ℝ) (T (y n)) (y n) - lam|)
    (fun n => norm_nonneg _) (fun n => ?_) ?_
  · have h := norm_T_sub_lam_sq_le hlam (y n)
    rw [hnorm n] at h
    simpa using h
  · have h : Filter.Tendsto (fun n => inner (𝕜 := ℝ) (T (y n)) (y n) - lam)
        Filter.atTop (nhds (lam - lam)) := hray.sub tendsto_const_nhds
    rw [sub_self] at h
    simpa using h.abs

/-- `tailSpan w j` is the closed span of `{w n : n ≥ j}` — the subspace
    `R j` of the assembly, and the subject of W2. -/
noncomputable def tailSpan (w : ℕ → H) (j : ℕ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range fun n : {n // j ≤ n} => w n)).topologicalClosure

theorem isClosed_tailSpan (w : ℕ → H) (j : ℕ) :
    IsClosed ((tailSpan w j : Submodule ℝ H) : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem mem_tailSpan (w : ℕ → H) {j n : ℕ} (hn : j ≤ n) : w n ∈ tailSpan w j :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩)

theorem tailSpan_le {w : ℕ → H} {j : ℕ} {V : Submodule ℝ H} (hV : IsClosed (V : Set H))
    (hmem : ∀ n, j ≤ n → w n ∈ V) : tailSpan w j ≤ V := by
  refine Submodule.topologicalClosure_minimal _ ?_ hV
  refine Submodule.span_le.mpr ?_
  rintro x ⟨n, rfl⟩
  exact hmem n n.2

/-- Every tail of a blocking sequence spans an ample subspace: the
    even-indexed and odd-indexed subsequences are orthonormal (hence
    weakly null) sequences of unit vectors of the tail span whose
    Rayleigh values converge to `lam₀` and `lam₁`, i.e. to `1` and
    `1/16` in one order or the other. -/
theorem ample_tailSpan (w : ℕ → H) (hworth : Orthonormal ℝ w) {lam₀ lam₁ : ℝ}
    (hpair : (lam₀ = 1 ∧ lam₁ = 1/16) ∨ (lam₀ = 1/16 ∧ lam₁ = 1))
    (hray : ∀ n, |inner (𝕜 := ℝ) (T (w n)) (w n) - (if Even n then lam₀ else lam₁)|
      ≤ 1 / ((n:ℝ) + 1))
    (j : ℕ) : Ample (tailSpan w j) := by
  classical
  haveI : CompleteSpace ↥(tailSpan w j) := (isClosed_tailSpan w j).completeSpace_coe
  have hbase : Filter.Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmemlam : ∀ (lam : ℝ) (idx : ℕ → ℕ), StrictMono idx → (∀ k, j ≤ idx k) →
      (∀ k, |inner (𝕜 := ℝ) (T (w (idx k))) (w (idx k)) - lam| ≤ 1 / ((k:ℝ)+1)) →
      (lam = 1 ∨ lam = 1/16) → lam ∈ PlufWO9.essSpec (compress (tailSpan w j)) := by
    intro lam idx hidx hidxj hb hlam
    refine mem_essSpec_compress_of_rayleigh_seq (tailSpan w j) hlam (fun k => w (idx k))
      (fun k => mem_tailSpan w (hidxj k)) (fun k => hworth.1 (idx k)) ?_ ?_
    · intro z
      exact PlufWO9.tendsto_inner_of_orthonormal (hworth.comp idx hidx.injective) z
    · have hdiff : Filter.Tendsto (fun k => inner (𝕜 := ℝ) (T (w (idx k))) (w (idx k)) - lam)
          Filter.atTop (nhds 0) := by
        refine squeeze_zero_norm (fun k => ?_) hbase
        simpa using hb k
      have := hdiff.add (tendsto_const_nhds (x := lam) (f := Filter.atTop (α := ℕ)))
      simpa using this
  have hcastle : ∀ (a k : ℕ), k ≤ a → 1/((a:ℝ)+1) ≤ 1/((k:ℝ)+1) := by
    intro a k hk
    have hka : (k:ℝ) ≤ (a:ℝ) := by exact_mod_cast hk
    apply one_div_le_one_div_of_le <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  have h0 : lam₀ ∈ PlufWO9.essSpec (compress (tailSpan w j)) := by
    refine hmemlam lam₀ (fun k => 2*(j+k)) (fun a b hab => by dsimp only; omega)
      (fun k => by dsimp only; omega) (fun k => ?_) ?_
    · have hk := hray (2*(j+k))
      rw [if_pos (even_two_mul _)] at hk
      exact hk.trans (hcastle _ k (by omega))
    · rcases hpair with ⟨e, -⟩ | ⟨e, -⟩
      · exact Or.inl e
      · exact Or.inr e
  have h1 : lam₁ ∈ PlufWO9.essSpec (compress (tailSpan w j)) := by
    refine hmemlam lam₁ (fun k => 2*(j+k)+1) (fun a b hab => by dsimp only; omega)
      (fun k => by dsimp only; omega) (fun k => ?_) ?_
    · have hk := hray (2*(j+k)+1)
      rw [if_neg (by simp [parity_simps])] at hk
      exact hk.trans (hcastle _ k (by omega))
    · rcases hpair with ⟨-, e⟩ | ⟨-, e⟩
      · exact Or.inr e
      · exact Or.inl e
  refine ⟨?_, isClosed_tailSpan w j, ?_, ?_⟩
  · intro hbot
    have hwj : w j ∈ tailSpan w j := mem_tailSpan w (le_refl j)
    rw [hbot, Submodule.mem_bot] at hwj
    have hn := hworth.1 j
    rw [hwj, norm_zero] at hn
    norm_num at hn
  · rcases hpair with ⟨e, -⟩ | ⟨-, e⟩
    · rw [← e]; exact h0
    · rw [← e]; exact h1
  · rcases hpair with ⟨-, e⟩ | ⟨e, -⟩
    · rw [← e]; exact h1
    · rw [← e]; exact h0

/-- W3 in the conditional (quarantined) shape prescribed by the work
    order's fallback clause: the entire assembly, with W1's conclusion
    taken as a hypothesis. The unconditional `blocking_lemma` below is
    this theorem applied to `exists_blocking_sequence`, so the assembly
    is machine-checked either way. -/
theorem blocking_lemma_of_sequence (G : Set (Submodule ℝ H)) (hctble : G.Countable)
    (hamp : ∀ g ∈ G, Ample g)
    (hdir : ∀ M ∈ G, ∀ M' ∈ G, ∃ P ∈ G, P ≤ M ⊓ M')
    (N : Submodule ℝ H) (hN : IsClosed (N : Set H))
    {q : Submodule ℝ H} (hq : q ∈ G) (hqN : ¬ Ample (q ⊓ N))
    (hseq : ∀ (h : ℕ → Submodule ℝ H), (∀ n, h (n+1) ≤ h n) → (∀ n, Ample (h n)) →
      ∀ {lam₀ lam₁ : ℝ}, ((lam₀ = 1 ∧ lam₁ = 1/16) ∨ (lam₀ = 1/16 ∧ lam₁ = 1)) →
      lam₀ ∉ PlufWO9.essSpec (compress (h 0 ⊓ N)) →
      ∃ w : ℕ → H,
        (∀ n, w n ∈ h n) ∧
        Orthonormal ℝ w ∧
        (∀ m n, m ≠ n → inner (𝕜 := ℝ) (T (w m)) (w n) = 0) ∧
        (∀ n, w n ∉ N) ∧
        (∀ m n, m ≠ n →
          inner (𝕜 := ℝ) ((Nᗮ).starProjection (w m)) ((Nᗮ).starProjection (w n)) = 0) ∧
        (∀ n, |inner (𝕜 := ℝ) (T (w n)) (w n) - (if Even n then lam₀ else lam₁)|
          ≤ 1 / (n + 1))) :
    ∃ R : Submodule ℝ H, IsClosed (R : Set H) ∧
      R ⊓ N = ⊥ ∧
      (∀ g ∈ G, Ample (R ⊓ g)) ∧
      Ample R := by
  classical
  have hqcl : IsClosed ((q : Set H)) := (hamp q hq).2.1
  have hqNcl : IsClosed (((q ⊓ N : Submodule ℝ H)) : Set H) := hqcl.inter hN
  obtain ⟨lam₀, lam₁, hpair, hnot0⟩ :
      ∃ lam₀ lam₁ : ℝ, ((lam₀ = 1 ∧ lam₁ = 1/16) ∨ (lam₀ = 1/16 ∧ lam₁ = 1)) ∧
        lam₀ ∉ PlufWO9.essSpec (compress (q ⊓ N)) := by
    by_cases h1 : (1:ℝ) ∈ PlufWO9.essSpec (compress (q ⊓ N))
    · by_cases h2 : (1/16:ℝ) ∈ PlufWO9.essSpec (compress (q ⊓ N))
      · refine absurd ?_ hqN
        refine ⟨?_, hqNcl, h1, h2⟩
        intro hbot
        rw [hbot] at h1
        exact notMem_essSpec_compress_bot 1 h1
      · exact ⟨1/16, 1, Or.inr ⟨rfl, rfl⟩, h2⟩
    · exact ⟨1, 1/16, Or.inl ⟨rfl, rfl⟩, h1⟩
  have hlam₀ : lam₀ = 1 ∨ lam₀ = 1/16 := by
    rcases hpair with ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inl e
    · exact Or.inr e
  obtain ⟨hh, hhG, hhmono, hh0q, hhcof⟩ := exists_decreasing_cofinal hctble hq hdir
  have hhamp : ∀ n, Ample (hh n) := fun n => hamp _ (hhG n)
  have hhanti : Antitone hh := antitone_nat_of_succ_le hhmono
  have hh0cl : IsClosed (((hh 0 ⊓ N : Submodule ℝ H)) : Set H) := (hhamp 0).2.1.inter hN
  have hnot : lam₀ ∉ PlufWO9.essSpec (compress (hh 0 ⊓ N)) := fun hmem =>
    hnot0 (essSpec_compress_mono hh0cl hqNcl (inf_le_inf_right N hh0q) hlam₀ hmem)
  obtain ⟨w, hwmem, hworth, hwT, hwN, hwy, hwray⟩ := hseq hh hhmono hhamp hpair hnot
  haveI : CompleteSpace ↥N := hN.completeSpace_coe
  have hidem : ∀ a b : H, inner (𝕜 := ℝ) ((Nᗮ).starProjection a) b
      = inner (𝕜 := ℝ) ((Nᗮ).starProjection a) ((Nᗮ).starProjection b) := by
    intro a b
    rw [← Submodule.inner_starProjection_left_eq_right]
    congr 1
    exact (Submodule.starProjection_eq_self_iff.mpr ((Nᗮ).starProjection_apply_mem a)).symm
  refine ⟨tailSpan w 0, isClosed_tailSpan w 0, ?_, ?_, ample_tailSpan w hworth hpair hwray 0⟩
  · have hyne : ∀ n, (Nᗮ).starProjection (w n) ≠ 0 := by
      intro n hz
      apply hwN n
      have hmem : w n ∈ (Nᗮ)ᗮ := (Submodule.starProjection_apply_eq_zero_iff _).mp hz
      rwa [Submodule.orthogonal_orthogonal] at hmem
    rw [eq_bot_iff]
    rintro x ⟨hxR, hxN⟩
    have hPx : (Nᗮ).starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
      exact hxN
    have hcoef : ∀ m, inner (𝕜 := ℝ) (w m) x = 0 := by
      intro m
      set c : ℝ := ‖(Nᗮ).starProjection (w m)‖^2 with hc
      have hc0 : c ≠ 0 := by
        rw [hc]
        exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hyne m))
      set g : H →L[ℝ] ℝ := innerSL ℝ ((Nᗮ).starProjection (w m)) - c • innerSL ℝ (w m) with hg
      have hgker : tailSpan w 0 ≤ LinearMap.ker ((g : H →L[ℝ] ℝ) : H →ₗ[ℝ] ℝ) := by
        refine tailSpan_le (ContinuousLinearMap.isClosed_ker g) (fun n _ => ?_)
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hg,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
          smul_eq_mul]
        rcases eq_or_ne n m with rfl | hne
        · rw [PlufWO13.Aux.inner_starProjection_self, ← hc]
          have hs : inner (𝕜 := ℝ) (w n) (w n) = 1 := by
            rw [real_inner_self_eq_norm_sq, hworth.1 n]; norm_num
          rw [hs]; ring
        · rw [hidem, hwy m n (Ne.symm hne), hworth.2 (Ne.symm hne)]
          ring
      have hgx := LinearMap.mem_ker.mp (hgker hxR)
      simp only [ContinuousLinearMap.coe_coe, hg, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul] at hgx
      have hleft : inner (𝕜 := ℝ) ((Nᗮ).starProjection (w m)) x = 0 := by
        rw [Submodule.inner_starProjection_left_eq_right, hPx, inner_zero_right]
      rw [hleft] at hgx
      have hzz : c * inner (𝕜 := ℝ) (w m) x = 0 := by linarith
      exact (mul_eq_zero.mp hzz).resolve_left hc0
    have hxker : tailSpan w 0 ≤ LinearMap.ker ((innerSL ℝ x : H →L[ℝ] ℝ) : H →ₗ[ℝ] ℝ) := by
      refine tailSpan_le (ContinuousLinearMap.isClosed_ker _) (fun n _ => ?_)
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
      rw [real_inner_comm]
      exact hcoef n
    have hxx := LinearMap.mem_ker.mp (hxker hxR)
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hxx
    rw [Submodule.mem_bot]
    exact inner_self_eq_zero.mp hxx
  · intro g hg
    obtain ⟨j, hj⟩ := hhcof g hg
    have hle : tailSpan w j ≤ tailSpan w 0 ⊓ g :=
      le_inf (tailSpan_le (isClosed_tailSpan w 0) (fun n _ => mem_tailSpan w (Nat.zero_le n)))
        (tailSpan_le (hamp g hg).2.1 (fun n hn => hj (hhanti hn (hwmem n))))
    have hclinf : IsClosed (((tailSpan w 0 ⊓ g : Submodule ℝ H)) : Set H) :=
      (isClosed_tailSpan w 0).inter (hamp g hg).2.1
    exact ample_of_ample_le (ample_tailSpan w hworth hpair hwray j) hclinf hle

theorem blocking_lemma (G : Set (Submodule ℝ H)) (hctble : G.Countable)
    (hamp : ∀ g ∈ G, Ample g)
    (hdir : ∀ M ∈ G, ∀ M' ∈ G, ∃ P ∈ G, P ≤ M ⊓ M')
    (N : Submodule ℝ H) (hN : IsClosed (N : Set H))
    {q : Submodule ℝ H} (hq : q ∈ G) (hqN : ¬ Ample (q ⊓ N))
    (hGN : ∀ g ∈ G, g ⊓ N ≠ ⊥) :
    ∃ R : Submodule ℝ H, IsClosed (R : Set H) ∧
      R ⊓ N = ⊥ ∧
      (∀ g ∈ G, Ample (R ⊓ g)) ∧
      Ample R := by
  refine blocking_lemma_of_sequence G hctble hamp hdir N hN hq hqN ?_
  intro hh hhmono hhamp lam₀ lam₁ hpair hnot
  exact exists_blocking_sequence hh hhmono hhamp N hN hpair hnot

/-! ### Axiom audit -/

#print axioms finCodim_of_constraints
#print axioms exists_unit_constrained_rayleigh
#print axioms exists_unit_constrained_rayleigh_notMem
#print axioms exists_unit_constrained_rayleigh_notMem_other
#print axioms perturb_unit
#print axioms exists_decreasing_cofinal
#print axioms exists_blocking_sequence
#print axioms compress_exact_diagonal
#print axioms blocking_lemma_of_sequence
#print axioms blocking_lemma

end PlufWO14
