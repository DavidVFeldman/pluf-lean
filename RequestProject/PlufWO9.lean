/-
  PlufWO9.lean — Work Order 9 for the pluf project (Feldman–Wilce).

  Scope: the harvest commission recommended by the WO-7a census. It
  converts probe material into contracted, reusable infrastructure, and
  closes target (d) as a paper-facing statement:
    (A) target (d): Paper I, Proposition 2.3 as printed, in both regimes
        (the triple argument for H from WO-6, the principality argument in
        finite dimension from WO-7a), stated at the paper's generality;
    (B) the essential spectrum layer: `essSpec` and its supporting
        theorems, contracted as a stable API;
    (C) the approximate-eigenvector substitute for spectral subspaces:
        the engine theorem and the closed-span construction that will
        stand in for the Borel functional calculus in Paper I §5;
    (D) the general HilbertBasis block API, superseding the standard-basis
        `PlufWO1.block` / `PlufWO2.block` for the basis-relative work of
        Paper II §6, together with the corrected Q2 and the reindexing
        lemma;
    (E) the ω₁-recursion combinator, with the universe tax factored into
        a lemma.

  All of this exists in `PlufWO7a.lean` as probe material. This work order
  asks for it as a *contracted API*: stable names, minimal hypotheses,
  docstrings stating what each item is for, and no dependence on the probe
  file — `PlufWO7a.lean` remains in the repository as the census record and
  MUST NOT be deleted or edited.

  DELIVERY NOTE (WO-9). Every item below is proved *in this file*: no
  declaration of `PlufWO7a` is used, so the contracted API is independent
  of the probe record even though the probe file is imported (as the
  contract prescribes) to keep the census green.  Dependence on the
  earlier work orders WO-1 … WO-6 is retained where the mathematics is
  theirs (Part A2 uses `PlufWO6.no_prime_filter`, and its optional
  generalization `PlufWO6.not_prime_of_triple`).

  Ground rules as in WO-1–WO-8, including the codified counterexample
  license. Nothing classical is assumed: CH enters only as a hypothesis
  (an equinumerosity assumption), never as an axiom.

  Base: the WO-7a artifact (CI runs #1–#8; 149 theorems). All prior
  theorems must remain green.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.
-/
import RequestProject.PlufWO7a

open Set

namespace PlufWO9

/-! ### Part A: target (d) — Paper I, Proposition 2.3, as printed -/

section PrimeFilters

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- In dimension at least two, every nonzero vector is avoided by two
    subspaces that jointly span the space. (In the paper's argument this
    replaces the triple `A, B, C`, which does not exist in odd dimension.) -/
theorem exists_pair_sup_top_notMem (h2 : 2 ≤ Module.finrank ℝ V) (v : V) (hv0 : v ≠ 0) :
    ∃ P Q : Submodule ℝ V, P ⊔ Q = ⊤ ∧ v ∉ P ∧ v ∉ Q := by
  have hne : (ℝ ∙ v) ≠ ⊤ := by
    intro h
    have h1 : Module.finrank ℝ ↥(ℝ ∙ v) = 1 := finrank_span_singleton hv0
    rw [h] at h1
    simp only [finrank_top] at h1
    omega
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ (ℝ ∙ v) := by
    by_contra hcon
    push_neg at hcon
    exact hne (eq_top_iff.mpr fun x _ => hcon x)
  set S : Submodule ℝ V := (ℝ ∙ v) ⊔ (ℝ ∙ w) with hS
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  have hSC : S ⊓ C = ⊥ := hC.1.eq_bot
  refine ⟨(ℝ ∙ w) ⊔ C, (ℝ ∙ (v + w)) ⊔ C, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← hC.2.eq_top]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      have h1 : w ∈ (ℝ ∙ w) ⊔ C := Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)
      have h2 : v + w ∈ (ℝ ∙ (v + w)) ⊔ C :=
        Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      have h3 : (v + w) - w ∈ ((ℝ ∙ w) ⊔ C) ⊔ ((ℝ ∙ (v + w)) ⊔ C) :=
        Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)
      simpa using h3
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
  · intro hmem
    rw [Submodule.mem_sup] at hmem
    obtain ⟨y, hy, c, hc, hyc⟩ := hmem
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hce : c = v - a • w := eq_sub_of_add_eq' hyc
    have hcS : c ∈ S := by
      rw [hce]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
        (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)))
    have hc0 : c = 0 := by
      have hmem2 : c ∈ S ⊓ C := ⟨hcS, hc⟩
      rwa [hSC, Submodule.mem_bot] at hmem2
    rw [hc0, add_zero] at hyc
    have ha : a ≠ 0 := by rintro rfl; simp at hyc; exact hv0 hyc.symm
    apply hw
    rw [Submodule.mem_span_singleton]
    exact ⟨a⁻¹, by rw [← hyc, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩
  · intro hmem
    rw [Submodule.mem_sup] at hmem
    obtain ⟨y, hy, c, hc, hyc⟩ := hmem
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hce : c = v - a • (v + w) := eq_sub_of_add_eq' hyc
    have hcS : c ∈ S := by
      rw [hce]
      refine Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
        (Submodule.smul_mem _ _ ?_)
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
    have hc0 : c = 0 := by
      have hmem2 : c ∈ S ⊓ C := ⟨hcS, hc⟩
      rwa [hSC, Submodule.mem_bot] at hmem2
    rw [hc0, add_zero] at hyc
    have ha : a ≠ 0 := by rintro rfl; simp at hyc; exact hv0 hyc.symm
    apply hw
    rw [Submodule.mem_span_singleton]
    refine ⟨(1 - a) / a, ?_⟩
    have hsum : a • v + a • w = v := by rw [smul_add] at hyc; exact hyc
    have h5 : (1 - a) • v = a • w := by
      rw [sub_smul, one_smul, eq_comm, eq_sub_iff_add_eq, add_comm]; exact hsum
    rw [div_eq_mul_inv, mul_comm, mul_smul, h5, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- The finite-dimensional half of Proposition 2.3, at the generality the
    argument actually has: no inner product, no topology, any real vector
    space of dimension at least two. A proper nonempty meet-closed
    upward-closed family has a member of least dimension, contained in
    every member; primeness applied to a pair of subspaces spanning the
    space and avoiding a fixed nonzero vector of that least member gives
    the contradiction. -/
theorem no_prime_filter_of_finrank_ge_two [FiniteDimensional ℝ V]
    (h2 : 2 ≤ Module.finrank ℝ V) (π : Set (Submodule ℝ V))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ V, M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ V) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ V, M ⊔ N ∈ π → M ∈ π ∨ N ∈ π) := by
  intro hprime
  classical
  obtain ⟨M₀, hM₀⟩ := hne
  have hex : ∃ n, ∃ M ∈ π, Module.finrank ℝ M = n := ⟨_, M₀, hM₀, rfl⟩
  obtain ⟨M, hM, hMcard⟩ := Nat.find_spec hex
  have hmin : ∀ N ∈ π, Nat.find hex ≤ Module.finrank ℝ N := fun N hN => Nat.find_le ⟨N, hN, rfl⟩
  have hMle : ∀ N ∈ π, M ≤ N := by
    intro N hN
    have h1 : M ⊓ N ∈ π := hinf M hM N hN
    have h2 : Module.finrank ℝ ↥(M ⊓ N) ≤ Module.finrank ℝ ↥M := Submodule.finrank_mono inf_le_left
    have h3 := hmin _ h1
    rw [hMcard] at h2
    have h4 : Module.finrank ℝ ↥(M ⊓ N) = Module.finrank ℝ ↥M := by omega
    have h5 : M ⊓ N = M := Submodule.eq_of_le_of_finrank_eq inf_le_left h4
    exact le_trans (le_of_eq h5.symm) inf_le_right
  have hMne : M ≠ ⊥ := fun h => hbot (h ▸ hM)
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
  obtain ⟨P, Q, hPQ, hvP, hvQ⟩ := exists_pair_sup_top_notMem h2 v hv0
  have htop : (⊤ : Submodule ℝ V) ∈ π := hup M₀ hM₀ ⊤ le_top
  rcases hprime P Q (hPQ ▸ htop) with hP | hP
  · exact hvP (hMle P hP hvM)
  · exact hvQ (hMle Q hP hvM)

end PrimeFilters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A1 (Paper I, Proposition 2.3, finite-dimensional regime). The lattice
    of subspaces of a real inner-product space of finite dimension at least
    two carries no prime filter. This is `PlufWO7a`'s group D, re-sited with
    the paper's hypotheses and without the unused oddness assumption the
    probe retained. -/
theorem no_prime_filter_finrank (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (h2 : 2 ≤ Module.finrank ℝ V)
    (π : Set (Submodule ℝ V)) (hne : π.Nonempty)
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ V, M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ V) ∉ π) :
    ¬ (∀ M N : Submodule ℝ V, M ⊔ N ∈ π → M ∈ π ∨ N ∈ π) :=
  no_prime_filter_of_finrank_ge_two h2 π hup hinf hbot hne

/-- A2 (Paper I, Proposition 2.3, the statement the paper makes), the
    infinite-dimensional regime: no proper nonempty filter of closed
    subspaces of the separable infinite-dimensional space `PlufWO1.H` is
    prime. Together with `no_prime_filter_finrank` this is the packaging
    of Proposition 2.3 delivered by this work order: two named corollaries
    rather than one disjunction, because the two regimes have different
    primeness clauses (the closed join in the infinite-dimensional case,
    the plain join in the finite-dimensional one). The optional
    generalization asked for by the work order is carried out below, in
    `no_prime_filter_of_infinite_hilbertBasis`: the triple argument runs at
    an arbitrary infinite orthonormal basis, so the infinite-dimensional
    regime does not need separability.

    The hypothesis `hcl` is retained from the contract but is not needed. -/
theorem no_prime_filter_paper (π : Set (Submodule ℝ PlufWO1.H))
    (hcl : ∀ M ∈ π, IsClosed (M : Set PlufWO1.H)) (hne : π.Nonempty)
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ PlufWO1.H,
      IsClosed (N : Set PlufWO1.H) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ PlufWO1.H) ∉ π) :
    ¬ (∀ M N : Submodule ℝ PlufWO1.H, IsClosed (M : Set PlufWO1.H) →
        IsClosed (N : Set PlufWO1.H) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π) :=
  PlufWO6.no_prime_filter π hup hinf hbot hne

/-! ### Part B: the essential spectrum layer -/

/-- B0. The essential spectrum, by the Weyl-sequence definition installed
    in the census (Mathlib has no essential spectrum, no Calkin algebra and
    no Fredholm theory): `lam ∈ essSpec T` iff there is a sequence of unit
    vectors tending weakly to `0` with `‖(T - lam) xₙ‖ → 0`. -/
def essSpec (T : E →L[ℝ] E) : Set ℝ :=
  {lam | ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
    (∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0)) ∧
    Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖) Filter.atTop (nhds 0)}

omit [CompleteSpace E] in
theorem mem_essSpec_iff (T : E →L[ℝ] E) (lam : ℝ) :
    lam ∈ essSpec T ↔ ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
      (∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0)) ∧
      Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖) Filter.atTop (nhds 0) := Iff.rfl

omit [CompleteSpace E] in
/-- B3. A weakly null sequence has norms of projections onto a fixed
    finite-dimensional subspace tending to `0`. This is the technical core
    of B2. -/
theorem tendsto_norm_proj_finiteDimensional_of_weaklyNull
    (W : Submodule ℝ E) (hfin : Module.Finite ℝ ↥W) (x : ℕ → E)
    (hw : ∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ‖W.starProjection (x n)‖) Filter.atTop (nhds 0) := by
  have hfd : FiniteDimensional ℝ ↥W := hfin
  set b := stdOrthonormalBasis ℝ ↥W with hb
  have key : ∀ n, W.starProjection (x n) = ∑ i, (inner (𝕜 := ℝ) ((b i : E)) (x n)) • ((b i : E)) := by
    intro n
    rw [Submodule.starProjection_apply, b.orthogonalProjection_apply_eq_sum]
    push_cast
    simp
  have hsum : Filter.Tendsto (fun n => ∑ i, (inner (𝕜 := ℝ) ((b i : E)) (x n)) • ((b i : E)))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun n => ∑ i, (inner (𝕜 := ℝ) ((b i : E)) (x n)) • ((b i : E)))
        Filter.atTop (nhds (∑ _i : Fin (Module.finrank ℝ ↥W), (0 : E))) := by
      refine tendsto_finset_sum _ fun i _ => ?_
      have h1 : Filter.Tendsto (fun n => inner (𝕜 := ℝ) ((b i : E)) (x n)) Filter.atTop (nhds 0) := by
        simpa [real_inner_comm] using hw ((b i : E))
      simpa using h1.smul_const ((b i : E))
    simpa using h
  simpa [key] using hsum.norm

omit [CompleteSpace E] in
/-- A Weyl sequence for `T` at `lam` can be pushed into `Wᗮ` when `W` is
    finite-dimensional, by subtracting the projection onto `W` (which tends
    to `0` by `tendsto_norm_proj_finiteDimensional_of_weaklyNull`) and
    renormalizing. -/
theorem exists_weyl_sequence_in_orthogonal (T : E →L[ℝ] E)
    (W : Submodule ℝ E) (hfin : Module.Finite ℝ ↥W) (lam : ℝ)
    (x : ℕ → E) (hx1 : ∀ n, ‖x n‖ = 1)
    (hxw : ∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0))
    (hxT : Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖) Filter.atTop (nhds 0)) :
    ∃ z : ℕ → E, (∀ n, z n ∈ Wᗮ) ∧ (∀ n, ‖z n‖ = 1) ∧
      Filter.Tendsto (fun n => ‖T (z n) - lam • z n‖) Filter.atTop (nhds 0) := by
  have hfd : FiniteDimensional ℝ ↥W := hfin
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ → E, p = fun n => W.starProjection (x n) := ⟨_, rfl⟩
  have hp : Filter.Tendsto (fun n => ‖p n‖) Filter.atTop (nhds 0) := by
    rw [hpdef]
    exact tendsto_norm_proj_finiteDimensional_of_weaklyNull W hfin x hxw
  obtain ⟨y, hydef⟩ : ∃ y : ℕ → E, y = fun n => x n - p n := ⟨_, rfl⟩
  have hyV : ∀ n, y n ∈ Wᗮ := by
    intro n
    rw [hydef, hpdef]
    exact W.sub_starProjection_mem_orthogonal (v := x n)
  have hyn : Filter.Tendsto (fun n => ‖y n‖) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n => 1 - ‖p n‖) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop (α := ℕ))).sub hp
    have h2 : Filter.Tendsto (fun n => 1 + ‖p n‖) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop (α := ℕ))).add hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 (fun n => ?_) (fun n => ?_)
    · have h := norm_sub_norm_le (x n) (p n)
      rw [hydef]; simp only; rw [hx1 n] at h; linarith
    · have h := norm_sub_le (x n) (p n)
      rw [hydef]; simp only; rw [hx1 n] at h; linarith
  have hyT : Filter.Tendsto (fun n => ‖T (y n) - lam • y n‖) Filter.atTop (nhds 0) := by
    have hbound : ∀ n, ‖T (y n) - lam • y n‖ ≤ ‖T (x n) - lam • x n‖ + (‖T‖ + |lam|) * ‖p n‖ := by
      intro n
      have he : T (y n) - lam • y n = (T (x n) - lam • x n) - (T (p n) - lam • p n) := by
        rw [hydef]; simp only [map_sub, smul_sub]; abel
      rw [he]
      refine (norm_sub_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖T (p n)‖ ≤ ‖T‖ * ‖p n‖ := T.le_opNorm _
      have h2 : ‖lam • p n‖ = |lam| * ‖p n‖ := by simp [norm_smul]
      rw [h2]; nlinarith [norm_nonneg (p n)]
    have hlim : Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖ + (‖T‖ + |lam|) * ‖p n‖)
        Filter.atTop (nhds 0) := by
      simpa using hxT.add (hp.const_mul (‖T‖ + |lam|))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => norm_nonneg _) hbound
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (hyn.eventually_const_lt (show (1:ℝ)/2 < 1 by norm_num))
  refine ⟨fun n => (‖y (n + N)‖)⁻¹ • y (n + N), fun n => Wᗮ.smul_mem _ (hyV _), fun n => ?_, ?_⟩
  · have h := hN (n + N) (Nat.le_add_left _ _)
    have hne : ‖y (n + N)‖ ≠ 0 := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (‖y (n+N)‖)⁻¹),
      inv_mul_cancel₀ hne]
  · have hshift : Filter.Tendsto (fun n => ‖T (y (n+N)) - lam • y (n+N)‖) Filter.atTop (nhds 0) :=
      hyT.comp (Filter.tendsto_add_atTop_nat N)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hshift.const_mul (2:ℝ)) (fun n => norm_nonneg _) (fun n => ?_)
    have h := hN (n + N) (Nat.le_add_left _ _)
    have he : T ((‖y (n+N)‖)⁻¹ • y (n+N)) - lam • ((‖y (n+N)‖)⁻¹ • y (n+N))
        = (‖y (n+N)‖)⁻¹ • (T (y (n+N)) - lam • y (n+N)) := by
      rw [ContinuousLinearMap.map_smul, smul_sub, smul_comm (‖y (n+N)‖)⁻¹ lam]
    rw [he, norm_smul]
    have hinv : ‖(‖y (n+N)‖)⁻¹‖ ≤ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    nlinarith [norm_nonneg (T (y (n+N)) - lam • y (n+N))]

omit [CompleteSpace E] in
/-- An orthonormal sequence is weakly null; this is Bessel's inequality,
    `Orthonormal.inner_products_summable`. -/
theorem tendsto_inner_of_orthonormal {u : ℕ → E} (hu : Orthonormal ℝ u) (y : E) :
    Filter.Tendsto (fun n => inner (𝕜 := ℝ) (u n) y) Filter.atTop (nhds 0) := by
  have hsum : Summable fun n => ‖inner (𝕜 := ℝ) (u n) y‖ ^ 2 :=
    Orthonormal.inner_products_summable y hu
  have h0 : Filter.Tendsto (fun n => ‖inner (𝕜 := ℝ) (u n) y‖ ^ 2) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.sqrt_sq_eq_abs] using h0.sqrt

omit [CompleteSpace E] in
/-- The engine, in its hypothesis form: if against every finite-dimensional
    subspace `W` and every tolerance `d` there is a unit vector of `V ⊓ Wᗮ`
    moved less than `d` by `T - lam`, then there is an *orthonormal*
    sequence in `V` of approximate eigenvectors with prescribed tolerances.
    Each new vector is chosen orthogonal to the (finite-dimensional) span of
    its predecessors. -/
theorem exists_orthonormal_approx_eigenvectors_of_forall (T : E →L[ℝ] E) (lam : ℝ)
    (V : Submodule ℝ E) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (H : ∀ W : Submodule ℝ E, Module.Finite ℝ ↥W → ∀ d : ℝ, 0 < d →
      ∃ v : E, v ∈ V ∧ v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ (∀ n, u n ∈ V) ∧ ∀ n, ‖T (u n) - lam • u n‖ < eps n := by
  classical
  have key : ∀ l : List E, ∃ v : E, v ∈ V ∧ v ∈ (Submodule.span ℝ {x | x ∈ l})ᗮ ∧ ‖v‖ = 1 ∧
      ‖T v - lam • v‖ < eps l.length := by
    intro l
    have hfin : Module.Finite ℝ ↥(Submodule.span ℝ {x | x ∈ l}) :=
      FiniteDimensional.span_of_finite ℝ l.finite_toSet
    exact H _ hfin _ (heps l.length)
  choose pick hpick0 hpick1 hpick2 hpick3 using key
  let L : ℕ → List E := fun n => Nat.rec ([] : List E) (fun _ l => pick l :: l) n
  have hLsucc : ∀ n, L (n+1) = pick (L n) :: L n := fun n => rfl
  have hLlen : ∀ n, (L n).length = n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [hLsucc n, List.length_cons, ih]
  set u : ℕ → E := fun n => pick (L n) with hu
  have hmem : ∀ n m, m < n → u m ∈ L n := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
      · rw [hLsucc n]; exact List.mem_cons_of_mem _ (ih m h)
      · rw [hLsucc n, h]; exact List.mem_cons_self
  have horth : ∀ n m, m < n → inner (𝕜 := ℝ) (u m) (u n) = 0 := fun n m hmn =>
    hpick1 (L n) (u m) (Submodule.subset_span (hmem n m hmn))
  refine ⟨u, ⟨fun n => hpick2 (L n), ?_⟩, fun n => hpick0 (L n), fun n => ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact horth j i h
    · rw [real_inner_comm]; exact horth i j h
  · have h := hpick3 (L n)
    rwa [hLlen n] at h

omit [CompleteSpace E] in
/-- B1. The essential spectrum is closed. -/
theorem isClosed_essSpec (T : E →L[ℝ] E) : IsClosed (essSpec T) := by
  rw [← isSeqClosed_iff_isClosed]
  intro lams lam hmem hlim
  have H : ∀ W : Submodule ℝ E, Module.Finite ℝ ↥W → ∀ d : ℝ, 0 < d →
      ∃ v : E, v ∈ (⊤ : Submodule ℝ E) ∧ v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d := by
    intro W hW d hd
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hlim) (d/2) (by linarith)
    obtain ⟨x, hx1, hxw, hxT⟩ := hmem k
    obtain ⟨z, hz1, hz2, hz3⟩ :=
      exists_weyl_sequence_in_orthogonal T W hW (lams k) x hx1 hxw hxT
    obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 hz3) (d/2) (by linarith)
    refine ⟨z m, Submodule.mem_top, hz1 m, hz2 m, ?_⟩
    have h1 : ‖T (z m) - lams k • z m‖ < d/2 := by
      have h := hm m le_rfl
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using h
    have h2 : |lams k - lam| < d/2 := by
      have h := hk k le_rfl
      simpa [Real.dist_eq] using h
    have he : T (z m) - lam • z m = (T (z m) - lams k • z m) + (lams k - lam) • z m := by
      module
    calc ‖T (z m) - lam • z m‖ ≤ ‖T (z m) - lams k • z m‖ + ‖(lams k - lam) • z m‖ := by
          rw [he]; exact norm_add_le _ _
      _ = ‖T (z m) - lams k • z m‖ + |lams k - lam| := by rw [norm_smul, hz2 m]; simp
      _ < d/2 + d/2 := by linarith
      _ = d := by ring
  obtain ⟨u, hu, -, hut⟩ :=
    exists_orthonormal_approx_eigenvectors_of_forall T lam ⊤ (fun n => 1/(n+1))
      (fun n => by positivity) H
  refine ⟨u, fun n => hu.1 n, fun y => tendsto_inner_of_orthonormal hu y, ?_⟩
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hut n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The Weyl datum extracted from a point of the essential spectrum: unit
    vectors in `V ⊓ Wᗮ` with arbitrarily small defect, for every
    finite-dimensional `W`. This is the hypothesis the engine consumes. -/
theorem exists_unit_approx_eigenvector_mem (T : E →L[ℝ] E) (lam : ℝ)
    (V : Submodule ℝ E) (hV : IsClosed (V : Set E)) (hfc : Module.Finite ℝ ↥Vᗮ)
    (hlam : lam ∈ essSpec T) (W : Submodule ℝ E) (hW : Module.Finite ℝ ↥W)
    (d : ℝ) (hd : 0 < d) :
    ∃ v : E, v ∈ V ∧ v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d := by
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  haveI hWfd : FiniteDimensional ℝ ↥W := hW
  haveI hVfd : FiniteDimensional ℝ ↥Vᗮ := hfc
  have hsup : Module.Finite ℝ ↥(W ⊔ Vᗮ) := Submodule.finiteDimensional_sup W Vᗮ
  obtain ⟨x, hx1, hxw, hxT⟩ := hlam
  obtain ⟨z, hz1, hz2, hz3⟩ :=
    exists_weyl_sequence_in_orthogonal T (W ⊔ Vᗮ) hsup lam x hx1 hxw hxT
  obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 hz3) d hd
  have hzm := hz1 m
  have hmemW : z m ∈ Wᗮ := Submodule.orthogonal_le le_sup_left hzm
  have hmemV : z m ∈ V := by
    have h : z m ∈ Vᗮᗮ := Submodule.orthogonal_le le_sup_right hzm
    rwa [Submodule.orthogonal_orthogonal] at h
  refine ⟨z m, hmemV, hmemW, hz2 m, ?_⟩
  have h := hm m le_rfl
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using h

/-- The contracted form of the engine at a point of the essential spectrum,
    relative to a closed subspace of finite codimension: an orthonormal
    sequence *inside* `V` with caller-prescribed defects. Both B2 and C1
    are instances. -/
theorem exists_orthonormal_approx_eigenvectors_mem (T : E →L[ℝ] E) (lam : ℝ)
    (hlam : lam ∈ essSpec T) (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    (hfc : Module.Finite ℝ ↥Vᗮ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ (∀ n, u n ∈ V) ∧ ∀ n, ‖T (u n) - lam • u n‖ < ε n :=
  exists_orthonormal_approx_eigenvectors_of_forall T lam V ε hε
    (fun W hW d hd => exists_unit_approx_eigenvector_mem T lam V hV hfc hlam W hW d hd)

/-- B2 (the load-bearing item). Passing to a closed subspace of finite
    codimension does not shrink the essential spectrum: a point of
    `essSpec T` is witnessed by an *orthonormal* — hence weakly null —
    sequence lying inside `V`. MINIMAL HYPOTHESES: `V` closed with
    finite-dimensional orthocomplement; neither self-adjointness of `T`
    (which the paper's Calkin-algebra argument uses) nor any finite-rank,
    compactness or Fredholm input is needed. -/
theorem essSpec_le_of_finCodim (T : E →L[ℝ] E) (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) (hfc : Module.Finite ℝ ↥Vᗮ)
    (lam : ℝ) (hlam : lam ∈ essSpec T) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ (∀ n, u n ∈ V) ∧
      Filter.Tendsto (fun n => ‖T (u n) - lam • u n‖) Filter.atTop (nhds 0) := by
  obtain ⟨u, hu, huV, hut⟩ :=
    exists_orthonormal_approx_eigenvectors_mem T lam hlam V hV hfc (fun n => 1/(n+1))
      (fun n => by positivity)
  refine ⟨u, hu, huV, ?_⟩
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hut n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The compression of `T` to a closed subspace `V`. -/
noncomputable def compress (T : E →L[ℝ] E) (V : Submodule ℝ E) [CompleteSpace ↥V] :
    ↥V →L[ℝ] ↥V :=
  (V.orthogonalProjection).comp (T.comp V.subtypeL)

/-- B2, in the form the paper states it: the essential spectrum does not
    shrink when `T` is compressed to a closed subspace of finite
    codimension. -/
theorem essSpec_subset_essSpec_compress (T : E →L[ℝ] E) (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) (hfc : Module.Finite ℝ ↥Vᗮ) :
    haveI : CompleteSpace ↥V := hV.completeSpace_coe
    essSpec T ⊆ essSpec (compress T V) := by
  haveI : CompleteSpace ↥V := hV.completeSpace_coe
  intro lam hlam
  obtain ⟨u, hu, huV, hut⟩ := essSpec_le_of_finCodim T V hV hfc lam hlam
  refine ⟨fun n => ⟨u n, huV n⟩, fun n => by simpa using hu.1 n, ?_, ?_⟩
  · intro y
    have h := tendsto_inner_of_orthonormal hu (y : E)
    simpa [Submodule.coe_inner] using h
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hut
    have hproj : (compress T V) ⟨u n, huV n⟩ - lam • (⟨u n, huV n⟩ : ↥V)
        = V.orthogonalProjection (T (u n) - lam • u n) := by
      have hlamu : V.orthogonalProjection (lam • u n) = lam • (⟨u n, huV n⟩ : ↥V) := by
        rw [map_smul]
        congr 1
        exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨u n, huV n⟩ : ↥V)
      simp [compress, map_sub, hlamu]
    rw [hproj]
    exact V.norm_orthogonalProjection_apply_le (T (u n) - lam • u n)

/-! ### Part C: the substitute for spectral subspaces -/

/-- C1 (the engine). From a bounded operator and a point of the essential
    spectrum, an orthonormal sequence of approximate eigenvectors with
    prescribed decay of the defects: the decay rate `ε` is a parameter
    supplied by the caller. This is the census's replacement for the Borel
    functional calculus. -/
theorem exists_orthonormal_approx_eigenvectors (T : E →L[ℝ] E) (lam : ℝ)
    (hlam : lam ∈ essSpec T) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ ∀ n, ‖T (u n) - lam • u n‖ < ε n := by
  have htopcl : IsClosed ((⊤ : Submodule ℝ E) : Set E) := by
    simp
  have htopfin : Module.Finite ℝ ↥(⊤ : Submodule ℝ E)ᗮ := by
    rw [Submodule.top_orthogonal_eq_bot]
    infer_instance
  obtain ⟨u, hu, -, hut⟩ :=
    exists_orthonormal_approx_eigenvectors_mem T lam hlam ⊤ htopcl htopfin ε hε
  exact ⟨u, hu, hut⟩

/-- The substitute for a spectral subspace: the closed span of an
    approximate-eigenvector sequence. -/
def approxEigenSpan (u : ℕ → E) : Submodule ℝ E :=
  (Submodule.span ℝ (Set.range u)).topologicalClosure

omit [CompleteSpace E] in
theorem isClosed_approxEigenSpan (u : ℕ → E) :
    IsClosed (approxEigenSpan u : Set E) :=
  Submodule.isClosed_topologicalClosure _

omit [CompleteSpace E] in
theorem mem_approxEigenSpan (u : ℕ → E) (n : ℕ) : u n ∈ approxEigenSpan u :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

omit [CompleteSpace E] in
/-- C2 (the substitute subspace). The closed span `approxEigenSpan u` of an
    orthonormal approximate-eigenvector sequence contains the sequence, is
    infinite-dimensional, and carries `T` uniformly close to `lam`:
    `‖T x - lam • x‖ ≤ (∑' n, ε n) * ‖x‖` for every `x` in it.
    THE TOLERANCE CLAUSE is this global bound with the *total* mass
    `∑' n, ε n` of the defect sequence; Paper I §5 obtains any tolerance it
    likes by choosing `ε` summable with small sum. -/
theorem approx_eigen_span_spec (T : E →L[ℝ] E) (lam : ℝ) (u : ℕ → E)
    (hu : Orthonormal ℝ u) (ε : ℕ → ℝ)
    (hdef : ∀ n, ‖T (u n) - lam • u n‖ < ε n) (hsum : Summable ε) :
    (∀ n, u n ∈ approxEigenSpan u) ∧ ¬ FiniteDimensional ℝ ↥(approxEigenSpan u) ∧
      ∀ x ∈ approxEigenSpan u, ‖T x - lam • x‖ ≤ (∑' n, ε n) * ‖x‖ := by
  classical
  have hεpos : ∀ n, 0 < ε n := fun n => lt_of_le_of_lt (norm_nonneg _) (hdef n)
  set C : ℝ := ∑' n, ε n with hC
  have hCnn : 0 ≤ C := tsum_nonneg fun n => (hεpos n).le
  set A : E →L[ℝ] E := T - lam • (ContinuousLinearMap.id ℝ E) with hA
  have hAapp : ∀ y : E, A y = T y - lam • y := by intro y; simp [hA]
  refine ⟨mem_approxEigenSpan u, ?_, ?_⟩
  · intro hfd
    have hli : LinearIndependent ℝ
        (fun n : ℕ => (⟨u n, mem_approxEigenSpan u n⟩ : ↥(approxEigenSpan u))) := by
      refine LinearIndependent.of_comp (approxEigenSpan u).subtype ?_
      simpa using hu.linearIndependent
    have hfin : Finite ℕ := hli.finite
    exact (Set.infinite_univ (α := ℕ)) (Set.finite_univ)
  · have hspan : ∀ x ∈ Submodule.span ℝ (Set.range u), ‖A x‖ ≤ C * ‖x‖ := by
      intro x hx
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
      have hx' : x = ∑ i ∈ c.support, c i • u i := by
        rw [← hc, Finsupp.sum]
      have hcoef : ∀ i ∈ c.support, |c i| ≤ ‖x‖ := by
        intro i hi
        have hinner : inner (𝕜 := ℝ) (u i) x = c i := by
          rw [hx', inner_sum, Finset.sum_eq_single i]
          · rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hu.1 i]
            ring
          · intro j _ hji
            rw [real_inner_smul_right, hu.2 (Ne.symm hji), mul_zero]
          · intro hnot; exact absurd hi hnot
        calc |c i| = |inner (𝕜 := ℝ) (u i) x| := by rw [hinner]
          _ ≤ ‖u i‖ * ‖x‖ := abs_real_inner_le_norm _ _
          _ = ‖x‖ := by rw [hu.1 i, one_mul]
      have hAx : A x = ∑ i ∈ c.support, c i • A (u i) := by
        rw [hx', map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      calc ‖A x‖ = ‖∑ i ∈ c.support, c i • A (u i)‖ := by rw [hAx]
        _ ≤ ∑ i ∈ c.support, ‖c i • A (u i)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ c.support, ‖x‖ * ε i := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_smul, Real.norm_eq_abs]
            have h1 : ‖A (u i)‖ ≤ ε i := by rw [hAapp]; exact (hdef i).le
            have h2 : |c i| ≤ ‖x‖ := hcoef i hi
            nlinarith [abs_nonneg (c i), norm_nonneg (A (u i)), (hεpos i).le, norm_nonneg x]
        _ = ‖x‖ * ∑ i ∈ c.support, ε i := by rw [Finset.mul_sum]
        _ ≤ ‖x‖ * C := by
            have : ∑ i ∈ c.support, ε i ≤ C :=
              Summable.sum_le_tsum _ (fun i _ => (hεpos i).le) hsum
            exact mul_le_mul_of_nonneg_left this (norm_nonneg x)
        _ = C * ‖x‖ := by ring
    have hclosed : IsClosed {x : E | ‖A x‖ ≤ C * ‖x‖} :=
      isClosed_le (A.continuous.norm) (continuous_const.mul continuous_norm)
    have hsub : (approxEigenSpan u : Set E) ⊆ {x : E | ‖A x‖ ≤ C * ‖x‖} := by
      rw [approxEigenSpan, Submodule.topologicalClosure_coe]
      exact closure_minimal hspan hclosed
    intro x hx
    have := hsub hx
    rwa [Set.mem_setOf_eq, hAapp] at this

/-! ### Part D: the general HilbertBasis block API -/

section Bases

variable {ι : Type*} (b : HilbertBasis ι ℝ E)

/-- D1. The block of a set of indices relative to an arbitrary Hilbert
    basis: the closed span of the corresponding basis vectors. This
    supersedes the standard-basis `block` of WO-1/WO-2 for the
    basis-relative work of Paper II §6. -/
def blockB (S : Set ι) : Submodule ℝ E :=
  (Submodule.span ℝ (b '' S)).topologicalClosure

/-- The block, characterized by inner products against the basis vectors
    off `S`. -/
theorem mem_blockB_iff_inner (S : Set ι) (x : E) :
    x ∈ blockB b S ↔ ∀ i ∉ S, inner (𝕜 := ℝ) x (b i) = 0 := by
  have hfwd : ∀ y : E, y ∈ blockB b S → ∀ i ∉ S, inner (𝕜 := ℝ) y (b i) = 0 := by
    intro y hy i hi
    have hle : Submodule.span ℝ (b '' S) ≤ (Submodule.span ℝ {b i})ᗮ := by
      rw [Submodule.span_le]
      rintro z ⟨j, hj, rfl⟩
      intro w hw
      rw [Submodule.mem_span_singleton] at hw
      obtain ⟨t, rfl⟩ := hw
      have hij : i ≠ j := fun hh => hi (hh ▸ hj)
      rw [real_inner_smul_left, b.orthonormal.2 hij, mul_zero]
    have hcl := Submodule.topologicalClosure_minimal _ hle
      (Submodule.isClosed_orthogonal (Submodule.span ℝ {b i}))
    have h2 := hcl hy (b i) (Submodule.mem_span_singleton_self _)
    rw [real_inner_comm] at h2
    exact h2
  refine ⟨hfwd x, fun h => ?_⟩
  set K := blockB b S with hK
  have hKc : IsClosed (K : Set E) := Submodule.isClosed_topologicalClosure _
  have hKcomplete : CompleteSpace K := hKc.completeSpace_coe
  have hz : x - K.starProjection x = 0 := by
    have hzero : ∀ i, inner (𝕜 := ℝ) (b i) (x - K.starProjection x) = 0 := by
      intro i
      have hsub : x - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (v := x)
      by_cases hi : i ∈ S
      · have hbK : b i ∈ K :=
          Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        exact hsub (b i) hbK
      · have h1 : inner (𝕜 := ℝ) x (b i) = 0 := h i hi
        have h2 : inner (𝕜 := ℝ) (K.starProjection x) (b i) = 0 :=
          hfwd _ (K.starProjection_apply_mem x) i hi
        rw [real_inner_comm]
        simp [inner_sub_left, h1, h2]
    apply b.repr.injective (a₁ := x - K.starProjection x) (a₂ := 0)
    ext i
    simpa [HilbertBasis.repr_apply_apply, inner_sub_right] using hzero i
  have hx : x = K.starProjection x := by linear_combination (norm := module) hz
  rw [hx]
  exact K.starProjection_apply_mem x

/-- The coordinate characterization of the block (probe Q4). -/
theorem mem_blockB_iff (S : Set ι) (x : E) :
    x ∈ blockB b S ↔ ∀ i ∉ S, b.repr x i = 0 := by
  rw [mem_blockB_iff_inner]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · rw [HilbertBasis.repr_apply_apply, real_inner_comm]; exact h i hi
  · have := h i hi
    rw [HilbertBasis.repr_apply_apply] at this
    rw [real_inner_comm]; exact this

omit [CompleteSpace E] in
theorem isClosed_blockB (S : Set ι) : IsClosed (blockB b S : Set E) :=
  Submodule.isClosed_topologicalClosure _

end Bases

/-- The standard Hilbert basis of the paper's `H = ℓ²(ℕ; ℝ)`: the
    tautological one, whose `repr` is the identity. -/
noncomputable def stdHilbertBasis : HilbertBasis ℕ ℝ PlufWO1.H :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ PlufWO1.H)

/-- D2. Agreement with the standard-basis block of the earlier work
    orders: no bridging isometry is needed, the two subspaces of `H` are
    equal, so every existing result about `PlufWO1.block` transfers to
    `blockB` without restatement. -/
theorem blockB_stdBasis_eq (S : Set ℕ) : blockB stdHilbertBasis S = PlufWO1.block S := by
  ext x
  rw [mem_blockB_iff, PlufWO1.mem_block_iff]
  constructor
  · intro h n hn
    simpa [stdHilbertBasis] using h n hn
  · intro h n hn
    simpa [stdHilbertBasis] using h n hn

section Bases2

/-- D3 (probe Q3). Reindexing a `HilbertBasis` along an equivalence of
    index types. -/
theorem hilbertBasis_reindex {ι ι' : Type*} (b : HilbertBasis ι ℝ E) (e : ι ≃ ι') :
    ∃ b' : HilbertBasis ι' ℝ E, ∀ i, b' (e i) = b i := by
  have horth : Orthonormal ℝ (fun j : ι' => b (e.symm j)) :=
    b.orthonormal.comp _ e.symm.injective
  have hrange : Set.range (fun j : ι' => b (e.symm j)) = Set.range b := by
    rw [show (fun j : ι' => b (e.symm j)) = (b ∘ e.symm) from rfl, Set.range_comp,
      e.symm.range_eq_univ, Set.image_univ]
  have hsp : ⊤ ≤ (Submodule.span ℝ (Set.range fun j : ι' => b (e.symm j))).topologicalClosure := by
    rw [hrange, b.dense_span]
  refine ⟨HilbertBasis.mk horth hsp, fun i => ?_⟩
  rw [HilbertBasis.coe_mk horth hsp]
  simp

omit [CompleteSpace E] in
/-- An orthonormal set in a separable space is countable (probe Q1). -/
theorem countable_of_orthonormal [TopologicalSpace.SeparableSpace E]
    (s : Set E) (hs : Orthonormal ℝ ((↑) : s → E)) : s.Countable := by
  have hdist : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 < dist x y := by
    intro x hx y hy hxy
    have h1 : ‖x‖ = 1 := hs.1 ⟨x, hx⟩
    have h2 : ‖y‖ = 1 := hs.1 ⟨y, hy⟩
    have h3 : inner (𝕜 := ℝ) x y = 0 :=
      hs.2 (i := ⟨x, hx⟩) (j := ⟨y, hy⟩) (by simpa [Subtype.ext_iff] using hxy)
    have hsq : ‖x - y‖ ^ 2 = 2 := by rw [norm_sub_sq_real, h1, h2, h3]; ring
    have hnn : (0:ℝ) ≤ ‖x - y‖ := norm_nonneg _
    have hgt : (1:ℝ) < ‖x - y‖ := by nlinarith
    simpa [dist_eq_norm] using hgt
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun x : E => Metric.ball x (1/2))
    (a := s) ?_ (fun i _ => Metric.isOpen_ball) (fun i _ => ⟨i, by simp⟩)
  intro x hx y hy hxy
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  rintro z hz hz'
  have h1 := Metric.mem_ball.mp hz
  have h2 := Metric.mem_ball.mp hz'
  have h3 := dist_triangle x z y
  have hd := hdist x hx y hy hxy
  rw [dist_comm z x] at h1
  linarith

/-- D4 (the corrected Q2). A separable Hilbert space, together with a
    countable orthogonal decomposition into closed subspaces, admits a
    Hilbert basis indexed by a countable type and adapted to the
    decomposition: each basis vector lies in one summand. NOTE: the
    arbitrary-index form of this statement is FALSE (an `ℕ`-indexed basis
    forces `E` infinite-dimensional; the census formalized the
    counterexample `E = ℝ`, `M 0 = ⊤`), and it MUST NOT be generalized. -/
theorem exists_countable_hilbertBasis_of_decomposition
    [TopologicalSpace.SeparableSpace E]
    (M : ℕ → Submodule ℝ E) (hMc : ∀ n, IsClosed ((M n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ M m, ∀ y ∈ M n, inner (𝕜 := ℝ) x y = 0)
    (hspan : ⨆ n, M n = ⊤) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E), ∀ i, ∃ n, b i ∈ M n := by
  classical
  haveI hcomp : ∀ n, CompleteSpace ↥(M n) := fun n => (hMc n).completeSpace_coe
  have h : ∀ n, ∃ (w : Set ↥(M n)) (b : HilbertBasis w ℝ ↥(M n)), ⇑b = ((↑) : w → ↥(M n)) :=
    fun n => exists_hilbertBasis ℝ ↥(M n)
  choose w bb hbb using h
  have hworth : ∀ n, Orthonormal ℝ ((↑) : w n → ↥(M n)) := by
    intro n; rw [← hbb n]; exact (bb n).orthonormal
  have hcount : ∀ n, (w n).Countable := fun n => countable_of_orthonormal (w n) (hworth n)
  haveI : ∀ n, Countable ↥(w n) := fun n => (hcount n).to_subtype
  let J : Type _ := Σ n : ℕ, ↥(w n)
  haveI : Countable J := by infer_instance
  let v : J → E := fun p => ((p.2 : ↥(M p.1)) : E)
  have hvmem : ∀ p : J, v p ∈ M p.1 := fun p => (p.2 : ↥(M p.1)).2
  have hv : Orthonormal ℝ v := by
    constructor
    · rintro ⟨n, i⟩
      simpa [v] using (hworth n).1 i
    · rintro ⟨n, i⟩ ⟨m, j⟩ hij
      by_cases hnm : n = m
      · subst hnm
        have hne : i ≠ j := by rintro rfl; exact hij rfl
        simpa [v, Submodule.coe_inner] using (hworth n).2 hne
      · exact horth hnm _ (hvmem ⟨n, i⟩) _ (hvmem ⟨m, j⟩)
  have perp : ∀ y : E, (∀ p, inner (𝕜 := ℝ) y (v p) = 0) → ∀ n, ∀ z ∈ M n,
      inner (𝕜 := ℝ) y z = 0 := by
    intro y hy n z hz
    set φ : ↥(M n) →L[ℝ] ℝ := (innerSL ℝ y).comp ((M n).subtypeL) with hφ
    have h1 : ∀ i : w n, φ (bb n i) = 0 := by
      intro i
      rw [hφ]
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerSL_apply_apply]
      rw [hbb n]
      exact hy ⟨n, i⟩
    have h2 : HasSum (fun i => (bb n).repr ⟨z, hz⟩ i • bb n i) ⟨z, hz⟩ :=
      (bb n).hasSum_repr ⟨z, hz⟩
    have h3 : HasSum (fun i => (bb n).repr ⟨z, hz⟩ i • φ (bb n i)) (φ ⟨z, hz⟩) := by
      simpa using h2.mapL φ
    have h4 : φ ⟨z, hz⟩ = 0 := by
      have h5 : HasSum (fun _ : w n => (0:ℝ)) (φ ⟨z, hz⟩) := by simpa [h1] using h3
      simpa using h5.unique hasSum_zero
    simpa [hφ] using h4
  have hbot : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ p, inner (𝕜 := ℝ) y (v p) = 0 := by
      intro p
      have hp := hy (v p) (Submodule.subset_span ⟨p, rfl⟩)
      rw [real_inner_comm]; exact hp
    have hle : ∀ n, M n ≤ (Submodule.span ℝ {y})ᗮ := by
      intro n x hx w hw
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [real_inner_smul_left, perp y hy' n x hx, mul_zero]
    have htop : (⊤ : Submodule ℝ E) ≤ (Submodule.span ℝ {y})ᗮ := by
      rw [← hspan]; exact iSup_le hle
    exact inner_self_eq_zero.mp
      (htop (Submodule.mem_top (x := y)) y (Submodule.mem_span_singleton_self y))
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat J
  let e : J ≃ ↥(Set.range f) := Equiv.ofInjective f hf
  have hv' : Orthonormal ℝ fun i : ↥(Set.range f) => v (e.symm i) :=
    hv.comp _ e.symm.injective
  have hrange : Set.range (fun i : ↥(Set.range f) => v (e.symm i)) = Set.range v := by
    rw [show (fun i : ↥(Set.range f) => v (e.symm i)) = (v ∘ e.symm) from rfl, Set.range_comp,
      e.symm.range_eq_univ, Set.image_univ]
  refine ⟨↥(Set.range f), inferInstance,
    HilbertBasis.mkOfOrthogonalEqBot hv' (by rw [hrange]; exact hbot), fun i => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact ⟨(e.symm i).1, hvmem (e.symm i)⟩

end Bases2

/-! ### Part A, optional item: the triple argument at an arbitrary orthonormal
basis

The work order asks, as an optional extra, whether the triple construction of
WO-6 — even coordinates, odd coordinates, diagonal — generalizes from the
standard basis of the separable space `PlufWO1.H` to an arbitrary orthonormal
basis, and so gives Proposition 2.3 in infinite-dimensional spaces that need
not be separable. It does, and cheaply, now that Part D supplies
basis-relative blocks: pair up the index set (any infinite index set admits
`ι ≃ ι × Bool`), and run the WO-6 triple against the paired basis. -/

section GeneralTriple

variable {κ : Type*}

omit [CompleteSpace E] in
/-- A vector all of whose coordinates in a Hilbert basis vanish is zero. -/
theorem eq_zero_of_repr_eq_zero (c : HilbertBasis κ ℝ E) {x : E}
    (h : ∀ p, c.repr x p = 0) : x = 0 := by
  apply c.repr.injective
  ext p
  simpa using h p

omit [CompleteSpace E] in
/-- The diagonal coordinate of a basis vector. -/
theorem repr_basis_apply_self (c : HilbertBasis κ ℝ E) (p : κ) :
    c.repr (c p) p = 1 := by
  rw [HilbertBasis.repr_apply_apply, real_inner_self_eq_norm_mul_norm, c.orthonormal.1 p]
  norm_num

omit [CompleteSpace E] in
/-- The off-diagonal coordinates of a basis vector. -/
theorem repr_basis_apply_ne (c : HilbertBasis κ ℝ E) {p q : κ} (h : q ≠ p) :
    c.repr (c p) q = 0 := by
  rw [HilbertBasis.repr_apply_apply]
  exact c.orthonormal.2 h

omit [CompleteSpace E] in
/-- A subspace containing every vector of a Hilbert basis is dense. -/
theorem topologicalClosure_eq_top_of_basis_mem (c : HilbertBasis κ ℝ E)
    (K : Submodule ℝ E) (h : ∀ p, c p ∈ K) : K.topologicalClosure = ⊤ := by
  have h1 : Submodule.span ℝ (Set.range c) ≤ K := by
    rw [Submodule.span_le]
    rintro y ⟨p, rfl⟩
    exact h p
  have h2 := Submodule.topologicalClosure_mono h1
  rw [c.dense_span] at h2
  exact top_le_iff.mp h2

omit [CompleteSpace E] in
/-- Basis vectors indexed inside `S` lie in the block of `S`. -/
theorem basis_mem_blockB (c : HilbertBasis κ ℝ E) (S : Set κ) {p : κ} (hp : p ∈ S) :
    c p ∈ blockB c S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨p, hp, rfl⟩)

variable {ι : Type*}

/-- The diagonal subspace attached to a Hilbert basis indexed by `ι × Bool`:
    the vectors whose two coordinates in each pair agree. -/
noncomputable def diagB (c : HilbertBasis (ι × Bool) ℝ E) : Submodule ℝ E :=
  ⨅ i : ι, LinearMap.ker ((innerSL ℝ (c (i, false) - c (i, true)) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ)

omit [CompleteSpace E] in
theorem mem_diagB (c : HilbertBasis (ι × Bool) ℝ E) (x : E) :
    x ∈ diagB c ↔ ∀ i : ι, c.repr x (i, false) = c.repr x (i, true) := by
  simp only [diagB, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left, sub_eq_zero,
    HilbertBasis.repr_apply_apply]

omit [CompleteSpace E] in
theorem isClosed_diagB (c : HilbertBasis (ι × Bool) ℝ E) :
    IsClosed (diagB c : Set E) := by
  have h : (diagB c : Set E)
      = ⋂ i : ι, {x : E | innerSL ℝ (c (i, false) - c (i, true)) x = 0} := by
    ext x
    simp [diagB, LinearMap.mem_ker]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_eq (innerSL ℝ (c (i, false) - c (i, true))).continuous continuous_const

/-- Proposition 2.3 in every real Hilbert space carrying a Hilbert basis
    indexed by a product `ι × Bool`: no nonempty proper filter of closed
    subspaces is prime. The triple is the WO-6 one, transported to the given
    basis: the `false` block, the `true` block, and the diagonal. -/
theorem no_prime_filter_of_hilbertBasis_prod_bool
    (c : HilbertBasis (ι × Bool) ℝ E) (π : Set (Submodule ℝ E))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ E) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ E, IsClosed (M : Set E) → IsClosed (N : Set E) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π) := by
  have hdiag : ∀ i : ι, c (i, false) + c (i, true) ∈ diagB c := by
    intro i
    rw [mem_diagB]
    intro j
    have h1 : c.repr (c (i, false) + c (i, true)) (j, false)
        = c.repr (c (i, false)) (j, false) + c.repr (c (i, true)) (j, false) := by
      simp [map_add]
    have h2 : c.repr (c (i, false) + c (i, true)) (j, true)
        = c.repr (c (i, false)) (j, true) + c.repr (c (i, true)) (j, true) := by
      simp [map_add]
    by_cases hj : j = i
    · subst hj
      rw [h1, h2, repr_basis_apply_self, repr_basis_apply_self,
        repr_basis_apply_ne c (by simp : ((j, false) : ι × Bool) ≠ (j, true)),
        repr_basis_apply_ne c (by simp : ((j, true) : ι × Bool) ≠ (j, false))]
      ring
    · rw [h1, h2, repr_basis_apply_ne c (by simp [hj] : ((j, false) : ι × Bool) ≠ (i, false)),
        repr_basis_apply_ne c (by simp : ((j, false) : ι × Bool) ≠ (i, true)),
        repr_basis_apply_ne c (by simp : ((j, true) : ι × Bool) ≠ (i, false)),
        repr_basis_apply_ne c (by simp [hj] : ((j, true) : ι × Bool) ≠ (i, true))]
  have hAmem : ∀ x ∈ blockB c {p : ι × Bool | p.2 = false}, ∀ i : ι,
      c.repr x (i, true) = 0 := by
    intro x hx i
    exact (mem_blockB_iff c _ x).mp hx (i, true) (by simp)
  have hBmem : ∀ x ∈ blockB c {p : ι × Bool | p.2 = true}, ∀ i : ι,
      c.repr x (i, false) = 0 := by
    intro x hx i
    exact (mem_blockB_iff c _ x).mp hx (i, false) (by simp)
  refine PlufWO6.not_prime_of_triple π hup hinf hbot hne
    (blockB c {p : ι × Bool | p.2 = false}) (blockB c {p : ι × Bool | p.2 = true}) (diagB c)
    (isClosed_blockB _ _) (isClosed_blockB _ _) (isClosed_diagB c) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    refine eq_zero_of_repr_eq_zero c (fun p => ?_)
    obtain ⟨i, bb⟩ := p
    cases bb
    · exact hBmem x hxB i
    · exact hAmem x hxA i
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxA, hxC⟩
    refine eq_zero_of_repr_eq_zero c (fun p => ?_)
    obtain ⟨i, bb⟩ := p
    cases bb
    · rw [(mem_diagB c x).mp hxC i]; exact hAmem x hxA i
    · exact hAmem x hxA i
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨hxB, hxC⟩
    refine eq_zero_of_repr_eq_zero c (fun p => ?_)
    obtain ⟨i, bb⟩ := p
    cases bb
    · exact hBmem x hxB i
    · rw [← (mem_diagB c x).mp hxC i]; exact hBmem x hxB i
  · refine topologicalClosure_eq_top_of_basis_mem c _ (fun p => ?_)
    obtain ⟨i, bb⟩ := p
    cases bb
    · exact Submodule.mem_sup_left (basis_mem_blockB c _ (by simp))
    · exact Submodule.mem_sup_right (basis_mem_blockB c _ (by simp))
  · refine topologicalClosure_eq_top_of_basis_mem c _ (fun p => ?_)
    obtain ⟨i, bb⟩ := p
    cases bb
    · exact Submodule.mem_sup_left (basis_mem_blockB c _ (by simp))
    · have h1 : c (i, false) + c (i, true) ∈
          blockB c {p : ι × Bool | p.2 = false} ⊔ diagB c :=
        Submodule.mem_sup_right (hdiag i)
      have h2 : c (i, false) ∈ blockB c {p : ι × Bool | p.2 = false} ⊔ diagB c :=
        Submodule.mem_sup_left (basis_mem_blockB c _ (by simp))
      simpa using sub_mem h1 h2
  · refine topologicalClosure_eq_top_of_basis_mem c _ (fun p => ?_)
    obtain ⟨i, bb⟩ := p
    cases bb
    · have h1 : c (i, false) + c (i, true) ∈
          blockB c {p : ι × Bool | p.2 = true} ⊔ diagB c :=
        Submodule.mem_sup_right (hdiag i)
      have h2 : c (i, true) ∈ blockB c {p : ι × Bool | p.2 = true} ⊔ diagB c :=
        Submodule.mem_sup_left (basis_mem_blockB c _ (by simp))
      simpa using sub_mem h1 h2
    · exact Submodule.mem_sup_left (basis_mem_blockB c _ (by simp))

/-- Pairing up an infinite index type. -/
theorem nonempty_equiv_prod_bool (ι : Type*) [Infinite ι] : Nonempty (ι ≃ ι × Bool) := by
  have h : Cardinal.mk (ι × Bool) = Cardinal.mk ι := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.mk_bool, Cardinal.lift_ofNat, Cardinal.lift_id']
    refine Cardinal.mul_eq_left (Cardinal.aleph0_le_mk ι) ?_ (by norm_num)
    exact le_trans (by norm_num) (Cardinal.aleph0_le_mk ι)
  exact (Cardinal.eq.mp h).map Equiv.symm

/-- A2, generalized (the optional item of the work order): Proposition 2.3
    holds in EVERY real Hilbert space with an infinite orthonormal basis —
    separability plays no role, so this covers non-separable
    infinite-dimensional spaces as well. -/
theorem no_prime_filter_of_infinite_hilbertBasis [Infinite ι]
    (b : HilbertBasis ι ℝ E) (π : Set (Submodule ℝ E))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ E, IsClosed (N : Set E) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ E) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ E, IsClosed (M : Set E) → IsClosed (N : Set E) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π) := by
  obtain ⟨e⟩ := nonempty_equiv_prod_bool ι
  obtain ⟨c, -⟩ := hilbertBasis_reindex b e
  exact no_prime_filter_of_hilbertBasis_prod_bool c π hup hinf hbot hne

end GeneralTriple

/-! ### Part E: the ω₁-recursion combinator -/

/-- E1 (probe R1). Under CH — supplied as an equinumerosity hypothesis on
    the type in question, never as an axiom — an enumeration of a type of
    size continuum by the countable ordinals. The universe lifting is
    handled inside: callers see only `Set.Iio (Ordinal.omega 1)`. -/
theorem exists_enumeration_of_CH {α : Type} (hcard : Cardinal.mk α = Cardinal.continuum)
    (hCH : Cardinal.continuum = Cardinal.aleph 1) :
    ∃ f : (Set.Iio (Ordinal.omega 1)) → α, Function.Surjective f := by
  have hCH0 : (Cardinal.continuum.{0}) = Cardinal.aleph.{0} 1 :=
    Cardinal.lift_inj.mp (by
      rw [Cardinal.lift_continuum, Cardinal.lift_aleph, Ordinal.lift_one]
      exact hCH)
  have h1 : Cardinal.mk (Set.Iio (Ordinal.omega 1)) = Cardinal.lift ((Ordinal.omega 1).card) :=
    Ordinal.mk_Iio_ordinal _
  rw [Ordinal.card_omega] at h1
  have h2 : Cardinal.aleph 1 = Cardinal.lift (Cardinal.aleph.{0} 1) := by
    rw [Cardinal.lift_aleph, Ordinal.lift_one]
  rw [h2, Cardinal.lift_lift, ← hCH0, ← hcard] at h1
  have h3 : Cardinal.mk (Set.Iio (Ordinal.omega 1)) = Cardinal.mk (ULift α) := by
    rw [Cardinal.mk_uLift]; exact h1
  obtain ⟨e⟩ := Cardinal.eq.mp h3
  exact ⟨fun i => (e i).down, fun a => ⟨e.symm (ULift.up a), by simp⟩⟩

/-- E2 (the combinator). Transfinite recursion over the countable ordinals
    producing a strictly increasing ω₁-chain. The caller supplies ONE step
    function (strictly increasing) and ONE bookkeeping map absorbing a
    countable family of earlier values; NO successor/limit case split is
    exposed. -/
theorem exists_omega1_chain {β : Type} [PartialOrder β]
    (step : β → β) (hstep : ∀ b, b < step b)
    (limit : (ℕ → β) → β) (hlimit : ∀ f : ℕ → β, ∀ n, f n ≤ limit f)
    (b₀ : β) :
    ∃ c : (Set.Iio (Ordinal.omega 1)) → β,
      ∀ i j : (Set.Iio (Ordinal.omega 1)), i < j → c i < c j := by
  classical
  set P : Ordinal → (ℕ → Ordinal) → Prop :=
    fun a g => (∀ n, g n < a) ∧ ∀ γ < a, ∃ n, g n = γ with hP
  have hex : ∀ a : Ordinal, 0 < a → a < Ordinal.omega 1 → ∃ g, P a g := by
    intro a hpos ha
    have hcount : (Set.Iio a).Countable := by
      rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one]
      have h := (Ordinal.isInitial_omega 1).card_lt_card (a := a)
      rw [Ordinal.card_omega] at h
      exact h.mpr ha
    obtain ⟨f, hf⟩ := hcount.exists_eq_range ⟨0, hpos⟩
    refine ⟨f, fun n => ?_, fun γ hγ => ?_⟩
    · have hmem : f n ∈ Set.Iio a := by rw [hf]; exact ⟨n, rfl⟩
      exact hmem
    · have hmem : γ ∈ Set.range f := by rw [← hf]; exact hγ
      obtain ⟨n, rfl⟩ := hmem
      exact ⟨n, rfl⟩
  set G : Ordinal → ℕ → Ordinal := fun a => if h : ∃ g, P a g then h.choose else fun _ => 0
    with hG
  have hGspec : ∀ a : Ordinal, (∃ g, P a g) → P a (G a) := by
    intro a h
    rw [hG]; simp only [dif_pos h]
    exact h.choose_spec
  set F : ∀ a : Ordinal, (∀ b, b < a → β) → β :=
    fun a ih => step (limit fun n => if h : G a n < a then ih (G a n) h else b₀) with hF
  set c : Ordinal → β := (inferInstanceAs (WellFoundedLT Ordinal)).wf.fix F with hc
  have hceq : ∀ a : Ordinal,
      c a = step (limit fun n => if h : G a n < a then c (G a n) else b₀) := by
    intro a
    rw [hc]
    exact WellFounded.fix_eq _ F a
  have hmono : ∀ a : Ordinal, a < Ordinal.omega 1 → ∀ γ < a, c γ < c a := by
    intro a ha γ hγ
    have hpos : 0 < a := (zero_le γ).trans_lt hγ
    have hspec := hGspec a (hex a hpos ha)
    obtain ⟨n, hn⟩ := hspec.2 γ hγ
    have hle : c γ ≤ limit fun n => if h : G a n < a then c (G a n) else b₀ := by
      have h2 := hlimit (fun n => if h : G a n < a then c (G a n) else b₀) n
      simpa [hn, hγ] using h2
    calc c γ ≤ _ := hle
      _ < step _ := hstep _
      _ = c a := (hceq a).symm
  exact ⟨fun i => c i.1, fun i j hij => hmono j.1 j.2 i.1 hij⟩

/-! ### Axiom audit -/

#print axioms no_prime_filter_finrank
#print axioms no_prime_filter_paper
#print axioms no_prime_filter_of_finrank_ge_two
#print axioms no_prime_filter_of_infinite_hilbertBasis
#print axioms exists_orthonormal_approx_eigenvectors_mem
#print axioms mem_blockB_iff_inner
#print axioms isClosed_essSpec
#print axioms essSpec_le_of_finCodim
#print axioms essSpec_subset_essSpec_compress
#print axioms tendsto_norm_proj_finiteDimensional_of_weaklyNull
#print axioms exists_orthonormal_approx_eigenvectors
#print axioms approx_eigen_span_spec
#print axioms mem_blockB_iff
#print axioms isClosed_blockB
#print axioms blockB_stdBasis_eq
#print axioms hilbertBasis_reindex
#print axioms exists_countable_hilbertBasis_of_decomposition
#print axioms exists_enumeration_of_CH
#print axioms exists_omega1_chain

end PlufWO9
