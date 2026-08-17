/-
  PlufWO7a.lean — Work Order 7a for the pluf project (Feldman–Wilce).

  THIS IS A SCOPING COMMISSION. Its primary deliverable is a REPORT, not a
  body of theorems. The Lean content below is a small set of PROBES:
  minimal statements whose purpose is to measure, by actually attempting
  them, what Mathlib supports for the remaining unverified mathematics of
  the series. Probes are cheap by design; a probe that fails is as
  informative as one that succeeds, and failure is an expected, reportable,
  non-defective outcome.

  TARGET (the mathematics WO-7 would have to verify, NOT contracted here):
    * Paper I, §5: ample subspaces; upward inheritance of ampleness; the
      escape lemma; the blocking lemma; Theorem 5.6 (a pluf with no round
      slices, under CH); the eccentricity-interval proposition.
    * Paper II, Theorem 5.4: a non-diagonalizable pluf, under CH.
    * Paper II, Propositions 5.5–5.6: the one-witness reduction and the
      coordinatizability of countable chains (gated out of WO-5 for want of
      `HilbertBasis` infrastructure).
    * Paper I, Proposition 2.3 in odd finite dimension (the Kochen–Specker
      route; a separate and probably small item).

  Those arguments need three bodies of infrastructure, and the probes are
  grouped accordingly:
    (P) essential spectrum: definition, closedness, invariance under
        finite-rank perturbation and under passage to a finite-codimension
        block, and a Weyl-sequence characterization;
    (Q) orthonormal bases as objects: assembly of a `HilbertBasis` from an
        orthogonal decomposition, reindexing along an equivalence,
        countability of orthonormal sets in a separable space, and
        basis-relative blocks;
    (R) transfinite recursion of length ω₁ with countable bookkeeping at
        limit stages, and CH as a hypothesis furnishing an ω₁-enumeration.

  Base: the WO-8 artifact (CI runs #1–#7 green, 133 theorems). Prior files
  must remain untouched and green.

  Toolchain: leanprover/lean4:v4.28.0, Mathlib pinned as in the repo.

  OUTCOME OF THIS COMMISSION (full report in `REPORT-WO7a.md`): probes P2,
  P3, P4, Q1, Q3, Q4, R1 and R2 are PROVED below. Probe Q2 is FALSE as
  stated; it is commented out, refuted by
  `hilbertBasis_nat_of_decomposition_false`, and replaced by the corrected
  form `exists_countable_hilbertBasis_of_decomposition`, which is proved.
  Probe P1 is a question about Mathlib's coverage and is answered in the
  docstring of `essSpec` below.

  Within group P the probes are stated in the order P4, P3, P2 (rather than
  P2, P3, P4) because P2 is proved *from* P3 and P4; the statements
  themselves are those of the work order.
-/
import RequestProject.PlufWO8

open Set

namespace PlufWO7a

/-! ### Group P — essential spectrum

Paper I §5 uses: the essential spectrum of a bounded self-adjoint operator;
that it is unchanged when the operator is compressed to a closed subspace of
finite codimension; that a point of it is approached by a Weyl sequence;
and that ampleness (two-sided accumulation of the essential spectrum at a
value) is inherited upward along the filter. -/

section EssentialSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- P1. Does Mathlib have an essential spectrum at all? If a definition
    exists (under any name — check `spectrum`, `IsCompactOperator`, Calkin
    algebra, Fredholm theory), state the probe against it. If not, supply
    the Weyl-sequence definition below and prove it CLOSED; report which
    route was taken and what a from-scratch development would cost.

    Weyl form: `λ ∈ essSpec T` iff there is a sequence of unit vectors
    tending weakly to 0 with `‖(T - λ) x_n‖ → 0`.

    ANSWER TO P1. Mathlib (this pin) has *no* essential spectrum, no Calkin
    algebra and no Fredholm theory: a search for `essentialSpectrum`,
    `Fredholm` or `Calkin` returns nothing but a TODO comment in
    `Mathlib/Analysis/Normed/Operator/Banach.lean` ("once mathlib has
    Fredholm operators"). What does exist is `spectrum`, `IsCompactOperator`
    and the compact-operator ideal, plus the full orthogonal-projection API.
    The Weyl-sequence definition below is therefore the route taken. -/
def essSpec (T : E →L[ℝ] E) : Set ℝ :=
  {lam | ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
    (∀ y : E, Filter.Tendsto (fun n => inner (𝕜 := ℝ) (x n) y) Filter.atTop (nhds 0)) ∧
    Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖) Filter.atTop (nhds 0)}

omit [CompleteSpace E] in
/-- P4 (probe). A weakly null sequence has norms of projections onto a
    fixed finite-dimensional subspace tending to 0. (Isolated because it is
    the technical core of P3 and may be the only genuinely missing piece.) -/
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
/-- The construction behind P3: a Weyl sequence for `T` at `lam` can be
    pushed into `Wᗮ` when `W` is finite-dimensional, by subtracting the
    projection onto `W` (which tends to `0` by P4) and renormalizing. -/
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

/-- P3 (probe; the load-bearing one for Paper I §5). Compression to a
    closed subspace of finite codimension does not shrink the essential
    spectrum: if `V` is closed with finite-dimensional orthocomplement and
    `lam ∈ essSpec T`, then `lam` belongs to the essential spectrum of the
    compression of `T` to `V`.

    (A Weyl sequence for `T` can be corrected by subtracting its projection
    onto the finite-dimensional `Vᗮ`, which tends to 0 in norm because the
    sequence tends weakly to 0 and `Vᗮ` is finite-dimensional. THIS is the
    step whose cost we most need measured.)

    NOTE. The self-adjointness hypothesis `hT` is not used: the argument
    works for any bounded operator. It is retained because the work order
    asked for it. -/
theorem essSpec_le_of_finCodim (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V : Submodule ℝ E) (hVc : IsClosed (V : Set E))
    (hfin : Module.Finite ℝ ↥Vᗮ) (lam : ℝ) (hlam : lam ∈ essSpec T) :
    ∃ x : ℕ → E, (∀ n, x n ∈ V) ∧ (∀ n, ‖x n‖ = 1) ∧
      Filter.Tendsto (fun n => ‖T (x n) - lam • x n‖) Filter.atTop (nhds 0) := by
  obtain ⟨x, hx1, hxw, hxT⟩ := hlam
  have hcV : CompleteSpace ↥V := hVc.completeSpace_coe
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_weyl_sequence_in_orthogonal T Vᗮ hfin lam x hx1 hxw hxT
  refine ⟨z, fun n => ?_, hz2, hz3⟩
  have := hz1 n
  rwa [Submodule.orthogonal_orthogonal] at this

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
/-- If, against every finite-dimensional subspace `W` and every tolerance
    `d`, there is a unit vector of `Wᗮ` moved less than `d` by `T - lam`,
    then there is an *orthonormal* sequence of approximate eigenvectors with
    prescribed tolerances. This is the engine of P2: each new vector is
    chosen orthogonal to the (finite-dimensional) span of its
    predecessors. -/
theorem exists_orthonormal_approx_eigenvectors (T : E →L[ℝ] E) (lam : ℝ)
    (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (H : ∀ W : Submodule ℝ E, Module.Finite ℝ ↥W → ∀ d : ℝ, 0 < d →
      ∃ v : E, v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d) :
    ∃ u : ℕ → E, Orthonormal ℝ u ∧ ∀ n, ‖T (u n) - lam • u n‖ < eps n := by
  classical
  have key : ∀ l : List E, ∃ v : E, v ∈ (Submodule.span ℝ {x | x ∈ l})ᗮ ∧ ‖v‖ = 1 ∧
      ‖T v - lam • v‖ < eps l.length := by
    intro l
    have hfin : Module.Finite ℝ ↥(Submodule.span ℝ {x | x ∈ l}) :=
      FiniteDimensional.span_of_finite ℝ l.finite_toSet
    exact H _ hfin _ (heps l.length)
  choose pick hpick1 hpick2 hpick3 using key
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
  refine ⟨u, ⟨fun n => hpick2 (L n), ?_⟩, fun n => ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact horth j i h
    · rw [real_inner_comm]; exact horth i j h
  · have h := hpick3 (L n)
    rwa [hLlen n] at h

omit [CompleteSpace E] in
/-- P2 (probe). The essential spectrum is closed. -/
theorem isClosed_essSpec (T : E →L[ℝ] E) : IsClosed (essSpec T) := by
  rw [← isSeqClosed_iff_isClosed]
  intro lams lam hmem hlim
  have H : ∀ W : Submodule ℝ E, Module.Finite ℝ ↥W → ∀ d : ℝ, 0 < d →
      ∃ v : E, v ∈ Wᗮ ∧ ‖v‖ = 1 ∧ ‖T v - lam • v‖ < d := by
    intro W hW d hd
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hlim) (d/2) (by linarith)
    obtain ⟨x, hx1, hxw, hxT⟩ := hmem k
    obtain ⟨z, hz1, hz2, hz3⟩ :=
      exists_weyl_sequence_in_orthogonal T W hW (lams k) x hx1 hxw hxT
    obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 hz3) (d/2) (by linarith)
    refine ⟨z m, hz1 m, hz2 m, ?_⟩
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
  obtain ⟨u, hu, hut⟩ :=
    exists_orthonormal_approx_eigenvectors T lam (fun n => 1/(n+1)) (fun n => by positivity) H
  refine ⟨u, fun n => hu.1 n, fun y => tendsto_inner_of_orthonormal hu y, ?_⟩
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hut n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end EssentialSpectrum

/-! ### Group Q — orthonormal bases as objects

Paper II Propositions 5.5–5.6 quantify over orthonormal bases; the WO-5
census reported the needed API absent. These probes measure exactly what is
missing. -/

section Bases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Q1 (probe). An orthonormal set in a separable space is countable. -/
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

/- Q2 (probe; the assembly step). Given a countable orthogonal
    decomposition of `E` into closed subspaces and an orthonormal basis of
    each piece, there is an orthonormal basis of `E` indexed by ℕ whose
    members lie in the pieces — the construction Proposition 5.6 needs to
    coordinatize a countable chain. State whatever weakened form is
    provable at reasonable cost and REPORT the gap between it and the form
    above.

    THIS PROBE IS FALSE AS STATED, so it is commented out here rather than
    deleted. An `ℕ`-indexed `HilbertBasis` forces `E` to be separable *and*
    infinite-dimensional, and neither follows from the hypotheses: take
    `E = ℝ`, `M 0 = ⊤`, `M n = ⊥` for `n ≠ 0`. See
    `hilbertBasis_nat_of_decomposition_false` for the refutation and
    `exists_countable_hilbertBasis_of_decomposition` for the corrected
    statement, which is proved.

theorem exists_hilbertBasis_of_decomposition
    (M : ℕ → Submodule ℝ E) (hMc : ∀ n, IsClosed ((M n : Set E)))
    (horth : Pairwise fun m n => ∀ x ∈ M m, ∀ y ∈ M n, inner (𝕜 := ℝ) x y = 0)
    (hspan : ⨆ n, M n = ⊤) :
    ∃ (b : HilbertBasis ℕ ℝ E), ∀ i, ∃ n, b i ∈ M n := by
  sorry
-/

/-- Refutation of Q2 as stated. The hypotheses of Q2 are satisfied by
    `E = ℝ` with `M 0 = ⊤` and `M n = ⊥` for `n ≠ 0`, yet `ℝ` admits no
    `ℕ`-indexed Hilbert basis (two members of an orthonormal family in `ℝ`
    would be orthogonal unit scalars). -/
theorem hilbertBasis_nat_of_decomposition_false :
    ∃ M : ℕ → Submodule ℝ ℝ, (∀ n, IsClosed ((M n : Set ℝ))) ∧
      (Pairwise fun m n => ∀ x ∈ M m, ∀ y ∈ M n, inner (𝕜 := ℝ) x y = 0) ∧
      (⨆ n, M n = ⊤) ∧ ¬ ∃ b : HilbertBasis ℕ ℝ ℝ, ∀ i, ∃ n, b i ∈ M n := by
  refine ⟨fun n => if n = 0 then ⊤ else ⊥, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases h : n = 0 <;> simp [h]
  · intro m n hmn x hx y hy
    by_cases hm : m = 0
    · have hn : n ≠ 0 := by rintro rfl; exact hmn hm
      simp only [hn, if_false, Submodule.mem_bot] at hy
      simp [hy]
    · simp only [hm, if_false, Submodule.mem_bot] at hx
      simp [hx]
  · exact le_antisymm le_top (le_iSup_of_le 0 (by simp))
  · rintro ⟨b, -⟩
    have h01 : inner (𝕜 := ℝ) (b 0) (b 1) = 0 := b.orthonormal.2 (by norm_num)
    have h0 : ‖b 0‖ = 1 := b.orthonormal.1 0
    have h1 : ‖b 1‖ = 1 := b.orthonormal.1 1
    simp only [RCLike.inner_apply, conj_trivial] at h01
    rcases mul_eq_zero.mp h01 with h | h <;> simp [h] at h0 h1

/-- Q2, corrected. For a separable Hilbert space with a countable
    orthogonal decomposition into closed subspaces there is a Hilbert basis,
    indexed by a countable type, each of whose members lies in one of the
    pieces. This is the form Paper II, Proposition 5.6 can use: the index
    type must be allowed to be an arbitrary countable type (it is `ℕ` only
    when `E` is infinite-dimensional), and separability of `E` is needed. -/
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
  -- a vector orthogonal to every `v p` is orthogonal to every piece, hence zero
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
      intro n x hx u hu
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [real_inner_smul_left, perp y hy' n x hx, mul_zero]
    have htop : (⊤ : Submodule ℝ E) ≤ (Submodule.span ℝ {y})ᗮ := by
      rw [← hspan]; exact iSup_le hle
    exact inner_self_eq_zero.mp
      (htop (Submodule.mem_top (x := y)) y (Submodule.mem_span_singleton_self y))
  -- reindex by a set of naturals, so that the index type lives in `Type`
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

/-- Q3 (probe). Reindexing a `HilbertBasis` along an equivalence of index
    types. Expected cheap; included to confirm. -/
theorem hilbertBasis_reindex {ι ι' : Type} (b : HilbertBasis ι ℝ E) (e : ι ≃ ι') :
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

/-- Q4 (probe). Basis-relative blocks: the closed span of a subfamily, with
    the coordinate characterization of membership. This is `PlufWO1.block`
    with the standard basis replaced by an arbitrary one; the probe measures
    whether the WO-1 machinery generalizes cheaply or must be rebuilt. -/
theorem mem_blockB_iff {ι : Type} (b : HilbertBasis ι ℝ E) (S : Set ι) (x : E) :
    x ∈ (Submodule.span ℝ (b '' S)).topologicalClosure ↔ ∀ i ∉ S, inner (𝕜 := ℝ) x (b i) = 0 := by
  have hfwd : ∀ y : E, y ∈ (Submodule.span ℝ (b '' S)).topologicalClosure →
      ∀ i ∉ S, inner (𝕜 := ℝ) y (b i) = 0 := by
    intro y hy i hi
    have hle : Submodule.span ℝ (b '' S) ≤ (Submodule.span ℝ {b i})ᗮ := by
      rw [Submodule.span_le]
      rintro z ⟨j, hj, rfl⟩
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨t, rfl⟩ := hu
      have hij : i ≠ j := fun hh => hi (hh ▸ hj)
      rw [real_inner_smul_left, b.orthonormal.2 hij, mul_zero]
    have hcl := Submodule.topologicalClosure_minimal _ hle
      (Submodule.isClosed_orthogonal (Submodule.span ℝ {b i}))
    have h2 := hcl hy (b i) (Submodule.mem_span_singleton_self _)
    rw [real_inner_comm] at h2
    exact h2
  refine ⟨hfwd x, fun h => ?_⟩
  set K := (Submodule.span ℝ (b '' S)).topologicalClosure with hK
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

end Bases

/-! ### Group R — transfinite recursion and CH

Both CH constructions are ω₁-length recursions in which the object built at
stage `α` must respect countably many constraints accumulated before `α`,
and in which CH supplies an ω₁-enumeration of the objects to be defeated. -/

section Transfinite

/-- R1 (probe). CH, as a hypothesis, yields an ω₁-enumeration of a set of
    cardinality continuum. State CH as `Cardinal.continuum = Cardinal.aleph 1`
    (or whatever spelling Mathlib prefers — report) and produce the
    enumeration.

    REPORT. Mathlib has no `ContinuumHypothesis` predicate; the spelling in
    the probe is the idiomatic one, and `𝔠 = ℵ₁` (notations `Cardinal.continuum`,
    `Cardinal.aleph 1`, with `ω₁ = Ordinal.omega 1` on the ordinal side) is
    what one states. The friction here is purely universe-theoretic: the
    hypothesis is stated at a universe of its own and the interval
    `Set.Iio ω₁` lives one universe up, so `Cardinal.lift_continuum`,
    `Cardinal.lift_aleph` and `Ordinal.mk_Iio_ordinal` are needed to line the
    cardinalities up. -/
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

/-- R2 (probe; the recursion pattern). A schematic ω₁-recursion: given a
    successor step and a limit step that consumes the countably many
    previous values, produce a chain indexed by the countable ordinals. The
    purpose is to measure how painful Mathlib's ordinal recursion is in
    practice, NOT to prove anything about plufs. Any faithful rendering of
    "build an increasing ω₁-chain by transfinite recursion, with countable
    bookkeeping at limits" is an acceptable answer to this probe; state what
    you actually managed and report the friction.

    REPORT. The recursion was done in the fully general form: no case split
    between successors and limits is needed. At every stage `a < ω₁` the set
    `Set.Iio a` is countable (`Cardinal.countable_iff_lt_aleph_one` together
    with `Ordinal.mk_Iio_ordinal` and `Ordinal.isInitial_omega`), so a
    single surjection `ℕ → Set.Iio a` feeds *all* previous values to
    `limit`, and one `step` on top of that makes the value strictly larger
    than every earlier one. `WellFounded.fix` over `Ordinal` and its
    unfolding lemma `WellFounded.fix_eq` are the only recursion tools
    used. -/
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

end Transfinite

/-! ### Group D — Paper I, Proposition 2.3 in odd finite dimension

Target (d) of the work order. It was not among the probes; it is added here
because measuring it changed its price. WO-6 proved Proposition 2.3 for the
paper's separable infinite-dimensional `H` (`PlufWO6.no_prime_filter`) via a
triple of subspaces pairwise meeting trivially and pairwise spanning, and
recorded that no such triple exists in odd finite dimension, where "the
Kochen–Specker route remains the only one we have". Mathlib has no
Kochen–Specker theorem, so that route would have been expensive.

It is not needed. In *finite* dimension a proper nonempty meet-closed
upward-closed family has a member of least dimension, and that member is
contained in every member; primeness applied to a pair of subspaces that
spans the whole space while neither contains a fixed nonzero vector of the
least member gives the contradiction directly. Dimension `≥ 2` suffices, and
parity plays no role. -/

section PrimeFilters

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
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

/-- D1. Proposition 2.3 in finite dimension: the lattice of subspaces of a
    real vector space of dimension at least two carries no prime filter. No
    Kochen–Specker input is used; `π.Nonempty` is the same minimal repair
    that WO-6 had to make to the printed statement. -/
theorem no_prime_filter_of_finrank_ge_two
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
  -- the member of least dimension is contained in every member
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

/-- D2. Target (d): Paper I, Proposition 2.3 in odd finite dimension, in the
    shape of `PlufWO6.no_prime_filter` (closedness hypotheses and the closed
    join). Oddness of `n` is not needed — the statement holds in every
    finite dimension `≥ 2` — but it is kept because it is the case the work
    order asks about. -/
theorem no_prime_filter_odd_finrank (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n)
    (π : Set (Submodule ℝ (EuclideanSpace ℝ (Fin n))))
    (hup : ∀ M ∈ π, ∀ N : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      IsClosed (N : Set (EuclideanSpace ℝ (Fin n))) → M ≤ N → N ∈ π)
    (hinf : ∀ M ∈ π, ∀ N ∈ π, M ⊓ N ∈ π)
    (hbot : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ∉ π)
    (hne : π.Nonempty) :
    ¬ (∀ M N : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        IsClosed (M : Set (EuclideanSpace ℝ (Fin n))) →
        IsClosed (N : Set (EuclideanSpace ℝ (Fin n))) →
        (M ⊔ N).topologicalClosure ∈ π → M ∈ π ∨ N ∈ π) := by
  intro hprime
  refine no_prime_filter_of_finrank_ge_two (V := EuclideanSpace ℝ (Fin n)) ?_ π ?_ hinf hbot hne ?_
  · simp only [finrank_euclideanSpace, Fintype.card_fin]
    omega
  · intro M hM N hMN
    exact hup M hM N (Submodule.closed_of_finiteDimensional N) hMN
  · intro M N hMN
    refine hprime M N (Submodule.closed_of_finiteDimensional M)
      (Submodule.closed_of_finiteDimensional N) ?_
    rwa [(Submodule.closed_of_finiteDimensional (M ⊔ N)).submodule_topologicalClosure_eq]

end PrimeFilters

/-! ### Deliverable

The REPORT is the deliverable. For each of P, Q, R it should state: what
Mathlib already provides (with names), which probes succeeded and at what
cost, which failed and why, what would have to be built from scratch, and an
estimate — in units of "commissions comparable to WO-2 through WO-8" — of
the cost of each of:

  (a) Paper II Propositions 5.5–5.6 (needs Q only);
  (b) Paper I §5 in full (needs P and R);
  (c) Paper II Theorem 5.4 (needs Q and R);
  (d) Paper I Proposition 2.3 in odd finite dimension (needs none of the
      above; a Kochen–Specker-style argument in finite dimension —
      estimate separately and say whether it is worth a small commission).

A recommended decomposition into future work orders, with a suggested
order, is the final item. If some target is judged infeasible at acceptable
cost, say so plainly: an honest "this one should stay hand-checked" is a
valuable answer and will be respected.

Probes that were not attempted should be listed as such rather than
silently omitted.

The report is in `REPORT-WO7a.md` at the root of the repository. -/

/-! ### Audited roll-up of the probes that were proved -/

#print axioms PlufWO7a.tendsto_norm_proj_finiteDimensional_of_weaklyNull
#print axioms PlufWO7a.exists_weyl_sequence_in_orthogonal
#print axioms PlufWO7a.essSpec_le_of_finCodim
#print axioms PlufWO7a.tendsto_inner_of_orthonormal
#print axioms PlufWO7a.exists_orthonormal_approx_eigenvectors
#print axioms PlufWO7a.isClosed_essSpec
#print axioms PlufWO7a.countable_of_orthonormal
#print axioms PlufWO7a.hilbertBasis_nat_of_decomposition_false
#print axioms PlufWO7a.exists_countable_hilbertBasis_of_decomposition
#print axioms PlufWO7a.hilbertBasis_reindex
#print axioms PlufWO7a.mem_blockB_iff
#print axioms PlufWO7a.exists_enumeration_of_CH
#print axioms PlufWO7a.exists_omega1_chain
#print axioms PlufWO7a.exists_pair_sup_top_notMem
#print axioms PlufWO7a.no_prime_filter_of_finrank_ge_two
#print axioms PlufWO7a.no_prime_filter_odd_finrank

end PlufWO7a
