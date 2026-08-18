/-
  PlufWO17/PartC.lean — Work Order 17, Part C: the model space.

  C1: Paper V, Lemma 6.1 — an exponential sum with `m` distinct exponents and a
      nonzero coefficient vector has fewer than `m` real zeros. Proved in the
      cardinality form `expSum_card_zeros_lt` (induction on the number of
      exponents, dividing by one exponential and applying Rolle) and delivered
      in the contracted negative form `expSum_zeros_lt`.
  C2: Paper V, Example 6.2 — the model space realizes every cofinite set.
  C3: the conditional consequence of Section 6.
-/
import RequestProject.PlufWO17.Basic

open Set

namespace PlufWO17

open PlufWO16 (supp toFun)

/-! ### C1: zeros of an exponential sum -/

/-- An exponential sum with exponent set `s` and coefficient function `a`. -/
noncomputable def expSum (s : Finset ℝ) (a : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ mu ∈ s, a mu * Real.exp (mu * x)

theorem hasDerivAt_expSum (s : Finset ℝ) (a : ℝ → ℝ) (x : ℝ) :
    HasDerivAt (expSum s a) (∑ mu ∈ s, a mu * mu * Real.exp (mu * x)) x := by
  have hmain : HasDerivAt (fun y : ℝ => ∑ mu ∈ s, a mu * Real.exp (mu * y))
      (∑ mu ∈ s, a mu * mu * Real.exp (mu * x)) x := by
    refine HasDerivAt.fun_sum fun mu _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => mu * y) mu x := by
      simpa using (hasDerivAt_id x).const_mul mu
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (mu * y)) (Real.exp (mu * x) * mu) x :=
      (Real.hasDerivAt_exp (mu * x)).comp x h1
    have h3 := h2.const_mul (a mu)
    convert h3 using 1
    ring
  exact hmain

/-- Rolle's theorem, in counting form: a differentiable function with `k` zeros
    has a derivative with at least `k - 1` zeros. -/
theorem exists_deriv_zeros (f f' : ℝ → ℝ) (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (Z : Finset ℝ) (hZ : ∀ z ∈ Z, f z = 0) :
    ∃ Z' : Finset ℝ, Z.card ≤ Z'.card + 1 ∧ ∀ z ∈ Z', f' z = 0 := by
  classical
  rcases Nat.eq_zero_or_pos Z.card with h0 | hpos
  · exact ⟨∅, by simp [h0], by simp⟩
  set n := Z.card with hn
  set g : Fin n ↪o ℝ := Z.orderEmbOfFin hn.symm with hg
  have hmem : ∀ i : Fin n, g i ∈ Z := fun i => Z.orderEmbOfFin_mem hn.symm i
  have hstep : ∀ i : Fin (n - 1), ∃ c : ℝ,
      g ⟨i, by omega⟩ < c ∧ c < g ⟨i + 1, by omega⟩ ∧ f' c = 0 := by
    intro i
    have hlt : g ⟨(i : ℕ), by omega⟩ < g ⟨(i : ℕ) + 1, by omega⟩ := by
      apply g.strictMono
      exact Fin.mk_lt_mk.2 (Nat.lt_succ_self _)
    have hcont : ContinuousOn f (Icc (g ⟨(i : ℕ), by omega⟩) (g ⟨(i : ℕ) + 1, by omega⟩)) :=
      fun x _ => (hderiv x).continuousAt.continuousWithinAt
    have heq : f (g ⟨(i : ℕ), by omega⟩) = f (g ⟨(i : ℕ) + 1, by omega⟩) := by
      rw [hZ _ (hmem _), hZ _ (hmem _)]
    obtain ⟨c, hc, hc0⟩ :=
      exists_hasDerivAt_eq_zero hlt hcont heq (fun x _ => hderiv x)
    exact ⟨c, hc.1, hc.2, hc0⟩
  choose c hc1 hc2 hc0 using hstep
  have hcmono : StrictMono c := by
    intro i j hij
    have h1 : c i < g ⟨(i : ℕ) + 1, by omega⟩ := hc2 i
    have h2 : g ⟨(i : ℕ) + 1, by omega⟩ ≤ g ⟨(j : ℕ), by omega⟩ := by
      apply g.monotone
      exact Fin.mk_le_mk.2 (by exact_mod_cast hij)
    have h3 : g ⟨(j : ℕ), by omega⟩ < c j := hc1 j
    linarith
  refine ⟨Finset.image c Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hcmono.injective, Finset.card_univ,
      Fintype.card_fin]
    omega
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact hc0 i

/-- C1, cardinality form (the form the induction supports; see the REPORT note
    at `expSum_zeros_lt`). An exponential sum whose exponent set `s` is
    nonempty and whose coefficients are nonzero on `s` has fewer than `#s`
    real zeros. -/
theorem expSum_card_zeros_lt (n : ℕ) : ∀ (s : Finset ℝ) (a : ℝ → ℝ),
    s.card = n → s.Nonempty → (∀ mu ∈ s, a mu ≠ 0) →
    ∀ Z : Finset ℝ, (∀ x ∈ Z, expSum s a x = 0) → Z.card < n := by
  classical
  induction n with
  | zero => intro s a hcard hne _ _ _; rw [Finset.card_eq_zero.1 hcard] at hne; simp at hne
  | succ n ih =>
    intro s a hcard hne ha Z hZ
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- a single exponent: the sum never vanishes
      subst hn0
      obtain ⟨mu, hmu⟩ := Finset.card_eq_one.1 hcard
      have hZempty : Z = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        have := hZ x hx
        rw [expSum, hmu, Finset.sum_singleton] at this
        exact (ha mu (by simp [hmu]))
          (by
            have hexp : Real.exp (mu * x) ≠ 0 := Real.exp_ne_zero _
            exact (mul_eq_zero.1 this).resolve_right hexp)
      simp [hZempty]
    · -- divide by one exponential and differentiate
      obtain ⟨mu1, hmu1⟩ := hne
      set s' : Finset ℝ := s.image (fun mu => mu - mu1) with hs'
      set a' : ℝ → ℝ := fun nu => a (nu + mu1) with ha'
      have hinj : Set.InjOn (fun mu => mu - mu1) ↑s := fun p _ q _ h => by
        simpa using sub_left_injective h
      have hcard' : s'.card = n + 1 := by
        rw [hs', Finset.card_image_of_injOn hinj, hcard]
      have hzero_mem : (0 : ℝ) ∈ s' := by
        rw [hs']
        exact Finset.mem_image.2 ⟨mu1, hmu1, by ring⟩
      have ha'ne : ∀ nu ∈ s', a' nu ≠ 0 := by
        intro nu hnu
        rw [hs', Finset.mem_image] at hnu
        obtain ⟨mu, hmu, rfl⟩ := hnu
        simpa [ha', sub_add_cancel] using ha mu hmu
      -- the divided sum has the same zeros
      have hGzero : ∀ x ∈ Z, expSum s' a' x = 0 := by
        intro x hx
        have : expSum s' a' x = Real.exp (-mu1 * x) * expSum s a x := by
          rw [hs', expSum, expSum, Finset.sum_image hinj, Finset.mul_sum]
          refine Finset.sum_congr rfl fun mu _ => ?_
          have hexp : Real.exp (-mu1 * x) * Real.exp (mu * x) = Real.exp ((mu - mu1) * x) := by
            rw [← Real.exp_add]
            ring_nf
          show a (mu - mu1 + mu1) * Real.exp ((mu - mu1) * x)
            = Real.exp (-mu1 * x) * (a mu * Real.exp (mu * x))
          rw [show mu - mu1 + mu1 = mu by ring, ← mul_assoc, mul_comm (Real.exp (-mu1 * x)) (a mu),
            mul_assoc, hexp]
        rw [this, hZ x hx, mul_zero]
      -- its derivative is an exponential sum with one exponent fewer
      set b : ℝ → ℝ := fun nu => a' nu * nu with hb
      have hderiv : ∀ x, HasDerivAt (expSum s' a') (expSum (s'.erase 0) b x) x := by
        intro x
        have h := hasDerivAt_expSum s' a' x
        have hsum : ∑ nu ∈ s', a' nu * nu * Real.exp (nu * x)
            = expSum (s'.erase 0) b x := by
          rw [expSum,
            Finset.sum_erase s' (f := fun nu => b nu * Real.exp (nu * x)) (by simp [hb])]
        rwa [hsum] at h
      obtain ⟨Z', hZ'card, hZ'⟩ :=
        exists_deriv_zeros (expSum s' a') (fun x => expSum (s'.erase 0) b x) hderiv Z hGzero
      have hcarderase : (s'.erase 0).card = n := by
        rw [Finset.card_erase_of_mem hzero_mem, hcard']
        omega
      have hne' : (s'.erase 0).Nonempty := by
        rw [← Finset.card_pos, hcarderase]
        exact hnpos
      have hbne : ∀ nu ∈ s'.erase 0, b nu ≠ 0 := by
        intro nu hnu
        exact mul_ne_zero (ha'ne nu (Finset.mem_of_mem_erase hnu))
          (Finset.ne_of_mem_erase hnu)
      have := ih (s'.erase 0) b hcarderase hne' hbne Z' hZ'
      omega

/-- C1 (Paper V, Lemma 6.1). An exponential sum with `m` distinct exponents and
    a nonzero coefficient vector has at most `m - 1` real zeros.

    REPORT (work order, Part C1: "state the conclusion in whichever form the
    induction supports … and REPORT the choice"). The induction is run in the
    cardinality form `expSum_card_zeros_lt` above — a `Finset` of exponents, a
    `Finset` of zeros, and the strict inequality `#Z < #s` — because the
    induction step discards a vanishing coefficient and erases an exponent, and
    both operations are `Finset` operations. The contracted negative form is
    derived from it here, and is what C2 consumes. -/
theorem expSum_zeros_lt (m : ℕ) (μ : Fin m → ℝ) (hμ : Function.Injective μ)
    (a : Fin m → ℝ) (ha : a ≠ 0) (t : Fin m → ℝ) (ht : Function.Injective t)
    (hz : ∀ i, ∑ k, a k * Real.exp (μ k * t i) = 0) :
    False := by
  classical
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (funext fun k => absurd k.isLt (by omega)) ha
    · exact h
  haveI : NeZero m := ⟨by omega⟩
  -- the exponent set, with the vanishing coefficients discarded
  set K : Finset (Fin m) := Finset.univ.filter (fun k => a k ≠ 0) with hK
  have hKne : K.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    apply ha
    funext k
    have : k ∉ K := by rw [hcon]; simp
    rw [hK] at this
    simpa using this
  set s : Finset ℝ := K.image μ with hs
  have hinj : Set.InjOn μ ↑K := fun p _ q _ h => hμ h
  have hcards : s.card = K.card := Finset.card_image_of_injOn hinj
  set c : ℝ → ℝ := fun x => a (Function.invFun μ x) with hc
  have hcmu : ∀ k : Fin m, c (μ k) = a k := by
    intro k
    rw [hc]
    simp [Function.leftInverse_invFun hμ k]
  have hcne : ∀ x ∈ s, c x ≠ 0 := by
    intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [hcmu k]
    rw [hK] at hk
    simpa using hk
  set Z : Finset ℝ := Finset.univ.image t with hZdef
  have hZcard : Z.card = m := by
    rw [hZdef, Finset.card_image_of_injective _ ht, Finset.card_univ, Fintype.card_fin]
  have hZzero : ∀ x ∈ Z, expSum s c x = 0 := by
    intro x hx
    rw [hZdef, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [expSum, hs, Finset.sum_image hinj]
    have : ∑ k ∈ K, c (μ k) * Real.exp (μ k * t i)
        = ∑ k, a k * Real.exp (μ k * t i) := by
      rw [hK]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hak : a k = 0
      · simp [hak]
      · simp [hak, hcmu k]
    rw [this, hz i]
  have hlt := expSum_card_zeros_lt s.card s c rfl (by
      rw [hs]
      exact hKne.image μ) hcne Z hZzero
  have hKle : K.card ≤ m := by simpa using Finset.card_le_univ K
  omega


/-! ### C2: the model space realizes every cofinite set -/

theorem geom_apply {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (n : ℕ) :
    (geom lam : ∀ _ : ℕ, ℝ) n = lam ^ n :=
  geom_apply' (by rw [abs_of_pos h0]; exact h1) n

/-- The dimension count of Example 6.2: evaluation at the `#S` points of `S` is
    a linear map from an `#S + 1`-dimensional coefficient space, so some nonzero
    coefficient vector is killed by it. -/
theorem exists_nonzero_vanishing (lam : ℕ → ℝ) (S : Finset ℕ) :
    ∃ a : Fin (S.card + 1) → ℝ, a ≠ 0 ∧ ∀ s ∈ S, ∑ i, a i * lam i ^ s = 0 := by
  classical
  set m := S.card + 1 with hm
  set L : (Fin m → ℝ) →ₗ[ℝ] (↥S → ℝ) :=
    { toFun := fun a s => ∑ i, a i * lam (i : ℕ) ^ (s : ℕ)
      map_add' := fun a b => by
        funext s
        simp only [Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := fun c a => by
        funext s
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring } with hL
  have hninj : ¬ Function.Injective L := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective (f := L) hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, Fintype.card_coe] at hle
    omega
  rw [Function.not_injective_iff] at hninj
  obtain ⟨u, v, huv, hne⟩ := hninj
  refine ⟨u - v, sub_ne_zero.2 hne, fun s hs => ?_⟩
  have hzero : L (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h2 := congrFun hzero ⟨s, hs⟩
  simp only [hL, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.zero_apply,
    sub_mul] at h2
  rw [Finset.sum_sub_distrib] at h2
  simpa [sub_mul, Finset.sum_sub_distrib] using h2

/-- C2 (Paper V, Example 6.2). For distinct `λ₁, …` in `(0,1)`, the closed span
    of the `geom (λ k)` realizes every cofinite subset of `ℕ` as a support.

    Proof (paper, rewritten): put `m = |S| + 1`. By C1 with `μ k = log (λ k)`,
    a nontrivial combination of `geom (λ 1), …, geom (λ m)` vanishes at no more
    than `m - 1` points of `ℕ`; in particular those vectors are independent, so
    their span has dimension `m`. Evaluation at the `m - 1` points of `S` is a
    linear map to `ℝ^(m-1)`, so some nonzero `x` in the span vanishes on `S`;
    having at least and at most `m - 1` zeros, its zero set is exactly `S`. -/
theorem exists_supp_compl_finite (lam : ℕ → ℝ)
    (hpos : ∀ k, 0 < lam k) (hlt : ∀ k, lam k < 1) (hinj : Function.Injective lam)
    (S : Finset ℕ) :
    ∃ x ∈ (Submodule.span ℝ (Set.range fun k => geom (lam k))).topologicalClosure,
      supp x = (↑S : Set ℕ)ᶜ := by
  classical
  set m := S.card + 1 with hm
  obtain ⟨a, ha0, haS⟩ := exists_nonzero_vanishing lam S
  set x : H := ∑ i : Fin m, a i • geom (lam (i : ℕ)) with hxdef
  have hxmem : x ∈ Submodule.span ℝ (Set.range fun k => geom (lam k)) :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i : ℕ), rfl⟩)
  have hcoord : ∀ n : ℕ, toFun x n = ∑ i : Fin m, a i * lam (i : ℕ) ^ n := by
    intro n
    rw [hxdef, map_sum]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show toFun (geom (lam (i : ℕ))) n = lam (i : ℕ) ^ n from
        geom_apply (hpos _) (hlt _) n]
  -- off `S` the combination cannot vanish: that would give `m` zeros
  have hkey : ∀ n : ℕ, n ∉ S → ∑ i : Fin m, a i * lam (i : ℕ) ^ n ≠ 0 := by
    intro n hn hcon
    set T : Finset ℕ := insert n S with hT
    have hTcard : T.card = m := by rw [hT, Finset.card_insert_of_notMem hn, hm]
    have hTzero : ∀ j ∈ T, ∑ i : Fin m, a i * lam (i : ℕ) ^ j = 0 := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hcon
      · exact haS j hj
    refine expSum_zeros_lt m (fun i => Real.log (lam (i : ℕ))) ?_ a ha0
      (fun i => ((T.orderEmbOfFin hTcard i : ℕ) : ℝ)) ?_ ?_
    · intro i j hij
      have h := congrArg Real.exp hij
      simp only [Real.exp_log (hpos (i : ℕ)), Real.exp_log (hpos (j : ℕ))] at h
      exact Fin.ext (hinj h)
    · intro i j hij
      simp only [Nat.cast_inj] at hij
      exact (T.orderEmbOfFin hTcard).injective hij
    · intro i
      have hmem : (T.orderEmbOfFin hTcard i : ℕ) ∈ T := T.orderEmbOfFin_mem hTcard i
      have := hTzero _ hmem
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm (Real.log (lam (k : ℕ))), Real.exp_nat_mul,
        Real.exp_log (hpos (k : ℕ))]
  refine ⟨x, Submodule.le_topologicalClosure _ hxmem, ?_⟩
  ext n
  simp only [PlufWO16.mem_supp_iff, mem_compl_iff, Finset.mem_coe]
  rw [show ((x : ∀ _ : ℕ, ℝ) n) = toFun x n from rfl, hcoord n]
  exact ⟨fun hne hnS => hne (haS n hnS), fun hnS => hkey n hnS⟩

/-! ### C3: the conditional consequence -/

/-- C3 (Paper V, Section 6, the conditional). Suppose the closed span above has
    no nonzero vector with infinitely many vanishing coordinates. Then its
    support family is `{∅} ∪ {cofinite sets}`; it has no minimal nonempty
    member; the sets containing no nonempty support are exactly the coinfinite
    sets, and among the subsets of `ℕ` these have no maximal element, so the
    conclusion of (SM) fails for the family. In particular the support family
    is the scrawl family of no circuit family.

    Deliver the last clause as the negation of `IsScrawlFamily`; the chain
    above is the argument. The hypothesis is Paper V's Question 9.3 and is
    supplied here, not proved. -/
theorem not_isScrawlFamily_of_cofiniteOnly (M : Submodule ℝ H)
    (hM : IsClosed (M : Set H))
    (hcof : ∀ x ∈ M, x ≠ 0 → (supp x)ᶜ.Finite)
    (hall : ∀ S : Finset ℕ, ∃ x ∈ M, supp x = (↑S : Set ℕ)ᶜ) :
    ¬ IsScrawlFamily (suppFamily M) := by
  classical
  rintro ⟨C, hC, -, hF⟩
  obtain ⟨c, hc⟩ := hC.nonempty
  obtain ⟨p, hp⟩ := hC.ne_empty c hc
  -- a circuit is a member of the family, hence a support, hence cofinite
  have hcF : c ∈ suppFamily M := by
    rw [hF]
    exact ⟨{c}, by simpa using hc, by simp⟩
  obtain ⟨x, hxM, hxs⟩ := hcF
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, PlufWO16.supp_zero] at hxs
    exact absurd (hxs ▸ hp : p ∈ (∅ : Set ℕ)) (by simp)
  have hfin : (supp x)ᶜ.Finite := hcof x hxM hx0
  -- so is the circuit with one point deleted, which is therefore also a member
  set S : Finset ℕ := hfin.toFinset ∪ {p} with hS
  have hScompl : (↑S : Set ℕ)ᶜ = c \ {p} := by
    have hScoe : (↑S : Set ℕ) = (supp x)ᶜ ∪ {p} := by
      rw [hS]
      simp
    rw [hScoe, Set.compl_union, compl_compl, hxs, Set.diff_eq]
  obtain ⟨y, hyM, hys⟩ := hall S
  have hmem : c \ {p} ∈ suppFamily M := ⟨y, hyM, by rw [hys, hScompl]⟩
  rw [hF] at hmem
  obtain ⟨D, hD, hDeq⟩ := hmem
  -- the deleted circuit is still cofinite, hence nonempty
  have hne : (c \ {p}).Nonempty := by
    rw [← hScompl]
    exact (S.finite_toSet.infinite_compl).nonempty
  rw [hDeq] at hne
  obtain ⟨z, hz⟩ := hne
  simp only [mem_iUnion, exists_prop] at hz
  obtain ⟨d, hdD, -⟩ := hz
  have hdsub : d ⊆ c \ {p} := by
    rw [hDeq]
    exact fun w hw => mem_biUnion hdD hw
  have hdc : d = c := hC.antichain d (hD hdD) c hc (fun w hw => (hdsub hw).1)
  exact (hdsub (hdc ▸ hp)).2 rfl

end PlufWO17
