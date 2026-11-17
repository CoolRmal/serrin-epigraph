module

public import SerrinEpigraph.RecoveryMinimality
public import SerrinEpigraph.FinitePerimeterMinimality
public import SerrinEpigraph.PlaneTiltTranslatedNontriviality
public import SerrinEpigraph.DiffuseTiltTranslatedConvergence
public import SerrinEpigraph.PerimeterLocality

/-!
# Moving-center phase compactness, perimeter minimality, and sharp planar limits

This file establishes the moving-center variational comparison and energy-identification
theorems (MC2–MC4 and SD4) without origin-centered curvature assumptions:
- transferring recovery bounds across annular agreement at moving centers,
- concentric-ball and open-set perimeter minimality against arbitrary measurable competitors,
- all-center sharp perimeter bounds under the planar energy bound, and
- simultaneous convergence of primitive gradient mass, rescaled phase energy, and diffuse tilt
  along any moving-center planar blowdown limit.
-/

public section
noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- A real sequence bounded above by `M` whose `ENNReal.ofReal` liminf is at least
`ENNReal.ofReal M` converges to `M`. -/
theorem tendsto_of_liminf_ofReal_ge_of_le {u : ℕ → ℝ} {M : ℝ}
    (hu0 : ∀ j, 0 ≤ u j)
    (hliminf : ENNReal.ofReal M ≤ liminf (fun j ↦ ENNReal.ofReal (u j)) atTop)
    (hle : ∀ j, u j ≤ M) :
    Tendsto u atTop (𝓝 M) := by
  apply tendsto_order.2
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ Eventually.of_forall fun j ↦ (hle j).trans_lt hb⟩
  by_cases ha0 : a < 0
  · exact Eventually.of_forall fun j ↦ ha0.trans_le (hu0 j)
  · have ha_nonneg : 0 ≤ a := not_lt.mp ha0
    have hMpos : 0 < M := ha_nonneg.trans_lt ha
    have hlt : ENNReal.ofReal a < liminf (fun j ↦ ENNReal.ofReal (u j)) atTop :=
      ((ENNReal.ofReal_lt_ofReal_iff hMpos).mpr ha).trans_le hliminf
    filter_upwards [eventually_lt_of_lt_liminf hlt] with j hj
    by_contra hju
    exact (not_le_of_gt hj) (ENNReal.ofReal_le_ofReal (not_lt.mp hju))

/-- A measurable compact perturbation of a locally finite-perimeter set that has finite
perimeter in an open neighborhood of the perturbation also has finite perimeter in every ball. -/
theorem variationalPerimeter_ball_ne_top_of_compact_perturbation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D K Ω : Set (Space d)}
    (hD : MeasurableSet D)
    (hPE : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D))
    (hDΩ : variationalPerimeter b D Ω ≠ ⊤) (n : ℕ) :
    variationalPerimeter b D (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨V, hVo, hWV, hVΩ, _⟩ := exists_open_between_and_isCompact_closure hWc hΩ hWΩ
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVo isClosed_closure hWV
  have hχval (x : Space d) : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
  have hχΩ : tsupport χ ⊆ Ω := by
    change closure (Function.support χ) ⊆ Ω
    rwa [hχsupport]
  have hbound : variationalPerimeter b D (ball 0 ((n : ℝ) + 1)) ≤
      variationalPerimeter b D Ω + variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) := by
    unfold variationalPerimeter
    refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
      iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
    let F₁ : Space d → Space d := fun x ↦ χ x • F x
    let F₂ : Space d → Space d := fun x ↦ (1 - χ x) • F x
    have hF₁ : ContDiff ℝ 1 F₁ := hχsmooth.smul hF
    have hF₂ : ContDiff ℝ 1 F₂ := (contDiff_const.sub hχsmooth).smul hF
    have hs₁K : tsupport F₁ ⊆ tsupport F := tsupport_smul_subset_right χ F
    have hs₂K : tsupport F₂ ⊆ tsupport F := tsupport_smul_subset_right (fun x ↦ 1 - χ x) F
    have hc₁ : HasCompactSupport F₁ := hc.of_isClosed_subset (isClosed_tsupport _) hs₁K
    have hc₂ : HasCompactSupport F₂ := hc.of_isClosed_subset (isClosed_tsupport _) hs₂K
    have hs₁Ω : tsupport F₁ ⊆ Ω := (tsupport_smul_subset_left χ F).trans hχΩ
    have hs₂B : tsupport F₂ ⊆ ball 0 ((n : ℝ) + 1) := hs₂K.trans hs
    have hu₁ (x : Space d) : ‖F₁ x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (hχval x).1]
      exact (mul_le_mul_of_nonneg_left (hunit x) (hχval x).1).trans
        (by simpa only [mul_one] using (hχval x).2)
    have hu₂ (x : Space d) : ‖F₂ x‖ ≤ 1 := by
      have h1χ : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχval x).2
      have h1χ_le : 1 - χ x ≤ 1 := sub_le_self 1 (hχval x).1
      rw [norm_smul, Real.norm_of_nonneg h1χ]
      exact (mul_le_mul_of_nonneg_left (hunit x) h1χ).trans (by simpa only [mul_one] using h1χ_le)
    have hFsum : F = fun x ↦ F₁ x + F₂ x := by
      funext x
      simp only [F₁, F₂, ← add_smul, add_sub_cancel, one_smul]
    have hdiv (x : Space d) :
        fieldDivergence b F x = fieldDivergence b F₁ x + fieldDivergence b F₂ x := by
      have hd : fderiv ℝ F x = fderiv ℝ F₁ x + fderiv ℝ F₂ x := by
        rw [hFsum]
        exact fderiv_add (hF₁.differentiable_one x) (hF₂.differentiable_one x)
      simp only [fieldDivergence, hd, add_apply, inner_add_right,
        Finset.sum_add_distrib]
    have hint_eq (A : Set (Space d)) (G : Space d → Space d)
        (hGs : tsupport G ⊆ tsupport F) :
        (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x) =
          ∫ x in tsupport F, A.indicator (fieldDivergence b G) x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [fieldDivergence_zero_of_notMem_tsupport b G (fun hh ↦ hx (hGs hh)), mul_zero]]
      refine setIntegral_congr_fun hc.measurableSet fun x _ ↦ ?_
      by_cases hxA : x ∈ A <;> simp [hxA]
    have hi₁ : IntegrableOn (D.indicator (fieldDivergence b F₁)) (tsupport F) :=
      ((fieldDivergence_continuous b hF₁).continuousOn.integrableOn_compact hc).indicator hD
    have hi₂ : IntegrableOn (D.indicator (fieldDivergence b F₂)) (tsupport F) :=
      ((fieldDivergence_continuous b hF₂).continuousOn.integrableOn_compact hc).indicator hD
    have hsplit : (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x) +
        (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x) := by
      rw [hint_eq D F subset_rfl, hint_eq D F₁ hs₁K, hint_eq D F₂ hs₂K, ← integral_add hi₁ hi₂]
      refine setIntegral_congr_fun hc.measurableSet fun x _ ↦ ?_
      by_cases hxD : x ∈ D <;> simp [hxD, hdiv x]
    have hF₂_DE : (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x) =
        ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x := by
      apply integral_congr_ae
      filter_upwards [hED] with x hx
      by_cases hxK : x ∈ K
      · have hxnot : x ∉ tsupport F₂ := by
          rw [notMem_tsupport_iff_eventuallyEq]
          filter_upwards [hWo.mem_nhds (hKW hxK)] with y hy
          have h1 : χ y = 1 := (hχone y).mp (subset_closure hy)
          simp [F₂, h1]
        simp [fieldDivergence_zero_of_notMem_tsupport b F₂ hxnot]
      · have heq := hx hxK
        by_cases hxE : x ∈ E
        · simp [hxE, heq.mp hxE]
        · have hxD : x ∉ D := fun hh ↦ hxE (heq.mpr hh)
          simp [hxE, hxD]
    rw [hsplit, hF₂_DE]
    calc
      ENNReal.ofReal ‖(∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x) +
          ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖ ≤
        ENNReal.ofReal (‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x‖ +
          ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ENNReal.ofReal ‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₁ x‖ +
          ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F₂ x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ (⨆ (G : Space d → Space d) (_ : ContDiff ℝ 1 G) (_ : HasCompactSupport G)
            (_ : tsupport G ⊆ Ω) (_ : ∀ x, ‖G x‖ ≤ 1),
            ENNReal.ofReal ‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x‖) +
          (⨆ (G : Space d → Space d) (_ : ContDiff ℝ 1 G) (_ : HasCompactSupport G)
            (_ : tsupport G ⊆ ball 0 ((n : ℝ) + 1)) (_ : ∀ x, ‖G x‖ ≤ 1),
            ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x‖) :=
        add_le_add
          (le_iSup_of_le F₁ (le_iSup_of_le hF₁ (le_iSup_of_le hc₁
            (le_iSup_of_le hs₁Ω (le_iSup_of_le hu₁ le_rfl)))))
          (le_iSup_of_le F₂ (le_iSup_of_le hF₂ (le_iSup_of_le hc₂
            (le_iSup_of_le hs₂B (le_iSup_of_le hu₂ le_rfl)))))
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hDΩ, hPE n⟩) hbound

/-- Concentric-ball minimality for a locally finite-perimeter set implies open-set minimality
against every measurable compact perturbation, without assuming local finiteness of the
competitor in advance. -/
theorem perimeter_open_minimality_of_concentric_ball_comparison {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E D K Ω : Set (Space d)}
    (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hPE : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    (hmin : ∀ s r : ℝ, 0 < s → r < s →
      (∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r), x ∈ E ↔ x ∈ D) →
      variationalPerimeter b E (ball 0 s) ≤ variationalPerimeter b D (ball 0 s))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter b E Ω ≤ variationalPerimeter b D Ω := by
  by_cases hDΩ : variationalPerimeter b D Ω = ⊤
  · rw [hDΩ]
    exact le_top
  · exact perimeter_minimality_of_concentric_ball_comparison b hE hD hPE
      (variationalPerimeter_ball_ne_top_of_compact_perturbation b hD hPE hK hΩ hKΩ hED hDΩ)
      hmin hK hΩ hKΩ hED

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Weighted variational perimeter on any test domain inside a compact set `K` is bounded by
the liminf of the primitive gradient mass of any normalized locally Lipschitz sequence
converging in `L¹(K)` to the phase indicator. -/
theorem RigidityHypotheses.perimeter_le_competitor_primitive_mass_liminf
    {d : ℕ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {v : ℕ → Space d → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E K Ω : Set (Space d)} (hE : MeasurableSet E) (hK : IsCompact K) (hΩ : Ω ⊆ K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0)) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter b E Ω ≤
      liminf (fun j ↦ ENNReal.ofReal
        (∫ x in K, ‖gradient (fun y ↦ phasePrimitive f (v j y)) x‖)) atTop := by
  unfold variationalPerimeter
  simp_rw [ENNReal.mul_iSup]
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
    iSup_le fun hs ↦ iSup_le fun hb ↦ ?_
  have hsub : tsupport F ⊆ K := hs.trans hΩ
  have hcont := fieldDivergence_continuous b hF
  have hsupport : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hcompact : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have hp (j : ℕ) : LocallyLipschitz (fun x ↦ phasePrimitive f (v j x)) :=
    hr.phasePrimitive_comp_locallyLipschitz h (hv j) (hval j)
  have hptest := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict K)
    (fun j x ↦ phasePrimitive f (v j x)) (E.indicator (fun _ ↦ phasePrimitive f 1))
    (fieldDivergence b F) C
    (fun j ↦ (hp j).continuous.continuousOn.integrableOn_compact hK)
    ((continuousOn_const.integrableOn_compact hK).indicator hE)
    hcont.aestronglyMeasurable hC
    (hr.competitorPrimitive_integral_limit h hv hval hE hK ht)
  have hrestrict : (∫ x in K,
      E.indicator (fun _ ↦ phasePrimitive f 1) x * fieldDivergence b F x) =
      ∫ x, E.indicator (fun _ ↦ phasePrimitive f 1) x * fieldDivergence b F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fieldDivergence_zero_of_notMem_tsupport b F (fun hh ↦ hx (hsub hh)), mul_zero]
  have hlim := ENNReal.tendsto_ofReal hptest.norm
  rw [hrestrict, ofReal_norm_integral_weighted_indicator volume E (fieldDivergence b F)
    (hr.phasePrimitive_one_pos h).le] at hlim
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun j ↦ ENNReal.ofReal_le_ofReal
    (norm_setIntegral_mul_divergence_le_gradient_of_locallyLipschitz b (hp j)
      (fun x ↦ h.phasePrimitive_mem_Icc (hval j x)) hF hc hK hsub hb))

/-- Weighted variational perimeter on any test domain inside a compact set `K` is bounded by
the liminf of the rescaled diffuse energy of any normalized locally Lipschitz sequence. -/
theorem RigidityHypotheses.perimeter_le_competitor_energy_liminf
    {d : ℕ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {v : ℕ → Space d → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E K Ω : Set (Space d)} (hE : MeasurableSet E) (hK : IsCompact K) (hΩ : Ω ⊆ K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0)) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter b E Ω ≤
      liminf (fun j ↦ ENNReal.ofReal
        (∫ x in K, rescaledPhaseEnergyDensity f (R j) (v j) x)) atTop :=
  (hr.perimeter_le_competitor_primitive_mass_liminf h b hv hval hE hK hΩ ht).trans
    (liminf_le_liminf (Eventually.of_forall fun j ↦ ENNReal.ofReal_le_ofReal
      (hr.competitorPrimitive_gradient_integral_le_energy h (hv j) (hval j) (hR j) hK)))

/-- Moving-center inner-ball energy comparison with vanishing annular gluing error. -/
theorem RigidityHypotheses.translated_exists_inner_energy_comparison_error
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {v : ℕ → Space (m + 1) → ℝ} {z : Space (m + 1) → ℝ}
    (hv : ∀ j, LocallyLipschitz (v j)) (hvval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {r t B : ℝ} (hradius : 0 < r) (ht : 0 < t)
    (hz : IntegrableOn z (closedBall 0 (r + t) \ ball 0 r))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    (hEB : ∀ j,
      (∫ x in closedBall 0 (r + t) \ ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x) +
      (∫ x in closedBall 0 (r + t) \ ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B)
    (hUz : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t) \ ball 0 r,
      ‖zeroExtension g u (c j + R j • x) - z x‖) atTop (𝓝 0))
    (hvz : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t) \ ball 0 r,
      ‖v j x - z x‖) atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ j,
      (∫ x in ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x) ≤
      (∫ x in closedBall 0 (r + t), rescaledPhaseEnergyDensity f (R j) (v j) x) + ε j := by
  have hU : ∀ j, LocallyLipschitz (fun y ↦ zeroExtension g u (c j + R j • y)) :=
    fun j ↦ locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUval : ∀ j x, zeroExtension g u (c j + R j • x) ∈ Icc (0 : ℝ) 1 :=
    fun _ _ ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  obtain ⟨η, ε, he, hη⟩ := hr.exists_annular_gluing_sequence h hU hv hUval hvval
    hradius ht hz hR hRtop hEB hUz hvz
  refine ⟨ε, he, fun j ↦ ?_⟩
  obtain ⟨hd, _, hs, hone, hval, hcomp⟩ := hη j
  exact hr.translated_inner_energy_le_of_glued_comparison h (c j)
    (zero_lt_one.trans_le (hR j)) ht.le (hv j) hd.locallyLipschitz (hvval j) hval
    (hs.trans ball_subset_closedBall) hone hcomp

/-- Moving-center version of `perimeter_le_recovery_bound_of_annular_agreement`: a recovery
sequence for a competitor agreeing with a moving-center blowdown limit on an annulus bounds
the limiting phase perimeter on every strictly smaller ball. -/
theorem RigidityHypotheses.translated_perimeter_le_recovery_bound_of_annular_agreement
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {r t a : ℝ} (hradius : 0 < r) (ht : 0 < t) (har : a < r)
    (c : ℕ → Space (m + 1)) {R B : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hagree : ∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (c j + R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hvlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖v j x - D.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hvbound : ∀ j, (∫ x in closedBall 0 (r + t),
      rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B j)
    {M : ℝ} (hBt : Tendsto B atTop (𝓝 M)) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter basis E (ball 0 a) ≤
      ENNReal.ofReal M := by
  let U : ℕ → Space (m + 1) → ℝ := fun j x ↦ zeroExtension g u (c j + R j • x)
  let K : Set (Space (m + 1)) := closedBall 0 (r + t)
  let S : Set (Space (m + 1)) := K \ ball 0 r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUval (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRpos (j : ℕ) : 0 < R j := zero_lt_one.trans_le (hR j)
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hiD : IntegrableOn (D.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hD
  have hUi (j : ℕ) := ((hU j).continuous.continuousOn.integrableOn_compact hK).sub hiE
  have hvi (j : ℕ) := ((hv j).continuous.continuousOn.integrableOn_compact hK).sub hiD
  have hUz := integral_norm_sub_tendsto_of_subset (show S ⊆ K from sdiff_subset)
    (fun j ↦ (hUi j).norm) hUlim
  have hvz := integral_norm_sub_tendsto_of_subset (show S ⊆ K from sdiff_subset)
    (fun j ↦ (hvi j).norm) hvlim
  have hsame (x : Space (m + 1)) (hx : x ∈ S) :
      E.indicator (fun _ ↦ (1 : ℝ)) x = D.indicator (fun _ ↦ (1 : ℝ)) x := by
    by_cases hxE : x ∈ E
    · simp only [indicator_of_mem hxE, indicator_of_mem ((hagree x hx).mp hxE)]
    · have hxD : x ∉ D := fun hh ↦ hxE ((hagree x hx).mpr hh)
      simp only [indicator_of_notMem hxE, indicator_of_notMem hxD]
  have hvz' : Tendsto (fun j ↦ ∫ x in S,
      ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    convert hvz using 1
    funext j
    exact setIntegral_congr_fun (μ := volume) (hK.measurableSet.diff measurableSet_ball)
      (fun x hx ↦ by rw [hsame x hx])
  obtain ⟨M₀, hM₀⟩ := hBt.bddAbove_range
  have hEB (j : ℕ) :
      (∫ x in S, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in S, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ L * (r + t) ^ m + M₀ := by
    have hiU := h.integrableOn_rescaledPhaseEnergy (hU j) (hUval j) (R j) hK
    have hiv := h.integrableOn_rescaledPhaseEnergy (hv j) (hval j) (R j) hK
    have hEU := setIntegral_mono_set hiU
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hUval j)))
      (Eventually.of_forall (show S ⊆ K from sdiff_subset))
    have hEv := setIntegral_mono_set hiv
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hval j)))
      (Eventually.of_forall (show S ⊆ K from sdiff_subset))
    exact add_le_add
      (hEU.trans (hr.translated_rescaled_energy_le_surface_bound h hbound (c j) (hRpos j)
        (add_pos hradius ht)))
      (hEv.trans ((hvbound j).trans (hM₀ (mem_range_self j))))
  obtain ⟨ε, hεt, hcomp⟩ := hr.translated_exists_inner_energy_comparison_error h c hv hval
    hradius ht (hiE.mono_set sdiff_subset) hR hRtop hEB hUz hvz'
  have hsmall : closedBall (0 : Space (m + 1)) a ⊆ K :=
    closedBall_subset_closedBall (by linarith)
  have hUsmall := integral_norm_sub_tendsto_of_subset hsmall (fun j ↦ (hUi j).norm) hUlim
  apply (hr.perimeter_le_competitor_energy_liminf h basis hRpos hU hUval hE
    (isCompact_closedBall 0 a) ball_subset_closedBall hUsmall).trans
  apply liminf_ofReal_le_of_comparison _ hBt hεt
  intro j
  have hi := (h.integrableOn_rescaledPhaseEnergy (hU j) (hUval j) (R j)
    (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have he := setIntegral_mono_set hi
    (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hUval j)))
    (Eventually.of_forall (closedBall_subset_ball har))
  exact he.trans ((hcomp j).trans (add_le_add (hvbound j) le_rfl))

/-- General finite-perimeter recovery and annular gluing bound any moving-center blowdown
limit's interior perimeter by a measurable competitor's larger-ball perimeter. -/
theorem RigidityHypotheses.translated_limiting_perimeter_le_measurable_competitor
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {r t a s : ℝ} (hradius : 0 < r) (ht : 0 < t) (har : a < r) (hrts : r + t < s)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (c j + R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hagree : ∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ D) :
    variationalPerimeter basis E (ball 0 a) ≤ variationalPerimeter basis D (ball 0 s) := by
  by_cases htop : variationalPerimeter basis D (ball 0 s) = ⊤
  · rw [htop]
    exact le_top
  have hP : variationalPerimeter basis D (ball 0 s) ≤
      ENNReal.ofReal (variationalPerimeter basis D (ball 0 s)).toReal := by
    rw [ENNReal.ofReal_toReal htop]
  obtain ⟨n, v, B, _, hnt, hv, hval, hvlim, hvbound, hBt⟩ :=
    hr.exists_finitePerimeter_recovery h basis hD hrts ENNReal.toReal_nonneg hP R
      (fun j ↦ zero_lt_one.trans_le (hR j)) hRt
  have he := hr.translated_perimeter_le_recovery_bound_of_annular_agreement h hbound basis
    hradius ht har (fun j ↦ c (n j)) (fun j ↦ hR (n j)) (hRt.comp hnt) hv hval hE hD
    hagree (hUlim.comp hnt) hvlim hvbound hBt
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal htop] at he
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp he

/-- Any moving-center blowdown limit under an all-center surface bound minimizes perimeter
against every measurable competitor agreeing with it outside a strictly smaller concentric
closed ball. -/
theorem RigidityHypotheses.translated_limiting_phase_perimeter_minimality
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {s r₀ : ℝ} (hs : 0 < s) (hr₀ : r₀ < s)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (c j + R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hagree : ∀ x ∈ ball 0 s \ closedBall 0 r₀, x ∈ E ↔ x ∈ D) :
    variationalPerimeter basis E (ball 0 s) ≤ variationalPerimeter basis D (ball 0 s) := by
  unfold variationalPerimeter at ⊢
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
    iSup_le fun hFs ↦ iSup_le fun hunit ↦ ?_
  obtain ⟨a, has, hFa⟩ := exists_lt_subset_ball (isClosed_tsupport F) hFs
  obtain ⟨r, hlow, hrs⟩ := exists_between (max_lt has (max_lt hs hr₀))
  have har : a < r := (le_max_left _ _).trans_lt hlow
  have hrpos : 0 < r := (le_max_left 0 r₀).trans (le_max_right a (max 0 r₀)) |>.trans_lt hlow
  have hr₀r : r₀ < r := (le_max_right 0 r₀).trans (le_max_right a (max 0 r₀)) |>.trans_lt hlow
  let t := (s - r) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hrts : r + t < s := by dsimp [t]; linarith
  have hsmall : closedBall (0 : Space (m + 1)) (r + t) ⊆ ball 0 s :=
    closedBall_subset_ball hrts
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ)))
      (closedBall 0 s) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).indicator hE
  have hUc (j : ℕ) : Continuous (fun x ↦ zeroExtension g u (c j + R j • x)) :=
    (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz
      (c j) (R j)).continuous
  have hlim := integral_norm_sub_tendsto_of_subset (hsmall.trans ball_subset_closedBall)
    (fun j ↦ (((hUc j).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).sub hiE).norm) hUlim
  have hcomp := hr.translated_limiting_perimeter_le_measurable_competitor h hbound basis
    hrpos ht har hrts c hR hRt hE hD hlim (fun x hx ↦ hagree x ⟨hsmall hx.1,
      fun hx₀ ↦ hx.2 (closedBall_subset_ball hr₀r hx₀)⟩)
  apply le_trans _ hcomp
  unfold variationalPerimeter
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hc
    (le_iSup_of_le hFa (le_iSup_of_le hunit le_rfl))))

/-- Concentric-ball measurable-competitor perimeter minimality up to null sets for any
moving-center blowdown limit under an all-center surface-energy bound. -/
theorem RigidityHypotheses.translated_limiting_phase_perimeter_minimality_ae
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {s r₀ : ℝ} (hs : 0 < s) (hr₀ : r₀ < s)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (c j + R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hagree : ∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀), x ∈ E ↔ x ∈ D) :
    variationalPerimeter basis E (ball 0 s) ≤ variationalPerimeter basis D (ball 0 s) := by
  let A := ball (0 : Space (m + 1)) s \ closedBall 0 r₀
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  let E' := (E \ A) ∪ (D ∩ A)
  have hE' : MeasurableSet E' := (hE.diff hA).union (hD.inter hA)
  have hEE' : E =ᵐ[volume] E' := by
    have ha : ∀ᵐ x ∂volume, x ∈ A → (x ∈ E ↔ x ∈ D) := (ae_restrict_iff' hA).mp hagree
    filter_upwards [ha] with x hx
    apply propext
    by_cases hxA : x ∈ A
    · simpa only [E', mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_true_eq_false,
        and_false, and_true, false_or] using hx hxA
    · simp only [E', mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_false_eq_true,
        and_true, and_false, or_false]
  have hlimE' : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (c j + R j • x) - E'.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    convert hUlim using 1
    funext j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (phaseIndicator_congr_ae hEE')] with x hx
    rw [hx]
  rw [variationalPerimeter_congr_ae basis hEE']
  apply hr.translated_limiting_phase_perimeter_minimality h hbound basis hs hr₀ c hR hRt
    hE' hD hlimE'
  intro x hx
  have hxA : x ∈ A := hx
  simp only [E', mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_true_eq_false,
    and_false, and_true, false_or]

/-- An all-center surface-energy bound controls rescaled energy on every ball `closedBall z r`
in translated dilation coordinates, via the shifted physical center `c₀ + R • z`. -/
theorem RigidityHypotheses.translated_rescaled_energy_closedBall_le_surface_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (c₀ z : Space (m + 1)) {R r : ℝ} (hR : 0 < R) (hradius : 0 < r) :
    (∫ x in closedBall z r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c₀ + R • y)) x) ≤ L * r ^ m := by
  rw [← setIntegral_closedBall_comp_add_left _ z r]
  have heq : (fun x ↦ rescaledPhaseEnergyDensity f R
      (fun y ↦ zeroExtension g u (c₀ + R • y)) (z + x)) =
      fun x ↦ rescaledPhaseEnergyDensity f R
        (fun y ↦ zeroExtension g u ((c₀ + R • z) + R • y)) x := by
    funext x
    rw [rescaledPhaseEnergyDensity_translate_dilation f _ c₀ hR,
      rescaledPhaseEnergyDensity_translate_dilation f _ (c₀ + R • z) hR, smul_add, add_assoc]
  rw [heq]
  exact hr.translated_rescaled_energy_le_surface_bound h hbound (c₀ + R • z) hR hradius

/-- Under a general all-center surface-energy bound `L`, any moving-center blowdown limit `E`
satisfies the corresponding weighted perimeter bound on every ball `ball z r`. -/
theorem RigidityHypotheses.translated_limiting_phase_perimeter_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (z : Space (m + 1)) (r : ℝ) (hradius : 0 < r) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter basis E (ball z r) ≤
      ENNReal.ofReal (L * r ^ m) := by
  let U : ℕ → Space (m + 1) → ℝ := fun j x ↦ zeroExtension g u (c j + R j • x)
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUval (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  apply (hr.perimeter_le_competitor_energy_liminf h basis hR hU hUval hE
    (isCompact_closedBall z r) ball_subset_closedBall
    (hlocal (closedBall z r) (isCompact_closedBall z r))).trans
  exact liminf_ofReal_le_of_comparison
    (F := fun _ ↦ L * r ^ m) (ε := fun _ ↦ 0)
    (fun j ↦ by
      simpa only [add_zero] using hr.translated_rescaled_energy_closedBall_le_surface_bound
        h hbound (c j) z (hR j) hradius)
    tendsto_const_nhds tendsto_const_nhds

/-- Under the sharp planar energy bound `hsharp`, any moving-center blowdown limit `E`
satisfies the sharp Euclidean ball perimeter bound at every center `z` and positive radius `r`. -/
theorem RigidityHypotheses.translated_limiting_phase_sharp_perimeter_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (z : Space (m + 1)) (r : ℝ) (hradius : 0 < r) :
    variationalPerimeter basis E (ball z r) ≤
      ENNReal.ofReal (volume.real (closedBall (0 : Space m) 1) * r ^ m) := by
  have he := hr.translated_limiting_phase_perimeter_bound h hsharp c hR hE hlocal
    basis z r hradius
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  rw [mul_assoc, ENNReal.ofReal_mul hc.le] at he
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp he

/-- Open-set compact-perturbation perimeter minimality for any moving-center blowdown limit
under an all-center surface-energy bound, deduced via `perimeter_minimality_of_concentric_ball_comparison`. -/
theorem RigidityHypotheses.translated_limiting_phase_open_minimality
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * ρ ^ m)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E D K Ω : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hlocal : ∀ C : Set (Space (m + 1)), IsCompact C →
      Tendsto (fun j ↦ ∫ x in C, ‖zeroExtension g u (c j + R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hED : ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) :
    variationalPerimeter basis E Ω ≤ variationalPerimeter basis D Ω := by
  have hc0 : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  have hPE (n : ℕ) : variationalPerimeter basis E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := by
    intro htop
    have hb := hr.translated_limiting_phase_perimeter_bound h hbound c
      (fun j ↦ zero_lt_one.trans_le (hR j)) hE hlocal basis 0 ((n : ℝ) + 1) (by positivity)
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc0).ne'] at hb
    exact ENNReal.ofReal_ne_top (top_unique hb)
  exact perimeter_open_minimality_of_concentric_ball_comparison basis hE hD hPE
    (fun s r hs hr₀ hagree ↦ hr.translated_limiting_phase_perimeter_minimality_ae h hbound
      basis hs hr₀ c hR hRt hE hD (hlocal _ (isCompact_closedBall 0 s)) hagree)
    hK hΩ hKΩ hED

/-- Under the sharp planar energy bound `hsharp`, if a moving-center blowdown sequence
converges locally in `L¹` to the halfspace `{y | 0 < inner ℝ e y}` (`‖e‖ = 1`), then on every
`closedBall 0 r` (`0 < r`), both primitive gradient mass and rescaled phase energy converge to
`phasePrimitive f 1 * (r ^ m * volume.real (closedBall (0 : Space m) 1))`, and the diffuse tilt
along `e` converges to zero. -/
theorem RigidityHypotheses.translated_energy_and_tilt_tendsto_of_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c j + R j • y))) x‖) atTop
        (𝓝 (phasePrimitive f 1 * (r ^ m * volume.real (closedBall (0 : Space m) 1)))) ∧
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x) atTop
        (𝓝 (phasePrimitive f 1 * (r ^ m * volume.real (closedBall (0 : Space m) 1)))) ∧
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) e x) atTop (𝓝 0) := by
  let H : Set (Space (m + 1)) := {y : Space (m + 1) | 0 < inner ℝ e y}
  let U : ℕ → Space (m + 1) → ℝ := fun j x ↦ zeroExtension g u (c j + R j • x)
  let M : ℝ := phasePrimitive f 1 * (r ^ m * volume.real (closedBall (0 : Space m) 1))
  let b₀ := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUval (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hPne : variationalPerimeter b₀ H (ball 0 r) ≠ ⊤ := by
    rw [positive_halfspace_perimeter_closedBall_volume b₀ he hradius]
    exact measure_closedBall_lt_top.ne
  have hM_eq : ENNReal.ofReal M =
      ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter b₀ H (ball 0 r) := by
    dsimp [M]
    rw [ENNReal.ofReal_mul (hr.phasePrimitive_one_pos h).le,
      ← positive_halfspace_perimeter_toReal b₀ he hradius, ENNReal.ofReal_toReal hPne]
  have hliminf : ENNReal.ofReal M ≤ liminf (fun j ↦ ENNReal.ofReal
      (∫ x in closedBall 0 r,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c j + R j • y))) x‖)) atTop := by
    rw [hM_eq]
    exact hr.perimeter_le_competitor_primitive_mass_liminf h b₀ hU hUval hH
      (isCompact_closedBall 0 r) ball_subset_closedBall
      (hlocal (closedBall 0 r) (isCompact_closedBall 0 r))
  have hGE (j : ℕ) :
      (∫ x in closedBall 0 r,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c j + R j • y))) x‖) ≤
      ∫ x in closedBall 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x :=
    hr.competitorPrimitive_gradient_integral_le_energy h (hU j) (hUval j) (hR j)
      (isCompact_closedBall 0 r)
  have hEM (j : ℕ) :
      (∫ x in closedBall 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x) ≤ M := by
    have hb := hr.translated_rescaled_energy_le_surface_bound h hsharp (c j) (hR j) hradius
    exact hb.trans_eq (by dsimp [M]; ring)
  have hG : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c j + R j • y))) x‖) atTop
        (𝓝 M) :=
    tendsto_of_liminf_ofReal_ge_of_le
      (fun j ↦ integral_nonneg fun _ ↦ norm_nonneg _) hliminf (fun j ↦ (hGE j).trans (hEM j))
  have hE : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x) atTop
        (𝓝 M) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hG tendsto_const_nhds hGE hEM
  exact ⟨hG, hE, hr.translated_diffuseTilt_tendsto_zero h hsharp c hR he
    (fun s _ ↦ hlocal _ (isCompact_closedBall 0 s)) hradius⟩

end SerrinEpigraph
