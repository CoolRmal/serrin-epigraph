module

public import SerrinEpigraph.PhaseCalibrationSlab

/-!
# The calibration defect vanishes along planar blow-downs (Step A)
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **Step A: the calibration defect vanishes.** Along aligned planar blow-downs, the phase
calibration defect `e_R(v) - √(2W(v)) ∂ₜ v` of the rotated rescalings integrates to `o(1)` over
the cylinder `B_r × (-1, 1)`: the calibration integral is the integrated jump of `Φ(v)`, which is
asymptotically at least `σ ω r ^ m` (HA8), while the energy of the cylinder is asymptotically at
most `σ ω (r + h) ^ m` for every `h > 0` (sharp ball energy and FE3 tails). -/
theorem RigidityHypotheses.tendsto_setIntegral_phaseCalibrationDefect_of_aligned
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e)) {r : ℝ} (hr0 : 0 < r) :
    Tendsto (fun j ↦ ∫ z in horizontal ⁻¹' ball (0 : Space m) r ∩
        (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1,
      phaseCalibrationDefect f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z)
      atTop (𝓝 0) := by
  set Z : Set (Space (m + 1)) := horizontal ⁻¹' ball (0 : Space m) r ∩
    (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1
  have hcl : Continuous (fun z : Space (m + 1) ↦ (z (Fin.last m) : ℝ)) := continuous_last
  have hZm : MeasurableSet Z :=
    (measurableSet_ball.preimage continuous_horizontal.measurable).inter
      (measurableSet_Ioo.preimage hcl.measurable)
  have hZball : Z ⊆ closedBall (0 : Space (m + 1)) (r + 1) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h1 : ‖horizontal z‖ < r := by
      have hz1' : horizontal z ∈ ball (0 : Space m) r := hz1
      rwa [mem_ball, dist_zero_right] at hz1'
    have h2 : |z (Fin.last m)| < 1 := abs_lt.mpr hz2
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_horizontal_add_abs_last z]
  have hZb : Bornology.IsBounded Z := isBounded_closedBall.subset hZball
  -- the defect is nonnegative, so it suffices to bound the integrals eventually from above
  have hnonneg : ∀ j, 0 ≤ ∫ z in Z,
      phaseCalibrationDefect f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z :=
    fun j ↦ setIntegral_nonneg hZm fun z _ ↦
      hr.phaseCalibrationDefect_rescaled_nonneg h (x j) (hR j) (Q j) z
  suffices key : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, (∫ z in Z,
      phaseCalibrationDefect f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤ η by
    rw [tendsto_order]
    refine ⟨fun a ha ↦ Eventually.of_forall fun j ↦ ha.trans_le (hnonneg j), fun a ha ↦ ?_⟩
    filter_upwards [key (a / 2) (half_pos ha)] with j hj
    linarith
  intro η hη
  set σ : ℝ := phasePrimitive f 1
  set ω : ℝ := volume.real (closedBall (0 : Space m) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  have hLip := hr.phasePrimitive_lipschitzOn h
  set L : ℝ := Real.sqrt (2 * normalizedPotential f 0)
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  -- the half-height `hh` of the slab around the plane
  obtain ⟨hh, hh0, hhη⟩ : ∃ hh : ℝ, 0 < hh ∧ σ * ω * ((r + hh) ^ m - r ^ m) < η / 4 := by
    have hc : ContinuousAt (fun t : ℝ ↦ σ * ω * ((r + t) ^ m - r ^ m)) 0 := by fun_prop
    have h0 : σ * ω * ((r + 0) ^ m - r ^ m) < η / 4 := by
      rw [add_zero, sub_self, mul_zero]
      positivity
    obtain ⟨t, ht1, ht2⟩ := (((hc.eventually (gt_mem_nhds h0)).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    exact ⟨t, ht2, ht1⟩
  -- the distance `β` to the upper phase above the slab
  obtain ⟨β, hβ0, hβη⟩ : ∃ β : ℝ, 0 < β ∧ L * β * (r ^ m * ω) ≤ η / 4 := by
    have hA0 : 0 ≤ L * (r ^ m * ω) := by positivity
    refine ⟨η / (4 * (L * (r ^ m * ω) + 1)), by positivity, ?_⟩
    have h1 : 0 < L * (r ^ m * ω) + 1 := by linarith
    calc L * (η / (4 * (L * (r ^ m * ω) + 1))) * (r ^ m * ω)
        = L * (r ^ m * ω) * (η / (4 * (L * (r ^ m * ω) + 1))) := by ring
      _ ≤ (L * (r ^ m * ω) + 1) * (η / (4 * (L * (r ^ m * ω) + 1))) := by
          gcongr
          linarith
      _ = η / 4 := by
          rw [mul_div_assoc', mul_comm 4, mul_div_mul_left η 4 h1.ne']
  -- the eventual estimates
  have hV := hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hlocal hQ
  have hE1 : ∀ᶠ j in atTop, (∫ z in closedBall (0 : Space (m + 1)) (r + hh),
      rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤
        σ * ((r + hh) ^ m * ω) + η / 4 := by
    obtain ⟨-, hE, -⟩ := hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp x hR
      he hlocal (r := r + hh) (by linarith)
    have hlt : σ * ((r + hh) ^ m * ω) < σ * ((r + hh) ^ m * ω) + η / 4 := by linarith
    filter_upwards [hE.eventually_lt_const hlt] with j hj
    rw [setIntegral_closedBall_rescaled_isometry f (zeroExtension g u) (x j) (hR j) (Q j)]
    exact hj.le
  have hE2 : ∀ᶠ j in atTop, (∫ z in tiltCylinder (verticalDirection m) (r + 1) ∩
      {z | hh ≤ |z (Fin.last m)|},
        rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤
          η / 4 := by
    have ht := hr.tendsto_energy_tail_of_aligned h hsharp x hR hRt (δ := fun _ ↦ 1)
      (fun _ ↦ one_pos) (by simpa using hRt) he hlocal hQ (r := r + 1) (by linarith) hh0
    simp only [inv_one, one_pow, one_mul] at ht
    filter_upwards [ht.eventually_lt_const (by positivity : (0 : ℝ) < η / 4)] with j hj
    exact hj.le
  filter_upwards [hE1, hE2, hV.upper (r + 1) 1 β one_pos hβ0, hV.lower (r + 1) 1 one_pos]
    with j hj1 hj2 hup hlow
  -- the estimate at index `j`
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x j + R j • Q j z)
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRj := hR j
  have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f (R j) v z :=
    hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
  -- the defect integral is the energy integral minus the calibration integral
  have iEZ : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v) Z :=
    (h.integrableOn_rescaledPhaseEnergy hvL hval (R j) (isCompact_closedBall _ _)).mono_set
      hZball
  have iJZ := hr.integrableOn_phaseCalibrationDensity h (x j) hRj.le (Q j) hZm hZb
  have hsplit : (∫ z in Z, phaseCalibrationDefect f (R j) v z) =
      (∫ z in Z, rescaledPhaseEnergyDensity f (R j) v z) -
        ∫ z in Z, Real.sqrt (2 * normalizedPotential f (v z)) * verticalDerivative v z :=
    integral_sub iEZ iJZ
  -- the calibration integral is the integrated jump of `Φ(v)` (exact slab calibration)
  have hJ : (∫ z in Z, Real.sqrt (2 * normalizedPotential f (v z)) * verticalDerivative v z) =
      ∫ y in ball (0 : Space m) r,
        (phasePrimitive f (v (point y 1)) - phasePrimitive f (v (point y (-1)))) :=
    hr.setIntegral_slab_phaseCalibration_eq h (x j) hRj.le (Q j) measurableSet_ball
      isBounded_ball one_pos
  -- the jump is at least `σ - L β` over the ball (HA8)
  have hjump : ∀ y ∈ ball (0 : Space m) r, σ - L * β ≤
      phasePrimitive f (v (point y 1)) - phasePrimitive f (v (point y (-1))) := by
    intro y hy
    have hy' : ‖y‖ < r := by rwa [mem_ball, dist_zero_right] at hy
    have hp1 : point y 1 ∈ closedBall (0 : Space (m + 1)) (r + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have := norm_point_le y 1
      rw [abs_one] at this
      linarith
    have hp2 : point y (-1) ∈ closedBall (0 : Space (m + 1)) (r + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have := norm_point_le y (-1)
      rw [abs_neg, abs_one] at this
      linarith
    have h0 : v (point y (-1)) = 0 := hlow (point y (-1)) hp2 (by rw [last_point])
    have h1 : 1 - β < v (point y 1) := hup (point y 1) hp1 (by rw [last_point])
    have h2 := hLip.dist_le_mul 1 ⟨zero_le_one, le_rfl⟩ (v (point y 1)) (hval _)
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hval _).2)] at h2
    have h3 : |σ - phasePrimitive f (v (point y 1))| ≤ L * β := by
      refine h2.trans ?_
      change L * (1 - v (point y 1)) ≤ L * β
      exact mul_le_mul_of_nonneg_left (by linarith) hL0
    rw [h0, phasePrimitive_zero, sub_zero]
    linarith [(abs_le.mp h3).2]
  have hjc : Continuous (fun y : Space m ↦
      phasePrimitive f (v (point y 1)) - phasePrimitive f (v (point y (-1)))) := by
    have hF := (hr.phasePrimitive_comp_locallyLipschitz h hvL hval).continuous
    exact (hF.comp (pointContinuousLinearMap.continuous.comp
        (continuous_id.prodMk continuous_const))).sub
      (hF.comp (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk continuous_const)))
  have hjumpi : IntegrableOn (fun y ↦
      phasePrimitive f (v (point y 1)) - phasePrimitive f (v (point y (-1))))
      (ball (0 : Space m) r) :=
    (hjc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      ball_subset_closedBall
  have hJlow : (σ - L * β) * (r ^ m * ω) ≤ ∫ y in ball (0 : Space m) r,
      (phasePrimitive f (v (point y 1)) - phasePrimitive f (v (point y (-1)))) := by
    rw [← volume_real_ball_eq_pow_mul_closedBall hr0]
    exact setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_lt_top.ne hjump hjumpi
  -- the energy of the cylinder: split along the slab `|t| < hh`
  set T : Set (Space (m + 1)) := {z | |z (Fin.last m)| < hh} with hT
  have hTm : MeasurableSet T :=
    (isOpen_lt (continuous_abs.comp hcl) continuous_const).measurableSet
  have hA1 : Z ∩ T ⊆ closedBall (0 : Space (m + 1)) (r + hh) := by
    intro z hz
    obtain ⟨⟨hz1, -⟩, hzT⟩ := hz
    have h1 : ‖horizontal z‖ < r := by
      have hz1' : horizontal z ∈ ball (0 : Space m) r := hz1
      rwa [mem_ball, dist_zero_right] at hz1'
    have h2 : |z (Fin.last m)| < hh := hzT
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_horizontal_add_abs_last z]
  have hA2 : Z \ T ⊆ tiltCylinder (verticalDirection m) (r + 1) ∩
      {z : Space (m + 1) | hh ≤ |z (Fin.last m)|} := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, hzT⟩ := hz
    have h1 : ‖horizontal z‖ < r := by
      have hz1' : horizontal z ∈ ball (0 : Space m) r := hz1
      rwa [mem_ball, dist_zero_right] at hz1'
    have h2 : |z (Fin.last m)| < 1 := abs_lt.mpr hz2
    refine ⟨mem_tiltCylinder_vertical_iff.mpr ⟨by linarith, by linarith⟩, ?_⟩
    simpa [hT] using hzT
  have iEB : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v)
      (closedBall (0 : Space (m + 1)) (r + hh)) :=
    h.integrableOn_rescaledPhaseEnergy hvL hval (R j) (isCompact_closedBall _ _)
  have iET : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v)
      (tiltCylinder (verticalDirection m) (r + 1) ∩
        {z : Space (m + 1) | hh ≤ |z (Fin.last m)|}) :=
    (h.integrableOn_rescaledPhaseEnergy hvL hval (R j)
      (isCompact_closedBall (0 : Space (m + 1)) (2 * (r + 1)))).mono_set
      (inter_subset_left.trans (ha6_tiltCylinder_subset_closedBall (r + 1)))
  have hsplitE := integral_inter_add_sdiff hTm iEZ
  have hEZT : (∫ z in Z ∩ T, rescaledPhaseEnergyDensity f (R j) v z) ≤
      ∫ z in closedBall (0 : Space (m + 1)) (r + hh), rescaledPhaseEnergyDensity f (R j) v z :=
    setIntegral_mono_set iEB (Eventually.of_forall fun z ↦ hE0 z) (Eventually.of_forall hA1)
  have hEZT' : (∫ z in Z \ T, rescaledPhaseEnergyDensity f (R j) v z) ≤
      ∫ z in tiltCylinder (verticalDirection m) (r + 1) ∩
        {z : Space (m + 1) | hh ≤ |z (Fin.last m)|}, rescaledPhaseEnergyDensity f (R j) v z :=
    setIntegral_mono_set iET (Eventually.of_forall fun z ↦ hE0 z) (Eventually.of_forall hA2)
  -- combine
  rw [hsplit, hJ]
  linarith [hsplitE, hEZT, hEZT', hj1, hj2, hJlow, hhη, hβη]

end SerrinEpigraph
