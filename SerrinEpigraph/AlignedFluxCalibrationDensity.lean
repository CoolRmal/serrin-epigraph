module

public import SerrinEpigraph.AlignedFluxCalibration

/-!
# The vertical flux identification (C⋆) for every admissible parameter tuple
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ## Auxiliary estimates for the density argument -/

/-- The flux pairing against a bounded continuous field is integrable on bounded sets. -/
private theorem calibDensity_integrableOn_inner_flux {v : Space (m + 1) → ℝ}
    (hvL : LocallyLipschitz v) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) {ζ : Space m → Space m}
    (hζ : Continuous ζ) {Z : ℝ} (hZ : ∀ y, ‖ζ y‖ ≤ Z) {S : Set (Space (m + 1))}
    (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) :
    IntegrableOn (fun z ↦ inner ℝ (ζ (horizontal z))
      ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) S :=
  ((integrableOn_flux_mass hvL hδ hR hS hSb).const_mul Z).mono'
    ((hζ.measurable.comp continuous_horizontal.measurable).inner
      (ha6_measurable_flux_vector R δ v)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact (abs_inner_flux_le_mass (v := v) hδ hR _ z).trans
        (mul_le_mul_of_nonneg_right (hZ _) (by positivity)))

/-- Replacing the test field in the flux pairing on `Q₁` by an `ε'`-close one costs at most
`ε'` times the flux mass. -/
private theorem calibDensity_abs_flux_sub_le {v : Space (m + 1) → ℝ} (hvL : LocallyLipschitz v)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) {ζ ξ : Space m → Space m} (hζ : Continuous ζ)
    (hξ : Continuous ξ) {Z ε' MB : ℝ} (hZζ : ∀ y, ‖ζ y‖ ≤ Z) (hZξ : ∀ y, ‖ξ y‖ ≤ Z)
    (hε' : 0 ≤ ε') (hd : ∀ y, ‖ζ y - ξ y‖ ≤ ε')
    (hmass : (∫ z in tiltCylinder (verticalDirection m) 1,
      δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) ≤ MB) :
    |(∫ z in tiltCylinder (verticalDirection m) 1, inner ℝ (ζ (horizontal z))
        ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) -
      ∫ z in tiltCylinder (verticalDirection m) 1, inner ℝ (ξ (horizontal z))
        ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))| ≤ ε' * MB := by
  have hQm : MeasurableSet (tiltCylinder (verticalDirection m) 1) :=
    (isOpen_tiltCylinder _ _).measurableSet
  have hQb : Bornology.IsBounded (tiltCylinder (verticalDirection m) 1) :=
    isBounded_tiltCylinder (norm_verticalDirection m) 1
  have hiζ := calibDensity_integrableOn_inner_flux hvL hδ hR hζ hZζ hQm hQb
  have hiξ := calibDensity_integrableOn_inner_flux hvL hδ hR hξ hZξ hQm hQb
  have hmI := integrableOn_flux_mass hvL hδ hR hQm hQb
  rw [← integral_sub hiζ hiξ]
  refine abs_integral_le_integral_abs.trans ?_
  calc (∫ z in tiltCylinder (verticalDirection m) 1, |inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) -
        inner ℝ (ξ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))|)
      ≤ ∫ z in tiltCylinder (verticalDirection m) 1,
          ε' * (δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) := by
        refine setIntegral_mono_on (hiζ.sub hiξ).abs (hmI.const_mul ε') hQm fun z _ ↦ ?_
        rw [← inner_sub_left]
        exact (abs_inner_flux_le_mass (v := v) hδ hR _ z).trans
          (mul_le_mul_of_nonneg_right (hd _) (by positivity))
    _ = ε' * ∫ z in tiltCylinder (verticalDirection m) 1,
          δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖ :=
        integral_const_mul _ _
    _ ≤ ε' * MB := mul_le_mul_of_nonneg_left hmass hε'

/-- The pairing of a compactly supported continuous field with the gradient of a Lipschitz
function is integrable. -/
private theorem calibDensity_integrable_inner_gradient {ζ : Space m → Space m}
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) {F : Space m → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) : Integrable (fun y ↦ inner ℝ (ζ y) (gradient F y)) := by
  obtain ⟨Z, hZ⟩ := hζ.bounded_above_of_compact_support hcζ
  have h1 : IntegrableOn (fun y ↦ inner ℝ (ζ y) (gradient F y)) (tsupport ζ) := by
    refine Measure.integrableOn_of_bounded (M := Z * C) hcζ.isCompact.measure_lt_top.ne
      (hζ.measurable.inner (measurable_gradient F)).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hZ y) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hZ y)))
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hF
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro y hy
  by_contra hn
  exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])

/-- Replacing the test field in the gradient pairing by an `ε'`-close one with support in
`B_r ⊆ B_ρ` costs at most `ε' (|B_r| + K) / 2`, where `K` bounds `∫_{B_ρ} (F² + |∇F|²)`. -/
private theorem calibDensity_abs_gradient_sub_le {F : Space m → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {ζ ξ : Space m → Space m} (hζ : Continuous ζ) (hξ : Continuous ξ)
    {r ρ K ε' : ℝ} (hζs : tsupport ζ ⊆ ball (0 : Space m) r)
    (hξs : tsupport ξ ⊆ ball (0 : Space m) r) (hrρ : r ≤ ρ) (hε' : 0 ≤ ε')
    (hd : ∀ y, ‖ζ y - ξ y‖ ≤ ε')
    (hK : (∫ y in ball (0 : Space m) ρ, (F y ^ 2 + ‖fderiv ℝ F y‖ ^ 2)) ≤ K) :
    |(∫ y, inner ℝ (ζ y) (gradient F y)) - ∫ y, inner ℝ (ξ y) (gradient F y)| ≤
      ε' * ((volume.real (ball (0 : Space m) r) + max K 0) / 2) := by
  have hcζ : HasCompactSupport ζ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζs)
  have hcξ : HasCompactSupport ξ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hξs)
  have hiζ := calibDensity_integrable_inner_gradient hζ hcζ hF
  have hiξ := calibDensity_integrable_inner_gradient hξ hcξ hF
  have hGρ : IntegrableOn (fun y ↦ F y ^ 2 + ‖fderiv ℝ F y‖ ^ 2) (ball (0 : Space m) ρ) :=
    (integrableOn_sq_of_lipschitz hF).add (integrableOn_fderiv_sq_of_lipschitz hF)
  have hGr : IntegrableOn (fun y ↦ F y ^ 2 + ‖fderiv ℝ F y‖ ^ 2) (ball (0 : Space m) r) :=
    hGρ.mono_set (ball_subset_ball hrρ)
  have hzero : ∀ y, y ∉ ball (0 : Space m) r →
      inner ℝ (ζ y) (gradient F y) - inner ℝ (ξ y) (gradient F y) = 0 := by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hζs h')),
      image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hξs h')), inner_zero_left, sub_zero]
  rw [← integral_sub hiζ hiξ, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hc : IntegrableOn (fun _ ↦ ε' / 2) (ball (0 : Space m) r) :=
    integrableOn_const measure_ball_lt_top.ne
  calc |∫ y in ball (0 : Space m) r,
          (inner ℝ (ζ y) (gradient F y) - inner ℝ (ξ y) (gradient F y))|
      ≤ ∫ y in ball (0 : Space m) r,
          |inner ℝ (ζ y) (gradient F y) - inner ℝ (ξ y) (gradient F y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y in ball (0 : Space m) r, (ε' / 2 + ε' / 2 * (F y ^ 2 + ‖fderiv ℝ F y‖ ^ 2)) := by
        refine setIntegral_mono_on (hiζ.sub hiξ).integrableOn.abs (hc.add (hGr.const_mul _))
          measurableSet_ball fun y _ ↦ ?_
        rw [← inner_sub_left]
        have h1 := abs_real_inner_le_norm (ζ y - ξ y) (gradient F y)
        rw [norm_gradient_eq_norm_fderiv] at h1
        have h2 : ‖ζ y - ξ y‖ * ‖fderiv ℝ F y‖ ≤ ε' * ‖fderiv ℝ F y‖ :=
          mul_le_mul_of_nonneg_right (hd y) (norm_nonneg _)
        have h3 := mul_nonneg hε' (sq_nonneg (‖fderiv ℝ F y‖ - 1))
        have h4 := mul_nonneg hε' (sq_nonneg (F y))
        nlinarith
    _ = ε' / 2 * volume.real (ball (0 : Space m) r) +
          ε' / 2 * ∫ y in ball (0 : Space m) r, (F y ^ 2 + ‖fderiv ℝ F y‖ ^ 2) := by
        rw [integral_add hc (hGr.const_mul _), setIntegral_const, integral_const_mul,
          smul_eq_mul]
        ring
    _ ≤ ε' / 2 * volume.real (ball (0 : Space m) r) + ε' / 2 * max K 0 := by
        gcongr
        exact (setIntegral_mono_set hGρ (Eventually.of_forall fun y ↦ by positivity)
          (Eventually.of_forall (ball_subset_ball hrρ))).trans (hK.trans (le_max_left _ _))
    _ = ε' * ((volume.real (ball (0 : Space m) r) + max K 0) / 2) := by ring

/-- The elementary real-number step of the density argument. -/
private theorem calibDensity_abs_add_mul_lt {Aζ Aξ Gζ Gξ σ ε ε' MB KB : ℝ} (hσ : 0 ≤ σ)
    (h1 : |Aξ + σ * Gξ| < ε / 2) (h2 : |Aζ - Aξ| ≤ ε' * MB) (h3 : |Gζ - Gξ| ≤ ε' * KB)
    (h4 : ε' * (MB + σ * KB) ≤ ε / 2) : |Aζ + σ * Gζ| < ε := by
  have h5 : |σ * (Gζ - Gξ)| ≤ σ * (ε' * KB) := by
    rw [abs_mul, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_left h3 hσ
  have h6 : Aζ + σ * Gζ = (Aξ + σ * Gξ) + (Aζ - Aξ) + σ * (Gζ - Gξ) := by ring
  rw [h6]
  refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) h5)).trans_lt ?_
  nlinarith

/-! ## (C⋆) for continuous test fields -/

/-- **(C⋆) for every admissible tuple.** A continuous test field `ζ` supported in `B_{3/4}` is
approximated in sup norm by a `C¹` field `ξ` with support inside that of `ζ`
(`Continuous.exists_contDiff_approx`), for which (C⋆) holds by
`RigidityHypotheses.tendsto_verticalFlux_add_of_contDiff`. The error is at most `ε'` times the
eventual flux-mass bound on `Q₁` plus `σ ε'` times `(|B_{3/4}| + max K 0) / 2`, a bound for
`∫_{B_{3/4}} |∇f_j|` from the `W^{1,2}(B_ρ)` field of `IsAlignedHeightLimit`. -/
theorem RigidityHypotheses.hasAlignedVerticalFluxIdentification_of_calibration
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0} (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hρ : 3 / 4 < ρ) (hρr₀ : ρ + |r₀| < 2) (hτ : 0 < τ) (hs₁ : 0 < s₁) (hs₂ : s₂ < 1) :
    HasAlignedVerticalFluxIdentification g u (phasePrimitive f 1) ℓ r₀ b ρ τ s₁ s₂ L c K := by
  intro x R Q δ e hal φ σl a H hlim ζ hζ hζs
  have hφ : StrictMono φ := hlim.1
  obtain ⟨-, hR, -, hδ, -, -, -, -, -, -⟩ := id hal
  have hσ0 : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  -- the flux mass on `Q₁` is eventually bounded
  have hmass := hφ.tendsto_atTop.eventually
    (hr.eventually_setIntegral_flux_mass_le_of_aligned h hsharp hal)
  set MB : ℝ := (phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1) /
    2 + 2 ^ m / 2
  set KB : ℝ := (volume.real (ball (0 : Space m) (3 / 4)) + max K 0) / 2
  have hMB0 : 0 ≤ MB := by
    have : 0 ≤ volume.real (closedBall (0 : Space m) 1) := measureReal_nonneg
    positivity
  have hKB0 : 0 ≤ KB := by
    have : 0 ≤ volume.real (ball (0 : Space m) (3 / 4)) := measureReal_nonneg
    have : 0 ≤ max K 0 := le_max_right _ _
    positivity
  have hcζ : HasCompactSupport ζ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζs)
  obtain ⟨Z0, hZ0⟩ := hζ.bounded_above_of_compact_support hcζ
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (2 * (MB + phasePrimitive f 1 * KB + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  -- a `C¹` approximation of `ζ` with support inside that of `ζ`
  obtain ⟨ξ, hξ, hξd, hξsupp⟩ :=
    hζ.exists_contDiff_approx 1 (continuous_const (y := ε')) (fun _ ↦ hε'0)
  have hξ1 : ContDiff ℝ 1 ξ := by simpa using hξ
  have hξs : tsupport ξ ⊆ ball (0 : Space m) (3 / 4) := (closure_mono hξsupp).trans hζs
  have hd : ∀ y, ‖ζ y - ξ y‖ ≤ ε' := fun y ↦ by
    rw [← dist_eq_norm, dist_comm]
    exact (hξd y).le
  have hZζ : ∀ y, ‖ζ y‖ ≤ Z0 + ε' := fun y ↦ (hZ0 y).trans (le_add_of_nonneg_right hε'0.le)
  have hZξ : ∀ y, ‖ξ y‖ ≤ Z0 + ε' := fun y ↦ by
    have h1 := norm_sub_le (ζ y) (ζ y - ξ y)
    rw [sub_sub_cancel] at h1
    linarith [hZ0 y, hd y]
  -- (C⋆) for the `C¹` field `ξ`
  have hT := hr.tendsto_verticalFlux_add_of_contDiff h hsharp hℓ hb0 hb1 hρ hρr₀ hτ hs₁ hs₂ hal
    hlim hξ1 hξs
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hT (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hmass
  refine ⟨max N₁ N₂, fun j hj ↦ ?_⟩
  have h1 := hN₁ j (le_of_max_le_left hj)
  have hjm := hN₂ j (le_of_max_le_right hj)
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  obtain ⟨C, hC⟩ := hlim.2.2.2.2.1 j
  have hA := calibDensity_abs_flux_sub_le
    (locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz
      (x (φ j)) (R (φ j)) (Q (φ j))) (hδ (φ j)) (hR (φ j)) hζ hξ1.continuous hZζ hZξ hε'0.le hd
    hjm
  have hG := calibDensity_abs_gradient_sub_le hC hζ hξ1.continuous hζs hξs hρ.le hε'0.le hd
    (hlim.2.2.2.2.2.1 j)
  have h4 : ε' * (MB + phasePrimitive f 1 * KB) ≤ ε / 2 := by
    rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hσ0.le hKB0]
  exact calibDensity_abs_add_mul_lt hσ0.le h1 hA hG h4

end SerrinEpigraph
