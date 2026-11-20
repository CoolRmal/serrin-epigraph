module

public import SerrinEpigraph.PhaseCalibrationDefect

/-!
# The calibrated flux defect, integrated (Step B)
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ## Auxiliary integrability facts -/

/-- A pairing with a field vanishing off `S` is supported in any superset of `S`. -/
private theorem phaseCalibrationFlux_support_inner_subset {Ξ : Space (m + 1) → Space m}
    {S T : Set (Space (m + 1))} (hΞS : ∀ z ∉ S, Ξ z = 0) (hST : S ⊆ T)
    (V : Space (m + 1) → Space m) :
    Function.support (fun z ↦ inner ℝ (Ξ z) (V z)) ⊆ T := by
  intro z hz
  by_contra hzT
  apply hz
  simp only [hΞS z fun hzS ↦ hzT (hST hzS), inner_zero_left]

/-- The flux pairing of a bounded measurable field supported in a bounded set is integrable. -/
private theorem phaseCalibrationFlux_integrable_inner_flux {v : Space (m + 1) → ℝ}
    (hvL : LocallyLipschitz v) (R δ : ℝ) {Ξ : Space (m + 1) → Space m} (hΞm : Measurable Ξ)
    {M : ℝ} (hΞM : ∀ z, ‖Ξ z‖ ≤ M) {S : Set (Space (m + 1))} (hSb : Bornology.IsBounded S)
    (hΞS : ∀ z ∉ S, Ξ z = 0) :
    Integrable (fun z ↦ inner ℝ (Ξ z)
      ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hΞM 0)
  obtain ⟨r, hSr⟩ := hSb.subset_closedBall (0 : Space (m + 1))
  refine (integrableOn_iff_integrable_of_support_subset
    (phaseCalibrationFlux_support_inner_subset hΞS hSr _)).mp ?_
  refine integrableOn_of_abs_le_mul_gradient_sq hvL
    (hΞm.inner (ha6_measurable_flux_vector R δ v)) measurableSet_closedBall
    isBounded_closedBall (C := M * |δ⁻¹ * R⁻¹|) fun z _ ↦ ?_
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have h1 : |δ⁻¹ * R⁻¹| * (|verticalDerivative v z| * ‖horizontal (gradient v z)‖) ≤
      |δ⁻¹ * R⁻¹| * ‖gradient v z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (ha6_abs_verticalDerivative_mul_le v z) (abs_nonneg _)
  have h2 : 0 ≤ |δ⁻¹ * R⁻¹| * (|verticalDerivative v z| * ‖horizontal (gradient v z)‖) := by
    positivity
  calc ‖Ξ z‖ * (|δ⁻¹ * R⁻¹| * |verticalDerivative v z| * ‖horizontal (gradient v z)‖)
      = ‖Ξ z‖ * (|δ⁻¹ * R⁻¹| * (|verticalDerivative v z| * ‖horizontal (gradient v z)‖)) := by
        ring
    _ ≤ M * (|δ⁻¹ * R⁻¹| * ‖gradient v z‖ ^ 2) := mul_le_mul (hΞM z) h1 h2 hM
    _ = M * |δ⁻¹ * R⁻¹| * ‖gradient v z‖ ^ 2 := by ring

/-- The pairing of a bounded measurable field supported in a bounded set with the horizontal
gradient of a Lipschitz function is integrable. -/
private theorem phaseCalibrationFlux_integrable_inner_horizontal_gradient
    {w : Space (m + 1) → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w) {Ξ : Space (m + 1) → Space m}
    (hΞm : Measurable Ξ) {M : ℝ} (hΞM : ∀ z, ‖Ξ z‖ ≤ M) {S : Set (Space (m + 1))}
    (hSb : Bornology.IsBounded S) (hΞS : ∀ z ∉ S, Ξ z = 0) :
    Integrable (fun z ↦ inner ℝ (Ξ z) (horizontal (gradient w z))) := by
  obtain ⟨r, hSr⟩ := hSb.subset_closedBall (0 : Space (m + 1))
  refine (integrableOn_iff_integrable_of_support_subset
    (phaseCalibrationFlux_support_inner_subset hΞS hSr _)).mp ?_
  refine Measure.integrableOn_of_bounded (M := M * K) measure_closedBall_lt_top.ne
    (hΞm.inner (continuous_horizontal.measurable.comp
      (measurable_gradient w))).aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 : ‖horizontal (gradient w z)‖ ≤ ‖gradient w z‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (horizontal_norm_sq_le_gradient w z)
  have h2 : ‖gradient w z‖ ≤ K := by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hw
  exact mul_le_mul (hΞM z) (h1.trans h2) (norm_nonneg _) ((norm_nonneg _).trans (hΞM z))

/-! ## Integrability and the integrated bound -/

theorem RigidityHypotheses.integrable_inner_flux_of_bounded
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (δ : ℝ)
    {Ξ : Space (m + 1) → Space m} (hΞm : Measurable Ξ) {M : ℝ} (hΞM : ∀ z, ‖Ξ z‖ ≤ M)
    {S : Set (Space (m + 1))} (hSb : Bornology.IsBounded S) (hΞS : ∀ z ∉ S, Ξ z = 0) :
    Integrable (fun z ↦ inner ℝ (Ξ z)
      ((δ⁻¹ * R⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) •
        horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z))) :=
  phaseCalibrationFlux_integrable_inner_flux
    (hr.lipschitzWith_rescaled h c hR.le Q).locallyLipschitz R δ hΞm hΞM hSb hΞS

theorem RigidityHypotheses.integrable_inner_primitiveFlux_of_bounded
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {Ξ : Space (m + 1) → Space m} (hΞm : Measurable Ξ) {M : ℝ} (hΞM : ∀ z, ‖Ξ z‖ ≤ M)
    {S : Set (Space (m + 1))} (hSb : Bornology.IsBounded S) (hΞS : ∀ z ∉ S, Ξ z = 0) :
    Integrable (fun z ↦ inner ℝ (Ξ z) (horizontal
      (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))) := by
  obtain ⟨K, hK⟩ := hr.exists_lipschitzWith_phasePrimitive_rescaled h c hR.le Q
  exact phaseCalibrationFlux_integrable_inner_horizontal_gradient hK hΞm hΞM hSb hΞS

theorem RigidityHypotheses.abs_integral_flux_sub_primitiveFlux_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {δ : ℝ} (hδ : 0 < δ)
    {Ξ : Space (m + 1) → Space m} (hΞm : Measurable Ξ) {M : ℝ} (hΞM : ∀ z, ‖Ξ z‖ ≤ M)
    {S : Set (Space (m + 1))} (hSm : MeasurableSet S)
    (hS2 : S ⊆ tiltCylinder (verticalDirection m) 2) (hΞS : ∀ z ∉ S, Ξ z = 0)
    {lam : ℝ} (hlam : 0 < lam) :
    |∫ z, inner ℝ (Ξ z)
        (((δ⁻¹ * R⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) •
            horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z)) -
          δ⁻¹ • horizontal
            (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))| ≤
      lam * M ^ 2 * (∫ z in S,
          phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z) +
        (2 * lam)⁻¹ * δ⁻¹ ^ 2 * ∫ z in tiltCylinder (verticalDirection m) 2,
          diffuseTiltDensity R (fun z ↦ zeroExtension g u (c + R • Q z))
            (verticalDirection m) z := by
  have hvL : LocallyLipschitz (fun z ↦ zeroExtension g u (c + R • Q z)) :=
    (hr.lipschitzWith_rescaled h c hR.le Q).locallyLipschitz
  have hQ2m : MeasurableSet (tiltCylinder (verticalDirection m) 2) :=
    (isOpen_tiltCylinder _ _).measurableSet
  have hQ2b : Bornology.IsBounded (tiltCylinder (verticalDirection m) 2) :=
    isBounded_tiltCylinder (norm_verticalDirection m) 2
  obtain ⟨r, hQ2r⟩ := hQ2b.subset_closedBall (0 : Space (m + 1))
  have hD0 := hr.phaseCalibrationDefect_rescaled_nonneg h c hR Q
  have hT0 : ∀ z, 0 ≤ diffuseTiltDensity R (fun z ↦ zeroExtension g u (c + R • Q z))
      (verticalDirection m) z := fun z ↦
    diffuseTiltDensity_nonneg hR _ (norm_verticalDirection m) z
  have hiD : IntegrableOn (fun z ↦ lam * M ^ 2 *
      phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z) S :=
    (hr.integrableOn_phaseCalibrationDefect h c hR.le Q hSm (hQ2b.subset hS2)).const_mul _
  have hiT : IntegrableOn (fun z ↦ (2 * lam)⁻¹ * δ⁻¹ ^ 2 *
      diffuseTiltDensity R (fun z ↦ zeroExtension g u (c + R • Q z)) (verticalDirection m) z)
      (tiltCylinder (verticalDirection m) 2) :=
    ((integrableOn_diffuseTiltDensity hvL (isCompact_closedBall _ r) R
      (norm_verticalDirection m)).mono_set hQ2r).const_mul _
  have hiD' := hiD.integrable_indicator hSm
  have hiT' := hiT.integrable_indicator hQ2m
  have hSb : Bornology.IsBounded S := hQ2b.subset hS2
  have hiF : Integrable (fun z ↦ inner ℝ (Ξ z)
      (((δ⁻¹ * R⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) •
          horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z)) -
        δ⁻¹ • horizontal
          (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))) := by
    refine ((hr.integrable_inner_flux_of_bounded h c hR Q δ hΞm hΞM hSb hΞS).sub
      ((hr.integrable_inner_primitiveFlux_of_bounded h c hR Q hΞm hΞM hSb hΞS).const_mul
        δ⁻¹)).congr (Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.sub_apply, inner_sub_right, real_inner_smul_right]
  refine (abs_integral_le_integral_abs.trans (integral_mono hiF.abs (hiD'.add hiT')
    fun z ↦ ?_)).trans_eq ?_
  · by_cases hz : z ∈ S
    · rw [Pi.add_apply, indicator_of_mem hz, indicator_of_mem (hS2 hz)]
      refine (hr.abs_inner_flux_sub_primitiveFlux_le h c hR Q hδ hlam (Ξ z) z).trans ?_
      have h1 : ‖Ξ z‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hΞM z) 2
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlam.le) (hD0 z)
      linarith
    · have h1 : 0 ≤ S.indicator (fun z ↦ lam * M ^ 2 *
          phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z) z :=
        indicator_nonneg (fun z _ ↦ mul_nonneg (mul_nonneg hlam.le (sq_nonneg M)) (hD0 z)) z
      have h2 : 0 ≤ (tiltCylinder (verticalDirection m) 2).indicator (fun z ↦
          (2 * lam)⁻¹ * δ⁻¹ ^ 2 * diffuseTiltDensity R
            (fun z ↦ zeroExtension g u (c + R • Q z)) (verticalDirection m) z) z :=
        indicator_nonneg (fun z _ ↦ mul_nonneg (by positivity) (hT0 z)) z
      simp only [Pi.add_apply, hΞS z hz, inner_zero_left, abs_zero]
      exact add_nonneg h1 h2
  · rw [integral_add' hiD' hiT', integral_indicator hSm, integral_indicator hQ2m,
      integral_const_mul, integral_const_mul]

end SerrinEpigraph
