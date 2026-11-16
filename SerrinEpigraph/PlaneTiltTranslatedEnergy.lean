module

public import SerrinEpigraph.PlaneTiltPhaseLimit

/-!
# Gradient and mass estimates for translated dilation families
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- Translation and dilation have the exact totalized gradient chain rule. -/
theorem gradient_comp_translate_dilation {d : ℕ} (v : Space d → ℝ)
    (c : Space d) (R : ℝ) (x : Space d) :
    gradient (fun y ↦ v (c + R • y)) x = R • gradient v (c + R • x) := by
  rw [show (fun y ↦ v (c + R • y)) = (fun y ↦ (fun z ↦ v (c + z)) (R • y)) from rfl,
    gradient_comp_dilation (fun z ↦ v (c + z))]
  simp only [gradient, fderiv_comp_add_left]

/-- A translated dilation preserves local Lipschitz regularity. -/
theorem locallyLipschitz_comp_translate_dilation {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) (c : Space d) (R : ℝ) :
    LocallyLipschitz (fun y ↦ v (c + R • y)) := by
  exact hv.comp (((isometry_add_left c).lipschitzWith.comp (lipschitzWith_smul R)).locallyLipschitz)

/-- Translating a ball and its integrand leaves its integral unchanged. -/
theorem setIntegral_closedBall_comp_add_left {d : ℕ} (v : Space d → ℝ)
    (c : Space d) (r : ℝ) :
    (∫ x in closedBall 0 r, v (c + x)) = ∫ x in closedBall c r, v x := by
  have hp : (fun x : Space d ↦ c + x) ⁻¹' closedBall c r = closedBall 0 r := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have ht := ((measurePreserving_add_left volume c).restrict_preimage
    (s := closedBall c r) measurableSet_closedBall).integral_comp
      (Homeomorph.addLeft c).measurableEmbedding v
  simpa only [hp] using ht

/-- Surface-order change of variables for an arbitrary translated dilation. -/
theorem setIntegral_closedBall_translate_dilation_weighted {m : ℕ}
    (v : Space (m + 1) → ℝ) (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r, R * v (c + R • x)) =
      (R ^ m)⁻¹ * ∫ x in closedBall c (R * r), v x := by
  rw [integral_const_mul,
    Measure.setIntegral_comp_smul_of_pos volume (fun x ↦ v (c + x)) _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_of_nonneg hR.le,
    finrank_euclideanSpace_fin, smul_eq_mul]
  rw [setIntegral_closedBall_comp_add_left, pow_succ]
  field_simp

/-- The rescaled energy of a translated dilation is the translated physical density
multiplied by the scale. -/
theorem rescaledPhaseEnergyDensity_translate_dilation {d : ℕ} (f : ℝ → ℝ)
    (U : Space d → ℝ) (c : Space d) {R : ℝ} (hR : 0 < R) (x : Space d) :
    rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • y)) x =
      R * phaseEnergyDensity f 0 U (c + R • x) := by
  by_cases hx : 0 < U (c + R • x)
  · simp only [rescaledPhaseEnergyDensity, phaseEnergyDensity, indicator_apply, mem_ofPred_eq,
      hx, ite_true, gradient_comp_translate_dilation, norm_smul,
      Real.norm_of_nonneg hR.le, add_zero]
    field_simp
  · simp [rescaledPhaseEnergyDensity, phaseEnergyDensity, hx]

/-- Exact energy change of variables for a translated dilation. -/
theorem integral_rescaledPhaseEnergyDensity_translate {m : ℕ} (f : ℝ → ℝ)
    (U : Space (m + 1) → ℝ) (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f R (fun y ↦ U (c + R • y)) x) =
      (R ^ m)⁻¹ * ∫ x in closedBall c (R * r), phaseEnergyDensity f 0 U x := by
  simp_rw [rescaledPhaseEnergyDensity_translate_dilation f U c hR]
  exact setIntegral_closedBall_translate_dilation_weighted _ c hR r

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The original all-center energy bound holds uniformly for every translated dilation. -/
theorem RigidityHypotheses.translated_rescaled_energy_le_surface_bound
    (_hr : RigidityHypotheses g u f) (_h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : Space (m + 1)) {R r : ℝ} (hR : 0 < R) (hradius : 0 < r) :
    (∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • y)) x) ≤ L * r ^ m := by
  rw [integral_rescaledPhaseEnergyDensity_translate f _ c hR]
  have hh := mul_le_mul_of_nonneg_left (hbound c (R * r) (mul_pos hR hradius))
    (inv_nonneg.mpr (pow_nonneg hR.le m))
  convert hh using 1
  rw [mul_pow]
  field_simp

/-- The pointwise primitive gradient is bounded by actual translated rescaled energy. -/
theorem RigidityHypotheses.translated_primitive_gradient_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (x : Space (m + 1)) :
    ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x‖ ≤
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • y)) x := by
  rw [gradient_comp_translate_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
    norm_smul, Real.norm_of_nonneg hR.le, hr.norm_gradient_phasePrimitive_zeroExtension h,
    rescaledPhaseEnergyDensity_translate_dilation f _ c hR]
  exact mul_le_mul_of_nonneg_left (hr.weightedGradient_le_energy h _) hR.le

/-- Translated primitive mass is bounded by the physical energy on the corresponding ball. -/
theorem RigidityHypotheses.translated_primitive_mass_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x‖) ≤
        (R ^ m)⁻¹ * ∫ x in closedBall c (R * r),
          phaseEnergyDensity f 0 (zeroExtension g u) x := by
  simp_rw [gradient_comp_translate_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
    norm_smul, Real.norm_of_nonneg hR.le]
  rw [setIntegral_closedBall_translate_dilation_weighted
    (fun x ↦ ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u y)) x‖) c hR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp_rw [hr.norm_gradient_phasePrimitive_zeroExtension h]
  exact integral_mono (hr.integrableOn_weightedGradient h (isCompact_closedBall c (R * r)))
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall c (R * r)))
    (hr.weightedGradient_le_energy h)

/-- An all-center surface-energy bound uniformly controls the primitive mass of every
translated dilation, including sequences whose centers escape to infinity. -/
theorem RigidityHypotheses.translated_primitive_mass_le_surface_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : Space (m + 1)) {R r : ℝ} (hR : 0 < R) (hradius : 0 < r) :
    (∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x‖) ≤
        L * r ^ m := by
  apply (hr.translated_primitive_mass_le_energy h c hR r).trans
  have hh := mul_le_mul_of_nonneg_left (hbound c (R * r) (mul_pos hR hradius))
    (inv_nonneg.mpr (pow_nonneg hR.le m))
  convert hh using 1
  rw [mul_pow]
  field_simp

/-- Modica's estimate controls the actual tilt of every translated dilation. -/
theorem RigidityHypotheses.translated_diffuseTilt_le_primitive_defect
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (x : Space (m + 1)) :
    diffuseTiltDensity R (fun y ↦ zeroExtension g u (c + R • y)) e x ≤
      2 * (‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x‖ -
        inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x) e) := by
  let w := Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • x)))
  have hq : ‖gradient (fun y ↦ zeroExtension g u (c + R • y)) x‖ ≤ R * w := by
    rw [gradient_comp_translate_dilation, norm_smul, Real.norm_of_nonneg hR.le]
    exact mul_le_mul_of_nonneg_left (hr.norm_gradient_zeroExtension_le_sqrt_potential h _) hR.le
  have hp : gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x =
      w • gradient (fun y ↦ zeroExtension g u (c + R • y)) x := by
    rw [gradient_comp_translate_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
      hr.gradient_phasePrimitive_zeroExtension h, gradient_comp_translate_dilation]
    simp only [w, smul_smul, mul_comm]
  rw [hp]
  exact tangential_energy_le_oriented_weighted_defect _ he hR (Real.sqrt_nonneg _) hq

/-- The translated pointwise estimate integrates on every compact set. -/
theorem RigidityHypotheses.integral_translated_diffuseTilt_le_primitive_defect
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) {e : Space (m + 1)} (he : ‖e‖ = 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    (∫ x in K, diffuseTiltDensity R (fun y ↦ zeroExtension g u (c + R • y)) e x) ≤
      2 * ∫ x in K,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x‖ -
          inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x) e := by
  have hv := locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c R
  have hp := locallyLipschitz_comp_translate_dilation
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h) c R
  have hg := integrableOn_gradient_of_locallyLipschitz hp hK
  have hgi : IntegrableOn (fun x ↦ inner ℝ
      (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • y))) x) e) K :=
    hg.inner_const e
  rw [← integral_const_mul]
  exact integral_mono (integrableOn_diffuseTiltDensity hv hK R he)
    ((hg.norm.sub hgi).const_mul 2) (hr.translated_diffuseTilt_le_primitive_defect h c hR he)

end SerrinEpigraph
