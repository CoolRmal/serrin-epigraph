module

public import SerrinEpigraph.RecoveryProfileExtension

/-!
# Exact action of the regularized one-dimensional transition
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The phase-coordinate primitive of the regularized transition action. -/
@[expose] noncomputable def recoveryActionPrimitive (f : ℝ → ℝ) (δ s : ℝ) : ℝ :=
  ∫ t in 0..s, (2 * normalizedPotential f t + δ) *
    (Real.sqrt (2 * (normalizedPotential f t + δ)))⁻¹

@[simp] theorem recoveryActionPrimitive_zero (f : ℝ → ℝ) (δ : ℝ) :
    recoveryActionPrimitive f δ 0 = 0 := by simp [recoveryActionPrimitive]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- The action integrand is continuous on the closed phase interval. -/
theorem RigidityHypotheses.recovery_action_integrand_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    ContinuousOn (fun s ↦ (2 * normalizedPotential f s + δ) *
      (Real.sqrt (2 * (normalizedPotential f s + δ)))⁻¹) (Icc (0 : ℝ) 1) :=
  ((continuousOn_const.mul h.normalizedPotential_continuousOn).add continuousOn_const).mul
    (hr.recovery_inverse_speed_continuousOn h hδ)

/-- The action primitive is continuous at both phase endpoints. -/
theorem RigidityHypotheses.recoveryActionPrimitive_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    ContinuousOn (recoveryActionPrimitive f δ) (Icc (0 : ℝ) 1) := by
  have hi : IntegrableOn (fun s ↦ (2 * normalizedPotential f s + δ) *
      (Real.sqrt (2 * (normalizedPotential f s + δ)))⁻¹) (uIcc (0 : ℝ) 1) volume := by
    simpa only [uIcc_of_le zero_le_one] using
      (hr.recovery_action_integrand_continuousOn h hδ).integrableOn_Icc (μ := volume)
  change ContinuousOn (fun s ↦ ∫ t in 0..s, (2 * normalizedPotential f t + δ) *
    (Real.sqrt (2 * (normalizedPotential f t + δ)))⁻¹) (Icc (0 : ℝ) 1)
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval hi

/-- Differentiating the action primitive gives the phase-coordinate action density. -/
theorem RigidityHypotheses.recoveryActionPrimitive_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (recoveryActionPrimitive f δ) ((2 * normalizedPotential f s + δ) *
      (Real.sqrt (2 * (normalizedPotential f s + δ)))⁻¹) s := by
  have hc := hr.recovery_action_integrand_continuousOn h hδ
  have hi := (hc.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc
    (μ := volume) hs.1.le
  have hc' := hc.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hc'.stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hc'.continuousAt (isOpen_Ioo.mem_nhds hs))

/-- Integrating the transition density in time equals the phase-coordinate action. -/
theorem RigidityHypotheses.recoveryProfileCore_action
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    (∫ t in 0..recoveryTravelTime f δ 1,
      2 * normalizedPotential f (recoveryProfileCore f δ t) + δ) =
      recoveryActionPrimitive f δ 1 := by
  have hT := hr.recoveryTravelTime_one_pos h hδ
  have hq := hr.recoveryProfileCore_continuousOn h hδ
  have hmap : MapsTo (recoveryProfileCore f δ) (Icc 0 (recoveryTravelTime f δ 1))
      (Icc (0 : ℝ) 1) := fun t ht ↦ (hr.recoveryProfileCore_spec h hδ ht).1
  have hcont := (hr.recoveryActionPrimitive_continuousOn h hδ).comp hq hmap
  have hw := h.normalizedPotential_continuousOn.comp hq hmap
  have hi : IntervalIntegrable
      (fun t ↦ 2 * normalizedPotential f (recoveryProfileCore f δ t) + δ)
      volume 0 (recoveryTravelTime f δ 1) :=
    ((continuousOn_const.mul hw).add continuousOn_const).intervalIntegrable_of_Icc hT.le
  have hd : ∀ t ∈ Ioo 0 (recoveryTravelTime f δ 1),
      HasDerivAt (fun s ↦ recoveryActionPrimitive f δ (recoveryProfileCore f δ s))
        (2 * normalizedPotential f (recoveryProfileCore f δ t) + δ) t := by
    intro t ht
    have hqt := hr.recoveryProfileCore_mem_Ioo h hδ ht
    have hwq := hr.normalizedPotential_nonneg h ⟨hqt.1.le, hqt.2.le⟩
    have hn : Real.sqrt (2 * (normalizedPotential f (recoveryProfileCore f δ t) + δ)) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity)).ne'
    have he := (hr.recoveryActionPrimitive_hasDerivAt h hδ hqt).comp t
      (hr.recoveryProfileCore_hasDerivAt h hδ ht)
    simpa only [Function.comp_def, mul_assoc, inv_mul_cancel₀ hn, mul_one] using he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hcont hd hi
  simpa only [Function.comp_def, hr.recoveryProfileCore_end h hδ, hr.recoveryProfileCore_zero h hδ,
    recoveryActionPrimitive_zero, sub_zero] using he

/-- The kinetic-plus-potential action has the same exact phase-coordinate formula. -/
theorem RigidityHypotheses.recoveryProfileCore_energy_integral
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    (∫ t in 0..recoveryTravelTime f δ 1,
      (deriv (recoveryProfileCore f δ) t) ^ 2 / 2 +
        normalizedPotential f (recoveryProfileCore f δ t)) =
      recoveryActionPrimitive f δ 1 := by
  rw [← hr.recoveryProfileCore_action h hδ]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (recoveryTravelTime f δ 1)] with t ht
  intro hmem
  rw [uIoc_of_le (hr.recoveryTravelTime_one_pos h hδ).le] at hmem
  exact hr.recoveryProfileCore_energy_identity h hδ
    ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩

end SerrinEpigraph
