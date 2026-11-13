module

public import SerrinEpigraph.DistanceRecovery

/-!
# Exact mass of the rescaled one-dimensional layer density
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The one-dimensional majorant supported on the scaled transition layer. -/
@[expose] noncomputable def recoveryLayerDensity (f : ℝ → ℝ) (δ R : ℝ) : ℝ → ℝ :=
  (Ioo 0 (recoveryTravelTime f δ 1 / R)).indicator
    (fun s ↦ R * (2 * normalizedPotential f (recoveryProfile f δ (R * s)) + δ))

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- On the unscaled transition interval, extending the core does not change the action. -/
theorem RigidityHypotheses.recoveryProfile_action
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    (∫ t in 0..recoveryTravelTime f δ 1,
      2 * normalizedPotential f (recoveryProfile f δ t) + δ) =
      recoveryActionPrimitive f δ 1 := by
  rw [← hr.recoveryProfileCore_action h hδ]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (hr.recoveryTravelTime_one_pos h hδ).le] at ht
  simp only [recoveryProfile_eq_core ht]

/-- Scaling the layer width and density inversely preserves the exact transition action. -/
theorem RigidityHypotheses.recoveryProfile_scaled_action
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R) :
    (∫ s in 0..recoveryTravelTime f δ 1 / R,
      R * (2 * normalizedPotential f (recoveryProfile f δ (R * s)) + δ)) =
      recoveryActionPrimitive f δ 1 := by
  rw [intervalIntegral.integral_const_mul]
  have he := intervalIntegral.smul_integral_comp_mul_left
    (fun t ↦ 2 * normalizedPotential f (recoveryProfile f δ t) + δ)
    (a := 0) (b := recoveryTravelTime f δ 1 / R) R
  simpa only [smul_eq_mul, mul_zero, mul_div_cancel₀ _ hR.ne',
    hr.recoveryProfile_action h hδ] using he

/-- The globally supported layer density has precisely the regularized action as total mass. -/
theorem RigidityHypotheses.integral_recoveryLayerDensity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R) :
    (∫ s, recoveryLayerDensity f δ R s) = recoveryActionPrimitive f δ 1 := by
  rw [recoveryLayerDensity, integral_indicator measurableSet_Ioo]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (div_nonneg (hr.recoveryTravelTime_one_pos h hδ).le hR.le)]
  exact hr.recoveryProfile_scaled_action h hδ hR

/-- The layer density is nonnegative everywhere. -/
theorem RigidityHypotheses.recoveryLayerDensity_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (s : ℝ) : 0 ≤ recoveryLayerDensity f δ R s := by
  apply indicator_nonneg
  intro t ht
  have hw := hr.normalizedPotential_nonneg h (hr.recoveryProfile_mem_Icc h hδ (R * t))
  exact mul_nonneg hR (by positivity)

/-- Compact support of the layer and continuity of its interior density give integrability. -/
theorem RigidityHypotheses.integrable_recoveryLayerDensity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    Integrable (recoveryLayerDensity f δ R) := by
  have hv : Continuous (fun t ↦ recoveryProfile f δ (R * t)) :=
    (hr.recoveryProfile_lipschitz h hδ).continuous.comp (continuous_const.mul continuous_id)
  have hW := h.normalizedPotential_continuousOn.comp_continuous hv
    (fun t ↦ hr.recoveryProfile_mem_Icc h hδ (R * t))
  have hc : Continuous (fun t ↦ R * (2 * normalizedPotential f (recoveryProfile f δ (R * t)) + δ)) :=
    continuous_const.mul ((continuous_const.mul hW).add continuous_const)
  have hi := hc.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_Icc (a := (0 : ℝ)) (b := recoveryTravelTime f δ 1 / R))
  exact (hi.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

end SerrinEpigraph
