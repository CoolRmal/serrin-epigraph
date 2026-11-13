module

public import SerrinEpigraph.RecoveryActionBounds

/-!
# Vanishing thickness of regularized recovery layers
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- Positive regularization bounds the time needed to reach the equilibrium phase. -/
theorem RigidityHypotheses.recoveryTravelTime_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    recoveryTravelTime f δ 1 ≤ (Real.sqrt (2 * δ))⁻¹ := by
  have hi := (hr.recovery_inverse_speed_continuousOn h hδ).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  have he := intervalIntegral.integral_mono_on zero_le_one hi
    (intervalIntegrable_const (c := (Real.sqrt (2 * δ))⁻¹)) (fun s hs ↦ by
      have hw := hr.normalizedPotential_nonneg h hs
      exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_le_sqrt (by linarith)))
  simpa only [recoveryTravelTime, intervalIntegral.integral_const, sub_zero, one_smul] using he

/-- The transition thickness vanishes when the scale dominates inverse regularized speed. -/
theorem RigidityHypotheses.recoveryThickness_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hscale : Tendsto (fun j ↦ (Real.sqrt (2 * δ j))⁻¹ / R j) atTop (𝓝 0)) :
    Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j) atTop (𝓝 0) := by
  apply squeeze_zero _ _ hscale
  · intro j
    exact div_nonneg (hr.recoveryTravelTime_one_pos h (hδ j)).le (hR j).le
  · intro j
    exact div_le_div_of_nonneg_right (hr.recoveryTravelTime_le h (hδ j)) (hR j).le

/-- At every positive signed distance the scaled profile is eventually exactly one. -/
theorem RigidityHypotheses.recoveryProfile_eventually_one
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j) atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ j in atTop, recoveryProfile f (δ j) (R j * s) = 1 := by
  filter_upwards [hwidth.eventually (gt_mem_nhds hs)] with j hj
  apply hr.recoveryProfile_eq_one h (hδ j)
  have he := (div_lt_iff₀ (hR j)).mp hj
  simpa only [mul_comm] using he.le

/-- The scaled transition converges pointwise to the positive half-line indicator. -/
theorem RigidityHypotheses.recoveryProfile_scaled_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j) atTop (𝓝 0))
    (s : ℝ) : Tendsto (fun j ↦ recoveryProfile f (δ j) (R j * s)) atTop
      (𝓝 (if 0 < s then (1 : ℝ) else 0)) := by
  split_ifs with hs
  · apply tendsto_const_nhds.congr'
    filter_upwards [hr.recoveryProfile_eventually_one h hδ hR hwidth hs] with j hj
    exact hj.symm
  · have he : ∀ j, recoveryProfile f (δ j) (R j * s) = 0 := fun j ↦
      hr.recoveryProfile_eq_zero h (hδ j)
        (mul_nonpos_of_nonneg_of_nonpos (hR j).le (le_of_not_gt hs))
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

end SerrinEpigraph
