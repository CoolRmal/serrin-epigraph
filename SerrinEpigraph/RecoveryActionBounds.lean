module

public import SerrinEpigraph.RecoveryAction

/-!
# Quantitative bounds for the regularized transition action
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The regularized action density lies within a square-root error of the limiting density. -/
theorem recovery_action_density_bounds {w δ : ℝ} (hw : 0 ≤ w) (hδ : 0 < δ) :
    Real.sqrt (2 * w) ≤ (2 * w + δ) * (Real.sqrt (2 * (w + δ)))⁻¹ ∧
      (2 * w + δ) * (Real.sqrt (2 * (w + δ)))⁻¹ ≤
        Real.sqrt (2 * w) + Real.sqrt (2 * δ) := by
  have ha := Real.sqrt_nonneg (2 * w)
  have hb := Real.sqrt_pos.mpr (show 0 < 2 * (w + δ) by positivity)
  have hc := Real.sqrt_nonneg (2 * δ)
  have ha2 := Real.sq_sqrt (show 0 ≤ 2 * w by positivity)
  have hb2 := Real.sq_sqrt (show 0 ≤ 2 * (w + δ) by positivity)
  have hc2 := Real.sq_sqrt (show 0 ≤ 2 * δ by positivity)
  have hab : Real.sqrt (2 * w) * Real.sqrt (2 * (w + δ)) ≤ 2 * w + δ := by
    have hp : (Real.sqrt (2 * w) * Real.sqrt (2 * (w + δ))) ^ 2 =
        4 * w * (w + δ) := by rw [mul_pow, ha2, hb2]; ring
    nlinarith [sq_nonneg δ]
  have hbc : Real.sqrt (2 * (w + δ)) ≤ Real.sqrt (2 * w) + Real.sqrt (2 * δ) := by
    nlinarith [mul_nonneg ha hc]
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ hb]
    exact hab
  · apply le_trans _ hbc
    rw [← div_eq_mul_inv, div_le_iff₀ hb]
    nlinarith

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- The total regularized action differs from the interface constant by at most √(2δ). -/
theorem RigidityHypotheses.recoveryActionPrimitive_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    phasePrimitive f 1 ≤ recoveryActionPrimitive f δ 1 ∧
      recoveryActionPrimitive f δ 1 ≤ phasePrimitive f 1 + Real.sqrt (2 * δ) := by
  have hc : ContinuousOn (fun s ↦ Real.sqrt (2 * normalizedPotential f s)) (Icc 0 1) :=
    (continuousOn_const.mul h.normalizedPotential_continuousOn).sqrt
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hj := (hr.recovery_action_integrand_continuousOn h hδ).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  constructor
  · exact intervalIntegral.integral_mono_on zero_le_one hi hj fun s hs ↦
      (recovery_action_density_bounds (hr.normalizedPotential_nonneg h hs) hδ).1
  · have he := intervalIntegral.integral_mono_on zero_le_one hj
      (hi.add (intervalIntegrable_const (c := Real.sqrt (2 * δ)))) fun s hs ↦
        (recovery_action_density_bounds (hr.normalizedPotential_nonneg h hs) hδ).2
    simpa only [intervalIntegral.integral_add hi intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul, phasePrimitive,
      recoveryActionPrimitive] using he

/-- Every positive regularization sequence tending to zero has the correct limiting action. -/
theorem RigidityHypotheses.recoveryActionPrimitive_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hzero : Filter.Tendsto δ Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun j ↦ recoveryActionPrimitive f (δ j) 1)
      Filter.atTop (𝓝 (phasePrimitive f 1)) := by
  have he : Filter.Tendsto (fun j ↦ Real.sqrt (2 * δ j)) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      (show Filter.Tendsto (fun j ↦ 2 * δ j) Filter.atTop (𝓝 0) by
        simpa using hzero.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using he.const_add (phasePrimitive f 1))
    (fun j ↦ (hr.recoveryActionPrimitive_bounds h (hδ j)).1)
    (fun j ↦ (hr.recoveryActionPrimitive_bounds h (hδ j)).2)

end SerrinEpigraph
