module

public import SerrinEpigraph.PhasePrimitive

/-!
# Regularized travel time for a one-dimensional recovery profile
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- Travel time with positive regularization of the potential, avoiding the singular
time needed to reach the equilibrium of the unregularized profile. -/
@[expose] noncomputable def recoveryTravelTime (f : ℝ → ℝ) (δ s : ℝ) : ℝ :=
  ∫ t in 0..s, (Real.sqrt (2 * (normalizedPotential f t + δ)))⁻¹

@[simp] theorem recoveryTravelTime_zero (f : ℝ → ℝ) (δ : ℝ) :
    recoveryTravelTime f δ 0 = 0 := by simp [recoveryTravelTime]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- The regularized reciprocal speed is continuous even at the equilibrium endpoint. -/
theorem RigidityHypotheses.recovery_inverse_speed_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    ContinuousOn (fun t ↦ (Real.sqrt (2 * (normalizedPotential f t + δ)))⁻¹)
      (Icc (0 : ℝ) 1) := by
  apply (continuousOn_const.mul
    (h.normalizedPotential_continuousOn.add continuousOn_const)).sqrt.inv₀
  intro x hx
  have hw := hr.normalizedPotential_nonneg h hx
  change Real.sqrt (2 * (normalizedPotential f x + δ)) ≠ 0
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

/-- The travel-time coordinate is continuous on the entire normalized interval. -/
theorem RigidityHypotheses.recoveryTravelTime_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    ContinuousOn (recoveryTravelTime f δ) (Icc (0 : ℝ) 1) := by
  have hi : IntegrableOn (fun t ↦ (Real.sqrt (2 * (normalizedPotential f t + δ)))⁻¹)
      (uIcc (0 : ℝ) 1) volume := by
    simpa only [uIcc_of_le zero_le_one] using
      (hr.recovery_inverse_speed_continuousOn h hδ).integrableOn_Icc (μ := volume)
  change ContinuousOn (fun s ↦ ∫ t in 0..s,
    (Real.sqrt (2 * (normalizedPotential f t + δ)))⁻¹) (Icc (0 : ℝ) 1)
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval hi

/-- The travel-time derivative is the reciprocal regularized speed. -/
theorem RigidityHypotheses.recoveryTravelTime_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (recoveryTravelTime f δ)
      (Real.sqrt (2 * (normalizedPotential f s + δ)))⁻¹ s := by
  have hc := hr.recovery_inverse_speed_continuousOn h hδ
  have hi := (hc.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc
    (μ := volume) hs.1.le
  have hc' := hc.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hc'.stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hc'.continuousAt (isOpen_Ioo.mem_nhds hs))

/-- Positive reciprocal speed makes the travel-time coordinate strictly increasing. -/
theorem RigidityHypotheses.recoveryTravelTime_strictMonoOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    StrictMonoOn (recoveryTravelTime f δ) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hc := hr.recovery_inverse_speed_continuousOn h hδ
  have hi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
    (hc.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc (μ := volume) hs.1
  rw [← sub_pos, recoveryTravelTime, recoveryTravelTime,
    intervalIntegral.integral_interval_sub_left (hi b hb) (hi a ha)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hc.mono (Icc_subset_Icc ha.1 hb.2)).intervalIntegrable_of_Icc hab.le) _ hab
  intro s hs
  have hw := hr.normalizedPotential_nonneg h ⟨ha.1.trans hs.1.le, hs.2.le.trans hb.2⟩
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

/-- The full regularized transition takes a strictly positive finite real time. -/
theorem RigidityHypotheses.recoveryTravelTime_one_pos
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    0 < recoveryTravelTime f δ 1 := by
  simpa only [recoveryTravelTime_zero] using
    hr.recoveryTravelTime_strictMonoOn h hδ (by norm_num) (by norm_num) zero_lt_one

end SerrinEpigraph
