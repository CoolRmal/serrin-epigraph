module

public import SerrinEpigraph.RescaledPhaseEnergy

/-!
# Uniform weighted gradient bounds
-/

public section

open MeasureTheory Metric
open scoped Pointwise

namespace SerrinEpigraph

noncomputable section

/-- The potential-weighted gradient associated with the phase primitive. -/
@[expose] def weightedGradientDensity {d : ℕ} (f : ℝ → ℝ) (v : Space d → ℝ)
    (x : Space d) : ℝ :=
  Real.sqrt (2 * normalizedPotential f (v x)) * ‖gradient v x‖

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Young's inequality controls the weighted gradient by the phase energy. -/
theorem RigidityHypotheses.weightedGradient_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    weightedGradientDensity f (zeroExtension g u) x ≤
      phaseEnergyDensity f 0 (zeroExtension g u) x := by
  by_cases hx : x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff x).mpr hx
    have hW := hr.normalizedPotential_nonneg h
      ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩
    have hs := Real.sq_sqrt (show 0 ≤ 2 * normalizedPotential f (zeroExtension g u x) by positivity)
    have hy := sq_nonneg
      (‖gradient (zeroExtension g u) x‖ - Real.sqrt (2 * normalizedPotential f (zeroExtension g u x)))
    simp only [weightedGradientDensity, phaseEnergyDensity, Set.indicator_apply,
      Set.mem_ofPred_eq, hp, ite_true, add_zero]
    nlinarith
  · have hp : ¬0 < zeroExtension g u x := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
    simp [weightedGradientDensity, h.gradient_zeroExtension_of_notMem hx,
      phaseEnergyDensity, hp]

/-- The weighted gradient is integrable on every compact set. -/
theorem RigidityHypotheses.integrableOn_weightedGradient
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (weightedGradientDensity f (zeroExtension g u)) K := by
  have hc : Continuous (fun x ↦ Real.sqrt (2 * normalizedPotential f (zeroExtension g u x))) :=
    (continuous_const.mul (h.normalizedPotential_continuousOn.comp_continuous
      h.zeroExtension_continuous
      (fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩))).sqrt
  apply (hr.integrableOn_phaseEnergy_zeroExtension h 0 hK).mono'
    (hc.measurable.mul (measurable_gradient _).norm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    change ‖weightedGradientDensity f (zeroExtension g u) x‖ ≤ _
    rw [Real.norm_of_nonneg (show 0 ≤ weightedGradientDensity f (zeroExtension g u) x by
      exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact hr.weightedGradient_le_energy h x)

/-- Positive dilation scales the weighted gradient by the dilation factor. -/
theorem weightedGradientDensity_dilation {d : ℕ} (f : ℝ → ℝ) (U : Space d → ℝ)
    {R : ℝ} (hR : 0 < R) (x : Space d) :
    weightedGradientDensity f (fun y ↦ U (R • y)) x =
      R * weightedGradientDensity f U (R • x) := by
  simp only [weightedGradientDensity, gradient_comp_dilation, norm_smul,
    Real.norm_eq_abs, abs_of_pos hR]
  ring

/-- Uniform local weighted gradient bounds for the dilated solution. -/
theorem RigidityHypotheses.rescaledWeightedGradient_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 1 ≤ R * r →
      (∫ x in closedBall 0 r,
        weightedGradientDensity f (fun y ↦ zeroExtension g u (R • y)) x) ≤ C * r ^ m := by
  obtain ⟨C, hC, hb⟩ := hr.phaseEnergy_surface_growth h
  refine ⟨C, hC, fun R r hR hRr ↦ ?_⟩
  simp_rw [weightedGradientDensity_dilation f _ hR]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume _ _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hi := integral_mono (hr.integrableOn_weightedGradient h (isCompact_closedBall 0 (R * r)))
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall 0 (R * r)))
    (hr.weightedGradient_le_energy h)
  calc
    _ ≤ R * ((R ^ (m + 1))⁻¹ * (C * (R * r) ^ m)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hi.trans (hb (R * r) hRr)) (by positivity)) hR.le
    _ = C * r ^ m := by rw [mul_pow, pow_succ]; field_simp

end

end SerrinEpigraph
