module

public import SerrinEpigraph.PhasePrimitive

/-!
# Spatial chain rule for the phase primitive
-/

public section

open MeasureTheory Metric Filter

namespace SerrinEpigraph

noncomputable section

/-- The phase primitive is nonnegative at nonnegative arguments. -/
theorem phasePrimitive_nonneg (f : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ phasePrimitive f s :=
  intervalIntegral.integral_nonneg_of_forall hs (fun _ ↦ Real.sqrt_nonneg _)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The chain rule holds for the totalized gradient, including the zero phase. -/
theorem RigidityHypotheses.gradient_phasePrimitive_zeroExtension
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    gradient (fun y ↦ phasePrimitive f (zeroExtension g u y)) x =
      Real.sqrt (2 * normalizedPotential f (zeroExtension g u x)) •
        gradient (zeroExtension g u) x := by
  by_cases hx : x ∈ epigraph g
  · have hu : DifferentiableAt ℝ u x :=
      (h.solution_contDiffOn.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
    have hU : DifferentiableAt ℝ (zeroExtension g u) x :=
      hu.congr_of_eventuallyEq (zeroExtension_eventuallyEq h.graph_contDiff.continuous hx)
    have hd := (h.phasePrimitive_hasDerivAt
      ⟨(h.zeroExtension_pos_iff x).mpr hx, hr.zeroExtension_lt_one x⟩).comp_hasFDerivAt x hU.hasFDerivAt
    have he : fderiv ℝ (fun y ↦ phasePrimitive f (zeroExtension g u y)) x =
        Real.sqrt (2 * normalizedPotential f (zeroExtension g u x)) •
          fderiv ℝ (zeroExtension g u) x := hd.fderiv
    simp only [gradient, he, map_smul]
  · have hmin : IsLocalMin (fun y ↦ phasePrimitive f (zeroExtension g u y)) x := by
      filter_upwards with y
      rw [zeroExtension_of_notMem hx, phasePrimitive_zero]
      exact phasePrimitive_nonneg f (h.zeroExtension_nonneg y)
    rw [h.gradient_zeroExtension_of_notMem hx, smul_zero]
    simp only [gradient, hmin.fderiv_eq_zero, map_zero]

/-- The primitive gradient norm is exactly the weighted gradient density. -/
theorem RigidityHypotheses.norm_gradient_phasePrimitive_zeroExtension
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u y)) x‖ =
      weightedGradientDensity f (zeroExtension g u) x := by
  rw [hr.gradient_phasePrimitive_zeroExtension h x, norm_smul]
  simp only [weightedGradientDensity, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Dilated phase primitives have uniformly bounded gradient integrals on fixed balls. -/
theorem RigidityHypotheses.rescaledPhasePrimitive_gradient_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 1 ≤ R * r →
      (∫ x in closedBall 0 r,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖) ≤ C * r ^ m := by
  obtain ⟨C, hC, hb⟩ := hr.rescaledWeightedGradient_bound h
  refine ⟨C, hC, fun R r hR hRr ↦ ?_⟩
  have he (x : Space (m + 1)) :
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖ =
        weightedGradientDensity f (fun y ↦ zeroExtension g u (R • y)) x := by
    rw [gradient_comp_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
      norm_smul, hr.norm_gradient_phasePrimitive_zeroExtension h,
      weightedGradientDensity_dilation f _ hR]
    simp only [Real.norm_eq_abs, abs_of_pos hR]
  simp_rw [he]
  exact hb R r hR hRr

end

end SerrinEpigraph
