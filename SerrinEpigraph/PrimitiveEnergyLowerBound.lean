module

public import SerrinEpigraph.SharpDivergenceBound

/-!
# Exact energy control of the rescaled primitive and its divergence tests
-/

public section

open MeasureTheory Metric Filter
open scoped Topology Pointwise ENNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The rescaled primitive gradient is pointwise bounded by the rescaled phase energy. -/
theorem RigidityHypotheses.rescaledPrimitive_gradient_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 < R) (x : Space (m + 1)) :
    ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖ ≤
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x := by
  rw [gradient_comp_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
    norm_smul, Real.norm_of_nonneg hR.le,
    hr.norm_gradient_phasePrimitive_zeroExtension h, rescaledPhaseEnergyDensity_dilation f _ hR]
  exact mul_le_mul_of_nonneg_left (hr.weightedGradient_le_energy h _) hR.le

/-- The primitive gradient mass is bounded by energy with the exact coefficient one. -/
theorem RigidityHypotheses.rescaledPrimitive_gradient_integral_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖) ≤
    ∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x := by
  simp_rw [gradient_comp_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
    norm_smul, Real.norm_of_nonneg hR.le,
    hr.norm_gradient_phasePrimitive_zeroExtension h, rescaledPhaseEnergyDensity_dilation f _ hR]
  rw [integral_const_mul, integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hR.le
  rw [Measure.setIntegral_comp_smul_of_pos volume _ _ hR,
    Measure.setIntegral_comp_smul_of_pos volume _ _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_of_nonneg hR.le, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono (hr.integrableOn_weightedGradient h (isCompact_closedBall 0 (R * r)))
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall 0 (R * r)))
    (hr.weightedGradient_le_energy h)

/-- Every admissible vector test of a rescaled primitive is bounded by its diffuse energy. -/
theorem RigidityHypotheses.rescaledPrimitive_divergence_test_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {R : ℝ} (hR : 0 < R) (r : ℝ) {F : Space (m + 1) → Space (m + 1)}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ closedBall 0 r) (hb : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x in closedBall 0 r,
      phasePrimitive f (zeroExtension g u (R • x)) * fieldDivergence b F x‖ ≤
    ∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x := by
  have hlip : LocallyLipschitz
      (fun x ↦ phasePrimitive f (zeroExtension g u (R • x))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul R).locallyLipschitz
  have hval (x : Space (m + 1)) :
      phasePrimitive f (zeroExtension g u (R • x)) ∈ Set.Icc 0 (phasePrimitive f 1) :=
    h.phasePrimitive_mem_Icc ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  exact (norm_setIntegral_mul_divergence_le_gradient_of_locallyLipschitz b hlip hval
    hF hc (isCompact_closedBall 0 r) hs hb).trans
    (hr.rescaledPrimitive_gradient_integral_le_energy h hR r)

/-- Each limiting primitive divergence pairing is bounded by the diffuse-energy liminf. -/
theorem RigidityHypotheses.primitive_limit_test_le_energy_liminf
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (r : ℝ)
    (v : Space (m + 1) → ℝ) (hv : IntegrableOn v (closedBall 0 r))
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖phasePrimitive f (zeroExtension g u (R j • x)) - v x‖) atTop (𝓝 0))
    {F : Space (m + 1) → Space (m + 1)} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ closedBall 0 r) (hb : ∀ x, ‖F x‖ ≤ 1) :
    ENNReal.ofReal ‖∫ x in closedBall 0 r, v x * fieldDivergence b F x‖ ≤
      liminf (fun j ↦ ENNReal.ofReal (∫ x in closedBall 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)) atTop := by
  have hcont := fieldDivergence_continuous b hF
  have hsupport : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hcompact : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have htest := integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict (closedBall 0 r))
    (fun j x ↦ phasePrimitive f (zeroExtension g u (R j • x))) v (fieldDivergence b F) C
    (fun j ↦ ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R j))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 r)) hv hcont.aestronglyMeasurable hC ht
  rw [← (ENNReal.tendsto_ofReal htest.norm).liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun j ↦ ENNReal.ofReal_le_ofReal
    (hr.rescaledPrimitive_divergence_test_le_energy h b (hR j) r hF hc hs hb)))

end SerrinEpigraph
