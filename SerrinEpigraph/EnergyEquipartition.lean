module

public import SerrinEpigraph.RescaledDiscrepancy

/-!
# Asymptotic agreement of diffuse energy and phase-primitive variation
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The rescaled discrepancy is locally integrable for normalized locally Lipschitz functions. -/
theorem Hypotheses.integrableOn_rescaledDiscrepancy (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (R : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (rescaledDiscrepancyDensity f R v) K := by
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv.continuous hval
  exact (((hW.continuousOn.integrableOn_compact hK).const_mul R).sub
    ((integrableOn_gradient_sq_of_locallyLipschitz hv hK).div_const (2 * R))).indicator
      (isOpen_lt continuous_const hv.continuous).measurableSet

/-- The rescaled discrepancy of the solution is nonnegative everywhere. -/
theorem RigidityHypotheses.rescaledDiscrepancy_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 < R) (x : Space (m + 1)) :
    0 ≤ rescaledDiscrepancyDensity f R (fun y ↦ zeroExtension g u (R • y)) x := by
  rw [rescaledDiscrepancyDensity_dilation f _ hR]
  exact mul_nonneg hR.le (hr.phaseDiscrepancy_nonneg h _)

/-- The diffuse energy minus primitive variation lies between zero and the bulk discrepancy. -/
theorem RigidityHypotheses.phaseEnergy_sub_primitive_gradient_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    phaseEnergyDensity f 0 (zeroExtension g u) x -
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u y)) x‖ ∈
        Icc 0 (phaseDiscrepancyDensity f (zeroExtension g u) x) := by
  rw [hr.norm_gradient_phasePrimitive_zeroExtension h x]
  refine ⟨sub_nonneg.mpr (hr.weightedGradient_le_energy h x), ?_⟩
  by_cases hx : x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff x).mpr hx
    have hM : ‖gradient (zeroExtension g u) x‖ ^ 2 / 2 ≤
        normalizedPotential f (zeroExtension g u x) := by
      rw [h.gradient_zeroExtension hx, zeroExtension_of_mem hx]
      exact hr.modica_bound h hx
    have hW : 0 ≤ 2 * normalizedPotential f (zeroExtension g u x) := by
      nlinarith [sq_nonneg ‖gradient (zeroExtension g u) x‖]
    have hsq := Real.sq_sqrt hW
    have hroot : ‖gradient (zeroExtension g u) x‖ ≤
        Real.sqrt (2 * normalizedPotential f (zeroExtension g u x)) := by
      nlinarith [norm_nonneg (gradient (zeroExtension g u) x), Real.sqrt_nonneg
        (2 * normalizedPotential f (zeroExtension g u x))]
    rw [phaseEnergyDensity, phaseDiscrepancyDensity,
      indicator_of_mem (s := {y | 0 < zeroExtension g u y}) hp,
      indicator_of_mem (s := {y | 0 < zeroExtension g u y}) hp]
    dsimp only [weightedGradientDensity]
    nlinarith [mul_nonneg (norm_nonneg (gradient (zeroExtension g u) x)) (sub_nonneg.mpr hroot)]
  · have hp : ¬0 < zeroExtension g u x := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
    simp [phaseEnergyDensity, phaseDiscrepancyDensity, weightedGradientDensity,
      hp, h.gradient_zeroExtension_of_notMem hx]

/-- The same sharp discrepancy bound holds for the rescaled energy and primitive. -/
theorem RigidityHypotheses.rescaledEnergy_sub_primitive_gradient_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 < R) (x : Space (m + 1)) :
    rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x -
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x‖ ∈
        Icc 0 (rescaledDiscrepancyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) := by
  rw [rescaledPhaseEnergyDensity_dilation f _ hR,
    gradient_comp_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
    norm_smul, Real.norm_of_nonneg hR.le, rescaledDiscrepancyDensity_dilation f _ hR, ← mul_sub]
  have hb := hr.phaseEnergy_sub_primitive_gradient_bounds h (R • x)
  exact ⟨mul_nonneg hR.le hb.1, mul_le_mul_of_nonneg_left hb.2 hR.le⟩

/-- Vanishing bulk defects imply vanishing discrepancy on every compact set. -/
theorem RigidityHypotheses.rescaledDiscrepancy_tendsto_zero_compact
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hB : ∀ k : ℕ, Tendsto (fun j ↦
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      rescaledDiscrepancyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)
        atTop (𝓝 0) := by
  obtain ⟨r, hradius⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have hsub : K ⊆ closedBall 0 (k + 1 : ℝ) :=
    hradius.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  apply squeeze_zero (fun j ↦ integral_nonneg (hr.rescaledDiscrepancy_nonneg h (hR j))) _
    (hr.rescaledDiscrepancy_tendsto_zero h hR hB k)
  intro j
  have hv := h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hval (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  exact setIntegral_mono_set
    (h.integrableOn_rescaledDiscrepancy hv hval (R j) (isCompact_closedBall _ _))
    (Eventually.of_forall (hr.rescaledDiscrepancy_nonneg h (hR j))) (Eventually.of_forall hsub)

/-- Along the common defect scales, diffuse energy and primitive gradient mass agree
asymptotically on every compact set. -/
theorem RigidityHypotheses.rescaled_energy_primitive_gap_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hB : ∀ k : ℕ, Tendsto (fun j ↦
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦
      (∫ x in K, rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x) -
      (∫ x in K, ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖))
        atTop (𝓝 0) := by
  have hb (j : ℕ) :
      (∫ x in K, rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x) -
      (∫ x in K, ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖) ∈
      Icc 0 (∫ x in K,
        rescaledDiscrepancyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x) := by
    have hv := h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
    have hval (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
    have hi := h.integrableOn_rescaledPhaseEnergy hv hval (R j) hK
    dsimp only [Function.comp_def] at hi
    have hg : IntegrableOn
        (fun x ↦ ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖) K := by
      apply hi.mono' (measurable_gradient _).norm.aestronglyMeasurable
      exact Eventually.of_forall (fun x ↦ by
        rw [norm_norm]
        exact hr.rescaledPrimitive_gradient_le_energy h (hR j) x)
    rw [← integral_sub hi hg]
    refine ⟨integral_nonneg (fun x ↦
      (hr.rescaledEnergy_sub_primitive_gradient_bounds h (hR j) x).1), ?_⟩
    exact integral_mono (hi.sub hg) (h.integrableOn_rescaledDiscrepancy hv hval (R j) hK)
      (fun x ↦ (hr.rescaledEnergy_sub_primitive_gradient_bounds h (hR j) x).2)
  exact squeeze_zero (fun j ↦ (hb j).1) (fun j ↦ (hb j).2)
    (hr.rescaledDiscrepancy_tendsto_zero_compact h hR hB hK)

end SerrinEpigraph
