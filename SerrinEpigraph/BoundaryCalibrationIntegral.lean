module

public import SerrinEpigraph.BoundaryCalibration

/-!
# Integrable boundary calibrations for smooth nonnegative competitors
-/

public section
noncomputable section

open InnerProductSpace MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The closed foliation gradient is continuous throughout the half-closed level strip. -/
theorem RigidityHypotheses.closedLevelGradient_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ContinuousOn (hr.closedLevelGradient h) {p | p.2 ∈ Set.Ico (0 : ℝ) 1} := by
  intro p hp
  rcases eq_or_lt_of_le hp.1 with hz | hp0
  · have he : p = (p.1, 0) := by ext <;> simp [hz]
    rw [he]
    exact (hr.closedLevelGradient_continuousAt_zero h p.1).continuousWithinAt
  · have hd := h.solution_contDiffOn_closure.continuousOn_fderivWithin
      (uniqueDiffOn_closure_epigraph h.graph_contDiff.differentiable_one) le_rfl
    have hc : ContinuousOn (gradientWithin u (closure (epigraph g)))
        (closure (epigraph g)) :=
      (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn hd
    have ht := (hc _ (hr.levelPoint_mem_closure h p)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨(hr.levelPoint_contDiffAt h ⟨hp0, hp.2⟩).continuousAt,
          Filter.Eventually.of_forall (hr.levelPoint_mem_closure h)⟩)
    have hcAt : ContinuousAt (hr.closedLevelGradient h) p := ht
    exact hcAt.continuousWithinAt

/-- Smooth competitors below one have continuous closed calibration density even at zeros. -/
theorem RigidityHypotheses.boundaryCalibratedDensity_continuous
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1) :
    Continuous (fun x ↦ hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x)) := by
  have hB : Continuous (fun x ↦ hr.closedLevelGradient h (horizontal x, v x)) :=
    (hr.closedLevelGradient_continuousOn h).comp_continuous
      (continuous_horizontal.prodMk hv.continuous) (fun x ↦ hval x)
  have hG : Continuous (gradient v) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp
      (hv.continuous_fderiv (by norm_num))
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv.continuous
      (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩)
  exact (((hB.inner hG).sub ((hB.norm.pow 2).div_const 2)).add hW).add continuous_const

/-- The calibration density of a smooth competitor is integrable on compact sets. -/
theorem RigidityHypotheses.integrableOn_boundaryCalibratedDensity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x)) K :=
  (hr.boundaryCalibratedDensity_continuous h hv hval).continuousOn.integrableOn_compact hK

/-- Smooth normalized competitors have finite phase energy on every compact set. -/
theorem Hypotheses.integrableOn_phaseEnergy_competitor (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v)
    (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) 1) (c : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (phaseEnergyDensity f c v) K := by
  have hG : Continuous (gradient v) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hv.continuous_fderiv (by norm_num))
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv.continuous hval
  have hi := ((((hG.norm.pow 2).div_const 2).add hW).add
    (continuous_const (y := c))).continuousOn.integrableOn_compact (μ := volume) hK
  exact hi.indicator ((isOpen_lt continuous_const hv.continuous).measurableSet)

/-- The pointwise calibration bound integrates for competitors that can touch the zero phase. -/
theorem RigidityHypotheses.integral_boundaryCalibratedDensity_le_phaseEnergy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    (∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x)) ≤
      ∫ x in K, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) v x := by
  apply integral_mono (hr.integrableOn_boundaryCalibratedDensity h hv hval hK)
    (h.integrableOn_phaseEnergy_competitor hv (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩) _ hK)
  exact hr.boundaryCalibratedDensity_le_phaseEnergy h (fun x ↦ (hval x).1)

end SerrinEpigraph
