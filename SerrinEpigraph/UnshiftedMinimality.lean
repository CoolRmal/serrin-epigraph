module

public import SerrinEpigraph.CrossBoundaryMinimality
public import SerrinEpigraph.AnnularSlopeComparison

/-!
# Unshifted free-boundary energy comparison

The exact Neumann energy identity removes the additive phase constant from the
calibration comparison. The competitor class remains compact C¹ perturbations
of the zero extension with values in [0,1).
-/

public section

open MeasureTheory Metric

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The constant phase-energy shift vanishes under the original rigidity hypotheses. -/
theorem RigidityHypotheses.phaseEnergy_shift_eq_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    κ ^ 2 / 2 - normalizedPotential f 0 = 0 := by
  rw [hr.kappa_sq_eq_twice_potential h]
  ring

/-- Compact C¹ perturbations cannot decrease the unshifted free-boundary energy
on any compact set containing their support. -/
theorem RigidityHypotheses.unshifted_phaseEnergy_minimal_on_compact
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in K, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
      ∫ x in K, phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u y + φ y) x := by
  simpa only [hr.phaseEnergy_shift_eq_zero h] using
    hr.phaseEnergy_minimal_on_compact h hφ hK hsupp hval

/-- Every compact C¹ perturbation admits an enclosing ball on which the original
unshifted phase energy is no larger than the competitor energy. -/
theorem RigidityHypotheses.unshifted_phaseEnergy_minimal_compact_perturbation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ R : ℝ, tsupport φ ⊆ closedBall 0 R ∧
      (∫ x in closedBall 0 R, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        ∫ x in closedBall 0 R,
          phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u y + φ y) x := by
  simpa only [hr.phaseEnergy_shift_eq_zero h] using
    hr.phaseEnergy_minimal_compact_perturbation h hφ hsupp hval

end SerrinEpigraph
