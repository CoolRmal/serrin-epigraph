module

public import SerrinEpigraph.PhasePrimitiveRegularity
public import SerrinEpigraph.PhaseIndicatorApproximation

/-!
# Approximation of the phase primitive by a phase indicator
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

noncomputable section

/-- Error from replacing the primitive by its two equilibrium values. -/
@[expose] def primitiveIndicatorError {d : ℕ} (f : ℝ → ℝ) (U : Space d → ℝ)
    (x : Space d) : ℝ :=
  |phasePrimitive f 1 * positivePhaseIndicator U x - phasePrimitive f (U x)|

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The primitive's Lipschitz constant transfers the indicator error pointwise. -/
theorem RigidityHypotheses.primitiveIndicatorError_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    primitiveIndicatorError f (zeroExtension g u) x ≤
      Real.sqrt (2 * normalizedPotential f 0) * phaseIndicatorError (zeroExtension g u) x := by
  by_cases hp : 0 < zeroExtension g u x
  · have he := (hr.phasePrimitive_lipschitzOn h).dist_le_mul 1
      (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) (zeroExtension g u x)
      ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩
    simp only [primitiveIndicatorError, phaseIndicatorError, positivePhaseIndicator,
      Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_true, mul_one]
    convert he using 1
    rw [Real.dist_eq]
    rfl
  · have hz := le_antisymm (le_of_not_gt hp) (h.zeroExtension_nonneg x)
    simp [primitiveIndicatorError, phaseIndicatorError, positivePhaseIndicator, hz]

/-- The primitive indicator error is integrable on every compact set after dilation. -/
theorem RigidityHypotheses.integrableOn_primitiveIndicatorError
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (R : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ primitiveIndicatorError f (zeroExtension g u) (R • x)) K := by
  have hc : Continuous (fun x : Space (m + 1) ↦ zeroExtension g u (R • x)) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul R)
  have hi : IntegrableOn ({x | 0 < zeroExtension g u (R • x)}.indicator (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator
      (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
  have hΦ : Continuous (fun x : Space (m + 1) ↦ phasePrimitive f (zeroExtension g u (R • x))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp (continuous_id.const_smul R)
  exact ((hi.const_mul (phasePrimitive f 1)).sub (hΦ.continuousOn.integrableOn_compact hK)).abs

/-- On each fixed ball the dilated phase primitive approaches the weighted phase indicator. -/
theorem RigidityHypotheses.primitiveIndicatorError_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫ x in closedBall 0 r,
      primitiveIndicatorError f (zeroExtension g u) (R • x)) atTop (𝓝 0) := by
  have ht := (hr.phaseIndicatorError_tendsto_zero h hradius).const_mul
    (Real.sqrt (2 * normalizedPotential f 0))
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro R
    exact integral_nonneg (fun x ↦ abs_nonneg _)
  · intro R
    dsimp only
    rw [← integral_const_mul]
    exact integral_mono
      (hr.integrableOn_primitiveIndicatorError h R (isCompact_closedBall 0 r))
      ((h.integrableOn_phaseIndicatorError R (isCompact_closedBall 0 r)).const_mul _)
      (fun x ↦ hr.primitiveIndicatorError_le h (R • x))

end

end SerrinEpigraph
