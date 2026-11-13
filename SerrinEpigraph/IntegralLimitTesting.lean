module

public import SerrinEpigraph.GlobalPhaseSet

/-!
# Testing local integral limits against bounded functions
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Integral convergence permits testing against any bounded measurable scalar function. -/
theorem integral_mul_tendsto_of_integral_norm_sub_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (v ψ : X → ℝ) (C : ℝ)
    (hF : ∀ j, Integrable (F j) μ) (hv : Integrable v μ)
    (hψ : AEStronglyMeasurable ψ μ) (hbound : ∀ x, ‖ψ x‖ ≤ C)
    (ht : Tendsto (fun j ↦ ∫ x, ‖F j x - v x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x, F j x * ψ x ∂μ) atTop (𝓝 (∫ x, v x * ψ x ∂μ)) := by
  have hmulF (j : ℕ) := (hF j).mul_bdd hψ (Eventually.of_forall hbound)
  have hmulv := hv.mul_bdd hψ (Eventually.of_forall hbound)
  have hmajor := ht.const_mul C
  simp only [mul_zero] at hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
  · intro j
    exact norm_nonneg _
  · intro j
    dsimp only
    rw [← integral_sub (hmulF j) hmulv]
    calc
      ‖∫ x, F j x * ψ x - v x * ψ x ∂μ‖ ≤
          ∫ x, ‖F j x * ψ x - v x * ψ x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, C * ‖F j x - v x‖ ∂μ := by
        apply integral_mono ((hmulF j).sub hmulv).norm (((hF j).sub hv).norm.const_mul C)
        intro x
        simp only [Pi.sub_apply]
        rw [← sub_mul, norm_mul]
        exact (mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)).trans_eq (mul_comm _ _)
      _ = C * ∫ x, ‖F j x - v x‖ ∂μ := integral_const_mul _ _

/-- A uniform bound on tested integrals passes to their integral-norm limit. -/
theorem integral_mul_bound_of_integral_limit
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (v ψ : X → ℝ) (C B : ℝ)
    (hF : ∀ j, Integrable (F j) μ) (hv : Integrable v μ)
    (hψ : AEStronglyMeasurable ψ μ) (hbound : ∀ x, ‖ψ x‖ ≤ C)
    (ht : Tendsto (fun j ↦ ∫ x, ‖F j x - v x‖ ∂μ) atTop (𝓝 0))
    (hB : ∀ j, ‖∫ x, F j x * ψ x ∂μ‖ ≤ B) :
    ‖∫ x, v x * ψ x ∂μ‖ ≤ B := by
  exact le_of_tendsto
    (integral_mul_tendsto_of_integral_norm_sub_tendsto μ F v ψ C hF hv hψ hbound ht).norm
    (Eventually.of_forall hB)

/-- The primitive subsequence converges against every bounded measurable local test. -/
theorem RigidityHypotheses.phasePrimitive_tested_phase_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      ∀ (k : ℕ) (ψ : Space (m + 1) → ℝ) (C : ℝ),
        AEStronglyMeasurable ψ (volume.restrict (closedBall 0 (k + 1 : ℝ))) →
        (∀ x, ‖ψ x‖ ≤ C) →
        Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          phasePrimitive f (zeroExtension g u (R (φ j) • x)) * ψ x) atTop
          (𝓝 (∫ x in closedBall 0 (k + 1 : ℝ),
            E.indicator (fun _ ↦ phasePrimitive f 1) x * ψ x)) := by
  obtain ⟨φ, hφ, E, hE, ht⟩ := hr.phasePrimitive_measurable_phase_limit h R hR hRtop
  refine ⟨φ, hφ, E, hE, fun k ψ C hψ hb ↦ ?_⟩
  apply integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict (closedBall 0 (k + 1 : ℝ))) _ _ ψ C _ _ hψ hb (ht k)
  · intro j
    exact ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R (φ j)))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 (k + 1 : ℝ))
  · exact (continuousOn_const.integrableOn_compact
      (isCompact_closedBall 0 (k + 1 : ℝ))).indicator hE

end SerrinEpigraph
