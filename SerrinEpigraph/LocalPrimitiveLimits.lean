module

public import SerrinEpigraph.IntegralCauchyApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Local integral limits of the unsmoothed phase primitive
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- An integral Cauchy sequence of integrable real functions has an integrable limit. -/
theorem exists_integral_limit_of_cauchy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (hF : ∀ j, Integrable (F j) μ)
    (hc : ∀ ε, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N, (∫ x, ‖F i x - F j x‖ ∂μ) < ε) :
    ∃ v : X → ℝ, Integrable v μ ∧
      Tendsto (fun j ↦ ∫ x, ‖F j x - v x‖ ∂μ) atTop (𝓝 0) := by
  let G := fun j ↦ (hF j).toL1 (F j)
  have he (i j : ℕ) : dist (G i) (G j) = ∫ x, ‖F i x - F j x‖ ∂μ := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF i).coeFn_toL1, (hF j).coeFn_toL1] with x hi hj
    simp only [G, hi, hj, dist_eq_norm]
  have hG : CauchySeq G := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    exact ⟨N, fun i hi j hj ↦ (he i j).symm ▸ hN i hi j hj⟩
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hG
  refine ⟨v, L1.integrable_coeFn v, ?_⟩
  have ht := tendsto_iff_dist_tendsto_zero.mp hv
  apply ht.congr'
  exact Eventually.of_forall (fun j ↦ by
    dsimp only
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF j).coeFn_toL1] with x hx
    simp only [G, hx, dist_eq_norm])

/-- The unsmoothed primitive has local integrable limits along one subsequence on all integer balls. -/
theorem RigidityHypotheses.phasePrimitive_local_integral_limits
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, ∃ v : Space (m + 1) → ℝ,
      IntegrableOn v (Metric.closedBall 0 (k + 1 : ℝ)) ∧
        Tendsto (fun j ↦ ∫ x in Metric.closedBall 0 (k + 1 : ℝ),
          ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) - v x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hc⟩ := hr.phasePrimitive_integral_cauchy_subsequence h R hR
  refine ⟨φ, hφ, fun k ↦ ?_⟩
  apply exists_integral_limit_of_cauchy (volume.restrict (Metric.closedBall 0 (k + 1 : ℝ)))
    (fun j x ↦ phasePrimitive f (zeroExtension g u (R (φ j) • x))) _ (hc k)
  intro j
  exact ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
    (continuous_id.const_smul (R (φ j)))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 (k + 1 : ℝ))

end SerrinEpigraph
