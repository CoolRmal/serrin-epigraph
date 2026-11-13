module

public import SerrinEpigraph.CrossBoundaryMinimality
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Local energy bounds for Lipschitz competitors
-/

public section

open MeasureTheory Metric InnerProductSpace Filter

namespace SerrinEpigraph

/-- A locally Lipschitz competitor has a bounded totalized gradient on each compact set. -/
theorem gradient_bound_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K) :
    ∃ C : NNReal, ∀ x ∈ K, ‖gradient v x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨C, hC⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space d) R)
  refine ⟨C, fun x hx ↦ ?_⟩
  have hd := norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem (hR hx)) hC
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hd

/-- Local Lipschitz regularity gives a uniform gradient bound for all normalized averages. -/
theorem normalizedMollify_gradient_bound_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K) :
    ∃ C : NNReal, ∀ n x, x ∈ K → ‖gradient (normalizedMollify v n) x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨C, hC⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space d) (R + 1))
  refine ⟨C, fun n x hx ↦ ?_⟩
  have hm := normalizedMollify_lipschitzOn_closedBall hv.continuous hC n
  have hd := norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem (hR hx)) hm
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hd

/-- Locally Lipschitz competitors are differentiable almost everywhere in Euclidean space. -/
theorem ae_differentiableAt_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) : ∀ᵐ x, DifferentiableAt ℝ v x := by
  have hn : ∀ n : ℕ, ∀ᵐ x, x ∈ ball (0 : Space d) (n : ℝ) → DifferentiableAt ℝ v x := by
    intro n
    obtain ⟨C, hC⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : Space d) (n : ℝ))
    filter_upwards [hC.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx
    intro hxb
    exact (hx (ball_subset_closedBall hxb)).differentiableAt
      (closedBall_mem_nhds_of_mem hxb)
  filter_upwards [ae_all_iff.mpr hn] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa only [mem_ball, dist_zero_right] using hn)

/-- The squared gradient of a locally Lipschitz competitor is integrable on compact sets. -/
theorem integrableOn_gradient_sq_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ ‖gradient v x‖ ^ 2) K := by
  obtain ⟨C, hC⟩ := gradient_bound_of_locallyLipschitz hv hK
  have hi : IntegrableOn (fun _ : Space d ↦ (C : ℝ) ^ 2) K :=
    continuousOn_const.integrableOn_compact hK
  apply hi.mono' ((measurable_gradient v).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x hx) 2

/-- Every normalized locally Lipschitz competitor has finite local phase energy. -/
theorem Hypotheses.integrableOn_lipschitz_phaseEnergy
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) 1) (c : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (phaseEnergyDensity f c v) K := by
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv.continuous hval
  have hi := (((integrableOn_gradient_sq_of_locallyLipschitz hv hK).div_const 2).add
    (hW.continuousOn.integrableOn_compact hK)).add
      (continuousOn_const.integrableOn_compact (μ := volume) hK (f := fun _ ↦ c))
  exact hi.indicator (isOpen_lt continuous_const hv.continuous).measurableSet

end SerrinEpigraph
