module

public import SerrinEpigraph.ModicaBound
public import SerrinEpigraph.LipschitzMollificationDerivative

/-!
# The sharp global Lipschitz bound for the zero extension

Local Lipschitz regularity and a bounded totalized derivative give a global
Lipschitz bound by averaging. This includes the nonsmooth free boundary.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric ContinuousLinearMap InnerProductSpace
open scoped Topology Convolution NNReal

namespace SerrinEpigraph

/-- Agreement on a radius-two ball implies agreement of every fixed average
on a neighborhood of its center. -/
theorem mollify_eventuallyEq_of_eqOn_closedBall {d : ℕ} {v w : Space d → ℝ}
    {x : Space d} (he : EqOn v w (closedBall x 2)) (n : ℕ) :
    mollify v n =ᶠ[𝓝 x] mollify w n := by
  filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with z hz
  apply integral_congr_ae
  filter_upwards with t
  simp only [lsmul_apply, smul_eq_mul]
  by_cases ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut
  · have ht1 : ‖t‖ ≤ 1 :=
      (by simpa only [mem_ball, dist_zero_right] using ht :
        ‖t‖ < (averagingBump d n).rOut).le.trans (averagingBump_rOut_le_one d n)
    have hzt : z - t ∈ closedBall x 2 := by
      rw [mem_closedBall, dist_eq_norm]
      have heq : z - t - x = (z - x) - t := by abel
      rw [heq]
      apply (norm_sub_le _ _).trans
      have hz' : ‖z - x‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
      linarith
    rw [he hzt]
  · have hk : (averagingBump d n).normed volume t = 0 :=
      Function.notMem_support.mp (by simpa [(averagingBump d n).support_normed_eq] using ht)
    rw [hk, zero_mul, zero_mul]

/-- Averaging preserves a global bound on the derivative of a locally
Lipschitz function, even where the original function is not differentiable. -/
theorem norm_fderiv_mollify_le_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ v x‖ ≤ C)
    (n : ℕ) (x : Space d) : ‖fderiv ℝ (mollify v n) x‖ ≤ C := by
  obtain ⟨L, hL⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall x 2)
  obtain ⟨w, hw, he⟩ := hL.extend_real
  rw [(mollify_eventuallyEq_of_eqOn_closedBall he n).fderiv_eq,
    (mollify_hasFDerivAt_of_lipschitz hw n x).fderiv]
  let k := (averagingBump d n).normed volume
  have hi : Integrable (fun t ↦ k t * C) := (averagingBump d n).integrable_normed.mul_const C
  have hb : ‖∫ t, k t • fderiv ℝ w (x - t)‖ ≤ ∫ t, k t * C := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with t
    by_cases ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut
    · have ht1 : ‖t‖ ≤ 1 :=
        (by simpa only [mem_ball, dist_zero_right] using ht :
          ‖t‖ < (averagingBump d n).rOut).le.trans (averagingBump_rOut_le_one d n)
      have hxt : x - t ∈ ball x 2 := by
        simpa only [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using
          lt_of_le_of_lt ht1 (by norm_num : (1 : ℝ) < 2)
      have he' : v =ᶠ[𝓝 (x - t)] w := by
        filter_upwards [closedBall_mem_nhds_of_mem hxt] with y hy
        exact he hy
      rw [norm_smul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t),
        ← he'.fderiv_eq]
      exact mul_le_mul_of_nonneg_left (hC (x - t))
        ((averagingBump d n).nonneg_normed t)
    · have hk : k t = 0 := Function.notMem_support.mp (by
        simpa only [k, (averagingBump d n).support_normed_eq] using ht)
      simp [hk]
  rw [integral_mul_const, (averagingBump d n).integral_normed, one_mul] at hb
  exact hb

/-- A locally Lipschitz function with uniformly bounded totalized derivative
has that same sharp global Lipschitz constant. -/
theorem lipschitzWith_of_locallyLipschitz_fderiv_bound {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {C : ℝ≥0} (hC : ∀ x, ‖fderiv ℝ v x‖ ≤ C) :
    LipschitzWith C v := by
  have hlip (n : ℕ) : LipschitzWith C (mollify v n) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      ((mollify_contDiff hv.continuous n).differentiable (by simp))
    intro x
    exact norm_fderiv_mollify_le_of_locallyLipschitz hv hC n x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((mollify_tendsto hv.continuous x).dist
    (mollify_tendsto hv.continuous y))
  exact Eventually.of_forall (fun n ↦ (hlip n).dist_le_mul x y)

/-- Modica's estimate and the exact boundary slope bound the totalized gradient
of the zero extension by the prescribed Neumann constant everywhere. -/
theorem RigidityHypotheses.gradient_zeroExtension_norm_le_kappa
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    ‖gradient (zeroExtension g u) x‖ ≤ κ := by
  by_cases hx : x ∈ epigraph g
  · rw [h.gradient_zeroExtension hx]
    have hmod := hr.modica_bound h hx
    have hpot := hr.normalizedPotential_antitoneOn h
      (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      ⟨(h.positive x hx).le, (hr.solution_lt_one x hx).le⟩ (h.positive x hx).le
    have hk := hr.kappa_sq_eq_twice_potential h
    nlinarith [norm_nonneg (gradient u x), h.kappa_pos]
  · rw [h.gradient_zeroExtension_of_notMem hx, norm_zero]
    exact h.kappa_pos.le

/-- The zero extension has the sharp global Lipschitz constant prescribed by
the boundary condition; no smoothness of its extension across the graph is used. -/
theorem RigidityHypotheses.zeroExtension_lipschitzWith
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    LipschitzWith ⟨κ, h.kappa_pos.le⟩ (zeroExtension g u) := by
  apply lipschitzWith_of_locallyLipschitz_fderiv_bound h.zeroExtension_locallyLipschitz
  intro x
  change ‖fderiv ℝ (zeroExtension g u) x‖ ≤ κ
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    hr.gradient_zeroExtension_norm_le_kappa h x

end SerrinEpigraph
