module

public import SerrinEpigraph.RadialDilationEstimate

/-!
# Radial dilation estimates for locally Lipschitz functions
-/

public section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- Normalized mollification recovers the radial variation on a compact set. -/
theorem normalizedMollify_integral_radial_tendsto
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, ‖inner ℝ (gradient (normalizedMollify v n) x) x‖) atTop
      (𝓝 (∫ x in K, ‖inner ℝ (gradient v x) x‖)) := by
  obtain ⟨C, hC⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hv hK
  apply tendsto_integral_of_dominated_convergence (fun x ↦ (C : ℝ) * ‖x‖)
  · intro n
    have hm := ((measurable_gradient (normalizedMollify v n)).inner (𝕜 := ℝ) measurable_id).norm
    exact hm.aestronglyMeasurable.restrict
  · exact (continuous_const.mul continuous_id.norm).continuousOn.integrableOn_compact hK
  · intro n
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [norm_norm]
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right (hC n x hx) (norm_nonneg x))
  · filter_upwards [ae_restrict_of_ae
      (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hv)] with x hx
    exact (hx.inner tendsto_const_nhds).norm

/-- Mollification also recovers the local integral difference under a fixed dilation. -/
theorem normalizedMollify_integral_dilation_tendsto
    {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) B) (r a : ℝ) :
    Tendsto (fun n ↦ ∫ x in closedBall 0 r,
      ‖normalizedMollify v n (a • x) - normalizedMollify v n x‖) atTop
      (𝓝 (∫ x in closedBall 0 r, ‖v (a • x) - v x‖)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * B)
  · intro n
    have hc := (normalizedMollify_contDiff hv n).continuous
    exact (((hc.comp (continuous_id.const_smul a)).sub hc).norm.aestronglyMeasurable).restrict
  · exact continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)
  · intro n
    exact Eventually.of_forall (fun x ↦ by
      have ha := normalizedMollify_mem_Icc_of_bounds hv hval n (a • x)
      have hx := normalizedMollify_mem_Icc_of_bounds hv hval n x
      rw [norm_norm]
      calc
        _ ≤ ‖normalizedMollify v n (a • x)‖ + ‖normalizedMollify v n x‖ := norm_sub_le _ _
        _ ≤ 2 * B := by
          rw [Real.norm_of_nonneg ha.1, Real.norm_of_nonneg hx.1]
          linarith [ha.2, hx.2])
  · exact Eventually.of_forall (fun x ↦
      ((normalizedMollify_tendsto hv (a • x)).sub (normalizedMollify_tendsto hv x)).norm)

/-- The radial-variation estimate extends across the zero interface of a locally Lipschitz
function with bounded nonnegative range. -/
theorem integral_norm_dilation_sub_le_of_locallyLipschitz
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) B)
    {r a : ℝ} (hr : 0 ≤ r) (ha : 1 ≤ a) :
    (∫ x in closedBall 0 r, ‖v (a • x) - v x‖) ≤
      (a - 1) * ∫ x in closedBall 0 (a * r), ‖inner ℝ (gradient v x) x‖ := by
  apply le_of_tendsto_of_tendsto
    (normalizedMollify_integral_dilation_tendsto hv.continuous hval r a)
    ((normalizedMollify_integral_radial_tendsto hv
      (isCompact_closedBall 0 (a * r))).const_mul (a - 1))
  exact Eventually.of_forall (fun n ↦ integral_norm_dilation_sub_le
    ((normalizedMollify_contDiff hv.continuous n).of_le (by simp)) hr ha)

/-- The absolute radial derivative of a locally Lipschitz function is integrable on compact sets. -/
theorem integrableOn_radial_magnitude_of_locallyLipschitz
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ ‖inner ℝ (gradient v x) x‖) K := by
  obtain ⟨C, hC⟩ := gradient_bound_of_locallyLipschitz hv hK
  have hi : IntegrableOn (fun x : Space d ↦ (C : ℝ) * ‖x‖) K :=
    (continuous_const.mul continuous_id.norm).continuousOn.integrableOn_compact hK
  apply hi.mono' (((measurable_gradient _).inner (𝕜 := ℝ) measurable_id).norm.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [norm_norm]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg x))

end SerrinEpigraph
