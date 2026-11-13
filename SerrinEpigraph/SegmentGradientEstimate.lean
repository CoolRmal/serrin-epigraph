module

public import SerrinEpigraph.SimultaneousMollifiedCompactness

/-!
# Gradient control of differences along segments
-/

public section

open MeasureTheory InnerProductSpace

namespace SerrinEpigraph

noncomputable section

/-- A continuously differentiable function difference is the integral of its directional derivative
along the connecting segment. -/
theorem sub_eq_integral_segment_fderiv {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (x z : Space d) :
    v (x + z) - v x = ∫ t in (0 : ℝ)..1, fderiv ℝ v (x + t • z) z := by
  have hc : Continuous (fun t : ℝ ↦ x + t • z) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hi := (((hv.continuous_fderiv one_ne_zero).comp hc).clm_apply
    (continuous_const (y := z))).intervalIntegrable (μ := volume) 0 1
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ v (x + t • z))
      (fderiv ℝ v (x + t • z) z) t := by
    have hl : HasDerivAt (fun t : ℝ ↦ x + t • z) z t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const z).const_add x
    exact (hv.differentiable one_ne_zero (x + t • z)).hasFDerivAt.comp_hasDerivAt t hl
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi
  simpa only [zero_smul, one_smul, add_zero] using he.symm

/-- The absolute increment is bounded by segment length times the mean gradient norm. -/
theorem norm_sub_le_integral_segment_gradient {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (x z : Space d) :
    ‖v (x + z) - v x‖ ≤ ‖z‖ * ∫ t in (0 : ℝ)..1, ‖gradient v (x + t • z)‖ := by
  have hc : Continuous (fun t : ℝ ↦ x + t • z) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hd : Continuous (fun t : ℝ ↦ fderiv ℝ v (x + t • z) z) :=
    ((hv.continuous_fderiv one_ne_zero).comp hc).clm_apply continuous_const
  have hg : Continuous (fun t : ℝ ↦ ‖gradient v (x + t • z)‖) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map, Function.comp_def] using
      ((hv.continuous_fderiv one_ne_zero).comp hc).norm
  rw [sub_eq_integral_segment_fderiv hv x z, ← intervalIntegral.integral_const_mul]
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
  apply intervalIntegral.integral_mono_on zero_le_one
    (hd.norm.intervalIntegrable _ _) ((continuous_const.mul hg).intervalIntegrable _ _)
  intro t _
  have hb := (fderiv ℝ v (x + t • z)).le_opNorm z
  simpa only [gradient, LinearIsometryEquiv.norm_map, mul_comm, Pi.mul_apply] using hb

end

end SerrinEpigraph
