module

public import SerrinEpigraph.ThresholdRecovery

/-!
# Gradient estimates for variable-width threshold coordinates
-/

public section

open Set InnerProductSpace

namespace SerrinEpigraph

/-- Differentiation of the variable-width threshold coordinate. -/
theorem gradient_thresholdCoordinate {d : ℕ} {φ a : Space d → ℝ} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) (hpos : 0 < a x) (t : ℝ) :
    gradient (thresholdCoordinate φ a t) x =
      (φ x - t) • (-(a x ^ 2)⁻¹ • gradient a x) + (a x)⁻¹ • gradient φ x := by
  have hi := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt x ha.hasFDerivAt
  have hd := (hφ.hasFDerivAt.sub_const t).mul hi
  have hfun : (fun y ↦ φ y - t) * (fun y ↦ (a y)⁻¹) = thresholdCoordinate φ a t := by
    funext y
    simp only [Pi.mul_apply, thresholdCoordinate, div_eq_mul_inv]
  simp only [Function.comp_def] at hd
  rw [hfun] at hd
  have he : fderiv ℝ (thresholdCoordinate φ a t) x =
      (φ x - t) • (-(a x ^ 2)⁻¹ • fderiv ℝ a x) + (a x)⁻¹ • fderiv ℝ φ x := by
    exact hd.fderiv
  simp only [gradient, he, map_add, map_smul]

/-- The leading gradient is at most one; variation of the width contributes
only the coordinate height times its relative gradient. -/
theorem norm_gradient_thresholdCoordinate_le {d : ℕ} {φ a : Space d → ℝ} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) (hpos : 0 < a x)
    (hgrad : ‖gradient φ x‖ ≤ a x) (t : ℝ) :
    ‖gradient (thresholdCoordinate φ a t) x‖ ≤
      1 + ‖thresholdCoordinate φ a t x‖ * (‖gradient a x‖ / a x) := by
  rw [gradient_thresholdCoordinate hφ ha hpos t]
  have hg : (a x)⁻¹ * ‖gradient φ x‖ ≤ 1 := by
    calc
      _ ≤ (a x)⁻¹ * a x := mul_le_mul_of_nonneg_left hgrad (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  calc
    _ ≤ ‖(φ x - t) • (-(a x ^ 2)⁻¹ • gradient a x)‖ + ‖(a x)⁻¹ • gradient φ x‖ :=
      norm_add_le _ _
    _ = ‖thresholdCoordinate φ a t x‖ * (‖gradient a x‖ / a x) +
        (a x)⁻¹ * ‖gradient φ x‖ := by
      simp only [norm_smul, norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (a x))),
        Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), thresholdCoordinate, norm_div,
        Real.norm_of_nonneg hpos.le]
      field_simp
    _ ≤ 1 + ‖thresholdCoordinate φ a t x‖ * (‖gradient a x‖ / a x) := by linarith

end SerrinEpigraph
