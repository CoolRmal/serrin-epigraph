module

public import SerrinEpigraph.PhaseClearingBarrier

/-!
# A globally smooth signed clearing barrier

Using squared distance makes the barrier smooth at its center. It is negative
on the inner ball, so integration by parts over all space replaces the inner
sphere trace in the usual clearing comparison.
-/

public section
noncomputable section

open Set InnerProductSpace Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The signed Gaussian barrier, with its zero set at radius s. -/
@[expose] def phaseClearingGaussian {d : ℕ} (A b s : ℝ) (c x : Space d) : ℝ :=
  A * (1 - Real.exp (-b * (‖x - c‖ ^ 2 - s ^ 2)))

/-- The scalar coefficient of the Gaussian barrier's radial gradient. -/
@[expose] def phaseClearingGaussianCoefficient {d : ℕ}
    (A b s : ℝ) (c x : Space d) : ℝ :=
  2 * A * b * Real.exp (-b * (‖x - c‖ ^ 2 - s ^ 2))

theorem phaseClearingGaussian_contDiff {d : ℕ} (A b s : ℝ) (c : Space d) :
    ContDiff ℝ ⊤ (phaseClearingGaussian A b s c) := by
  unfold phaseClearingGaussian
  exact contDiff_const.mul (contDiff_const.sub
    (contDiff_const.mul (((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).sub
      contDiff_const)).exp)

theorem phaseClearingGaussian_hasGradientAt {d : ℕ} (A b s : ℝ) (c x : Space d) :
    HasGradientAt (phaseClearingGaussian A b s c)
      (phaseClearingGaussianCoefficient A b s c x • (x - c)) x := by
  have hn := (((hasFDerivAt_id x).sub_const c).norm_sq.sub_const (s ^ 2)).const_mul (-b)
  have hd := ((hasFDerivAt_const (1 : ℝ) x).sub hn.exp).const_mul A
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext y
    simp [phaseClearingGaussianCoefficient, InnerProductSpace.toDual_apply_apply]
    ring

theorem phaseClearingGaussianCoefficient_hasFDerivAt {d : ℕ}
    (A b s : ℝ) (c x : Space d) :
    HasFDerivAt (phaseClearingGaussianCoefficient A b s c)
      ((-2 * b * phaseClearingGaussianCoefficient A b s c x) • innerSL ℝ (x - c)) x := by
  have hn := (((hasFDerivAt_id x).sub_const c).norm_sq.sub_const (s ^ 2)).const_mul (-b)
  convert hn.exp.const_mul (2 * A * b) using 1
  · rfl
  · ext y
    simp [phaseClearingGaussianCoefficient]
    ring

theorem phaseClearingGaussian_gradient_hasFDerivAt {d : ℕ}
    (A b s : ℝ) (c x : Space d) :
    HasFDerivAt (gradient (phaseClearingGaussian A b s c))
      (phaseClearingGaussianCoefficient A b s c x • ContinuousLinearMap.id ℝ (Space d) +
        (-2 * b * phaseClearingGaussianCoefficient A b s c x) •
          (innerSL ℝ (x - c)).smulRight (x - c)) x := by
  have hd := (phaseClearingGaussianCoefficient_hasFDerivAt A b s c x).smul
    ((hasFDerivAt_id x).sub_const c)
  have he : gradient (phaseClearingGaussian A b s c) =
      fun y ↦ phaseClearingGaussianCoefficient A b s c y • (y - c) :=
    funext (fun y ↦ (phaseClearingGaussian_hasGradientAt A b s c y).gradient)
  rw [he]
  convert hd using 1
  · rfl
  · ext y
    simp only [add_apply, smul_apply, id_eq,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, smul_smul, smul_eq_mul]

/-- The full Laplacian formula holds even at the center. -/
theorem phaseClearingGaussian_laplacian {d : ℕ} (A b s : ℝ) (c x : Space d) :
    (Δ (phaseClearingGaussian A b s c)) x =
      phaseClearingGaussianCoefficient A b s c x * ((d : ℝ) - 2 * b * ‖x - c‖ ^ 2) := by
  have hd := phaseClearingGaussian_gradient_hasFDerivAt A b s c x
  rw [laplacian_eq_sum_gradient_derivative_of_differentiable hd.differentiableAt
    (EuclideanSpace.basisFun (Fin d) ℝ), hd.fderiv, radial_hessian_trace]
  ring

theorem phaseClearingGaussian_nonpos_inner {d : ℕ} {A b s : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) {c x : Space d} (hx : ‖x - c‖ ^ 2 ≤ s ^ 2) :
    phaseClearingGaussian A b s c x ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos hA
  have he : 1 ≤ Real.exp (-b * (‖x - c‖ ^ 2 - s ^ 2)) :=
    Real.one_le_exp_iff.mpr (by nlinarith)
  linarith

theorem phaseClearingGaussian_nonneg_outer {d : ℕ} {A b s : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) {c x : Space d} (hx : s ^ 2 ≤ ‖x - c‖ ^ 2) :
    0 ≤ phaseClearingGaussian A b s c x := by
  apply mul_nonneg hA
  have he : Real.exp (-b * (‖x - c‖ ^ 2 - s ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  linarith

end SerrinEpigraph
