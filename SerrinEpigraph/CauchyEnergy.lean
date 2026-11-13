module

public import SerrinEpigraph.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integral Cauchy bounds for the quotient energy
-/

public section

open MeasureTheory

namespace SerrinEpigraph

/-- The scalar integral Cauchy inequality in a form requiring only square integrability. -/
theorem abs_integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : Integrable (fun x ↦ a x ^ 2) μ)
    (hb : Integrable (fun x ↦ b x ^ 2) μ) :
    |∫ x, a x * b x ∂μ| ≤
      Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
  have hh := integral_rpow_mul_rpow_le (θ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (fun x ↦ sq_nonneg (a x)) (fun x ↦ sq_nonneg (b x)) ha hb
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [hhalf, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs] at hh
  have hnorm := norm_integral_le_integral_norm (fun x ↦ a x * b x) (μ := μ)
  simp only [Real.norm_eq_abs, abs_mul] at hnorm
  exact hnorm.trans hh

/-- Cauchy closes an energy estimate against the same lower moment on both factors. -/
theorem integral_mul_le_of_square_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} {J K : ℝ} (ha : Integrable (fun x ↦ a x ^ 2) μ)
    (hb : Integrable (fun x ↦ b x ^ 2) μ) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (haJ : (∫ x, a x ^ 2 ∂μ) ≤ J) (hbJ : (∫ x, b x ^ 2 ∂μ) ≤ K ^ 2 * J) :
    (∫ x, a x * b x ∂μ) ≤ K * J := by
  calc
    _ ≤ |∫ x, a x * b x ∂μ| := le_abs_self _
    _ ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) :=
      abs_integral_mul_le_sqrt ha hb
    _ ≤ Real.sqrt J * Real.sqrt (K ^ 2 * J) :=
      mul_le_mul (Real.sqrt_le_sqrt haJ) (Real.sqrt_le_sqrt hbJ)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = K * J := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
      nlinarith [Real.sq_sqrt hJ]

end SerrinEpigraph
