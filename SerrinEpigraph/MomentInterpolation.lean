module

public import SerrinEpigraph.Energy

/-!
# Interpolation of weighted moments

Moment bounds for an unbounded subsequence of exponents suffice for the growth argument.
-/

public section

open MeasureTheory

namespace SerrinEpigraph

private theorem weighted_moment_factorization {w z p q : ℝ}
    (hw : 0 ≤ w) (hz : 0 ≤ z) (hq : 0 < q) :
    (w * z ^ q) ^ (p / q) * w ^ (1 - p / q) = w * z ^ p := by
  rw [Real.mul_rpow hw (Real.rpow_nonneg hz _), ← Real.rpow_mul hz]
  rw [show q * (p / q) = p by field_simp]
  calc
    _ = (w ^ (p / q) * w ^ (1 - p / q)) * z ^ p := by ring
    _ = w * z ^ p := by
      rw [← Real.rpow_add' hw (by ring_nf; norm_num),
        show p / q + (1 - p / q) = 1 by ring, Real.rpow_one]

/-- Interpolating a weighted moment between a larger moment and the total weight. -/
theorem integral_weighted_rpow_interpolation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w z : α → ℝ} {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hw : ∀ x, 0 ≤ w x) (hz : ∀ x, 0 ≤ z x)
    (hwint : Integrable w μ) (hqint : Integrable (fun x ↦ w x * z x ^ q) μ) :
    (∫ x, w x * z x ^ p ∂μ) ≤
      (∫ x, w x * z x ^ q ∂μ) ^ (p / q) * (∫ x, w x ∂μ) ^ (1 - p / q) := by
  have hq : 0 < q := hp.trans hpq
  have hθ : 0 < p / q := div_pos hp hq
  have hθ1 : p / q < 1 := (div_lt_one hq).mpr hpq
  have hh := integral_rpow_mul_rpow_le hθ hθ1
    (fun x ↦ mul_nonneg (hw x) (Real.rpow_nonneg (hz x) _)) hw hqint hwint
  simpa only [weighted_moment_factorization (hw _) (hz _) hq] using hh

/-- A bound on a larger weighted moment also bounds every smaller positive moment. -/
theorem integral_weighted_rpow_le_of_higher_moment {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w z : α → ℝ} {p q A : ℝ} (hp : 0 < p) (hpq : p < q)
    (hA : 0 ≤ A) (hw : ∀ x, 0 ≤ w x) (hz : ∀ x, 0 ≤ z x)
    (hwint : Integrable w μ) (hqint : Integrable (fun x ↦ w x * z x ^ q) μ)
    (hbound : (∫ x, w x * z x ^ q ∂μ) ≤ A ^ q * ∫ x, w x ∂μ) :
    (∫ x, w x * z x ^ p ∂μ) ≤ A ^ p * ∫ x, w x ∂μ := by
  have hq : 0 < q := hp.trans hpq
  have hθ : 0 ≤ p / q := (div_pos hp hq).le
  have hV : 0 ≤ ∫ x, w x ∂μ := integral_nonneg hw
  have hI : 0 ≤ ∫ x, w x * z x ^ q ∂μ :=
    integral_nonneg fun x ↦ mul_nonneg (hw x) (Real.rpow_nonneg (hz x) _)
  calc
    _ ≤ (∫ x, w x * z x ^ q ∂μ) ^ (p / q) * (∫ x, w x ∂μ) ^ (1 - p / q) :=
      integral_weighted_rpow_interpolation hp hpq hw hz hwint hqint
    _ ≤ (A ^ q * ∫ x, w x ∂μ) ^ (p / q) * (∫ x, w x ∂μ) ^ (1 - p / q) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hI hbound hθ) (Real.rpow_nonneg hV _)
    _ = A ^ p * ∫ x, w x ∂μ := by
      rw [mul_comm (A ^ q), weighted_moment_factorization hV hA hq, mul_comm]

/-- The interpolation remains valid with any upper bound for the total weight. -/
theorem integral_weighted_rpow_le_of_higher_moment_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w z : α → ℝ} {p q A V : ℝ} (hp : 0 < p) (hpq : p < q)
    (hA : 0 ≤ A) (hw : ∀ x, 0 ≤ w x) (hz : ∀ x, 0 ≤ z x)
    (hwint : Integrable w μ) (hqint : Integrable (fun x ↦ w x * z x ^ q) μ)
    (hmass : (∫ x, w x ∂μ) ≤ V)
    (hbound : (∫ x, w x * z x ^ q ∂μ) ≤ A ^ q * V) :
    (∫ x, w x * z x ^ p ∂μ) ≤ A ^ p * V := by
  have hq : 0 < q := hp.trans hpq
  have hθ : 0 ≤ p / q := (div_pos hp hq).le
  have hθ' : 0 ≤ 1 - p / q := sub_nonneg.mpr ((div_lt_one hq).mpr hpq).le
  have hweight : 0 ≤ ∫ x, w x ∂μ := integral_nonneg hw
  have hV : 0 ≤ V := hweight.trans hmass
  have hI : 0 ≤ ∫ x, w x * z x ^ q ∂μ :=
    integral_nonneg fun x ↦ mul_nonneg (hw x) (Real.rpow_nonneg (hz x) _)
  calc
    _ ≤ (∫ x, w x * z x ^ q ∂μ) ^ (p / q) * (∫ x, w x ∂μ) ^ (1 - p / q) :=
      integral_weighted_rpow_interpolation hp hpq hw hz hwint hqint
    _ ≤ (A ^ q * V) ^ (p / q) * V ^ (1 - p / q) :=
      mul_le_mul (Real.rpow_le_rpow hI hbound hθ)
        (Real.rpow_le_rpow hweight hmass hθ') (Real.rpow_nonneg hweight _)
        (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hA _) hV) _)
    _ = A ^ p * V := by
      rw [mul_comm (A ^ q), weighted_moment_factorization hV hA hq, mul_comm]

end SerrinEpigraph
