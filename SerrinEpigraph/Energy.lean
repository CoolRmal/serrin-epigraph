module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-!
# Energy and Hölder closure for the negative-derivative quotient

These algebraic estimates isolate the coefficients in the high-power testing argument.
-/

public section

open MeasureTheory Filter

namespace SerrinEpigraph

/-- Eliminating the mixed term retains the two nonnegative energy remainders. -/
theorem energy_remainder_le {A B D E G q : ℝ} (hq : 0 ≤ q)
    (htest : (q - 1) * A + 2 * B + D ≤ 0)
    (hexpand : G = q ^ 2 / 4 * A + q * B + E) :
    G + q * (q - 2) / 4 * A + q / 2 * D ≤ E := by
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ q / 2 by positivity) htest]

/-- The quotient energy estimate has constant one for every exponent at least two. -/
theorem energy_le {A B D E G q : ℝ} (hq : 2 ≤ q) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (htest : (q - 1) * A + 2 * B + D ≤ 0)
    (hexpand : G = q ^ 2 / 4 * A + q * B + E) : G ≤ E := by
  have hq0 : 0 ≤ q := by linarith
  have hremA : 0 ≤ q * (q - 2) / 4 * A := by positivity
  have hremD : 0 ≤ q / 2 * D := by positivity
  linarith [energy_remainder_le hq0 htest hexpand]

/-- Cancelling the common Hölder power and raising to `m` closes the moment bound. -/
theorem le_rpow_mul_of_holder {I V K m : ℝ} (hI : 0 ≤ I) (hV : 0 ≤ V)
    (hK : 0 ≤ K) (hm : 0 < m)
    (h : I ≤ K * I ^ ((m - 1) / m) * V ^ (1 / m)) : I ≤ K ^ m * V := by
  rcases eq_or_lt_of_le hI with hzero | hpos
  · subst I
    positivity
  have hcancel : I ^ (1 / m) ≤ K * V ^ (1 / m) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hpos ((m - 1) / m))).mp
    calc
      I ^ (1 / m) * I ^ ((m - 1) / m) = I := by
        rw [← Real.rpow_add hpos]
        rw [show 1 / m + (m - 1) / m = 1 by field_simp; ring, Real.rpow_one]
      _ ≤ K * I ^ ((m - 1) / m) * V ^ (1 / m) := h
      _ = K * V ^ (1 / m) * I ^ ((m - 1) / m) := by ring
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hcancel hm.le
  simpa only [← Real.rpow_mul hI, one_div_mul_cancel hm.ne', Real.rpow_one,
    Real.mul_rpow hK (Real.rpow_nonneg hV _), ← Real.rpow_mul hV] using hpow

/-- Hölder interpolation between two nonnegative integrable densities. -/
theorem integral_rpow_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : α → ℝ} {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hF : Integrable F μ) (hG : Integrable G μ) :
    (∫ x, F x ^ θ * G x ^ (1 - θ) ∂μ) ≤
      (∫ x, F x ∂μ) ^ θ * (∫ x, G x ∂μ) ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (lt_div_iff₀ hθ).mpr (by simpa using hθ1)
    · field_simp; ring
  have hFp := (memLp_one_iff_integrable.mpr hF).norm_rpow_div (ENNReal.ofReal θ)
  have hGp := (memLp_one_iff_integrable.mpr hG).norm_rpow_div (ENNReal.ofReal (1 - θ))
  simp_rw [ENNReal.toReal_ofReal hθ.le, Real.norm_of_nonneg (hF0 _)] at hFp
  simp_rw [ENNReal.toReal_ofReal hθ'.le, Real.norm_of_nonneg (hG0 _)] at hGp
  have hdiv (r : ℝ) (hr : 0 < r) :
      (1 : ENNReal) / ENNReal.ofReal r = ENNReal.ofReal (1 / r) := by
    rw [ENNReal.ofReal_div_of_pos hr]
    simp
  rw [hdiv θ hθ] at hFp
  rw [hdiv (1 - θ) hθ'] at hGp
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (hF0 x) _)
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (hG0 x) _) hFp hGp
  simpa only [← Real.rpow_mul (hF0 _), ← Real.rpow_mul (hG0 _),
    mul_one_div_cancel hθ.ne', mul_one_div_cancel hθ'.ne', Real.rpow_one,
    one_div_one_div] using h

private theorem weighted_power_factorization_aux {w z m : ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hm : 0 < m) :
    (w * z ^ m) ^ ((m - 1) / m) * w ^ (1 - (m - 1) / m) = w * z ^ (m - 1) := by
  rw [Real.mul_rpow hw (Real.rpow_nonneg hz _), ← Real.rpow_mul hz]
  rw [show m * ((m - 1) / m) = m - 1 by field_simp]
  calc
    _ = (w ^ ((m - 1) / m) * w ^ (1 - (m - 1) / m)) * z ^ (m - 1) := by ring
    _ = w * z ^ (m - 1) := by
      rw [← Real.rpow_add' hw (by ring_nf; norm_num),
        show (m - 1) / m + (1 - (m - 1) / m) = 1 by ring, Real.rpow_one]

/-- The weighted lower moment is bounded by the higher moment and total weight. -/
theorem integral_weighted_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w z : α → ℝ} {m : ℝ} (hm : 1 < m)
    (hw : ∀ x, 0 ≤ w x) (hz : ∀ x, 0 ≤ z x)
    (hwint : Integrable w μ) (hmoment : Integrable (fun x ↦ w x * z x ^ m) μ) :
    (∫ x, w x * z x ^ (m - 1) ∂μ) ≤
      (∫ x, w x * z x ^ m ∂μ) ^ ((m - 1) / m) * (∫ x, w x ∂μ) ^ (1 / m) := by
  have hm0 : 0 < m := by linarith
  have hθ : 0 < (m - 1) / m := div_pos (by linarith) hm0
  have hθ1 : (m - 1) / m < 1 := (div_lt_one hm0).mpr (by linarith)
  have h := integral_rpow_mul_rpow_le hθ hθ1
    (fun x ↦ mul_nonneg (hw x) (Real.rpow_nonneg (hz x) _)) hw hmoment hwint
  simp only [weighted_power_factorization_aux (hw _) (hz _) hm0] at h
  simpa only [show 1 - (m - 1) / m = 1 / m by field_simp; ring] using h

/-- A first-order weighted moment estimate closes to a bound using only the total weight. -/
theorem integral_weighted_rpow_le_of_estimate {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w z : α → ℝ} {m K : ℝ} (hm : 1 < m) (hK : 0 ≤ K)
    (hw : ∀ x, 0 ≤ w x) (hz : ∀ x, 0 ≤ z x)
    (hwint : Integrable w μ) (hmoment : Integrable (fun x ↦ w x * z x ^ m) μ)
    (hestimate : (∫ x, w x * z x ^ m ∂μ) ≤ K * ∫ x, w x * z x ^ (m - 1) ∂μ) :
    (∫ x, w x * z x ^ m ∂μ) ≤ K ^ m * ∫ x, w x ∂μ := by
  apply le_rpow_mul_of_holder
    (integral_nonneg fun x ↦ mul_nonneg (hw x) (Real.rpow_nonneg (hz x) _))
    (integral_nonneg hw) hK (by linarith)
  simpa only [mul_assoc] using hestimate.trans
    (mul_le_mul_of_nonneg_left (integral_weighted_rpow_le hm hw hz hwint hmoment) hK)

end SerrinEpigraph
