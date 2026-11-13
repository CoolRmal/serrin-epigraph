module

public import SerrinEpigraph.Truncation
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Gradients of the smooth power tests
-/

public section

open InnerProductSpace

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient chain rule for positive-part powers includes points where the part is zero. -/
theorem gradient_positivePart_pow {t : E → ℝ} {x : E} {k : ℕ}
    (hk : 2 ≤ k) (ht : DifferentiableAt ℝ t x) :
    gradient (fun y ↦ max (t y) 0 ^ k) x =
      (k * max (t x) 0 ^ (k - 1)) • gradient t x := by
  have hd := (hasDerivAt_positivePart_pow hk (t x)).comp_hasFDerivAt x ht.hasFDerivAt
  have heq : fderiv ℝ (fun y ↦ max (t y) 0 ^ k) x =
      (k * max (t x) 0 ^ (k - 1)) • fderiv ℝ t x := by
    simpa only [Function.comp_def] using hd.fderiv
  simp only [gradient, heq, map_smul]

/-- Product rule for the gradient of a power test times its cutoff. -/
theorem gradient_positivePart_pow_mul {t η : E → ℝ} {x : E} {k : ℕ}
    (hk : 2 ≤ k) (ht : DifferentiableAt ℝ t x) (hη : DifferentiableAt ℝ η x) :
    gradient (fun y ↦ max (t y) 0 ^ k * η y) x =
      (η x * (k * max (t x) 0 ^ (k - 1))) • gradient t x +
        max (t x) 0 ^ k • gradient η x := by
  have hp := (hasDerivAt_positivePart_pow hk (t x)).comp_hasFDerivAt x ht.hasFDerivAt
  have hd := hp.mul hη.hasFDerivAt
  have heq : fderiv ℝ (fun y ↦ max (t y) 0 ^ k * η y) x =
      η x • ((k * max (t x) 0 ^ (k - 1)) • fderiv ℝ t x) +
        max (t x) 0 ^ k • fderiv ℝ η x := by
    simpa only [Function.comp_def, Pi.mul_def, add_comm] using hd.fderiv
  simp only [gradient, heq, map_add, map_smul, smul_smul]

/-- The ordinary power rule expressed as a gradient. -/
theorem gradient_nat_pow {η : E → ℝ} {x : E} (k : ℕ) (hη : DifferentiableAt ℝ η x) :
    gradient (fun y ↦ η y ^ k) x = (k * η x ^ (k - 1)) • gradient η x := by
  simp only [gradient, fderiv_fun_pow k hη, map_smul, nsmul_eq_mul]

omit [CompleteSpace E] in
/-- Expansion of a squared gradient in the two directions used by the power test. -/
theorem norm_smul_add_smul_sq (a b : ℝ) (X Y : E) :
    ‖a • X + b • Y‖ ^ 2 =
      a ^ 2 * ‖X‖ ^ 2 + 2 * a * b * inner ℝ X Y + b ^ 2 * ‖Y‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The power-test expansion with its nonnegative remainder, before integration. -/
theorem gradient_power_test_identity {t η : E → ℝ} {x : E} (n : ℕ)
    (ht : DifferentiableAt ℝ t x) (hη : DifferentiableAt ℝ η x) :
    ‖gradient (fun y ↦ max (t y) 0 ^ (n + 2) * η y) x‖ ^ 2 +
        ((n : ℝ) + 2) * (n + 1) * max (t x) 0 ^ (2 * n + 2) * η x ^ 2 *
          ‖gradient t x‖ ^ 2 =
      ((n : ℝ) + 2) * inner ℝ (gradient t x)
        (gradient (fun y ↦ max (t y) 0 ^ (2 * n + 3) * η y ^ 2) x) +
          max (t x) 0 ^ (2 * n + 4) * ‖gradient η x‖ ^ 2 := by
  have hη2 : DifferentiableAt ℝ (fun y ↦ η y ^ 2) x := by
    simpa only [Pi.pow_def] using hη.pow 2
  rw [gradient_positivePart_pow_mul (by omega) ht hη,
    gradient_positivePart_pow_mul (by omega) ht hη2, gradient_nat_pow 2 hη,
    norm_smul_add_smul_sq, inner_add_right]
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have he1 : n + 2 - 1 = n + 1 := by omega
  have he2 : 2 * n + 3 - 1 = 2 * n + 2 := by omega
  simp only [he1, he2, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, pow_add, pow_mul]
  ring

end SerrinEpigraph
