module

public import SerrinEpigraph.Basic
public import SerrinEpigraph.GradientPowerTests

/-!
# Derivative bounds used by the ball cutoff tests
-/

public section

open InnerProductSpace

namespace SerrinEpigraph

theorem norm_gradient_eq_norm_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (ψ : E → ℝ) (x : E) :
    ‖gradient ψ x‖ = ‖fderiv ℝ ψ x‖ := (toDual ℝ E).symm.norm_map _

@[simp] theorem norm_verticalDirection (m : ℕ) : ‖verticalDirection m‖ = 1 := by
  simp [verticalDirection, EuclideanSpace.single, PiLp.norm_single]

theorem verticalDerivative_sq_le_gradient_sq {m : ℕ} (ψ : Space (m + 1) → ℝ)
    (x : Space (m + 1)) : verticalDerivative ψ x ^ 2 ≤ ‖gradient ψ x‖ ^ 2 := by
  have hh := (fderiv ℝ ψ x).le_opNorm (verticalDirection m)
  rw [norm_verticalDirection, mul_one, ← norm_gradient_eq_norm_fderiv] at hh
  simpa only [Real.norm_eq_abs, sq_abs, verticalDerivative] using
    (pow_le_pow_left₀ (norm_nonneg _) hh 2)

/-- The derivative bound for a power of a nonnegative cutoff. -/
theorem norm_gradient_pow_le {d k : ℕ} {χ : Space d → ℝ} {x : Space d} {B : ℝ}
    (hχ : DifferentiableAt ℝ χ x) (hχ0 : 0 ≤ χ x) (hB : ‖fderiv ℝ χ x‖ ≤ B) :
    ‖gradient (fun y ↦ χ y ^ k) x‖ ≤ (k * B) * χ x ^ (k - 1) := by
  rw [gradient_nat_pow k hχ, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hχ0 _)),
    norm_gradient_eq_norm_fderiv]
  calc
    _ ≤ (k * χ x ^ (k - 1)) * B :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hχ0 _))
    _ = _ := by ring

/-- Squaring the derivative estimate gives exactly the lower cutoff moment. -/
theorem weighted_gradient_cutoff_pow_le {d k : ℕ} {χ : Space d → ℝ} {x : Space d}
    {B w z : ℝ} (hχ : DifferentiableAt ℝ χ x) (hχ0 : 0 ≤ χ x)
    (hB : ‖fderiv ℝ χ x‖ ≤ B) (hw : 0 ≤ w) (hz : 0 ≤ z) :
    w * z ^ (k - 1) * ‖gradient (fun y ↦ χ y ^ k) x‖ ^ 2 ≤
      (k * B) ^ 2 * w * (z * χ x ^ 2) ^ (k - 1) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_pow_le hχ hχ0 hB (k := k)) 2
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hw (pow_nonneg hz (k - 1)))
  convert hh' using 1
  simp only [mul_pow, ← pow_mul]
  ring

end SerrinEpigraph
