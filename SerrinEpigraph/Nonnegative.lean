module

public import SerrinEpigraph.FirstMoment
public import SerrinEpigraph.BallCutoff
public import SerrinEpigraph.SparseMoments

/-!
# Nonnegativity of the vertical derivative

The compact quotient tests give odd moment estimates on every ball. Subexponential mass
growth then excludes a positive negative quotient anywhere in the epigraph.
-/

public section

open MeasureTheory

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The PDE and the growth hypothesis force the vertical derivative to be nonnegative. -/
theorem Hypotheses.verticalDerivative_nonneg (h : Hypotheses g u f κ) :
    ∀ x ∈ epigraph g, 0 ≤ verticalDerivative u x := by
  obtain ⟨C, hC, hcut⟩ := exists_ball_cutoffs (m + 1)
  apply verticalDerivative_nonneg_of_odd_moment_estimates h hC
  intro R hR p hp
  obtain ⟨χ, hχ, hχc, hχsupp, hχone, hχbounds, hderiv⟩ := hcut R hR
  have hfirst := h.cutoff_first_moment (p - 2) (div_nonneg hC.le hR.le)
    hχ hχc hχsupp hχbounds hderiv
  have heq : 2 * (p - 2) + 5 = 2 * p + 1 := by omega
  have heq' : 2 * (p - 2) + 4 = 2 * p + 1 - 1 := by omega
  rw [heq, heq'] at hfirst
  have hb := ball_moment_le_of_cutoff_estimate h hR
    (mul_nonneg (Nat.cast_nonneg (2 * p + 1)) (div_nonneg hC.le hR.le))
    (by omega) hχ.continuous hχone hfirst
  convert hb using 1
  push_cast
  ring

end SerrinEpigraph
