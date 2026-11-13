module

public import SerrinEpigraph.Monotonicity
public import SerrinEpigraph.MomentInterpolation

/-!
# Odd moments suffice for monotonicity

Odd moments use integer powers in the energy test, avoiding fractional powers at the truncation.
-/

public section

open MeasureTheory

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Only odd moments starting at order five are needed to rule out a negative derivative. -/
theorem verticalDerivative_nonneg_of_odd_moment_estimates (h : Hypotheses g u f κ)
    {C : ℝ} (hC : 0 < C)
    (hmom : ∀ R : ℝ, 0 < R → ∀ p : ℕ, 2 ≤ p →
      (∫ y in epigraph g ∩ Metric.ball 0 R,
        u y ^ 2 * negativeQuotient u y ^ (2 * p + 1)) ≤
        (C * (2 * p + 1) / R) ^ (2 * p + 1) * squareMass g u (2 * R)) :
    ∀ x ∈ epigraph g, 0 ≤ verticalDerivative u x := by
  apply verticalDerivative_nonneg_of_moment_estimates h (C := 3 * C) (by positivity)
  intro R hR k hk
  have hmass : squareMass g u R ≤ squareMass g u (2 * R) := by
    apply setIntegral_mono_set
      (integrableOn_sq_epigraph_inter_ball h.solution_contDiffOn_closure.continuousOn (2 * R))
      (Filter.Eventually.of_forall fun y ↦ sq_nonneg (u y))
    exact Filter.Eventually.of_forall fun y hy ↦
      ⟨hy.1, Metric.ball_subset_ball (by linarith) hy.2⟩
  have hint := integrableOn_sq_mul_negativeQuotient_pow_epigraph_inter_ball h (2 * k + 1) R
  have hbound := hmom R hR k (by omega)
  have hp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpq : (k : ℝ) < (2 * k + 1 : ℕ) := by exact_mod_cast (show k < 2 * k + 1 by omega)
  have hinterp := integral_weighted_rpow_le_of_higher_moment_bound
    (μ := volume.restrict (epigraph g ∩ Metric.ball 0 R))
    (w := fun y ↦ u y ^ 2) (z := negativeQuotient u)
    (p := (k : ℝ)) (q := ((2 * k + 1 : ℕ) : ℝ))
    (A := C * (2 * k + 1) / R) (V := squareMass g u (2 * R)) hp hpq
    (by positivity) (fun y ↦ sq_nonneg (u y)) (negativeQuotient_nonneg u)
    (integrableOn_sq_epigraph_inter_ball h.solution_contDiffOn_closure.continuousOn R)
    (by simpa only [Real.rpow_natCast, IntegrableOn] using hint) hmass
    (by simpa only [Real.rpow_natCast] using hbound)
  simp only [Real.rpow_natCast] at hinterp
  apply hinterp.trans
  apply mul_le_mul_of_nonneg_right _ (squareMass_nonneg g u (2 * R))
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hR.le
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  nlinarith

end SerrinEpigraph
