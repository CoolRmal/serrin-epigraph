module

public import SerrinEpigraph.QuotientTests
public import SerrinEpigraph.WeakQuotient
public import SerrinEpigraph.CutoffDerivative

/-!
# Integrability of the weighted power-test error
-/

public section

open MeasureTheory

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The zero extension of a positive quotient power times a continuous cutoff is continuous. -/
theorem continuous_indicator_negativeQuotient_pow_mul (h : Hypotheses g u f κ)
    {k : ℕ} (hk : k ≠ 0) {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) :
    Continuous ((epigraph g).indicator (fun x ↦ negativeQuotient u x ^ k * χ x)) := by
  apply continuous_indicator
  · intro x hx
    have hxout : x ∉ epigraph g := fun hxi ↦
      hx.2 ((isOpen_epigraph h.graph_contDiff.continuous).interior_eq.symm ▸ hxi)
    simp only [negativeQuotient_eq_zero_of_mem_closure_not_mem_epigraph h hx.1 hxout,
      zero_pow hk, zero_mul]
  · exact ((continuousOn_negativeQuotient_closure h).pow k).mul hχ.continuousOn

/-- A compact continuous cutoff makes every positive quotient power integrable with weight `u²`. -/
theorem integrable_indicator_sq_mul_negativeQuotient_pow_mul (h : Hypotheses g u f κ)
    {k : ℕ} (hk : k ≠ 0) {χ : Space (m + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable ((epigraph g).indicator
      (fun x ↦ u x ^ 2 * negativeQuotient u x ^ k * χ x)) := by
  obtain ⟨hc, hs⟩ := hasCompactSupport_indicator_negativeQuotient_pow_mul h hk hχc
  have hh := integrable_mul_of_tsupport_subset (μ := volume)
    (h.solution_contDiffOn.continuousOn.pow 2)
    (continuous_indicator_negativeQuotient_pow_mul h hk hχ) hc hs
  apply hh.congr
  filter_upwards with x
  by_cases hx : x ∈ epigraph g
  · simp only [Set.indicator_of_mem hx, Pi.pow_apply]
    ring
  · simp only [Set.indicator_of_notMem hx, mul_zero]

/-- The squared cutoff gradient is an admissible integrable power-test error density. -/
theorem integrable_indicator_power_gradient_error (h : Hypotheses g u f κ)
    {k : ℕ} (hk : k ≠ 0) {η : Space (m + 1) → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    Integrable ((epigraph g).indicator
      (fun x ↦ u x ^ 2 * negativeQuotient u x ^ k * ‖gradient η x‖ ^ 2)) := by
  simp_rw [norm_gradient_eq_norm_fderiv]
  have hc : HasCompactSupport (fun x ↦ ‖fderiv ℝ η x‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (hηc.fderiv ℝ).norm.mul_left
      (f := fun x ↦ ‖fderiv ℝ η x‖)
  exact integrable_indicator_sq_mul_negativeQuotient_pow_mul h hk
    ((hη.continuous_fderiv one_ne_zero).norm.pow 2) hc

end SerrinEpigraph
