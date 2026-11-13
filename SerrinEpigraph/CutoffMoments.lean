module

public import SerrinEpigraph.QuotientRegularity
public import SerrinEpigraph.Energy
public import SerrinEpigraph.Mass
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Closing the cutoff moment estimate
-/

public section

open MeasureTheory

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Cutoff moments remain integrable on every bounded truncation. -/
theorem integrableOn_cutoff_moment (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) (k : ℕ) (R : ℝ) :
    IntegrableOn (fun x ↦ u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k)
      (epigraph g ∩ Metric.ball 0 R) := by
  have hc := (h.solution_contDiffOn_closure.continuousOn.pow 2).mul
    (((continuousOn_negativeQuotient_closure h).mul (hχ.pow 2).continuousOn).pow k)
  have hi : IntegrableOn (fun x ↦ u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k)
      (closure (epigraph g) ∩ Metric.closedBall 0 R) :=
    (hc.mono Set.inter_subset_left).integrableOn_compact
      ((isCompact_closedBall 0 R).inter_left isClosed_closure)
  exact hi.mono_set (Set.inter_subset_inter subset_closure Metric.ball_subset_closedBall)

/-- The first-order cutoff estimate closes to the desired ball-moment bound by Hölder. -/
theorem ball_moment_le_of_cutoff_estimate (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} {R K : ℝ} {k : ℕ}
    (hR : 0 < R) (hK : 0 ≤ K) (hk : 2 ≤ k) (hχ : Continuous χ)
    (hχone : ∀ x ∈ Metric.ball 0 R, χ x = 1)
    (hfirst :
      (∫ x in epigraph g ∩ Metric.ball 0 (2 * R),
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k) ≤
      K * ∫ x in epigraph g ∩ Metric.ball 0 (2 * R),
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (k - 1)) :
    (∫ x in epigraph g ∩ Metric.ball 0 R, u x ^ 2 * negativeQuotient u x ^ k) ≤
      K ^ k * squareMass g u (2 * R) := by
  have hpow : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hsub : epigraph g ∩ Metric.ball 0 R ⊆ epigraph g ∩ Metric.ball 0 (2 * R) :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith))
  have hi := integrableOn_cutoff_moment h hχ k (2 * R)
  have heq : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  have hclose := integral_weighted_rpow_le_of_estimate
    (μ := volume.restrict (epigraph g ∩ Metric.ball 0 (2 * R)))
    (w := fun x ↦ u x ^ 2) (z := fun x ↦ negativeQuotient u x * χ x ^ 2)
    (m := (k : ℝ)) hpow hK (fun x ↦ sq_nonneg (u x))
    (fun x ↦ mul_nonneg (negativeQuotient_nonneg u x) (sq_nonneg (χ x)))
    (integrableOn_sq_epigraph_inter_ball h.solution_contDiffOn_closure.continuousOn (2 * R))
    (by simpa only [Real.rpow_natCast, IntegrableOn] using hi)
    (by simpa only [heq, Real.rpow_natCast] using hfirst)
  simp only [Real.rpow_natCast] at hclose
  calc
    _ = ∫ x in epigraph g ∩ Metric.ball 0 R,
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k := by
      apply setIntegral_congr_fun ((isOpen_epigraph h.graph_contDiff.continuous).measurableSet.inter
        measurableSet_ball)
      intro x hx
      simp only [hχone x hx.2, one_pow, mul_one]
    _ ≤ ∫ x in epigraph g ∩ Metric.ball 0 (2 * R),
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k := by
      exact setIntegral_mono_set hi (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (sq_nonneg _) (pow_nonneg
          (mul_nonneg (negativeQuotient_nonneg u x) (sq_nonneg _)) k))
        (Filter.Eventually.of_forall fun x hx ↦ hsub hx)
    _ ≤ _ := hclose

end SerrinEpigraph
