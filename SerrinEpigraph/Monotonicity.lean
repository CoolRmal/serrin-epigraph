module

public import SerrinEpigraph.QuotientRegularity
public import SerrinEpigraph.MassGrowth
public import SerrinEpigraph.Mass
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Nonnegative vertical derivatives from the high-order moment estimates

The PDE-derived moment estimates remain explicit hypotheses of this analytic implication.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

private theorem ball_sq_integral_pos_aux (h : Hypotheses g u f κ)
    {x : Space (m + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ epigraph g) :
    0 < ∫ y in Metric.ball x r, u y ^ 2 := by
  have hsub : Metric.ball x r ⊆ epigraph g ∩ Metric.ball 0 (r + dist x 0) :=
    fun y hy ↦ ⟨hball hy, Metric.ball_subset_ball' (le_refl _) hy⟩
  have hint := (integrableOn_sq_epigraph_inter_ball
    h.solution_contDiffOn_closure.continuousOn (r + dist x 0)).mono_set hsub
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun y ↦ sq_nonneg (u y)) hint).mpr
  have heq : Function.support (fun y ↦ u y ^ 2) ∩ Metric.ball x r = Metric.ball x r := by
    apply Set.inter_eq_self_of_subset_right
    intro y hy
    exact ne_of_gt (sq_pos_of_pos (h.positive y (hball hy)))
  rw [heq]
  exact Metric.measure_ball_pos volume x hr

private theorem ball_moment_lowerBound_aux (h : Hypotheses g u f κ)
    {x : Space (m + 1)} {r a R : ℝ} (ha : 0 ≤ a)
    (hball : Metric.ball x r ⊆ epigraph g)
    (hlower : ∀ y ∈ Metric.ball x r, a ≤ negativeQuotient u y)
    (hR : r + dist x 0 ≤ R) (k : ℕ) :
    (∫ y in Metric.ball x r, u y ^ 2) * a ^ k ≤
      ∫ y in epigraph g ∩ Metric.ball 0 R, u y ^ 2 * negativeQuotient u y ^ k := by
  have hsub : Metric.ball x r ⊆ epigraph g ∩ Metric.ball 0 R :=
    fun y hy ↦ ⟨hball hy, Metric.ball_subset_ball' hR hy⟩
  have hint := integrableOn_sq_mul_negativeQuotient_pow_epigraph_inter_ball h k R
  have hsq := (integrableOn_sq_epigraph_inter_ball
    h.solution_contDiffOn_closure.continuousOn R).mono_set hsub
  calc
    _ = ∫ y in Metric.ball x r, u y ^ 2 * a ^ k := (integral_mul_const _ _).symm
    _ ≤ ∫ y in Metric.ball x r, u y ^ 2 * negativeQuotient u y ^ k := by
      apply setIntegral_mono_on (hsq.mul_const _) (hint.mono_set hsub) measurableSet_ball
      intro y hy
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha (hlower y hy) k) (sq_nonneg _)
    _ ≤ _ := setIntegral_mono_set hint
      (Eventually.of_forall fun y ↦ mul_nonneg (sq_nonneg _) (pow_nonneg
        (negativeQuotient_nonneg u y) k)) (Eventually.of_forall fun y hy ↦ hsub hy)

/-- The high-order quotient moment estimates exclude every negative vertical derivative. -/
theorem verticalDerivative_nonneg_of_moment_estimates (h : Hypotheses g u f κ)
    {C : ℝ} (hC : 0 < C)
    (hmom : ∀ R : ℝ, 0 < R → ∀ k : ℕ, 3 ≤ k →
      (∫ y in epigraph g ∩ Metric.ball 0 R, u y ^ 2 * negativeQuotient u y ^ k) ≤
        (C * k / R) ^ k * squareMass g u (2 * R)) :
    ∀ x ∈ epigraph g, 0 ≤ verticalDerivative u x := by
  intro x hx
  apply (negativeQuotient_eq_zero_iff (h.positive x hx)).mp
  apply le_antisymm _ (negativeQuotient_nonneg u x)
  by_contra! hz
  let a := negativeQuotient u x / 2
  have ha : 0 < a := half_pos hz
  have hc := (continuousOn_negativeQuotient_epigraph h x hx).continuousAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hnhds : ∀ᶠ y in 𝓝 x, y ∈ epigraph g :=
    (isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ epigraph g ∧ a < negativeQuotient u y :=
    hnhds.and
      (hc (isOpen_Ioi.mem_nhds (show a < negativeQuotient u x by dsimp [a]; linarith)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hΩ : Metric.ball x r ⊆ epigraph g := fun y hy ↦ (hball hy).1
  have hμ := ball_sq_integral_pos_aux h hr hΩ
  apply (not_le_of_gt ha)
  apply nonpos_of_moment_estimates (squareMass_nonneg g u) h.mass_growth hμ hC
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (r + dist x 0)]
    with R hR hlarge
  intro k hk
  exact (ball_moment_lowerBound_aux h ha.le hΩ (fun y hy ↦ (hball hy).2.le) hlarge k).trans
    (hmom R hR k hk)

end SerrinEpigraph
