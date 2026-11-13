module

public import SerrinEpigraph.GradientMassDuality
public import SerrinEpigraph.MollifiedPerimeterBound

/-!
# Perimeter controls the gradient mass of smooth phase averages
-/

public section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Smooth averaging of a measurable phase controls gradient mass on a ball
by perimeter in the ball enlarged by the averaging radius. -/
theorem integral_gradient_mollified_phase_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (n : ℕ) {r B : ℝ} (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 (r + (averagingBump d n).rOut)) ≤ ENNReal.ofReal B) :
    (∫ x in ball 0 r, ‖gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) x‖) ≤ B := by
  have hv : ContDiff ℝ 1 (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) :=
    (mollify_contDiff_of_locallyIntegrable (locallyIntegrable_phaseIndicator hE) n).of_le
      (by simp)
  have hg : Continuous (gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n)) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hi : IntegrableOn
      (fun x ↦ ‖gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) x‖) (ball 0 r) :=
    (hg.norm.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      ball_subset_closedBall
  have he := lintegral_gradient_le_of_divergence_bound b hv isOpen_ball
    (fun F hF hc hs hunit ↦ norm_mollified_phase_divergence_le b hE n hB hP hF hc hs hunit)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall
    (fun x ↦ norm_nonneg _))] at he
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

/-- Perimeter in a fixed larger ball eventually bounds the gradients of all
smooth averages on a smaller ball. -/
theorem eventually_integral_gradient_mollified_phase_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    {r R B : ℝ} (hrR : r < R) (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 R) ≤ ENNReal.ofReal B) :
    ∀ᶠ n in atTop,
      (∫ x in ball 0 r, ‖gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) x‖) ≤ B := by
  have hsmall : ∀ᶠ n : ℕ in atTop, (averagingBump d n).rOut < R - r :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr hrR))
  filter_upwards [hsmall] with n hn
  apply integral_gradient_mollified_phase_le b hE n hB
  exact (variationalPerimeter_mono b E (ball_subset_ball (by linarith))).trans hP

end SerrinEpigraph
