module

public import SerrinEpigraph.MollificationDuality

/-!
# Divergence-test control of smooth phase averages by perimeter
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter ContinuousLinearMap
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Each translated admissible vector test is controlled by perimeter in the enlarged ball. -/
theorem norm_translated_phase_divergence_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    {r ρ B : ℝ} (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 (r + ρ)) ≤ ENNReal.ofReal B)
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F)
    (hs : tsupport F ⊆ ball 0 r) (hunit : ∀ x, ‖F x‖ ≤ 1)
    {y : Space d} (hy : ‖y‖ ≤ ρ) :
    ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F (x + y)‖ ≤ B := by
  have hFt : ContDiff ℝ 1 (fun x ↦ F (x + y)) := hF.comp (contDiff_id.add contDiff_const)
  have hst := tsupport_translate_subset_ball hs hy
  have hct : HasCompactSupport (fun x ↦ F (x + y)) :=
    (isCompact_closedBall 0 (r + ρ)).of_isClosed_subset (isClosed_tsupport _)
      (hst.trans ball_subset_closedBall)
  have ht : ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
      fieldDivergence b (fun z ↦ F (z + y)) x‖ ≤ variationalPerimeter b E (ball 0 (r + ρ)) := by
    unfold variationalPerimeter
    exact le_iSup_of_le (fun x ↦ F (x + y)) (le_iSup_of_le hFt (le_iSup_of_le hct
      (le_iSup_of_le hst (le_iSup_of_le (fun x ↦ hunit (x + y)) le_rfl))))
  have hb := (ENNReal.ofReal_le_ofReal_iff hB).mp (ht.trans hP)
  simpa only [fieldDivergence_translate b hF] using hb

/-- Averaging a measurable phase does not increase its divergence-test bound, apart from
enlarging the test domain by the kernel radius. -/
theorem norm_mollified_phase_divergence_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (n : ℕ) {r B : ℝ} (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 (r + (averagingBump d n).rOut)) ≤ ENNReal.ofReal B)
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ ball 0 r) (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x, mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x * fieldDivergence b F x‖ ≤ B := by
  have hψ := fieldDivergence_continuous b hF
  have hsupport : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hψc : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hi : Measurable (E.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hE
  have hib (x : Space d) : ‖E.indicator (fun _ ↦ (1 : ℝ)) x‖ ≤ 1 := by
    by_cases hx : x ∈ E <;> simp [hx]
  rw [integral_mollify_mul_eq_average_tests hi hib hψ hψc n]
  let J := fun y : Space d ↦ ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F (x + y)
  let K := (averagingBump d n).normed volume
  have hbound (y : Space d) : ‖K y * J y‖ ≤ K y * B := by
    by_cases hy : K y = 0
    · simp [hy]
    · have hsupp : y ∈ ball (0 : Space d) (averagingBump d n).rOut := by
        rw [← (averagingBump d n).support_normed_eq (μ := volume)]
        exact hy
      have hn : ‖y‖ ≤ (averagingBump d n).rOut := by
        exact (mem_ball_zero_iff.mp hsupp).le
      rw [norm_mul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left
        (norm_translated_phase_divergence_le b hB hP hF hs hunit hn)
        ((averagingBump d n).nonneg_normed y)
  calc
    ‖∫ y, K y * J y‖ ≤ ∫ y, ‖K y * J y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, K y * B := integral_mono_of_nonneg
      (Eventually.of_forall (fun y ↦ norm_nonneg _))
      (((averagingBump d n).integrable_normed (μ := volume)).mul_const B)
      (Eventually.of_forall hbound)
    _ = B := by rw [integral_mul_const, (averagingBump d n).integral_normed, one_mul]

end SerrinEpigraph
