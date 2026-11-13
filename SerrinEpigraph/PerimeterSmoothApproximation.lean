module

public import SerrinEpigraph.SmoothPhaseRecovery

/-!
# Quantitative smooth phase approximation under a local perimeter bound
-/

public section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Perimeter in a larger open ball eventually controls mollified gradient
mass on a smaller closed ball. -/
theorem eventually_integral_gradient_mollified_phase_closedBall_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    {r R B : ℝ} (hrR : r < R) (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 R) ≤ ENNReal.ofReal B) :
    ∀ᶠ n in atTop,
      (∫ x in closedBall 0 r, ‖gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) x‖) ≤ B := by
  have hmid : r < (r + R) / 2 := by linarith
  have hmidR : (r + R) / 2 < R := by linarith
  filter_upwards [eventually_integral_gradient_mollified_phase_le b hE hmidR hB hP] with n hn
  have hv : ContDiff ℝ 1 (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) :=
    (mollify_contDiff_of_locallyIntegrable (locallyIntegrable_phaseIndicator hE) n).of_le
      (by simp)
  have hg : Continuous (gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n)) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hi : IntegrableOn (fun x ↦ ‖gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) x‖)
      (ball 0 ((r + R) / 2)) :=
    (hg.norm.continuousOn.integrableOn_compact (isCompact_closedBall 0 ((r + R) / 2))).mono_set
      ball_subset_closedBall
  exact (setIntegral_mono_set hi (Eventually.of_forall (fun x ↦ norm_nonneg _))
    (Eventually.of_forall (closedBall_subset_ball hmid))).trans hn

/-- A local perimeter bound supplies smooth normalized phases with any
prescribed positive integral-error tolerances and a common gradient-mass bound. -/
theorem exists_smoothPhase_approx_of_perimeter_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    {r R B : ℝ} (hrR : r < R) (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 R) ≤ ENNReal.ofReal B)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) :
    ∃ φ : ℕ → Space d → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) ∧
      (∀ j x, φ j x ∈ Icc (0 : ℝ) 1) ∧
      (∀ j, (∫ x in closedBall 0 r, ‖gradient (φ j) x‖) ≤ B) ∧
      ∀ j, (∫ x in closedBall 0 r, ‖φ j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) ≤ ε j := by
  have ht := mollify_phaseIndicator_integral_tendsto hE (isCompact_closedBall 0 r)
  have hg := eventually_integral_gradient_mollified_phase_closedBall_le b hE hrR hB hP
  have hc (j : ℕ) : ∃ n : ℕ,
      (∫ x in closedBall 0 r, ‖gradient (mollify (E.indicator (fun _ ↦ (1 : ℝ))) n) x‖) ≤ B ∧
      (∫ x in closedBall 0 r,
        ‖mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) < ε j :=
    (hg.and (ht.eventually (gt_mem_nhds (hε j)))).exists
  choose n hnG hnE using hc
  refine ⟨fun j ↦ mollify (E.indicator (fun _ ↦ (1 : ℝ))) (n j),
    fun j ↦ mollify_contDiff_of_locallyIntegrable (locallyIntegrable_phaseIndicator hE) (n j),
    fun j x ↦ mollify_phaseIndicator_mem_Icc hE (n j) x, hnG, fun j ↦ (hnE j).le⟩

end SerrinEpigraph
