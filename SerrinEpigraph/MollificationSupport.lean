module

public import SerrinEpigraph.MollificationBounds
public import SerrinEpigraph.ClosedCalibrationPath

/-!
# Compact support control for smoothing comparison pairs
-/

public section
noncomputable section

open MeasureTheory Filter ContinuousLinearMap Metric
open scoped Topology Convolution

namespace SerrinEpigraph

/-- Averaging enlarges a ball containing the support by at most one. -/
theorem mollify_eq_zero_of_notMem_closedBall {d : ℕ} {φ : Space d → ℝ} {R : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 R) (n : ℕ) {x : Space d}
    (hx : x ∉ closedBall 0 (R + 1)) : mollify φ n x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with t
  change (averagingBump d n).normed volume t * φ (x - t) = 0
  by_cases hk : (averagingBump d n).normed volume t = 0
  · rw [hk, zero_mul]
  · have ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut := by
      rw [← (averagingBump d n).support_normed_eq (μ := volume)]
      exact hk
    have ht1 : ‖t‖ ≤ 1 :=
      (by simpa only [mem_ball, dist_zero_right] using ht : ‖t‖ < (averagingBump d n).rOut).le.trans
        (averagingBump_rOut_le_one d n)
    have hφ : φ (x - t) = 0 := by
      by_contra hne
      have hb := hsupp (subset_tsupport φ hne)
      have hb' : ‖x - t‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hb
      apply hx
      simp only [mem_closedBall, dist_zero_right]
      calc
        ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
        _ ≤ R + 1 := add_le_add hb' ht1
    rw [hφ, mul_zero]

/-- The normalized approximations have topological supports in the same enlarged ball. -/
theorem normalizedMollify_tsupport_subset {d : ℕ} {φ : Space d → ℝ} {R : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 R) (n : ℕ) :
    tsupport (normalizedMollify φ n) ⊆ closedBall 0 (R + 1) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hnot
  have hz := mollify_eq_zero_of_notMem_closedBall hsupp n hnot
  exact hx (by simp only [normalizedMollify, hz, mul_zero])

/-- Compactly supported perturbations have uniformly compactly supported smooth approximations. -/
theorem normalizedMollify_uniform_support {d : ℕ} {φ : Space d → ℝ}
    (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ n, tsupport (normalizedMollify φ n) ⊆ closedBall 0 R := by
  obtain ⟨R, hR⟩ := hφ.isBounded.subset_closedBall (0 : Space d)
  exact ⟨R + 1, normalizedMollify_tsupport_subset hR⟩

/-- Normalized convolution is additive on continuous functions. -/
theorem normalizedMollify_add {d : ℕ} {v φ : Space d → ℝ}
    (hv : Continuous v) (hφ : Continuous φ) (n : ℕ) :
    normalizedMollify (fun x ↦ v x + φ x) n =
      fun x ↦ normalizedMollify v n x + normalizedMollify φ n x := by
  have hi (w : Space d → ℝ) (hw : Continuous w) :=
    ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (μ := volume) (lsmul ℝ ℝ) (averagingBump d n).continuous_normed hw.locallyIntegrable
  funext x
  have he := (hi v hv x).distrib_add (hi φ hφ x)
  change mollify (fun y ↦ v y + φ y) n x = mollify v n x + mollify φ n x at he
  simp only [normalizedMollify, he, mul_add]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Smoothing a continuous compact comparison pair preserves calibration integrals on a single
fixed ball for every approximation index. -/
theorem RigidityHypotheses.mollified_pair_calibration_eq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} (hv : Continuous v) (hφ : Continuous φ)
    (hsupp : HasCompactSupport φ)
    (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) 1)
    (hend : ∀ x, v x + φ x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ R : ℝ, ∀ n,
      (∫ x in closedBall 0 R, hr.boundaryCalibratedDensity h (horizontal x)
        (normalizedMollify (fun y ↦ v y + φ y) n x)
        (gradient (normalizedMollify (fun y ↦ v y + φ y) n) x)) =
      ∫ x in closedBall 0 R, hr.boundaryCalibratedDensity h (horizontal x)
        (normalizedMollify v n x) (gradient (normalizedMollify v n) x) := by
  obtain ⟨R, hR⟩ := normalizedMollify_uniform_support hsupp
  refine ⟨R, fun n ↦ ?_⟩
  have hV : ContDiff ℝ 1 (normalizedMollify v n) :=
    (normalizedMollify_contDiff hv n).of_le (by simp)
  have hΦ : ContDiff ℝ 1 (normalizedMollify φ n) :=
    (normalizedMollify_contDiff hφ n).of_le (by simp)
  have he := hr.boundaryCalibratedPath_endpoints h hV hΦ (isCompact_closedBall 0 R) (hR n)
    (normalizedMollify_mem_Ico hv hval n)
    (fun x ↦ by
      rw [← congrFun (normalizedMollify_add hv hφ n) x]
      exact normalizedMollify_mem_Ico (hv.add hφ) hend n x)
  simpa only [normalizedMollify_add hv hφ n] using he

end SerrinEpigraph
