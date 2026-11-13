module

public import SerrinEpigraph.Mollification
public import SerrinEpigraph.ZeroExtensionRegularity

/-!
# Uniform local gradient bounds for mollified zero extensions
-/

public section
noncomputable section

open MeasureTheory Filter ContinuousLinearMap Metric InnerProductSpace
open scoped Topology Convolution

namespace SerrinEpigraph

/-- Averaging bounds differences by any common bound on the translated differences. -/
theorem mollify_dist_le {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (n : ℕ) (x y : Space d) {A : ℝ}
    (hbound : ∀ t ∈ ball (0 : Space d) (averagingBump d n).rOut,
      dist (v (x - t)) (v (y - t)) ≤ A) :
    dist (mollify v n x) (mollify v n y) ≤ A := by
  let k := (averagingBump d n).normed volume
  have hi := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume) (lsmul ℝ ℝ) (averagingBump d n).continuous_normed hv.locallyIntegrable
  have hki : Integrable (fun t ↦ k t * A) volume :=
    (averagingBump d n).integrable_normed.mul_const A
  have hn : ‖∫ t, k t * v (x - t) - k t * v (y - t)‖ ≤ ∫ t, k t * A := by
    apply norm_integral_le_of_norm_le hki
    filter_upwards with t
    by_cases ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut
    · rw [← mul_sub, norm_mul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hbound t ht)
        ((averagingBump d n).nonneg_normed t)
    · have hz : k t = 0 := Function.notMem_support.mp (by
        simpa only [k, (averagingBump d n).support_normed_eq] using ht)
      simp only [hz, zero_mul, sub_zero, norm_zero, le_refl]
  have hix : Integrable (fun t ↦ k t * v (x - t)) volume := (hi x).integrable
  have hiy : Integrable (fun t ↦ k t * v (y - t)) volume := (hi y).integrable
  rw [integral_sub hix hiy, integral_mul_const] at hn
  simp only [k, (averagingBump d n).integral_normed, one_mul] at hn
  exact hn

/-- Every averaging radius is at most one. -/
theorem averagingBump_rOut_le_one (d n : ℕ) : (averagingBump d n).rOut ≤ 1 := by
  change 1 / ((n : ℝ) + 1) ≤ 1
  apply (div_le_one (by positivity)).mpr
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- A local Lipschitz bound survives averaging on a smaller ball, uniformly in the index. -/
theorem mollify_lipschitzOn_closedBall {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    {C : NNReal} {R : ℝ} (hlip : LipschitzOnWith C v (closedBall 0 (R + 1))) (n : ℕ) :
    LipschitzOnWith C (mollify v n) (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  apply mollify_dist_le hv n x y
  intro t ht
  have ht1 : ‖t‖ ≤ 1 :=
    (by simpa only [mem_ball, dist_zero_right] using ht : ‖t‖ < (averagingBump d n).rOut).le.trans
      (averagingBump_rOut_le_one d n)
  have hxt : x - t ∈ closedBall 0 (R + 1) := by
    simp only [mem_closedBall, dist_zero_right] at hx ⊢
    exact (norm_sub_le x t).trans (add_le_add hx ht1)
  have hyt : y - t ∈ closedBall 0 (R + 1) := by
    simp only [mem_closedBall, dist_zero_right] at hy ⊢
    exact (norm_sub_le y t).trans (add_le_add hy ht1)
  simpa only [dist_sub_right] using hlip.dist_le_mul _ hxt _ hyt

/-- The normalization contraction does not increase the local Lipschitz constant. -/
theorem normalizedMollify_lipschitzOn_closedBall {d : ℕ} {v : Space d → ℝ}
    (hv : Continuous v) {C : NNReal} {R : ℝ}
    (hlip : LipschitzOnWith C v (closedBall 0 (R + 1))) (n : ℕ) :
    LipschitzOnWith C (normalizedMollify v n) (closedBall 0 R) := by
  have hm := mollify_lipschitzOn_closedBall hv hlip n
  have hc := mollify_contraction_mem_Ioo n
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist ((1 - 1 / ((n : ℝ) + 2)) * mollify v n x)
    ((1 - 1 / ((n : ℝ) + 2)) * mollify v n y) ≤ _
  rw [dist_eq_norm, ← mul_sub, norm_mul, Real.norm_of_nonneg hc.1.le]
  calc
    _ ≤ ‖mollify v n x - mollify v n y‖ := mul_le_of_le_one_left (norm_nonneg _) hc.2.le
    _ ≤ _ := by simpa only [dist_eq_norm] using hm.dist_le_mul _ hx _ hy

/-- An upper bound is needed only on the translated kernel support to bound an average. -/
theorem mollify_le_of_local {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (n : ℕ) (x : Space d) {b : ℝ}
    (hb : ∀ t ∈ ball (0 : Space d) (averagingBump d n).rOut, v (x - t) ≤ b) :
    mollify v n x ≤ b := by
  let k := (averagingBump d n).normed volume
  have hi := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume) (lsmul ℝ ℝ) (averagingBump d n).continuous_normed hv.locallyIntegrable
  have hix : Integrable (fun t ↦ k t * v (x - t)) volume := (hi x).integrable
  have hib : Integrable (fun t ↦ k t * b) volume :=
    (averagingBump d n).integrable_normed.mul_const b
  have he : (∫ t, k t * v (x - t)) ≤ ∫ t, k t * b := by
    apply integral_mono hix hib
    intro t
    by_cases ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut
    · exact mul_le_mul_of_nonneg_left (hb t ht) ((averagingBump d n).nonneg_normed t)
    · have hz : k t = 0 := Function.notMem_support.mp (by
        simpa only [k, (averagingBump d n).support_normed_eq] using ht)
      simp only [hz, zero_mul, le_refl]
  rw [integral_mul_const] at he
  change (∫ t, k t * v (x - t)) ≤ b
  simpa only [k, (averagingBump d n).integral_normed, one_mul] using he

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- All normalized mollifications have a common gradient bound on each compact set. -/
theorem Hypotheses.normalizedMollify_gradient_bound (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ C : NNReal, ∀ n x, x ∈ K →
      ‖gradient (normalizedMollify (zeroExtension g u) n) x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
  obtain ⟨C, hC⟩ := h.zeroExtension_lipschitzOn_compact (isCompact_closedBall 0 (R + 1))
  refine ⟨C, fun n x hx ↦ ?_⟩
  have hm := normalizedMollify_lipschitzOn_closedBall h.zeroExtension_continuous hC n
  have hd := norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem (hR hx)) hm
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hd

/-- On each compact set all approximations stay uniformly below one, independently of the index. -/
theorem RigidityHypotheses.normalizedMollify_level_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ b < (1 : ℝ), ∀ n x, x ∈ K →
      normalizedMollify (zeroExtension g u) n x ∈ Set.Icc (0 : ℝ) b := by
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space (m + 1))
  have hne : (closedBall (0 : Space (m + 1)) (R + 1)).Nonempty :=
    ⟨0, by simp only [mem_closedBall, dist_self]; linarith⟩
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : Space (m + 1)) (R + 1)).exists_isMaxOn
    hne h.zeroExtension_continuous.continuousOn
  refine ⟨zeroExtension g u z, hr.zeroExtension_lt_one z, fun n x hx ↦ ?_⟩
  have h0 := mollify_nonneg h.zeroExtension_nonneg n x
  have hc := mollify_contraction_mem_Ioo n
  have hb : mollify (zeroExtension g u) n x ≤ zeroExtension g u z := by
    apply mollify_le_of_local h.zeroExtension_continuous
    intro t ht
    apply hmax
    have hxR : ‖x‖ ≤ R := (by simpa only [mem_ball, dist_zero_right] using hR hx : ‖x‖ < R).le
    have ht1 : ‖t‖ ≤ 1 :=
      (by simpa only [mem_ball, dist_zero_right] using ht :
        ‖t‖ < (averagingBump (m + 1) n).rOut).le.trans (averagingBump_rOut_le_one _ _)
    simp only [mem_closedBall, dist_zero_right]
    exact (norm_sub_le x t).trans (add_le_add hxR ht1)
  exact ⟨mul_nonneg hc.1.le h0, (mul_le_of_le_one_left h0 hc.2.le).trans hb⟩

end SerrinEpigraph
