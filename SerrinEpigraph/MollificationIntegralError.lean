module

public import SerrinEpigraph.LipschitzTranslationIntegral

/-!
# Averaging translation errors to control mollification
-/

public section

open MeasureTheory Metric ContinuousLinearMap

namespace SerrinEpigraph

noncomputable section

/-- A mollification error is bounded by the kernel average of the translation error. -/
theorem norm_mollify_sub_le {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (n : ℕ) (x : Space d) :
    ‖mollify v n x - v x‖ ≤ ∫ t,
      (averagingBump d n).normed volume t * ‖v (x - t) - v x‖ := by
  let k := (averagingBump d n).normed volume
  have hi : Integrable (fun t ↦ k t * v (x - t)) :=
    (((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (μ := volume) (lsmul ℝ ℝ) (averagingBump d n).continuous_normed hv.locallyIntegrable x).integrable
  have hc : Integrable (fun t ↦ k t * v x) := (averagingBump d n).integrable_normed.mul_const _
  have he : mollify v n x - v x = ∫ t, k t * (v (x - t) - v x) := by
    simp_rw [mul_sub]
    rw [integral_sub hi hc, integral_mul_const, (averagingBump d n).integral_normed, one_mul]
    rfl
  rw [he]
  have hb := norm_integral_le_integral_norm (μ := volume) (fun t ↦ k t * (v (x - t) - v x))
  apply hb.trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by
    dsimp only [k]
    rw [norm_mul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t)])

/-- Every averaging kernel vanishes outside the closed unit ball. -/
theorem averagingBump_normed_zero_of_notMem_unitBall {d n : ℕ} {t : Space d}
    (ht : t ∉ closedBall 0 1) : (averagingBump d n).normed volume t = 0 := by
  apply Function.notMem_support.mp
  rw [(averagingBump d n).support_normed_eq]
  intro hb
  apply ht
  exact ball_subset_closedBall ((ball_subset_ball (averagingBump_rOut_le_one d n)) hb)

/-- A uniform local translation error bound on the kernel support bounds the mollification error. -/
theorem integral_norm_mollify_sub_le {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (n : ℕ) (r A : ℝ)
    (hA : ∀ t ∈ ball (0 : Space d) (averagingBump d n).rOut,
      (∫ x in closedBall 0 r, ‖v (x - t) - v x‖) ≤ A) :
    (∫ x in closedBall 0 r, ‖mollify v n x - v x‖) ≤ A := by
  let k := (averagingBump d n).normed volume
  let F : Space d → Space d → ℝ := fun x t ↦ k t * ‖v (x - t) - v x‖
  have hF : Continuous F.uncurry :=
    ((averagingBump d n).continuous_normed.comp continuous_snd).mul
      (((hv.comp (continuous_fst.sub continuous_snd)).sub (hv.comp continuous_fst)).norm)
  have hfi : Integrable F.uncurry
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (closedBall 0 1))) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 r).prod (isCompact_closedBall 0 1))
  have he (x : Space d) : (∫ t, F x t) = ∫ t in closedBall 0 1, F x t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp only [F, k, averagingBump_normed_zero_of_notMem_unitBall ht, zero_mul]
  have hp := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_closedBall (0 : Space d) 1)
  have hle : (∫ x in closedBall 0 r, ‖mollify v n x - v x‖) ≤
      ∫ x in closedBall 0 r, ∫ t in closedBall 0 1, F x t := by
    apply integral_mono
      (((mollify_contDiff hv n).continuous.sub hv).norm.continuousOn.integrableOn_compact
        (isCompact_closedBall 0 r))
      (hp.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
    intro x
    dsimp only [Pi.sub_apply]
    rw [← he]
    exact norm_mollify_sub_le hv n x
  rw [integral_integral_swap hfi] at hle
  have hk : IntegrableOn (fun t : Space d ↦ k t * A) (closedBall 0 1) :=
    (((averagingBump d n).continuous_normed.mul continuous_const).continuousOn)
      |>.integrableOn_compact (isCompact_closedBall 0 1)
  have hb := setIntegral_mono_on hfi.integral_prod_right hk isClosed_closedBall.measurableSet
    (fun t _ ↦ ?_)
  · have hmass : (∫ t in closedBall 0 1, k t) = 1 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht ↦ averagingBump_normed_zero_of_notMem_unitBall ht)]
      exact (averagingBump d n).integral_normed
    rw [integral_mul_const, hmass, one_mul] at hb
    exact hle.trans hb
  · change (∫ x in closedBall 0 r, k t * ‖v (x - t) - v x‖) ≤ k t * A
    rw [integral_const_mul]
    by_cases ht' : t ∈ ball (0 : Space d) (averagingBump d n).rOut
    · exact mul_le_mul_of_nonneg_left (hA t ht') ((averagingBump d n).nonneg_normed t)
    · have hz : k t = 0 := Function.notMem_support.mp (by
        simpa only [k, (averagingBump d n).support_normed_eq] using ht')
      simp only [hz, zero_mul, le_refl]

/-- The mollification error of the primitive family is bounded uniformly in dilation by the
averaging radius times a fixed local constant. -/
theorem RigidityHypotheses.rescaledPhasePrimitive_mollification_error
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r : ℝ) (n : ℕ), 1 ≤ R → 1 ≤ r →
      (∫ x in closedBall 0 r,
        ‖mollify (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) n x -
          phasePrimitive f (zeroExtension g u (R • x))‖) ≤
        (1 / ((n : ℝ) + 1)) * (C * (r + 1) ^ m) := by
  obtain ⟨C, hC, hb⟩ := hr.rescaledPhasePrimitive_translation_bound h
  refine ⟨C, hC, fun R r n hR hradius ↦ ?_⟩
  apply integral_norm_mollify_sub_le
    ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul R)) n r
  intro t ht
  have htρ : ‖t‖ ≤ 1 / ((n : ℝ) + 1) := by
    exact (show ‖t‖ < (averagingBump (m + 1) n).rOut by simpa using ht).le
  have ht1 : ‖t‖ ≤ 1 := htρ.trans (averagingBump_rOut_le_one (m + 1) n)
  have hrr : 1 ≤ R * (r + ‖-t‖) := by
    have hpos : 0 ≤ ‖-t‖ := norm_nonneg _
    nlinarith
  have he := hb R r (-t) (by linarith) hrr
  simp only [norm_neg, ← sub_eq_add_neg] at he
  apply he.trans
  apply mul_le_mul htρ _ (mul_nonneg hC.le (pow_nonneg (by linarith [norm_nonneg t]) _))
    (by positivity)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [norm_nonneg t]) (by linarith) m) hC.le

end

end SerrinEpigraph
