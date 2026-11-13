module

public import SerrinEpigraph.SegmentGradientEstimate
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Local integral estimates under translation
-/

public section

open MeasureTheory Metric

namespace SerrinEpigraph

noncomputable section

/-- Translating a nonnegative integrand on a ball is controlled by its integral on the enlarged ball. -/
theorem integral_translate_closedBall_le {d : ℕ} {F : Space d → ℝ}
    (hF : Continuous F) (h0 : ∀ x, 0 ≤ F x) (r : ℝ) (z : Space d) :
    (∫ x in closedBall 0 r, F (x + z)) ≤ ∫ x in closedBall 0 (r + ‖z‖), F x := by
  have he := (measurePreserving_add_right volume z).setIntegral_image_emb
    (Homeomorph.addRight z).measurableEmbedding F (closedBall 0 r)
  rw [← he]
  apply setIntegral_mono_set
    (hF.continuousOn.integrableOn_compact (isCompact_closedBall 0 (r + ‖z‖)))
    (Filter.Eventually.of_forall h0)
  apply Filter.Eventually.of_forall
  rintro y ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ r := by simpa using hx
  simpa only [mem_closedBall, dist_zero_right] using
    (norm_add_le x z).trans (add_le_add hx' le_rfl)

/-- The local integral translation error of a smooth function is bounded by its gradient integral
on the ball enlarged by the translation length. -/
theorem integral_norm_translate_sub_le {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (r : ℝ) (z : Space d) :
    (∫ x in closedBall 0 r, ‖v (x + z) - v x‖) ≤
      ‖z‖ * ∫ x in closedBall 0 (r + ‖z‖), ‖gradient v x‖ := by
  have hg : Continuous (fun x ↦ ‖gradient v x‖) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (hv.continuous_fderiv one_ne_zero).norm
  let F : Space d → ℝ → ℝ := fun x t ↦ ‖gradient v (x + t • z)‖
  have hF : Continuous F.uncurry :=
    hg.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hfi : Integrable (Function.uncurry F)
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 r).prod isCompact_Icc)
  have hparam := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hi : IntegrableOn (fun x : Space d ↦ ‖v (x + z) - v x‖) (closedBall 0 r) :=
    (((hv.continuous.comp (continuous_id.add continuous_const)).sub hv.continuous).norm)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hle : (∫ x in closedBall 0 r, ‖v (x + z) - v x‖) ≤
      ∫ x in closedBall 0 r, ‖z‖ * ∫ t in Set.Icc (0 : ℝ) 1, F x t := by
    apply integral_mono hi
      ((continuous_const.mul hparam).continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
    intro x
    have he := norm_sub_le_integral_segment_gradient hv x z
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at he
    exact he
  rw [integral_const_mul, integral_integral_swap hfi] at hle
  apply hle.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  have ht : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x in closedBall 0 r, F x t) ≤ ∫ x in closedBall 0 (r + ‖z‖), ‖gradient v x‖ := by
    intro t ht
    have hn : ‖t • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      nlinarith [norm_nonneg z, ht.2]
    apply (integral_translate_closedBall_le hg (fun x ↦ norm_nonneg _) r (t • z)).trans
    exact setIntegral_mono_set
      (hg.continuousOn.integrableOn_compact (isCompact_closedBall 0 (r + ‖z‖)))
      (Filter.Eventually.of_forall (fun x ↦ norm_nonneg _))
      (Filter.Eventually.of_forall (closedBall_subset_closedBall (add_le_add le_rfl hn)))
  have he := setIntegral_mono_on hfi.integral_prod_right
    (continuousOn_const.integrableOn_compact (μ := volume) isCompact_Icc)
    measurableSet_Icc ht
  simpa only [setIntegral_const, Real.volume_real_Icc, sub_zero, max_eq_left zero_le_one,
    smul_eq_mul, one_mul, Function.uncurry_apply_pair] using he

end

end SerrinEpigraph
