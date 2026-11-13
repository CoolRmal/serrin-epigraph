module

public import SerrinEpigraph.PrimitiveRadialDefect
public import SerrinEpigraph.TranslationIntegral

/-!
# Dilation differences controlled by radial variation
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- Integration along a ray expresses a smooth dilation difference through its derivative. -/
theorem sub_eq_integral_dilation_fderiv {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (x : Space d) (a : ℝ) :
    v (a • x) - v x = ∫ t in (1 : ℝ)..a, fderiv ℝ v (t • x) x := by
  have hc : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
  have hi := (((hv.continuous_fderiv one_ne_zero).comp hc).clm_apply
    (continuous_const (y := x))).intervalIntegrable (μ := volume) 1 a
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ v (t • x))
      (fderiv ℝ v (t • x) x) t := by
    have hl : HasDerivAt (fun t : ℝ ↦ t • x) x t := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const x
    exact (hv.differentiable one_ne_zero (t • x)).hasFDerivAt.comp_hasDerivAt t hl
  simpa only [one_smul] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi).symm

/-- On an outward ray, the ordinary radial derivative is bounded by the unnormalized one. -/
theorem norm_dilation_sub_le_integral_radial {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (x : Space d) {a : ℝ} (ha : 1 ≤ a) :
    ‖v (a • x) - v x‖ ≤
      ∫ t in Icc (1 : ℝ) a, ‖inner ℝ (gradient v (t • x)) (t • x)‖ := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hc : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
  have hd := ((hv.continuous_fderiv one_ne_zero).comp hc).clm_apply (continuous_const (y := x))
  rw [sub_eq_integral_dilation_fderiv hv x a,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
  apply (intervalIntegral.norm_integral_le_integral_norm ha).trans
  apply intervalIntegral.integral_mono_on ha (hd.norm.intervalIntegrable _ _)
    (((hg.comp hc).inner hc).norm.intervalIntegrable _ _)
  intro t ht
  rw [real_inner_smul_right, norm_mul, Real.norm_of_nonneg (zero_le_one.trans ht.1),
    inner_gradient_left]
  exact le_mul_of_one_le_left (norm_nonneg _) ht.1

/-- Outward dilations of a nonnegative integrand on a ball are controlled by the enlarged ball. -/
theorem integral_dilate_closedBall_le {d : ℕ} {F : Space d → ℝ}
    (hF : Continuous F) (h0 : ∀ x, 0 ≤ F x) {r t a : ℝ}
    (hr : 0 ≤ r) (ht : 1 ≤ t) (hta : t ≤ a) :
    (∫ x in closedBall 0 r, F (t • x)) ≤ ∫ x in closedBall 0 (a * r), F x := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [Measure.setIntegral_comp_smul_of_pos volume _ _ ht0]
  simp only [smul_closedBall' ht0.ne', smul_zero, Real.norm_of_nonneg ht0.le,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hpow : 1 ≤ t ^ d := one_le_pow₀ ht
  calc
    _ ≤ ∫ x in closedBall 0 (t * r), F x :=
      mul_le_of_le_one_left (integral_nonneg h0) (by
        rw [inv_eq_one_div]
        exact (div_le_one (zero_lt_one.trans_le hpow)).mpr hpow)
    _ ≤ _ := setIntegral_mono_set
      (hF.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
      (Eventually.of_forall h0)
      (Eventually.of_forall (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hta hr)))

/-- A smooth function's local dilation difference is bounded by its radial variation on the
enlarged ball. -/
theorem integral_norm_dilation_sub_le {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {r a : ℝ} (hr : 0 ≤ r) (ha : 1 ≤ a) :
    (∫ x in closedBall 0 r, ‖v (a • x) - v x‖) ≤
      (a - 1) * ∫ x in closedBall 0 (a * r), ‖inner ℝ (gradient v x) x‖ := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  let A := fun x : Space d ↦ ‖inner ℝ (gradient v x) x‖
  have hA : Continuous A := (hg.inner continuous_id).norm
  let F : Space d → ℝ → ℝ := fun x t ↦ A (t • x)
  have hF : Continuous F.uncurry := hA.comp (continuous_snd.smul continuous_fst)
  have hfi : Integrable (Function.uncurry F)
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (Icc (1 : ℝ) a))) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 r).prod isCompact_Icc)
  have hparam := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc (a := (1 : ℝ)) (b := a))
  have hi : IntegrableOn (fun x : Space d ↦ ‖v (a • x) - v x‖) (closedBall 0 r) :=
    (((hv.continuous.comp (continuous_id.const_smul a)).sub hv.continuous).norm)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hle : (∫ x in closedBall 0 r, ‖v (a • x) - v x‖) ≤
      ∫ x in closedBall 0 r, ∫ t in Icc (1 : ℝ) a, F x t :=
    integral_mono hi (hparam.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
      (fun x ↦ norm_dilation_sub_le_integral_radial hv x ha)
  rw [integral_integral_swap hfi] at hle
  apply hle.trans
  have ht : ∀ t ∈ Icc (1 : ℝ) a,
      (∫ x in closedBall 0 r, F x t) ≤ ∫ x in closedBall 0 (a * r), A x :=
    fun t ht ↦ integral_dilate_closedBall_le hA (fun x ↦ norm_nonneg _) hr ht.1 ht.2
  have he := setIntegral_mono_on hfi.integral_prod_right
    (continuousOn_const.integrableOn_compact (μ := volume) isCompact_Icc) measurableSet_Icc ht
  simpa only [setIntegral_const, Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr ha),
    smul_eq_mul, Function.uncurry_apply_pair] using he

end SerrinEpigraph
