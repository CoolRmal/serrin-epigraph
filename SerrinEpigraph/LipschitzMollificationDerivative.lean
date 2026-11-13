module

public import SerrinEpigraph.LipschitzCompetitorEnergy
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating averages of Lipschitz functions
-/

public section
noncomputable section

open MeasureTheory Filter ContinuousLinearMap Metric InnerProductSpace
open scoped Topology Convolution

namespace SerrinEpigraph

/-- A globally Lipschitz function can be differentiated under the averaging integral;
its almost-everywhere derivative supplies the derivative of the smooth average. -/
theorem mollify_hasFDerivAt_of_lipschitz {d : ℕ} {v : Space d → ℝ} {C : NNReal}
    (hv : LipschitzWith C v) (n : ℕ) (x : Space d) :
    HasFDerivAt (mollify v n)
      (((averagingBump d n).normed volume ⋆[lsmul ℝ ℝ, volume] fderiv ℝ v) x) x := by
  let k := (averagingBump d n).normed volume
  have hk : Continuous k := (averagingBump d n).continuous_normed
  have hki : Integrable k := (averagingBump d n).integrable_normed
  have hmeas : AEStronglyMeasurable (fun t ↦ k t • fderiv ℝ v (x - t)) :=
    hk.aestronglyMeasurable.convolution_integrand_snd (lsmul ℝ ℝ)
      (measurable_fderiv ℝ v).aestronglyMeasurable x
  have hi : Integrable (fun t ↦ k t * v (x - t)) :=
    ((averagingBump d n).hasCompactSupport_normed.convolutionExists_left
      (lsmul ℝ ℝ) hk hv.continuous.locallyIntegrable x).integrable
  have hlip : ∀ᵐ t, LipschitzOnWith (Real.nnabs (k t * C))
      (fun z ↦ k t * v (z - t)) Set.univ := by
    filter_upwards with t
    apply LipschitzOnWith.of_dist_le_mul
    intro z _ w _
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    have hh := hv.dist_le_mul (z - t) (w - t)
    rw [dist_sub_right] at hh
    simpa only [Real.coe_nnabs, abs_mul, abs_of_nonneg C.coe_nonneg,
      Real.norm_eq_abs, mul_assoc, dist_eq_norm] using
      mul_le_mul_of_nonneg_left hh (norm_nonneg (k t))
  have hdiff : ∀ᵐ t, HasFDerivAt (fun z ↦ k t * v (z - t))
      (k t • fderiv ℝ v (x - t)) x := by
    have ha := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      hv.ae_differentiableAt
    filter_upwards [ha] with t ht
    have hd := ht.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const t)
    convert hd.const_mul (k t) using 1
    · rfl
    · simp only [ContinuousLinearMap.comp_id]
  have hh := hasFDerivAt_integral_of_dominated_loc_of_lip (𝕜 := ℝ)
    (s := Set.univ) (bound := fun t ↦ k t * C) (F := fun z t ↦ k t * v (z - t))
    Filter.univ_mem (Eventually.of_forall (fun z ↦
      (hk.mul (hv.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable))
    hi hmeas hlip (hki.mul_const C) hdiff
  exact hh.2

/-- The derivative of a globally Lipschitz function is locally integrable. -/
theorem locallyIntegrable_fderiv_of_lipschitz {d : ℕ} {v : Space d → ℝ} {C : NNReal}
    (hv : LipschitzWith C v) : LocallyIntegrable (fderiv ℝ v) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hi : IntegrableOn (fun _ : Space d ↦ (C : ℝ)) K :=
    continuousOn_const.integrableOn_compact hK
  apply hi.mono' (measurable_fderiv ℝ v).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ norm_fderiv_le_of_lipschitz ℝ hv)

/-- Averaged derivatives of a Lipschitz function converge almost everywhere by
Lebesgue differentiation. -/
theorem mollify_fderiv_tendsto_ae_of_lipschitz {d : ℕ} {v : Space d → ℝ} {C : NNReal}
    (hv : LipschitzWith C v) : ∀ᵐ x,
    Tendsto (fun n ↦ fderiv ℝ (mollify v n) x) atTop (𝓝 (fderiv ℝ v x)) := by
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := averagingBump d) (K := 2) tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall (fun n ↦ by
      change 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2)
      linarith)) (locallyIntegrable_fderiv_of_lipschitz hv)
  filter_upwards [ht] with x hx
  simpa only [(mollify_hasFDerivAt_of_lipschitz hv _ _).fderiv] using hx

/-- Normalized smooth averages recover the gradient of a Lipschitz competitor almost everywhere. -/
theorem normalizedMollify_gradient_tendsto_ae_of_lipschitz
    {d : ℕ} {v : Space d → ℝ} {C : NNReal} (hv : LipschitzWith C v) :
    ∀ᵐ x, Tendsto (fun n ↦ gradient (normalizedMollify v n) x) atTop (𝓝 (gradient v x)) := by
  filter_upwards [mollify_fderiv_tendsto_ae_of_lipschitz hv] with x hx
  have ht := ((toDual ℝ (Space d)).symm.continuous.tendsto (fderiv ℝ v x)).comp hx
  have hs := mollify_contraction_tendsto.smul ht
  simp_rw [normalizedMollify_gradient hv.continuous]
  simpa only [gradient, one_smul, Function.comp_def] using hs

/-- Localizing on a countable family of balls extends gradient convergence to all
locally Lipschitz competitors. -/
theorem normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v) :
    ∀ᵐ x, Tendsto (fun n ↦ gradient (normalizedMollify v n) x) atTop (𝓝 (gradient v x)) := by
  have hn : ∀ r : ℕ, ∀ᵐ x, x ∈ ball (0 : Space d) (r : ℝ) →
      Tendsto (fun n ↦ gradient (normalizedMollify v n) x) atTop (𝓝 (gradient v x)) := by
    intro r
    obtain ⟨C, hC⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : Space d) (r : ℝ))
    obtain ⟨w, hw, he⟩ := hC.extend_real
    filter_upwards [normalizedMollify_gradient_tendsto_ae_of_lipschitz hw] with x hx
    intro hxb
    have hlocal : v =ᶠ[𝓝 x] w := by
      filter_upwards [closedBall_mem_nhds_of_mem hxb] with z hz
      exact he hz
    rw [hlocal.gradient_eq]
    apply hx.congr'
    exact (normalizedMollify_gradient_eventuallyEq hlocal).symm
  filter_upwards [ae_all_iff.mpr hn] with x hx
  obtain ⟨r, hr⟩ := exists_nat_gt ‖x‖
  exact hx r (by simpa only [mem_ball, dist_zero_right] using hr)

end SerrinEpigraph
