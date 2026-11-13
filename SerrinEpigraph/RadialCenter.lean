module

public import SerrinEpigraph.RadialSpatial
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# First-order regularity at the center of a radial ball
-/

public section
noncomputable section
open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- A continuous radial slope vanishing at the center gives a zero right derivative there. -/
theorem RadialBallProfile.value_hasDerivWithinAt_zero {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    (v : RadialBallProfile f m R) : HasDerivWithinAt v.value 0 (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo (0 : ℝ) R)
    (fun t ht ↦ (v.value_derivative t ht).differentiableAt.differentiableWithinAt)
  · exact (v.value_continuous 0 ⟨le_rfl, v.radius_pos.le⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT v.radius_pos
  · have hp := v.slope_continuous 0 ⟨le_rfl, v.radius_pos.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE v.radius_pos, v.slope_zero] at hp
    apply (hp.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).congr'
    filter_upwards [Ioo_mem_nhdsGT v.radius_pos] with t ht
    exact (v.value_derivative t ht).deriv.symm

/-- Composing a zero right derivative with distance gives a zero spatial derivative at the center. -/
theorem hasFDerivAt_radial_center {d : ℕ} {q : ℝ → ℝ}
    (hq : HasDerivWithinAt q 0 (Ici 0) 0) (c : Space d) :
    HasFDerivAt (fun x ↦ q ‖x - c‖) (0 : Space d →L[ℝ] ℝ) c := by
  have hn : Tendsto (fun x : Space d ↦ ‖x - c‖) (𝓝 c) (𝓝[Ici 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun x ↦ norm_nonneg _)⟩
    have hc : Continuous (fun x : Space d ↦ ‖x - c‖) := by fun_prop
    simpa only [sub_self, norm_zero] using (hc.continuousAt (x := c)).tendsto
  have he := hq.isLittleO.comp_tendsto hn
  rw [hasFDerivAt_iff_isLittleO]
  simpa only [Function.comp_def, sub_zero, smul_zero, sub_self, norm_zero,
    zero_apply, Asymptotics.isLittleO_norm_right] using he

/-- The spatial ball profile is differentiable at its center with zero derivative. -/
theorem RadialBallProfile.spatial_hasFDerivAt_center {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    (v : RadialBallProfile f m R) (c : Space (m + 1)) :
    HasFDerivAt (v.spatial c) (0 : Space (m + 1) →L[ℝ] ℝ) c :=
  hasFDerivAt_radial_center v.value_hasDerivWithinAt_zero c

/-- The spatial ball profile is differentiable at every point of the open ball. -/
theorem RadialBallProfile.spatial_differentiableOn {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    (v : RadialBallProfile f m R) (c : Space (m + 1)) :
    DifferentiableOn ℝ (v.spatial c) (Metric.ball c R) := by
  intro x hx
  by_cases he : x = c
  · subst x
    exact (v.spatial_hasFDerivAt_center c).differentiableAt.differentiableWithinAt
  · exact (v.spatial_hasFDerivAt hx he).differentiableAt.differentiableWithinAt

/-- The spatial gradient vanishes at the center. -/
theorem RadialBallProfile.spatial_gradient_center {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    (v : RadialBallProfile f m R) (c : Space (m + 1)) :
    gradient (v.spatial c) c = 0 := by
  have he := (v.spatial_hasFDerivAt_center c).hasGradientAt.gradient
  simpa using he

/-- The norm of the spatial gradient is the absolute radial slope, including the center. -/
theorem RadialBallProfile.spatial_norm_gradient {m : ℕ} {f : ℝ → ℝ} {R : ℝ}
    (v : RadialBallProfile f m R) {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) :
    ‖gradient (v.spatial c) x‖ = |v.slope ‖x - c‖| := by
  by_cases he : x = c
  · subst x
    simp only [v.spatial_gradient_center, norm_zero, sub_self, v.slope_zero, abs_zero]
  · rw [(v.spatial_hasGradientAt hx he).gradient, norm_smul, Real.norm_eq_abs,
      abs_div, abs_of_nonneg (norm_nonneg _)]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr he))

/-- The spatial gradient is continuous at the center despite the singular radial coordinate. -/
theorem RadialBallProfile.spatial_gradient_continuousAt_center
    {m : ℕ} {f : ℝ → ℝ} {R : ℝ} (v : RadialBallProfile f m R)
    (c : Space (m + 1)) : ContinuousAt (gradient (v.spatial c)) c := by
  have hn : Tendsto (fun x : Space (m + 1) ↦ ‖x - c‖) (𝓝 c) (𝓝[Icc 0 R] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun x : Space (m + 1) ↦ ‖x - c‖) := by fun_prop
      simpa only [sub_self, norm_zero] using (hc.continuousAt (x := c)).tendsto
    · filter_upwards [Metric.ball_mem_nhds c v.radius_pos] with x hx
      exact ⟨norm_nonneg _, (show ‖x - c‖ < R by
        simpa only [Metric.mem_ball, dist_eq_norm] using hx).le⟩
  have hp := ((v.slope_continuous 0 ⟨le_rfl, v.radius_pos.le⟩).tendsto.comp hn).abs
  simp only [v.slope_zero, abs_zero] at hp
  rw [ContinuousAt, v.spatial_gradient_center]
  apply squeeze_zero_norm' _ hp
  filter_upwards [Metric.ball_mem_nhds c v.radius_pos] with x hx
  exact (v.spatial_norm_gradient hx).le

end SerrinEpigraph
