module

public import SerrinEpigraph.RadialRegularity

/-!
# Continuity of the radial Hessian at the center
-/

public section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The normalized radial rank-one term has norm bounded by its scalar coefficient. -/
theorem norm_radial_rank_one_le {d : ℕ} (b : ℝ) (z : Space d) :
    ‖(b / ‖z‖ ^ 2) • (innerSL ℝ z).smulRight z‖ ≤ |b| := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖z‖),
      ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    apply le_of_eq
    field_simp [hn]

/-- A vanishing scalar coefficient removes the directional singularity of a radial rank-one term. -/
theorem radial_rank_one_tendsto_zero {d : ℕ} {b : Space d → ℝ} {c : Space d}
    (hb : Tendsto b (𝓝 c) (𝓝 0)) :
    Tendsto (fun x ↦ (b x / ‖x - c‖ ^ 2) • (innerSL ℝ (x - c)).smulRight (x - c))
      (𝓝 c) (𝓝 (0 : Space d →L[ℝ] Space d)) := by
  apply squeeze_zero_norm (fun x ↦ norm_radial_rank_one_le (b x) (x - c))
  simpa only [abs_zero] using hb.abs

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ R : ℝ}

/-- The spatial Hessian is continuous at the center of the ball. -/
theorem RadialBallProfile.spatial_gradient_fderiv_continuousAt_center
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContinuousAt (fderiv ℝ (gradient (v.spatial c))) c := by
  let A := fun x : Space (m + 1) ↦ -radialAverage m (f ∘ v.value) ‖x - c‖
  let B := fun x : Space (m + 1) ↦ -f (v.spatial c x) - (m + 1 : ℝ) * A x
  have hF : ContinuousOn (f ∘ v.value) (Icc 0 R) :=
    h.reaction_contDiffOn.continuousOn.comp v.value_continuous
      (fun t ht ↦ (v.value_range t ht).1)
  have hAc : ContinuousOn A (Metric.closedBall c R) := by
    apply (radialAverage_continuousOn m v.radius_pos.le hF).neg.comp
      (by fun_prop : ContinuousOn (fun x ↦ ‖x - c‖) _)
    intro x hx
    exact ⟨norm_nonneg _, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx⟩
  have hA := hAc.continuousAt (Metric.closedBall_mem_nhds c v.radius_pos)
  have hreact : ContinuousOn (fun x ↦ f (v.spatial c x)) (Metric.closedBall c R) :=
    h.reaction_contDiffOn.continuousOn.comp (v.spatial_continuousOn c)
      (fun x hx ↦ (v.spatial_range hx).1)
  have hB : ContinuousAt B c :=
    (hreact.continuousAt (Metric.closedBall_mem_nhds c v.radius_pos)).neg.sub
      (hA.const_mul (m + 1 : ℝ))
  have hA0 : A c = -f (v.value 0) / (m + 1 : ℝ) := by
    simp only [A, sub_self, norm_zero, radialAverage_zero, Function.comp_apply, neg_div]
  have hB0 : B c = 0 := by
    dsimp only [B]
    rw [hA0]
    simp only [spatial, sub_self, norm_zero]
    field_simp
    ring
  have hBt : Tendsto B (𝓝 c) (𝓝 0) := by simpa only [hB0] using hB.tendsto
  have hlim := (hA.tendsto.smul_const (ContinuousLinearMap.id ℝ (Space (m + 1)))).add
    (radial_rank_one_tendsto_zero hBt)
  rw [add_zero, hA0] at hlim
  rw [ContinuousAt, (v.spatial_gradient_hasFDerivAt_center h c).fderiv]
  apply hlim.congr'
  filter_upwards [Metric.ball_mem_nhds c v.radius_pos] with x hx
  by_cases he : x = c
  · subst x
    simp only [(v.spatial_gradient_hasFDerivAt_center h c).fderiv,
      hA0, hB0, zero_div, zero_smul, add_zero]
  · have ht : ‖x - c‖ ∈ Ioc (0 : ℝ) R :=
      ⟨norm_pos_iff.mpr (sub_ne_zero.mpr he),
        (show ‖x - c‖ < R by simpa only [Metric.mem_ball, dist_eq_norm] using hx).le⟩
    have hAx : A x = v.slope ‖x - c‖ / ‖x - c‖ := (v.slope_div_eq_average h ht).symm
    rw [(v.spatial_gradient_hasFDerivAt hx he).fderiv]
    dsimp only [B]
    rw [hAx]
    simp only [spatial, mul_div_assoc]

/-- The gradient derivative is continuous throughout the open ball. -/
theorem RadialBallProfile.spatial_gradient_fderiv_continuousOn
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContinuousOn (fderiv ℝ (gradient (v.spatial c))) (Metric.ball c R) := by
  intro x hx
  by_cases he : x = c
  · subst x
    exact (v.spatial_gradient_fderiv_continuousAt_center h c).continuousWithinAt
  · exact (v.spatial_gradient_fderiv_continuousAt_off_center h hx he).continuousWithinAt

/-- The spatial radial profile is twice continuously differentiable on the whole open ball. -/
theorem RadialBallProfile.spatial_contDiffOn_two
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContDiffOn ℝ 2 (v.spatial c) (Metric.ball c R) := by
  have hg : ContDiffOn ℝ 1 (gradient (v.spatial c)) (Metric.ball c R) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    exact ⟨v.spatial_gradient_differentiableOn h c, by simp,
      contDiffOn_zero.mpr (v.spatial_gradient_fderiv_continuousOn h c)⟩
  have hd : ContDiffOn ℝ 1 (fderiv ℝ (v.spatial c)) (Metric.ball c R) := by
    have he := (toDual ℝ (Space (m + 1))).contDiff.comp_contDiffOn hg
    convert he using 1
    funext x
    simp [gradient]
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
  exact ⟨v.spatial_differentiableOn c, by simp, hd⟩

end SerrinEpigraph
