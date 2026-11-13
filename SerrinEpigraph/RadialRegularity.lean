module

public import SerrinEpigraph.RadialHessian

/-!
# Regularity of the spatial radial solution
-/

public section
noncomputable section
open Set InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ R : ℝ}

/-- The spatial gradient is differentiable everywhere in the open ball. -/
theorem RadialBallProfile.spatial_gradient_differentiableOn
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    DifferentiableOn ℝ (gradient (v.spatial c)) (Metric.ball c R) := by
  intro x hx
  by_cases he : x = c
  · subst x
    exact (v.spatial_gradient_hasFDerivAt_center h c).differentiableAt.differentiableWithinAt
  · exact (v.spatial_gradient_hasFDerivAt hx he).differentiableAt.differentiableWithinAt

/-- Continuity of the spatial derivative follows from differentiability of its gradient. -/
theorem RadialBallProfile.spatial_fderiv_continuousOn
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContinuousOn (fderiv ℝ (v.spatial c)) (Metric.ball c R) := by
  have hc := (toDual ℝ (Space (m + 1))).continuous.comp_continuousOn
    (v.spatial_gradient_differentiableOn h c).continuousOn
  convert hc using 1
  funext x
  simp [gradient]

/-- The spatial radial solution is continuously differentiable on the open ball. -/
theorem RadialBallProfile.spatial_contDiffOn_one
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContDiffOn ℝ 1 (v.spatial c) (Metric.ball c R) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
  exact ⟨v.spatial_differentiableOn c, by simp,
    contDiffOn_zero.mpr (v.spatial_fderiv_continuousOn h c)⟩

/-- Away from the center the radial Hessian is continuous. -/
theorem RadialBallProfile.spatial_gradient_fderiv_continuousAt_off_center
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ)
    {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) (hne : x ≠ c) :
    ContinuousAt (fderiv ℝ (gradient (v.spatial c))) x := by
  have ht : ‖x - c‖ ∈ Ioo (0 : ℝ) R :=
    ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hne),
      by simpa only [Metric.mem_ball, dist_eq_norm] using hx⟩
  have hq := (v.value_continuous _ ⟨ht.1.le, ht.2.le⟩).continuousAt
    (Icc_mem_nhds ht.1 ht.2)
  have hp := (v.slope_continuous _ ⟨ht.1.le, ht.2.le⟩).continuousAt
    (Icc_mem_nhds ht.1 ht.2)
  have hF := (h.reaction_contDiffOn.continuousOn _ (v.value_pos _ ht).le).continuousAt
    (Ici_mem_nhds (v.value_pos _ ht))
  have hn : ContinuousAt (fun y : Space (m + 1) ↦ ‖y - c‖) x := by fun_prop
  have hqc : ContinuousAt (fun y : Space (m + 1) ↦ v.value ‖y - c‖) x :=
    hq.comp (x := x) hn
  have hpc : ContinuousAt (fun y : Space (m + 1) ↦ v.slope ‖y - c‖) x :=
    hp.comp (x := x) hn
  have hfc : ContinuousAt (fun y : Space (m + 1) ↦ f (v.value ‖y - c‖)) x :=
    hF.comp (x := x) hqc
  have hz : ‖x - c‖ ≠ 0 := ht.1.ne'
  have hz2 : ‖x - c‖ ^ 2 ≠ 0 := pow_ne_zero _ hz
  have hrank : ContinuousAt
      (fun y : Space (m + 1) ↦ (innerSL ℝ (y - c)).smulRight (y - c)) x := by
    change ContinuousAt (fun y : Space (m + 1) ↦
      ContinuousLinearMap.smulRightL ℝ (Space (m + 1)) (Space (m + 1))
        (innerSL ℝ (y - c)) (y - c)) x
    fun_prop
  have hc : ContinuousAt (fun y : Space (m + 1) ↦
      (v.slope ‖y - c‖ / ‖y - c‖) • ContinuousLinearMap.id ℝ (Space (m + 1)) +
        ((-f (v.value ‖y - c‖) - (m + 1 : ℝ) * v.slope ‖y - c‖ / ‖y - c‖) /
          ‖y - c‖ ^ 2) • (innerSL ℝ (y - c)).smulRight (y - c)) x := by
    fun_prop
  apply hc.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hx, isOpen_ne.mem_nhds hne] with y hy hyne
  exact (v.spatial_gradient_hasFDerivAt hy hyne).fderiv

/-- The spatial radial profile is twice continuously differentiable away from the center. -/
theorem RadialBallProfile.spatial_contDiffOn_two_off_center
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContDiffOn ℝ 2 (v.spatial c) (Metric.ball c R \ {c}) := by
  let S := Metric.ball c R \ {c}
  have hS : IsOpen S := Metric.isOpen_ball.sdiff isClosed_singleton
  have hg : ContDiffOn ℝ 1 (gradient (v.spatial c)) S := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨(v.spatial_gradient_differentiableOn h c).mono sdiff_subset, by simp,
      contDiffOn_zero.mpr ?_⟩
    intro x hx
    exact (v.spatial_gradient_fderiv_continuousAt_off_center h hx.1
      (by simpa only [mem_singleton_iff] using hx.2)).continuousWithinAt
  have hd : ContDiffOn ℝ 1 (fderiv ℝ (v.spatial c)) S := by
    have he := (toDual ℝ (Space (m + 1))).contDiff.comp_contDiffOn hg
    convert he using 1
    funext x
    simp [gradient]
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen hS]
  exact ⟨(v.spatial_differentiableOn c).mono sdiff_subset, by simp, hd⟩

end SerrinEpigraph
