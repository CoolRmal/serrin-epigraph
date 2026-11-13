module

public import SerrinEpigraph.RadialHessianContinuity

/-!
# Boundary derivatives of radial comparison solutions
-/

public section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {f : ℝ → ℝ} {R : ℝ}

/-- The radial profile has its prescribed slope as a left derivative at the outer boundary. -/
theorem RadialBallProfile.value_hasDerivWithinAt_radius (v : RadialBallProfile f m R) :
    HasDerivWithinAt v.value (v.slope R) (Iic R) R := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo (0 : ℝ) R)
    (fun t ht ↦ (v.value_derivative t ht).differentiableAt.differentiableWithinAt)
  · exact (v.value_continuous R ⟨v.radius_pos.le, le_rfl⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsLT v.radius_pos
  · have hp := v.slope_continuous R ⟨v.radius_pos.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE v.radius_pos] at hp
    apply (hp.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)).congr'
    filter_upwards [Ioo_mem_nhdsLT v.radius_pos] with t ht
    exact (v.value_derivative t ht).deriv.symm

/-- The spatial boundary differential is the radial differential taken from inside the ball. -/
theorem RadialBallProfile.spatial_hasFDerivWithinAt_boundary (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.sphere c R) :
    HasFDerivWithinAt (v.spatial c)
      ((v.slope R / R) • innerSL ℝ (x - c)) (Metric.closedBall c R) x := by
  have hnorm : ‖x - c‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hne : x - c ≠ 0 := norm_ne_zero_iff.mp (hnorm ▸ v.radius_pos.ne')
  have hn := (hasFDerivAt_euclidean_norm hne).comp x ((hasFDerivAt_id x).sub_const c)
  have hmap : MapsTo (fun y : Space (m + 1) ↦ ‖y - c‖) (Metric.closedBall c R) (Iic R) := by
    intro y hy
    simpa only [mem_Iic, Metric.mem_closedBall, dist_eq_norm] using hy
  have he := v.value_hasDerivWithinAt_radius.comp_hasFDerivWithinAt_of_eq x
    hn.hasFDerivWithinAt hmap hnorm.symm
  convert he using 1
  · rfl
  · simp only [hnorm, ContinuousLinearMap.comp_id, smul_smul, div_eq_mul_inv]

/-- A positive-radius closed ball has unique differentials at all its points. -/
theorem uniqueDiffOn_closedBall_space {d : ℕ} (c : Space d) {R : ℝ} (hR : 0 < R) :
    UniqueDiffOn ℝ (Metric.closedBall c R) := by
  apply uniqueDiffOn_convex (convex_closedBall c R)
  exact ⟨c, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds c hR)⟩

/-- Evaluating the spatial boundary differential on the outward unit normal gives the radial slope. -/
theorem RadialBallProfile.spatial_normal_derivative (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.sphere c R) :
    fderivWithin ℝ (v.spatial c) (Metric.closedBall c R) x (R⁻¹ • (x - c)) =
      v.slope R := by
  have hnorm : ‖x - c‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hmem : x ∈ Metric.closedBall c R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, hnorm] using (le_refl R)
  rw [(v.spatial_hasFDerivWithinAt_boundary hx).fderivWithin
    (uniqueDiffOn_closedBall_space c v.radius_pos x hmem)]
  simp only [smul_apply, innerSL_apply_apply, inner_smul_right, smul_eq_mul,
    real_inner_self_eq_norm_sq, hnorm]
  field_simp [v.radius_pos.ne']

/-- The averaged derivative formula holds relative to the closed ball at every point. -/
theorem RadialBallProfile.spatial_hasFDerivWithinAt_closedBall
    (v : RadialBallProfile f m R) {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {c x : Space (m + 1)} (hx : x ∈ Metric.closedBall c R) :
    HasFDerivWithinAt (v.spatial c)
      ((-radialAverage m (f ∘ v.value) ‖x - c‖) • innerSL ℝ (x - c))
      (Metric.closedBall c R) x := by
  by_cases he : x = c
  · subst x
    simpa only [sub_self, map_zero, smul_zero] using
      (v.spatial_hasFDerivAt_center c).hasFDerivWithinAt (s := Metric.closedBall c R)
  have hnorm : ‖x - c‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have ht : ‖x - c‖ ∈ Ioc (0 : ℝ) R :=
    ⟨norm_pos_iff.mpr (sub_ne_zero.mpr he), hnorm⟩
  rw [← v.slope_div_eq_average h ht]
  rcases lt_or_eq_of_le hnorm with hlt | heq
  · exact (v.spatial_hasFDerivAt (by
      simpa only [Metric.mem_ball, dist_eq_norm] using hlt) he).hasFDerivWithinAt
  · have hs : x ∈ Metric.sphere c R := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using heq
    simpa only [heq] using v.spatial_hasFDerivWithinAt_boundary hs

/-- The radial comparison solution is continuously differentiable up to the boundary. -/
theorem RadialBallProfile.spatial_contDiffOn_one_closedBall
    (v : RadialBallProfile f m R) {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    ContDiffOn ℝ 1 (v.spatial c) (Metric.closedBall c R) := by
  have hF : ContinuousOn (f ∘ v.value) (Icc 0 R) :=
    h.reaction_contDiffOn.continuousOn.comp v.value_continuous
      (fun t ht ↦ (v.value_range t ht).1)
  have hA : ContinuousOn (fun x : Space (m + 1) ↦
      -radialAverage m (f ∘ v.value) ‖x - c‖) (Metric.closedBall c R) := by
    apply (radialAverage_continuousOn m v.radius_pos.le hF).neg.comp
      (by fun_prop : ContinuousOn (fun x ↦ ‖x - c‖) _)
    intro x hx
    exact ⟨norm_nonneg _, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx⟩
  have hc : ContinuousOn (fun x : Space (m + 1) ↦
      (-radialAverage m (f ∘ v.value) ‖x - c‖) • innerSL ℝ (x - c))
      (Metric.closedBall c R) := by fun_prop
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (uniqueDiffOn_closedBall_space c v.radius_pos)]
  exact ⟨by simp, _, contDiffOn_zero.mpr hc,
    fun x hx ↦ v.spatial_hasFDerivWithinAt_closedBall h hx⟩

end SerrinEpigraph
