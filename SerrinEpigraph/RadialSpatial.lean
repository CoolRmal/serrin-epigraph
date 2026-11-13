module

public import SerrinEpigraph.RadialFlux
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Spatial realization of radial ball profiles
-/

public section
noncomputable section
open Set

namespace SerrinEpigraph

/-- The spatial function centered at a prescribed point associated to a ball profile. -/
@[expose] def RadialBallProfile.spatial {f : ℝ → ℝ} {m : ℕ} {R : ℝ}
    (v : RadialBallProfile f m R) (c : Space (m + 1)) (x : Space (m + 1)) : ℝ :=
  v.value ‖x - c‖

/-- The norm derivative away from the origin is the normalized inner product. -/
theorem hasFDerivAt_euclidean_norm {d : ℕ} {x : Space d} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space d ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have he := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at he
  convert he using 1
  ext y
  simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
  field_simp
  ring

variable {m : ℕ} {f : ℝ → ℝ} {R : ℝ}

/-- Spatial radial profiles are continuous on the closed ball. -/
theorem RadialBallProfile.spatial_continuousOn (v : RadialBallProfile f m R)
    (c : Space (m + 1)) : ContinuousOn (v.spatial c) (Metric.closedBall c R) := by
  apply v.value_continuous.comp (by fun_prop : ContinuousOn (fun x ↦ ‖x - c‖) _)
  intro x hx
  exact ⟨norm_nonneg _, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx⟩

/-- The prescribed value range is preserved on the closed spatial ball. -/
theorem RadialBallProfile.spatial_range (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.closedBall c R) :
    v.spatial c x ∈ Icc (0 : ℝ) 1 := by
  apply v.value_range
  exact ⟨norm_nonneg _, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx⟩

/-- The spatial radial profile vanishes on the boundary sphere. -/
theorem RadialBallProfile.spatial_boundary_zero (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.sphere c R) : v.spatial c x = 0 := by
  have he : ‖x - c‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  simp only [spatial, he, v.boundary_zero]

/-- Positivity holds throughout the spatial ball, including its center. -/
theorem RadialBallProfile.spatial_pos (v : RadialBallProfile f m R)
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) : 0 < v.spatial c x := by
  by_cases he : x = c
  · simpa only [spatial, he, sub_self, norm_zero] using v.value_zero_pos hr h
  · exact v.value_pos _ ⟨norm_pos_iff.mpr (sub_ne_zero.mpr he),
      by simpa only [Metric.mem_ball, dist_eq_norm] using hx⟩

/-- Away from the center the spatial derivative has the usual radial formula. -/
theorem RadialBallProfile.spatial_hasFDerivAt (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) (hne : x ≠ c) :
    HasFDerivAt (v.spatial c)
      ((v.slope ‖x - c‖ / ‖x - c‖) • innerSL ℝ (x - c)) x := by
  have ht : ‖x - c‖ ∈ Ioo (0 : ℝ) R :=
    ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hne),
      by simpa only [Metric.mem_ball, dist_eq_norm] using hx⟩
  have hn := (hasFDerivAt_euclidean_norm (sub_ne_zero.mpr hne)).comp x
    ((hasFDerivAt_id x).sub_const c)
  have he := (v.value_derivative _ ht).comp_hasFDerivAt x hn
  convert he using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, smul_smul, div_eq_mul_inv]

/-- The spatial gradient is radial away from the center. -/
theorem RadialBallProfile.spatial_hasGradientAt (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) (hne : x ≠ c) :
    HasGradientAt (v.spatial c) ((v.slope ‖x - c‖ / ‖x - c‖) • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert v.spatial_hasFDerivAt hx hne using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply]

end SerrinEpigraph
