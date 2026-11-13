module

public import SerrinEpigraph.RadialHessianCenter

/-!
# The spatial Hessian away from the center
-/

public section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- Differentiating a radial vector field gives an identity part and a rank-one part. -/
theorem hasFDerivAt_radial_vectorField {d : ℕ} {k : ℝ → ℝ} {k' : ℝ}
    {c x : Space d} (hne : x ≠ c) (hk : HasDerivAt k k' ‖x - c‖) :
    HasFDerivAt (fun y ↦ k ‖y - c‖ • (y - c))
      (k ‖x - c‖ • ContinuousLinearMap.id ℝ (Space d) +
        (k' / ‖x - c‖) • (innerSL ℝ (x - c)).smulRight (x - c)) x := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const c
  have hn := (hasFDerivAt_euclidean_norm (sub_ne_zero.mpr hne)).comp x hi
  have he := (hk.comp_hasFDerivAt x hn).smul hi
  convert he using 1
  · rfl
  · ext y
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      smul_smul, div_eq_mul_inv, Function.comp_apply, id_eq, smul_eq_mul, mul_assoc]

variable {m : ℕ} {f : ℝ → ℝ} {R : ℝ}

/-- The radial equation determines the derivative of slope divided by radius. -/
theorem RadialBallProfile.slope_ratio_hasDerivAt (v : RadialBallProfile f m R)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt (fun t ↦ v.slope t / t)
      ((-f (v.value r) - (m + 1 : ℝ) * v.slope r / r) / r) r := by
  have he := (v.slope_derivative r hr).div (hasDerivAt_id r) hr.1.ne'
  convert he using 1
  · rfl
  · simp only [id_eq]
    field_simp [hr.1.ne']
    ring

/-- Away from the center, the gradient derivative has the radial Hessian formula. -/
theorem RadialBallProfile.spatial_gradient_hasFDerivAt (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) (hne : x ≠ c) :
    HasFDerivAt (gradient (v.spatial c))
      ((v.slope ‖x - c‖ / ‖x - c‖) • ContinuousLinearMap.id ℝ (Space (m + 1)) +
        ((-f (v.value ‖x - c‖) - (m + 1 : ℝ) * v.slope ‖x - c‖ / ‖x - c‖) /
          ‖x - c‖ ^ 2) • (innerSL ℝ (x - c)).smulRight (x - c)) x := by
  have ht : ‖x - c‖ ∈ Ioo (0 : ℝ) R :=
    ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hne),
      by simpa only [Metric.mem_ball, dist_eq_norm] using hx⟩
  have hd := hasFDerivAt_radial_vectorField hne (v.slope_ratio_hasDerivAt ht)
  have heq : gradient (v.spatial c) =ᶠ[𝓝 x]
      (fun y ↦ (v.slope ‖y - c‖ / ‖y - c‖) • (y - c)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx, isOpen_ne.mem_nhds hne] with y hy hyne
    exact (v.spatial_hasGradientAt hy hyne).gradient
  convert hd.congr_of_eventuallyEq heq using 1
  congr 1
  congr 1
  rw [div_div, pow_two]

/-- The trace of the radial Hessian splits into its identity and rank-one contributions. -/
theorem radial_hessian_trace {d : ℕ} (A B : ℝ) (z : Space d) :
    ∑ i : Fin d, inner ℝ
      ((A • ContinuousLinearMap.id ℝ (Space d) + B • (innerSL ℝ z).smulRight z)
        (EuclideanSpace.basisFun (Fin d) ℝ i)) (EuclideanSpace.basisFun (Fin d) ℝ i) =
      (d : ℝ) * A + B * ‖z‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he : ∀ i : Fin d, inner ℝ
      ((A • ContinuousLinearMap.id ℝ (Space d) + B • (innerSL ℝ z).smulRight z) (b i))
        (b i) = A + B * (inner ℝ z (b i)) ^ 2 := by
    intro i
    simp [inner_add_left, inner_smul_left, pow_two]
  change (∑ i : Fin d, inner ℝ
    ((A • ContinuousLinearMap.id ℝ (Space d) + B • (innerSL ℝ z).smulRight z) (b i))
      (b i)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, b.sum_sq_inner_left]
  simp

/-- Away from the center the spatial profile satisfies the original semilinear equation. -/
theorem RadialBallProfile.spatial_equation_off_center (v : RadialBallProfile f m R)
    {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) (hne : x ≠ c) :
    -(Δ (v.spatial c)) x = f (v.spatial c x) := by
  have hd := v.spatial_gradient_hasFDerivAt hx hne
  rw [laplacian_eq_sum_gradient_derivative_of_differentiable hd.differentiableAt
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ), hd.fderiv, radial_hessian_trace]
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  simp only [spatial, Nat.cast_add, Nat.cast_one]
  field_simp [hn]
  ring

/-- The spatial radial profile satisfies the original semilinear equation on the entire ball. -/
theorem RadialBallProfile.spatial_equation (v : RadialBallProfile f m R)
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) :
    -(Δ (v.spatial c)) x = f (v.spatial c x) := by
  by_cases he : x = c
  · subst x
    exact v.spatial_equation_center h c
  · exact v.spatial_equation_off_center hx he

end SerrinEpigraph
