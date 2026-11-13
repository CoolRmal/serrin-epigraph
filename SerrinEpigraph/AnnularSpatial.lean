module

public import SerrinEpigraph.AnnularMaximal
public import SerrinEpigraph.RadialHessian

/-!
# Spatial solutions on annuli
-/

public section
noncomputable section

open Set Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The open annulus with given center and radii. -/
@[expose] def radialAnnulus {d : ℕ} (c : Space d) (a b : ℝ) : Set (Space d) :=
  {x | ‖x - c‖ ∈ Ioo a b}

/-- The closed annulus with given center and radii. -/
@[expose] def closedRadialAnnulus {d : ℕ} (c : Space d) (a b : ℝ) : Set (Space d) :=
  {x | ‖x - c‖ ∈ Icc a b}

theorem isOpen_radialAnnulus {d : ℕ} (c : Space d) (a b : ℝ) :
    IsOpen (radialAnnulus c a b) :=
  isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm

variable {m : ℕ} {f : ℝ → ℝ} {a b : ℝ}

/-- Lift an increasing radial profile to a function of Euclidean distance. -/
@[expose] def IncreasingRadialSegment.spatial (v : IncreasingRadialSegment f m a b)
    (c x : Space (m + 1)) : ℝ := v.value ‖x - c‖

/-- The lifted profile is continuous on the closed annulus. -/
theorem IncreasingRadialSegment.spatial_continuousOn (v : IncreasingRadialSegment f m a b)
    (c : Space (m + 1)) : ContinuousOn (v.spatial c) (closedRadialAnnulus c a b) :=
  v.value_continuous.comp (continuous_id.sub continuous_const).norm.continuousOn
    (fun _ hx ↦ hx)

/-- The lifted profile has the normalized value range on the closed annulus. -/
theorem IncreasingRadialSegment.spatial_range (v : IncreasingRadialSegment f m a b)
    {c x : Space (m + 1)} (hx : x ∈ closedRadialAnnulus c a b) :
    v.spatial c x ∈ Icc (0 : ℝ) 1 := v.value_range _ hx

/-- The lifted profile is positive in the open annulus. -/
theorem IncreasingRadialSegment.spatial_pos (v : IncreasingRadialSegment f m a b)
    {c x : Space (m + 1)} (hx : x ∈ radialAnnulus c a b) : 0 < v.spatial c x :=
  v.value_pos _ hx

/-- The inner sphere has zero Dirichlet value. -/
theorem IncreasingRadialSegment.spatial_inner_zero (v : IncreasingRadialSegment f m a b)
    {c x : Space (m + 1)} (hx : x ∈ Metric.sphere c a) : v.spatial c x = 0 := by
  have he : ‖x - c‖ = a := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  simp only [spatial, he, v.inner_zero]

/-- The spatial derivative on the annulus is the radial slope times the unit radial covector. -/
theorem IncreasingRadialSegment.spatial_hasFDerivAt (v : IncreasingRadialSegment f m a b)
    {c x : Space (m + 1)} (hx : x ∈ radialAnnulus c a b) :
    HasFDerivAt (v.spatial c) ((v.slope ‖x - c‖ / ‖x - c‖) • innerSL ℝ (x - c)) x := by
  have hn0 : x - c ≠ 0 := norm_pos_iff.mp (v.inner_pos.trans hx.1)
  have hn := (hasFDerivAt_euclidean_norm hn0).comp x ((hasFDerivAt_id x).sub_const c)
  have he := (v.value_derivative _ hx).comp_hasFDerivAt x hn
  convert he using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, smul_smul, div_eq_mul_inv]

/-- The spatial gradient is radial. -/
theorem IncreasingRadialSegment.spatial_hasGradientAt (v : IncreasingRadialSegment f m a b)
    {c x : Space (m + 1)} (hx : x ∈ radialAnnulus c a b) :
    HasGradientAt (v.spatial c) ((v.slope ‖x - c‖ / ‖x - c‖) • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert v.spatial_hasFDerivAt hx using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply]

/-- The radial equation determines the derivative of slope divided by radius. -/
theorem IncreasingRadialSegment.slope_ratio_hasDerivAt (v : IncreasingRadialSegment f m a b)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (fun t ↦ v.slope t / t)
      ((-f (v.value r) - (m + 1 : ℝ) * v.slope r / r) / r) r := by
  have hr0 := (v.inner_pos.trans hr.1).ne'
  have he := (v.slope_derivative r hr).div (hasDerivAt_id r) hr0
  convert he using 1
  · rfl
  · simp only [id_eq]
    field_simp [hr0]
    ring

/-- The annular Hessian has the radial identity and rank-one formula. -/
theorem IncreasingRadialSegment.spatial_gradient_hasFDerivAt
    (v : IncreasingRadialSegment f m a b) {c x : Space (m + 1)}
    (hx : x ∈ radialAnnulus c a b) :
    HasFDerivAt (gradient (v.spatial c))
      ((v.slope ‖x - c‖ / ‖x - c‖) • ContinuousLinearMap.id ℝ (Space (m + 1)) +
        ((-f (v.value ‖x - c‖) - (m + 1 : ℝ) * v.slope ‖x - c‖ / ‖x - c‖) /
          ‖x - c‖ ^ 2) • (innerSL ℝ (x - c)).smulRight (x - c)) x := by
  have hne : x ≠ c := sub_ne_zero.mp (norm_pos_iff.mp (v.inner_pos.trans hx.1))
  have hd := hasFDerivAt_radial_vectorField hne (v.slope_ratio_hasDerivAt hx)
  have heq : gradient (v.spatial c) =ᶠ[𝓝 x]
      (fun y ↦ (v.slope ‖y - c‖ / ‖y - c‖) • (y - c)) := by
    filter_upwards [(isOpen_radialAnnulus c a b).mem_nhds hx] with y hy
    exact (v.spatial_hasGradientAt hy).gradient
  convert hd.congr_of_eventuallyEq heq using 1
  congr 1
  congr 1
  rw [div_div, pow_two]

/-- The spatial profile satisfies the original semilinear elliptic equation on the annulus. -/
theorem IncreasingRadialSegment.spatial_equation (v : IncreasingRadialSegment f m a b)
    {c x : Space (m + 1)} (hx : x ∈ radialAnnulus c a b) :
    -(Δ (v.spatial c)) x = f (v.spatial c x) := by
  have hd := v.spatial_gradient_hasFDerivAt hx
  rw [laplacian_eq_sum_gradient_derivative_of_differentiable hd.differentiableAt
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ), hd.fderiv, radial_hessian_trace]
  have hn : ‖x - c‖ ≠ 0 := (v.inner_pos.trans hx.1).ne'
  simp only [spatial, Nat.cast_add, Nat.cast_one]
  field_simp [hn]
  ring

/-- An outer endpoint value of one becomes the outer sphere Dirichlet value. -/
theorem IncreasingRadialSegment.spatial_outer_one (v : IncreasingRadialSegment f m a b)
    (hb : v.value b = 1) {c x : Space (m + 1)} (hx : x ∈ Metric.sphere c b) :
    v.spatial c x = 1 := by
  have he : ‖x - c‖ = b := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  simp only [spatial, he, hb]

end SerrinEpigraph
