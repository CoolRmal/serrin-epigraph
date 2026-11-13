module

public import SerrinEpigraph.RadialSlopeRatio
public import SerrinEpigraph.WeakEquation

/-!
# The isotropic Hessian at the center of a radial ball
-/

public section
noncomputable section
open Set Filter
open InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- A continuous scalar coefficient multiplying displacement is differentiable at the base point. -/
theorem hasFDerivAt_coefficient_smul_displacement {d : ℕ} {k : Space d → ℝ}
    {c : Space d} (hk : ContinuousAt k c) :
    HasFDerivAt (fun x ↦ k x • (x - c))
      (k c • ContinuousLinearMap.id ℝ (Space d)) c := by
  have ht : Tendsto (fun x ↦ k x - k c) (𝓝 c) (𝓝 0) := by
    simpa only [sub_self] using hk.tendsto.sub_const (k c)
  have ho := ((Asymptotics.isLittleO_one_iff ℝ).mpr ht).smul_isBigO
    (Asymptotics.isBigO_refl (fun x : Space d ↦ x - c) (𝓝 c))
  rw [hasFDerivAt_iff_isLittleO]
  simpa only [sub_self, smul_zero, sub_zero, smul_apply, ContinuousLinearMap.id_apply,
    one_smul, sub_smul] using ho

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ R : ℝ}

/-- The weighted-average formula expresses the spatial gradient without division by radius. -/
theorem RadialBallProfile.spatial_gradient_eq_average (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) {c x : Space (m + 1)} (hx : x ∈ Metric.ball c R) :
    gradient (v.spatial c) x =
      (-radialAverage m (f ∘ v.value) ‖x - c‖) • (x - c) := by
  by_cases he : x = c
  · subst x
    simp only [v.spatial_gradient_center, sub_self, smul_zero]
  · rw [(v.spatial_hasGradientAt hx he).gradient,
      v.slope_div_eq_average h ⟨norm_pos_iff.mpr (sub_ne_zero.mpr he),
        (show ‖x - c‖ < R by simpa only [Metric.mem_ball, dist_eq_norm] using hx).le⟩]

/-- The gradient is differentiable at the center with the isotropic derivative prescribed by the PDE. -/
theorem RadialBallProfile.spatial_gradient_hasFDerivAt_center
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    HasFDerivAt (gradient (v.spatial c))
      ((-f (v.value 0) / (m + 1 : ℝ)) • ContinuousLinearMap.id ℝ (Space (m + 1))) c := by
  let k := fun x : Space (m + 1) ↦ -radialAverage m (f ∘ v.value) ‖x - c‖
  have hF : ContinuousOn (f ∘ v.value) (Icc 0 R) :=
    h.reaction_contDiffOn.continuousOn.comp v.value_continuous
      (fun t ht ↦ (v.value_range t ht).1)
  have hc : ContinuousOn k (Metric.closedBall c R) := by
    apply (radialAverage_continuousOn m v.radius_pos.le hF).neg.comp
      (by fun_prop : ContinuousOn (fun x ↦ ‖x - c‖) _)
    intro x hx
    exact ⟨norm_nonneg _, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx⟩
  have hk : ContinuousAt k c := hc.continuousAt (Metric.closedBall_mem_nhds c v.radius_pos)
  have hd := hasFDerivAt_coefficient_smul_displacement hk
  have hk0 : k c = -f (v.value 0) / (m + 1 : ℝ) := by
    simp only [k, sub_self, norm_zero, radialAverage_zero, Function.comp_apply, neg_div]
  rw [hk0] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds c v.radius_pos] with x hx
  exact v.spatial_gradient_eq_average h hx

/-- Differentiability of the gradient suffices to compute the Laplacian as its trace. -/
theorem laplacian_eq_sum_gradient_derivative_of_differentiable
    {d : ℕ} {w : Space d → ℝ} {x : Space d}
    (hg : DifferentiableAt ℝ (gradient w) x)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space d)) :
    (Δ w) x = ∑ i, inner ℝ (fderiv ℝ (gradient w) x (b i)) (b i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ w) x := by
    have he := (toDual ℝ (Space d)).differentiableAt.comp x hg
    convert he using 1
    funext y
    simp [gradient]
  rw [laplacian_eq_sum_fderiv b hd]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y ↦ fderiv ℝ w y (b i)) =
      (fun y ↦ inner ℝ (b i) (gradient w y)) := by
    funext y
    rw [real_inner_comm, inner_gradient_left]
  rw [he]
  have hder := (innerSL ℝ (b i)).hasFDerivAt.comp x hg.hasFDerivAt
  have hv := congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (b i)) hder.fderiv
  calc
    _ = inner ℝ (b i) (fderiv ℝ (gradient w) x (b i)) := by
      simpa [Function.comp_def] using hv
    _ = _ := real_inner_comm _ _

/-- The spatial radial profile satisfies the original semilinear equation at the ball center. -/
theorem RadialBallProfile.spatial_equation_center (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) (c : Space (m + 1)) :
    -(Δ (v.spatial c)) c = f (v.spatial c c) := by
  have hd := v.spatial_gradient_hasFDerivAt_center h c
  rw [laplacian_eq_sum_gradient_derivative_of_differentiable hd.differentiableAt
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ), hd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
    RCLike.conj_to_real, OrthonormalBasis.inner_eq_one, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    spatial, sub_self, norm_zero]
  field_simp
  push_cast
  ring

end SerrinEpigraph
