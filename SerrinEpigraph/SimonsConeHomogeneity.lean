module

public import SerrinEpigraph.BoundaryChartGluing
public import SerrinEpigraph.MinimalSurfaceIdentities

/-!
# Smooth boundary charts of cones: homogeneity and the improved Kato inequality

Let `E` be a.e. invariant under the dilations `x ↦ a • x`, `a > 0`, and let `(E, U, F)` be a smooth
boundary chart. This module proves:

* the dilated function `y ↦ F (a • y)` is a smooth boundary chart of `E` on `a⁻¹ U`
  (`Simons.chart_dilate`), with normal `ν (a • y)` and second fundamental form `a • A (a • y)`;
* **homogeneity on the boundary piece** `M = U ∩ {F = 0}`: `M` is locally dilation invariant,
  `ν (a • x) = ν x` and `A x = a • A (a • x)`, hence `|A|² (a • x) = a⁻² |A|² x`;
* the **radial identities** at `x ∈ M`: the position vector is tangent (`⟪ν x, x⟫ = 0`), it is a
  null direction of `A` (`A x x = 0`), and `(δ_x A) z = -A z`;
* the **improved Kato inequality for cones** (`Simons.improved_kato`):
  `‖δ|A|²‖² + 8 |A|⁴ / |x|² ≤ 4 |A|² |∇_M A|²` at every nonzero point of `M`. The extra term comes
  from the radial direction: by the Codazzi equation the radial derivatives contribute `3 |A|²/|x|²`
  to `|∇_M A|²` but only `|A|²/|x|²` to `|δ|A||²`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

namespace Simons

variable {d : ℕ}

/-! ### 1. Dilated charts -/

section Dilation

variable {E U : Set (Space d)} {F : Space d → ℝ}

theorem hasFDerivAt_comp_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space d → G} {a : ℝ} {y : Space d} (hf : DifferentiableAt ℝ f (a • y)) :
    HasFDerivAt (fun z ↦ f (a • z)) (a • fderiv ℝ f (a • y)) y := by
  have h1 : HasFDerivAt (fun z : Space d ↦ a • z) (a • ContinuousLinearMap.id ℝ (Space d)) y :=
    (hasFDerivAt_id y).const_smul a
  have h2 : HasFDerivAt (fun z ↦ f (a • z))
      ((fderiv ℝ f (a • y)).comp (a • ContinuousLinearMap.id ℝ (Space d))) y :=
    hf.hasFDerivAt.comp y h1
  convert h2 using 1
  ext1 v
  simp

theorem gradient_comp_smul {f : Space d → ℝ} {a : ℝ} {y : Space d}
    (hf : DifferentiableAt ℝ f (a • y)) :
    gradient (fun z ↦ f (a • z)) y = a • gradient f (a • y) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, (hasFDerivAt_comp_smul hf).fderiv, real_inner_smul_left,
    inner_gradient_left]
  rfl

theorem chartNormal_comp_smul {f : Space d → ℝ} {a : ℝ} (ha : 0 < a) {y : Space d}
    (hf : DifferentiableAt ℝ f (a • y)) :
    chartNormal (fun z ↦ f (a • z)) y = chartNormal f (a • y) := by
  rw [chartNormal, chartNormal, gradient_comp_smul hf, norm_smul, Real.norm_of_nonneg ha.le,
    smul_smul, mul_inv, mul_assoc, mul_comm (‖gradient f (a • y)‖⁻¹) a, ← mul_assoc,
    inv_mul_cancel₀ ha.ne', one_mul]

/-- **Dilated charts.** If `E` is a.e. dilation invariant, then `y ↦ F (a • y)` is a smooth boundary
chart of `E` on `{y | a • y ∈ U}`. -/
theorem chart_dilate (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) {a : ℝ} (ha : 0 < a) :
    IsSmoothBoundaryChart E ((fun y ↦ a • y) ⁻¹' U) (fun y ↦ F (a • y)) where
  isOpen := h.isOpen.preimage (continuous_const_smul a)
  contDiffOn := h.contDiffOn.comp (contDiff_const_smul a).contDiffOn (fun _ hy ↦ hy)
  gradient_ne_zero y hy := by
    rw [gradient_comp_smul (h.hasFDerivAt hy).differentiableAt]
    exact smul_ne_zero ha.ne' (h.gradient_ne_zero _ hy)
  ae_mem_iff := by
    rw [ae_restrict_iff' (h.isOpen.preimage (continuous_const_smul a)).measurableSet]
    have h1 := (Measure.quasiMeasurePreserving_smul volume ha.ne').ae h.ae_mem_iff_of_mem
    filter_upwards [h1, hcone a ha] with y hy hyE hyU
    exact hyE.trans (hy hyU)

theorem chart_chartNormal_comp_smul (h : IsSmoothBoundaryChart E U F) {a : ℝ} (ha : 0 < a)
    {y : Space d} (hy : a • y ∈ U) :
    chartNormal (fun z ↦ F (a • z)) y = chartNormal F (a • y) :=
  chartNormal_comp_smul ha (h.hasFDerivAt hy).differentiableAt

theorem fderiv_chartNormal_comp_smul (h : IsSmoothBoundaryChart E U F) {a : ℝ} (ha : 0 < a)
    {y : Space d} (hy : a • y ∈ U) :
    fderiv ℝ (chartNormal (fun z ↦ F (a • z))) y = a • fderiv ℝ (chartNormal F) (a • y) := by
  have heq : chartNormal (fun z ↦ F (a • z)) =ᶠ[𝓝 y] fun z ↦ chartNormal F (a • z) := by
    filter_upwards [(h.isOpen.preimage (continuous_const_smul a)).mem_nhds hy] with z hz
    exact chart_chartNormal_comp_smul h ha hz
  rw [heq.fderiv_eq, (hasFDerivAt_comp_smul (h.differentiableAt_chartNormal hy)).fderiv]

theorem tangentialProj_comp_smul (h : IsSmoothBoundaryChart E U F) {a : ℝ} (ha : 0 < a)
    {y : Space d} (hy : a • y ∈ U) :
    tangentialProj (fun z ↦ F (a • z)) y = tangentialProj F (a • y) := by
  rw [tangentialProj, tangentialProj, chart_chartNormal_comp_smul h ha hy]

theorem secondFundamentalForm_comp_smul (h : IsSmoothBoundaryChart E U F) {a : ℝ} (ha : 0 < a)
    {y : Space d} (hy : a • y ∈ U) :
    secondFundamentalForm (fun z ↦ F (a • z)) y = a • secondFundamentalForm F (a • y) := by
  ext1 w
  simp only [secondFundamentalForm, ContinuousLinearMap.comp_apply, tangentialProj_comp_smul h ha hy,
    fderiv_chartNormal_comp_smul h ha hy, smul_apply, map_smul]

end Dilation

/-- Points `s • x` with `s` close to `1` stay in an open set containing `x`. -/
theorem eventually_smul_mem {V : Set (Space d)} (hV : IsOpen V) {x : Space d} (hx : x ∈ V) :
    ∀ᶠ s in 𝓝 (1 : ℝ), s • x ∈ V ∧ 0 < s := by
  have hc : Continuous (fun s : ℝ ↦ s • x) := continuous_id.smul continuous_const
  have h1 : Tendsto (fun s : ℝ ↦ s • x) (𝓝 1) (𝓝 x) := hc.tendsto' 1 x (one_smul ℝ x)
  exact (h1.eventually (hV.mem_nhds hx)).and (lt_mem_nhds one_pos)

theorem hasDerivAt_smul_one {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space d → G} {x : Space d} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun s : ℝ ↦ f (s • x)) (fderiv ℝ f x x) 1 := by
  have h1 : HasDerivAt (fun s : ℝ ↦ s • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) h1 (by simp)
  simpa [Function.comp_def] using h2

/-! ### 2. Homogeneity on the boundary piece of a cone -/

section Homogeneity

variable {E U : Set (Space d)} {F : Space d → ℝ}
  (h : IsSmoothBoundaryChart E U F)
  (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E)
include h hcone

theorem homog_eq_zero {a : ℝ} (ha : 0 < a) {x : Space d} (hxU : x ∈ U) (haxU : a • x ∈ U)
    (hx : F x = 0) : F (a • x) = 0 :=
  (chart_dilate h hcone ha).eq_zero_of_mem_measureTheoreticBoundary haxU
    (h.mem_measureTheoreticBoundary hxU hx)

theorem homog_chartNormal {a : ℝ} (ha : 0 < a) {x : Space d} (hxU : x ∈ U) (haxU : a • x ∈ U)
    (hx : F x = 0) : chartNormal F (a • x) = chartNormal F x := by
  rw [← chart_chartNormal_comp_smul h ha haxU]
  exact h.chartNormal_eq_of_mem_boundary (chart_dilate h hcone ha) hxU haxU
    (h.mem_measureTheoreticBoundary hxU hx)

theorem homog_secondFundamentalForm {a : ℝ} (ha : 0 < a) {x : Space d} (hxU : x ∈ U)
    (haxU : a • x ∈ U) (hx : F x = 0) :
    secondFundamentalForm F x = a • secondFundamentalForm F (a • x) := by
  rw [← h.secondFundamentalForm_eq_of_mem_boundary (chart_dilate h hcone ha) hxU haxU
    (h.mem_measureTheoreticBoundary hxU hx), secondFundamentalForm_comp_smul h ha haxU]

theorem homog_sqNormSecondFundamentalForm {a : ℝ} (ha : 0 < a) {x : Space d} (hxU : x ∈ U)
    (haxU : a • x ∈ U) (hx : F x = 0) :
    sqNormSecondFundamentalForm F x = a ^ 2 * sqNormSecondFundamentalForm F (a • x) := by
  rw [sqNormSecondFundamentalForm_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ),
    sqNormSecondFundamentalForm_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ),
    homog_secondFundamentalForm h hcone ha hxU haxU hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_apply, norm_smul, mul_pow, Real.norm_of_nonneg ha.le]

/-- **The position vector is tangent** at the points of `M`. -/
theorem fderiv_self_eq_zero {x : Space d} (hxU : x ∈ U) (hx : F x = 0) :
    fderiv ℝ F x x = 0 := by
  have hev : (fun s : ℝ ↦ F (s • x)) =ᶠ[𝓝 1] fun _ ↦ (0 : ℝ) := by
    filter_upwards [eventually_smul_mem h.isOpen hxU] with s hs
    exact homog_eq_zero h hcone hs.2 hxU hs.1 hx
  exact (hasDerivAt_smul_one (h.hasFDerivAt hxU).differentiableAt).unique
    ((hasDerivAt_const (1 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)

theorem inner_chartNormal_self_eq_zero {x : Space d} (hxU : x ∈ U) (hx : F x = 0) :
    inner ℝ (chartNormal F x) x = 0 := by
  rw [chartNormal, real_inner_smul_left, inner_gradient_left, fderiv_self_eq_zero h hcone hxU hx,
    mul_zero]

theorem tangentialProj_self {x : Space d} (hxU : x ∈ U) (hx : F x = 0) :
    tangentialProj F x x = x :=
  tangentialProj_eq_self_of_inner_eq_zero (inner_chartNormal_self_eq_zero h hcone hxU hx)

/-- The unit normal is constant along rays of `M`. -/
theorem fderiv_chartNormal_self {x : Space d} (hxU : x ∈ U) (hx : F x = 0) :
    fderiv ℝ (chartNormal F) x x = 0 := by
  have hev : (fun s : ℝ ↦ chartNormal F (s • x)) =ᶠ[𝓝 1] fun _ ↦ chartNormal F x := by
    filter_upwards [eventually_smul_mem h.isOpen hxU] with s hs
    exact homog_chartNormal h hcone hs.2 hxU hs.1 hx
  exact (hasDerivAt_smul_one (h.differentiableAt_chartNormal hxU)).unique
    ((hasDerivAt_const (1 : ℝ) (chartNormal F x)).congr_of_eventuallyEq hev)

/-- The radial direction is a null direction of the second fundamental form. -/
theorem secondFundamentalForm_self {x : Space d} (hxU : x ∈ U) (hx : F x = 0) :
    secondFundamentalForm F x x = 0 := by
  rw [h.secondFundamentalForm_apply hxU, tangentialProj_self h hcone hxU hx,
    fderiv_chartNormal_self h hcone hxU hx]

/-- The second fundamental form is homogeneous of degree `-1` along rays of `M`. -/
theorem fderiv_secondFundamentalForm_self {x : Space d} (hxU : x ∈ U) (hx : F x = 0)
    (z : Space d) :
    fderiv ℝ (fun y ↦ secondFundamentalForm F y z) x x = -secondFundamentalForm F x z := by
  have hev : (fun s : ℝ ↦ secondFundamentalForm F (s • x) z) =ᶠ[𝓝 1]
      fun s ↦ s⁻¹ • secondFundamentalForm F x z := by
    filter_upwards [eventually_smul_mem h.isOpen hxU] with s hs
    rw [homog_secondFundamentalForm h hcone hs.2 hxU hs.1 hx, smul_apply,
      smul_smul, inv_mul_cancel₀ hs.2.ne', one_smul]
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹ • secondFundamentalForm F x z)
      (-secondFundamentalForm F x z) 1 := by
    have := (hasDerivAt_inv (one_ne_zero (α := ℝ))).smul_const (secondFundamentalForm F x z)
    simpa using this
  exact (hasDerivAt_smul_one (h.differentiableAt_secondFundamentalForm_apply hxU z)).unique
    (hinv.congr_of_eventuallyEq hev)

theorem derivSecondFundamentalForm_self {x : Space d} (hxU : x ∈ U) (hx : F x = 0)
    (z : Space d) : derivSecondFundamentalForm F x x z = -secondFundamentalForm F x z := by
  rw [derivSecondFundamentalForm, tangentialProj_self h hcone hxU hx,
    fderiv_secondFundamentalForm_self h hcone hxU hx]

end Homogeneity


/-! ### 3. Splitting Hilbert-Schmidt sums along a unit vector -/

section Split

variable {ι : Type*} [Fintype ι]

theorem sum_inner_smul_self (b : OrthonormalBasis ι ℝ (Space d)) (e : Space d) :
    ∑ i, inner ℝ e (b i) • b i = e := by
  conv_rhs => rw [← b.sum_repr' e]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]

theorem sum_inner_sq_eq_one (b : OrthonormalBasis ι ℝ (Space d)) {e : Space d} (he : ‖e‖ = 1) :
    ∑ i, inner ℝ e (b i) ^ 2 = 1 := by
  calc ∑ i, inner ℝ e (b i) ^ 2 = ∑ i, inner ℝ (b i) e ^ 2 :=
        Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
    _ = ‖e‖ ^ 2 := (IsSmoothBoundaryChart.norm_sq_eq_sum_inner_sq b e).symm
    _ = 1 := by rw [he, one_pow]

/-- Splitting a Hilbert-Schmidt pairing along a unit vector `e`:
`∑ᵢ ⟪L bᵢ, M bᵢ⟫ = ⟪L e, M e⟫ + ∑ᵢ ⟪L (bᵢ - ⟪e, bᵢ⟫ e), M (bᵢ - ⟪e, bᵢ⟫ e)⟫`. -/
theorem sum_inner_split (b : OrthonormalBasis ι ℝ (Space d)) (L M : Space d →ₗ[ℝ] Space d)
    {e : Space d} (he : ‖e‖ = 1) :
    ∑ i, inner ℝ (L (b i)) (M (b i)) = inner ℝ (L e) (M e) +
      ∑ i, inner ℝ (L (b i - inner ℝ e (b i) • e)) (M (b i - inner ℝ e (b i) • e)) := by
  have hrepr := sum_inner_smul_self b e
  have hnorm := sum_inner_sq_eq_one b he
  have hL : L e = ∑ i, inner ℝ e (b i) • L (b i) := by
    conv_lhs => rw [← hrepr]
    rw [map_sum]
    simp only [map_smul]
  have hM : M e = ∑ i, inner ℝ e (b i) • M (b i) := by
    conv_lhs => rw [← hrepr]
    rw [map_sum]
    simp only [map_smul]
  have h1 : ∑ i, inner ℝ e (b i) * inner ℝ (L (b i)) (M e) = inner ℝ (L e) (M e) := by
    rw [hL, sum_inner]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_smul_left]
  have h2 : ∑ i, inner ℝ e (b i) * inner ℝ (L e) (M (b i)) = inner ℝ (L e) (M e) := by
    conv_rhs => rw [hM]
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_smul_right]
  have hexp : ∀ i, inner ℝ (L (b i - inner ℝ e (b i) • e)) (M (b i - inner ℝ e (b i) • e)) =
      inner ℝ (L (b i)) (M (b i)) - inner ℝ e (b i) * inner ℝ (L (b i)) (M e) -
        inner ℝ e (b i) * inner ℝ (L e) (M (b i)) +
          inner ℝ e (b i) ^ 2 * inner ℝ (L e) (M e) := by
    intro i
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hexp i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, h1, h2, ← Finset.sum_mul, hnorm]
  ring

/-- Splitting `‖u‖² = ∑ᵢ ⟪bᵢ, u⟫²` along a unit vector `e`. -/
theorem sum_inner_sq_split (b : OrthonormalBasis ι ℝ (Space d)) (u : Space d) {e : Space d}
    (he : ‖e‖ = 1) :
    ∑ i, inner ℝ (b i) u ^ 2 =
      inner ℝ e u ^ 2 + ∑ i, inner ℝ (b i - inner ℝ e (b i) • e) u ^ 2 := by
  have hrepr := sum_inner_smul_self b e
  have hnorm := sum_inner_sq_eq_one b he
  have h1 : ∑ i, inner ℝ e (b i) * inner ℝ (b i) u = inner ℝ e u := by
    conv_rhs => rw [← hrepr]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_smul_left]
  have hexp : ∀ i, inner ℝ (b i - inner ℝ e (b i) • e) u ^ 2 =
      inner ℝ (b i) u ^ 2 - 2 * inner ℝ e u * (inner ℝ e (b i) * inner ℝ (b i) u) +
        inner ℝ e (b i) ^ 2 * inner ℝ e u ^ 2 := by
    intro i
    rw [inner_sub_left, real_inner_smul_left]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hexp i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h1, ← Finset.sum_mul, hnorm]
  ring

end Split

/-! ### 4. The improved Kato inequality for cones -/

section Kato

variable {E U : Set (Space d)} {F : Space d → ℝ}

/-- The tangential gradient of `|A|²` in a direction `c`:
`⟪c, δ|A|²⟫ = 2 ∑ᵢ ⟪A bᵢ, P ((δ_c A)(P bᵢ))⟫`. -/
theorem inner_tangentialGradient_sqNorm (h : IsSmoothBoundaryChart E U F) {y : Space d}
    (hy : y ∈ U) (c : Space d) :
    inner ℝ c (tangentialGradient F (sqNormSecondFundamentalForm F) y) =
      2 * ∑ i, inner ℝ (secondFundamentalForm F y (EuclideanSpace.basisFun (Fin d) ℝ i))
        (tangentialProj F y (derivSecondFundamentalForm F y c
          (tangentialProj F y (EuclideanSpace.basisFun (Fin d) ℝ i)))) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hδn (i : Fin d) : ContDiffOn ℝ ∞
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) U :=
    h.contDiffOn_tangentialGradient_smooth (h.contDiffOn_inner_chartNormal (b i))
  have hdδn (i : Fin d) : DifferentiableAt ℝ
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y :=
    h.differentiableAt_of_contDiffOn hy (hδn i) (by simp)
  have hδ : tangentialGradient F (sqNormSecondFundamentalForm F) y =
      ∑ i, tangentialGradient F (fun x ↦ ‖tangentialGradient F
        (fun x ↦ inner ℝ (chartNormal F x) (b i)) x‖ ^ 2) y := by
    rw [(tangentialGradient_eventuallyEq F (h.sqNormSecondFundamentalForm_eventuallyEq hy)).eq_of_nhds,
      tangentialGradient_sum F _ fun i _ ↦ (hdδn i).norm_sq (𝕜 := ℝ)]
  rw [hδ, inner_sum, ← h.sum_inner_derivSecondFundamentalForm hy c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_tangentialGradient_norm_sq F (hdδn i), h.tangentialGradient_inner_chartNormal hy,
    h.derivSecondFundamentalForm_eq_tangentialHessian hy]
  rfl


/-- **Improved Kato inequality at a radial point.** Suppose the position vector `x` is tangent
(`⟪ν, x⟫ = 0`), is a null direction of `A` (`A x = 0`), and `A` is homogeneous of degree `-1`
along it (`(δ_x A) z = -A z`). Then `‖δ|A|²‖² + 8 |A|⁴ / |x|² ≤ 4 |A|² |∇_M A|²`. -/
theorem improved_kato (h : IsSmoothBoundaryChart E U F) {x : Space d} (hxU : x ∈ U)
    (hx0 : x ≠ 0) (hν : inner ℝ (chartNormal F x) x = 0)
    (hAx : secondFundamentalForm F x x = 0)
    (hD : ∀ z, derivSecondFundamentalForm F x x z = -secondFundamentalForm F x z) :
    ‖tangentialGradient F (sqNormSecondFundamentalForm F) x‖ ^ 2 +
        8 * sqNormSecondFundamentalForm F x ^ 2 / ‖x‖ ^ 2 ≤
      4 * sqNormSecondFundamentalForm F x * sqNormCovDerivSecondFundamentalForm F x := by
  have hne := h.gradient_ne_zero x hxU
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  set e : Space d := ‖x‖⁻¹ • x with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hrpos.ne']
  have hPe : tangentialProj F x e = e := by
    rw [he_def, map_smul, tangentialProj_eq_self_of_inner_eq_zero hν]
  have hνe : inner ℝ (chartNormal F x) e = 0 := by
    rw [he_def, real_inner_smul_right, hν, mul_zero]
  have hAe : secondFundamentalForm F x e = 0 := by rw [he_def, map_smul, hAx, smul_zero]
  have hAsym : ∀ u v, inner ℝ (secondFundamentalForm F x u) v =
      inner ℝ u (secondFundamentalForm F x v) := h.inner_secondFundamentalForm_comm hxU
  have hAe' : ∀ u, inner ℝ (secondFundamentalForm F x u) e = 0 := fun u ↦ by
    rw [hAsym, hAe, inner_zero_right]
  have hAP : ∀ u, secondFundamentalForm F x (tangentialProj F x u) =
      secondFundamentalForm F x u := h.secondFundamentalForm_tangentialProj hxU
  have hPA : ∀ u, tangentialProj F x (secondFundamentalForm F x u) =
      secondFundamentalForm F x u := fun u ↦
    tangentialProj_eq_self_of_inner_eq_zero (h.inner_chartNormal_secondFundamentalForm hxU u)
  have hPP : ∀ u, tangentialProj F x (tangentialProj F x u) = tangentialProj F x u :=
    tangentialProj_tangentialProj hne
  have hPsym : ∀ u v, inner ℝ (tangentialProj F x u) v = inner ℝ u (tangentialProj F x v) :=
    inner_tangentialProj_left F x
  have hDP : ∀ w z, derivSecondFundamentalForm F x (tangentialProj F x w) z =
      derivSecondFundamentalForm F x w z := by
    intro w z
    simp only [derivSecondFundamentalForm, hPP]
  have hDsmul : ∀ (c : ℝ) w z, derivSecondFundamentalForm F x (c • w) z =
      c • derivSecondFundamentalForm F x w z := by
    intro c w z
    simp only [derivSecondFundamentalForm, map_smul]
  have hDe : ∀ z, derivSecondFundamentalForm F x e z = -(‖x‖⁻¹ • secondFundamentalForm F x z) := by
    intro z
    rw [he_def, hDsmul, hD, smul_neg]
  have hTe : ∀ z, tangentialProj F x (derivSecondFundamentalForm F x e (tangentialProj F x z)) =
      -(‖x‖⁻¹ • secondFundamentalForm F x z) := by
    intro z
    rw [hDe, hAP, map_neg, map_smul, hPA]
  -- Codazzi: for tangent `w`, `P ((δ_w A) e) = P ((δ_e A) w)`
  have hcod : ∀ w, inner ℝ (chartNormal F x) w = 0 →
      tangentialProj F x (derivSecondFundamentalForm F x w e) =
        tangentialProj F x (derivSecondFundamentalForm F x e w) := by
    intro w hw
    apply ext_inner_left ℝ
    intro v
    rw [← hPsym, ← hPsym]
    have hu : inner ℝ (chartNormal F x) (tangentialProj F x v) = 0 :=
      inner_chartNormal_tangentialProj hne v
    calc inner ℝ (tangentialProj F x v) (derivSecondFundamentalForm F x w e)
        = inner ℝ e (derivSecondFundamentalForm F x w (tangentialProj F x v)) :=
          h.inner_derivSecondFundamentalForm_comm hxU w _ e
      _ = fderiv ℝ (fun y ↦ inner ℝ e (secondFundamentalForm F y (tangentialProj F x v))) x w := by
          rw [h.inner_derivSecondFundamentalForm hxU, tangentialProj_eq_self_of_inner_eq_zero hw]
      _ = fderiv ℝ (fun y ↦ inner ℝ w (secondFundamentalForm F y (tangentialProj F x v))) x e :=
          h.fderiv_inner_secondFundamentalForm_comm hxU hw hνe _
      _ = inner ℝ w (derivSecondFundamentalForm F x e (tangentialProj F x v)) := by
          rw [h.inner_derivSecondFundamentalForm hxU, hPe]
      _ = inner ℝ (tangentialProj F x v) (derivSecondFundamentalForm F x e w) :=
          h.inner_derivSecondFundamentalForm_comm hxU e w _
  -- the covariant Hilbert-Schmidt density and the gradient density in a direction `w`
  let Nf : Space d → ℝ := fun w ↦ ∑ i, ‖tangentialProj F x
    (derivSecondFundamentalForm F x w (tangentialProj F x (b i)))‖ ^ 2
  let gf : Space d → ℝ := fun w ↦ ∑ i, inner ℝ (secondFundamentalForm F x (b i))
    (tangentialProj F x (derivSecondFundamentalForm F x w (tangentialProj F x (b i))))
  set a2 := sqNormSecondFundamentalForm F x with ha2
  have ha2sum : ∑ i, ‖secondFundamentalForm F x (b i)‖ ^ 2 = a2 := by
    rw [ha2, sqNormSecondFundamentalForm_eq_sum b]
  have ha2nn : 0 ≤ a2 := sqNormSecondFundamentalForm_nonneg F x
  -- (K1) splitting `|∇_M A|²` along `e`
  have hK1 : sqNormCovDerivSecondFundamentalForm F x =
      Nf e + ∑ k, Nf (b k - inner ℝ e (b k) • e) := by
    have hsplit : ∀ i, ∑ k, ‖tangentialProj F x (derivSecondFundamentalForm F x (b k)
        (tangentialProj F x (b i)))‖ ^ 2 =
        ‖tangentialProj F x (derivSecondFundamentalForm F x e (tangentialProj F x (b i)))‖ ^ 2 +
        ∑ k, ‖tangentialProj F x (derivSecondFundamentalForm F x (b k - inner ℝ e (b k) • e)
          (tangentialProj F x (b i)))‖ ^ 2 := by
      intro i
      let L : Space d →L[ℝ] Space d := tangentialProj F x ∘L
        fderiv ℝ (fun y ↦ secondFundamentalForm F y (tangentialProj F x (b i))) x ∘L
          tangentialProj F x
      have := sum_inner_split b (L : Space d →ₗ[ℝ] Space d) (L : Space d →ₗ[ℝ] Space d) he
      simp only [ContinuousLinearMap.coe_coe, real_inner_self_eq_norm_sq] at this
      exact this
    rw [sqNormCovDerivSecondFundamentalForm, ← hb, Finset.sum_comm,
      Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib, Finset.sum_comm]
  -- (K2) splitting `‖δ|A|²‖²` along `e`
  have hgrad : ∀ c, inner ℝ c (tangentialGradient F (sqNormSecondFundamentalForm F) x) = 2 * gf c := by
    intro c
    rw [inner_tangentialGradient_sqNorm h hxU c, ← hb]
  have hK2 : ‖tangentialGradient F (sqNormSecondFundamentalForm F) x‖ ^ 2 =
      4 * gf e ^ 2 + 4 * ∑ k, gf (b k - inner ℝ e (b k) • e) ^ 2 := by
    rw [IsSmoothBoundaryChart.norm_sq_eq_sum_inner_sq b, sum_inner_sq_split b _ he, hgrad e]
    have hk : ∀ k, inner ℝ (b k - inner ℝ e (b k) • e)
        (tangentialGradient F (sqNormSecondFundamentalForm F) x) ^ 2 =
        4 * gf (b k - inner ℝ e (b k) • e) ^ 2 := fun k ↦ by
      rw [hgrad]
      ring
    rw [Finset.sum_congr rfl fun k _ ↦ hk k, ← Finset.mul_sum]
    ring
  -- (K3) the radial direction
  have hK3N : Nf e = ‖x‖⁻¹ ^ 2 * a2 := by
    show ∑ i, ‖tangentialProj F x (derivSecondFundamentalForm F x e (tangentialProj F x (b i)))‖ ^ 2
      = _
    rw [← ha2sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hTe, norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.mpr hrpos.le)]
  have hK3g : gf e = -(‖x‖⁻¹ * a2) := by
    show ∑ i, inner ℝ (secondFundamentalForm F x (b i))
      (tangentialProj F x (derivSecondFundamentalForm F x e (tangentialProj F x (b i)))) = _
    rw [← ha2sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hTe, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  -- (K5) `∑ₖ ‖A (bₖ - ⟪e, bₖ⟫ e)‖² = |A|²`
  have hK5 : ∑ k, ‖secondFundamentalForm F x (b k - inner ℝ e (b k) • e)‖ ^ 2 = a2 := by
    have := sum_inner_split b (secondFundamentalForm F x : Space d →ₗ[ℝ] Space d)
      (secondFundamentalForm F x : Space d →ₗ[ℝ] Space d) he
    simp only [ContinuousLinearMap.coe_coe, real_inner_self_eq_norm_sq, hAe, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at this
    rw [← this, ha2sum]
  -- (K4) the tangential directions orthogonal to `e`
  have hK4t : ∀ w, inner ℝ (chartNormal F x) w = 0 → inner ℝ e w = 0 →
      gf w ^ 2 + 2 * a2 * (‖x‖⁻¹ ^ 2 * ‖secondFundamentalForm F x w‖ ^ 2) ≤ a2 * Nf w := by
    intro w hw hew
    have hPw : tangentialProj F x w = w := tangentialProj_eq_self_of_inner_eq_zero hw
    have hadd : ∀ z₁ z₂, tangentialProj F x (derivSecondFundamentalForm F x w
        (tangentialProj F x (z₁ + z₂))) =
        tangentialProj F x (derivSecondFundamentalForm F x w (tangentialProj F x z₁)) +
          tangentialProj F x (derivSecondFundamentalForm F x w (tangentialProj F x z₂)) := by
      intro z₁ z₂
      rw [map_add, h.derivSecondFundamentalForm_add hxU, map_add]
    have hsm : ∀ (c : ℝ) z, tangentialProj F x (derivSecondFundamentalForm F x w
        (tangentialProj F x (c • z))) =
        c • tangentialProj F x (derivSecondFundamentalForm F x w (tangentialProj F x z)) := by
      intro c z
      rw [map_smul, h.derivSecondFundamentalForm_smul hxU, map_smul]
    let T : Space d →ₗ[ℝ] Space d :=
      { toFun := fun z ↦ tangentialProj F x (derivSecondFundamentalForm F x w (tangentialProj F x z))
        map_add' := hadd
        map_smul' := hsm }
    have hT : ∀ z, T z =
        tangentialProj F x (derivSecondFundamentalForm F x w (tangentialProj F x z)) := fun z ↦ rfl
    have hTe' : T e = -(‖x‖⁻¹ • secondFundamentalForm F x w) := by
      rw [hT, hPe, hcod w hw, ← hPw, hTe, hPw]
    have hTpe : ∀ z, inner ℝ e (T z) = -(‖x‖⁻¹ * inner ℝ z (secondFundamentalForm F x w)) := by
      intro z
      have h1 : inner ℝ e (T z) = inner ℝ z (T e) := by
        rw [hT, hT, ← hPsym, hPe, h.inner_derivSecondFundamentalForm_comm hxU w e _, hPsym]
      rw [h1, hTe', inner_neg_right, real_inner_smul_right]
    have hNw : Nf w = ‖T e‖ ^ 2 + ∑ i, ‖T (b i - inner ℝ e (b i) • e)‖ ^ 2 := by
      have := sum_inner_split b T T he
      simp only [real_inner_self_eq_norm_sq] at this
      exact this
    have hpyth : ∀ v : Space d, ‖v‖ ^ 2 = ‖v - inner ℝ e v • e‖ ^ 2 + inner ℝ e v ^ 2 := by
      intro v
      rw [norm_sub_sq_real, norm_smul, mul_pow, he, real_inner_smul_right, Real.norm_eq_abs, sq_abs,
        real_inner_comm e v]
      ring
    have hAwe : inner ℝ e (secondFundamentalForm F x w) = 0 := by
      rw [real_inner_comm, hAe' w]
    have hsumAw : ∑ i, inner ℝ (b i - inner ℝ e (b i) • e) (secondFundamentalForm F x w) ^ 2 =
        ‖secondFundamentalForm F x w‖ ^ 2 := by
      have h1 := sum_inner_sq_split b (secondFundamentalForm F x w) he
      rw [← IsSmoothBoundaryChart.norm_sq_eq_sum_inner_sq b, hAwe] at h1
      rw [h1]
      ring
    let R : Fin d → Space d := fun i ↦ T (b i - inner ℝ e (b i) • e) -
      inner ℝ e (T (b i - inner ℝ e (b i) • e)) • e
    have hNw' : Nf w = 2 * (‖x‖⁻¹ ^ 2 * ‖secondFundamentalForm F x w‖ ^ 2) +
        ∑ i, ‖R i‖ ^ 2 := by
      rw [hNw, hTe', norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.mpr hrpos.le)]
      have hsplit : ∀ i, ‖T (b i - inner ℝ e (b i) • e)‖ ^ 2 = ‖R i‖ ^ 2 +
          ‖x‖⁻¹ ^ 2 * inner ℝ (b i - inner ℝ e (b i) • e) (secondFundamentalForm F x w) ^ 2 := by
        intro i
        have h2 := hTpe (b i - inner ℝ e (b i) • e)
        rw [hpyth (T (b i - inner ℝ e (b i) • e)),
          show inner ℝ e (T (b i - inner ℝ e (b i) • e)) ^ 2 = ‖x‖⁻¹ ^ 2 *
            inner ℝ (b i - inner ℝ e (b i) • e) (secondFundamentalForm F x w) ^ 2 by
              rw [h2, neg_sq, mul_pow]]
      rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib, ← Finset.mul_sum,
        hsumAw]
      ring
    have hgw : gf w = ∑ i, inner ℝ (secondFundamentalForm F x (b i - inner ℝ e (b i) • e)) (R i) := by
      have := sum_inner_split b (secondFundamentalForm F x : Space d →ₗ[ℝ] Space d) T he
      simp only [ContinuousLinearMap.coe_coe, hAe, inner_zero_left, zero_add] at this
      rw [show gf w = ∑ i, inner ℝ (secondFundamentalForm F x (b i)) (T (b i)) from rfl, this]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [inner_sub_right, real_inner_smul_right, hAe', mul_zero, sub_zero]
    have hcs := sq_sum_inner_le Finset.univ
      (fun i ↦ secondFundamentalForm F x (b i - inner ℝ e (b i) • e)) R
    rw [hK5, ← hgw] at hcs
    have hexp : a2 * Nf w = 2 * a2 * (‖x‖⁻¹ ^ 2 * ‖secondFundamentalForm F x w‖ ^ 2) +
        a2 * ∑ i, ‖R i‖ ^ 2 := by
      rw [hNw']
      ring
    linarith
  have hK4 : ∀ k, gf (b k - inner ℝ e (b k) • e) ^ 2 + 2 * a2 * (‖x‖⁻¹ ^ 2 *
      ‖secondFundamentalForm F x (b k - inner ℝ e (b k) • e)‖ ^ 2) ≤
        a2 * Nf (b k - inner ℝ e (b k) • e) := by
    intro k
    have hew : inner ℝ e (b k - inner ℝ e (b k) • e) = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
      ring
    have h1 := hK4t (tangentialProj F x (b k - inner ℝ e (b k) • e))
      (inner_chartNormal_tangentialProj hne _) (by rw [← hPsym, hPe, hew])
    have hg : gf (tangentialProj F x (b k - inner ℝ e (b k) • e)) =
        gf (b k - inner ℝ e (b k) • e) := by
      simp only [gf, hDP]
    have hN : Nf (tangentialProj F x (b k - inner ℝ e (b k) • e)) =
        Nf (b k - inner ℝ e (b k) • e) := by
      simp only [Nf, hDP]
    rw [hg, hN, hAP] at h1
    exact h1
  have hsum4 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦ hK4 k
  rw [Finset.sum_add_distrib] at hsum4
  simp only [← Finset.mul_sum] at hsum4
  rw [hK5] at hsum4
  rw [hK2, hK1, hK3N, hK3g]
  have h8 : 8 * a2 ^ 2 / ‖x‖ ^ 2 = 8 * a2 * (‖x‖⁻¹ ^ 2 * a2) := by
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  rw [h8]
  nlinarith [hsum4]

/-- **Improved Kato inequality for cones** at a nonzero point of the boundary piece of a chart. -/
theorem improved_kato_of_cone (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) {x : Space d} (hxU : x ∈ U)
    (hx : F x = 0) (hx0 : x ≠ 0) :
    ‖tangentialGradient F (sqNormSecondFundamentalForm F) x‖ ^ 2 +
        8 * sqNormSecondFundamentalForm F x ^ 2 / ‖x‖ ^ 2 ≤
      4 * sqNormSecondFundamentalForm F x * sqNormCovDerivSecondFundamentalForm F x :=
  improved_kato h hxU hx0 (inner_chartNormal_self_eq_zero h hcone hxU hx)
    (secondFundamentalForm_self h hcone hxU hx) (derivSecondFundamentalForm_self h hcone hxU hx)

end Kato

end Simons

end SerrinEpigraph
