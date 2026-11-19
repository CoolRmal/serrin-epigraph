module

public import SerrinEpigraph.SimonsConeHomogeneity

/-!
# The stability inequality for the curvature of a minimizing cone

Let `T` be an a.e. dilation invariant perimeter minimizer with perimeter measure `μ` on an open
set `Ω`, and let `(T, V, F)` be a smooth boundary chart with `V ⊆ Ω` whose domain contains the part
of the boundary of `T` in the closed annulus `{a₀ ≤ |x| ≤ b₀}`, `a₀ > 0`. For every smooth radial
profile `φ` vanishing outside `(a₀, b₀)`,
`2 ∫_V |A|² φ(|x|)² / |x|² dμ ≤ ∫_V |A|² φ'(|x|)² dμ` (`Simons.integral_radial_le`).

The proof inserts `ζ = (|A|² + ε²)^{1/2} φ(|x|)` into the stability inequality (GR1), integrates by
parts on `M`, and uses the pointwise bound `c_ε Δ_M c_ε ≥ 2|A|²/|x|² - |A|⁴`
(`Simons.sqrt_mul_tangentialLaplacian_ge`), which combines Simons' identity with the improved
Kato inequality for cones; finally `ε → 0`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

namespace Simons

variable {d : ℕ}

/-! ### 1. A pointwise inequality from Simons' identity and the improved Kato inequality -/

section Pointwise

variable {E U : Set (Space d)} {F : Space d → ℝ}

theorem tangentialGradient_add_const (F f : Space d → ℝ) (c : ℝ) :
    tangentialGradient F (fun y ↦ f y + c) = tangentialGradient F f := by
  funext y
  simp only [tangentialGradient, gradient, fderiv_add_const]

theorem tangentialLaplacian_add_const (F f : Space d → ℝ) (c : ℝ) (y : Space d) :
    tangentialLaplacian F (fun y ↦ f y + c) y = tangentialLaplacian F f y := by
  rw [tangentialLaplacian, tangentialLaplacian, tangentialGradient_add_const]

theorem contDiffOn_sqrt_sqNorm (h : IsSmoothBoundaryChart E U F) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun y ↦ Real.sqrt (sqNormSecondFundamentalForm F y + ε ^ 2)) U :=
  (h.contDiffOn_sqNormSecondFundamentalForm.add contDiffOn_const).sqrt fun y _ ↦
    (add_pos_of_nonneg_of_pos (sqNormSecondFundamentalForm_nonneg F y) (pow_pos hε 2)).ne'

theorem sqNormCovDeriv_nonneg (F : Space d → ℝ) (y : Space d) :
    0 ≤ sqNormCovDerivSecondFundamentalForm F y :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- **Pointwise lower bound.** On a chart of a cone with vanishing mean curvature on `M`, the
function `c_ε = (|A|² + ε²)^{1/2}` satisfies `c_ε Δ_M c_ε ≥ 2 |A|² / |x|² - |A|⁴` at every nonzero
point of `M`. -/
theorem sqrt_mul_tangentialLaplacian_ge (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E)
    (hH : ∀ z ∈ U, F z = 0 → meanCurvature F z = 0) {x : Space d} (hxU : x ∈ U) (hx : F x = 0)
    (hx0 : x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    2 * sqNormSecondFundamentalForm F x / ‖x‖ ^ 2 - sqNormSecondFundamentalForm F x ^ 2 ≤
      Real.sqrt (sqNormSecondFundamentalForm F x + ε ^ 2) *
        tangentialLaplacian F (fun y ↦ Real.sqrt (sqNormSecondFundamentalForm F y + ε ^ 2)) x := by
  set c : Space d → ℝ := fun y ↦ Real.sqrt (sqNormSecondFundamentalForm F y + ε ^ 2) with hcdef
  have hc : ContDiffOn ℝ ∞ c U := contDiffOn_sqrt_sqNorm h hε
  have hc2 : ContDiffOn ℝ 2 c U := hc.of_le (by simp)
  have hcc : ∀ y, c y * c y = sqNormSecondFundamentalForm F y + ε ^ 2 := fun y ↦
    Real.mul_self_sqrt (add_nonneg (sqNormSecondFundamentalForm_nonneg F y) (sq_nonneg ε))
  have hfun : (fun y ↦ c y * c y) = fun y ↦ sqNormSecondFundamentalForm F y + ε ^ 2 := funext hcc
  have hlap := h.tangentialLaplacian_mul hxU hc2 hc2
  rw [hfun, tangentialLaplacian_add_const] at hlap
  have hsim := h.tangentialLaplacian_sqNormSecondFundamentalForm hH hxU hx
  have hdc : DifferentiableAt ℝ c x := h.differentiableAt_of_contDiffOn hxU hc (by simp)
  have hgrad := tangentialGradient_mul F hdc hdc
  rw [hfun, tangentialGradient_add_const] at hgrad
  have hkato := improved_kato_of_cone h hcone hxU hx hx0
  have hN := sqNormCovDeriv_nonneg F x
  have ha := sqNormSecondFundamentalForm_nonneg F x
  have hcx2 : c x ^ 2 = sqNormSecondFundamentalForm F x + ε ^ 2 := by rw [sq, hcc]
  have hgradsq : ‖tangentialGradient F (sqNormSecondFundamentalForm F) x‖ ^ 2 =
      4 * (sqNormSecondFundamentalForm F x + ε ^ 2) * ‖tangentialGradient F c x‖ ^ 2 := by
    rw [hgrad, ← two_smul ℝ (c x • tangentialGradient F c x), smul_smul, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, mul_pow, hcx2]
    ring
  have hr2 : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.mpr hx0
    positivity
  set a := sqNormSecondFundamentalForm F x with ha_def
  set N := sqNormCovDerivSecondFundamentalForm F x with hN_def
  set X := ‖tangentialGradient F c x‖ ^ 2 with hX_def
  set t := a / ‖x‖ ^ 2 with ht
  have h8 : 8 * a ^ 2 / ‖x‖ ^ 2 = 8 * a * t := by
    rw [ht]
    ring
  have hX : 0 ≤ X := sq_nonneg _
  have hk : (a + ε ^ 2) * X ≤ a * (N - 2 * t) := by
    rw [hgradsq, h8] at hkato
    nlinarith [hkato]
  have hD : 0 ≤ N - 2 * t := by
    rcases ha.lt_or_eq with hapos | ha0
    · by_contra hneg
      rw [not_le] at hneg
      have h1 : a * (N - 2 * t) < 0 := mul_neg_of_pos_of_neg hapos hneg
      have h2 : 0 ≤ (a + ε ^ 2) * X := mul_nonneg (by positivity) hX
      linarith
    · have ht0 : t = 0 := by rw [ht, ← ha0, zero_div]
      rw [ht0]
      linarith
  have hXD : X ≤ N - 2 * t := by
    have hpos : 0 < a + ε ^ 2 := by positivity
    have h1 : (a + ε ^ 2) * X ≤ (a + ε ^ 2) * (N - 2 * t) :=
      hk.trans (mul_le_mul_of_nonneg_right (by linarith [pow_pos hε 2]) hD)
    exact le_of_mul_le_mul_left h1 hpos
  have hcl : c x * tangentialLaplacian F c x =
      tangentialLaplacian F (sqNormSecondFundamentalForm F) x / 2 - X := by
    rw [real_inner_self_eq_norm_sq] at hlap
    linarith
  rw [hcl, hsim]
  have h2t : 2 * a / ‖x‖ ^ 2 = 2 * t := by
    rw [ht]
    ring
  rw [h2t]
  linarith

end Pointwise

/-! ### 2. Cut-offs and radial functions -/

section Radial

/-- A radial function with profile vanishing near `0` is smooth. -/
theorem contDiff_comp_norm_of_eq_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hφ0 : ∀ r, r < a₀ → φ r = 0) : ContDiff ℝ ∞ (fun x : Space d ↦ φ ‖x‖) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  by_cases hx : x = 0
  · subst hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : Space d) ha₀] with y hy
    rw [mem_ball, dist_zero_right] at hy
    exact hφ0 _ hy
  · exact hφ.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-- The gradient of a radial function is bounded by the derivative of its profile. -/
theorem norm_gradient_comp_norm_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hφ0 : ∀ r, r < a₀ → φ r = 0) (x : Space d) :
    ‖gradient (fun y : Space d ↦ φ ‖y‖) x‖ ≤ |deriv φ ‖x‖| := by
  by_cases hx : x = 0
  · subst hx
    have hev : (fun y : Space d ↦ φ ‖y‖) =ᶠ[𝓝 0] fun _ ↦ 0 := by
      filter_upwards [ball_mem_nhds (0 : Space d) ha₀] with y hy
      rw [mem_ball, dist_zero_right] at hy
      exact hφ0 _ hy
    rw [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero, norm_zero]
    exact abs_nonneg _
  · have hn : HasFDerivAt (fun y : Space d ↦ ‖y‖) (fderiv ℝ (fun y : Space d ↦ ‖y‖) x) x :=
      ((contDiffAt_norm ℝ (n := 1) hx).differentiableAt one_ne_zero).hasFDerivAt
    have hdφ : DifferentiableAt ℝ φ ‖x‖ := hφ.contDiffAt.differentiableAt (by simp)
    have hd := hdφ.hasDerivAt.comp_hasFDerivAt x hn
    rw [gradient, LinearIsometryEquiv.norm_map, show (fun y : Space d ↦ φ ‖y‖) =
      φ ∘ fun y : Space d ↦ ‖y‖ from rfl, hd.fderiv, norm_smul, Real.norm_eq_abs]
    have h1 : ‖fderiv ℝ (fun y : Space d ↦ ‖y‖) x‖ ≤ 1 := by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (lipschitzWith_one_norm (E := Space d))
      simpa using this
    calc |deriv φ ‖x‖| * ‖fderiv ℝ (fun y : Space d ↦ ‖y‖) x‖ ≤ |deriv φ ‖x‖| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |deriv φ ‖x‖| := mul_one _

/-- `φ(|x|)² / |x|²` is continuous when `φ` vanishes near `0`. -/
theorem continuous_sq_div_norm_sq {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hφ0 : ∀ r, r < a₀ → φ r = 0) : Continuous (fun x : Space d ↦ φ ‖x‖ ^ 2 / ‖x‖ ^ 2) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : x = 0
  · subst hx
    apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [ball_mem_nhds (0 : Space d) ha₀] with y hy
    rw [mem_ball, dist_zero_right] at hy
    simp [hφ0 _ hy]
  · exact ((hφ.continuous.comp continuous_norm).pow 2).continuousAt.div
      (continuous_norm.pow 2).continuousAt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

end Radial

/-! ### 3. Integrability on a chart -/

/-- A function continuous on the chart domain which vanishes `μ`-a.e. outside a compact subset of
the domain is integrable. -/
theorem integrable_of_ae_mem_or_eq_zero {V S : Set (Space d)} {μ : Measure (Space d)}
    [IsFiniteMeasure (μ.restrict V)] {g : Space d → ℝ} (hV : IsOpen V) (hg : ContinuousOn g V)
    (hS : IsCompact S) (hSV : S ⊆ V) (hzero : ∀ᵐ x ∂μ.restrict V, x ∈ S ∨ g x = 0) :
    Integrable g (μ.restrict V) := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hg.mono hSV)
  refine Integrable.of_bound (hg.aestronglyMeasurable hV.measurableSet) (max C 0) ?_
  filter_upwards [hzero] with x hx
  rcases hx with hx | hx
  · exact (hC x hx).trans (le_max_left _ _)
  · simp [hx]


/-! ### 4. The integral inequality -/

section Integral

variable {T V Ω : Set (Space d)} {F : Space d → ℝ} {μ : Measure (Space d)}
  {ν : Space d → Space d}

/-- **Stability inequality for the curvature of a minimizing cone.** For a smooth radial profile
`φ` vanishing outside `(a₀, b₀)` and a chart containing the boundary in the annulus
`a₀ ≤ |x| ≤ b₀`: `2 ∫_V |A|² φ(|x|)²/|x|² dμ ≤ ∫_V |A|² φ'(|x|)² dμ`. -/
theorem integral_radial_le (hT : MeasurableSet T)
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ T ↔ a • x ∈ T)
    (hp : IsPerimeterPolarOn (EuclideanSpace.basisFun (Fin d) ℝ) T Ω μ ν)
    (hmin : IsPerimeterMinimizingIn (EuclideanSpace.basisFun (Fin d) ℝ) T Ω)
    (h : IsSmoothBoundaryChart T V F) (hVΩ : V ⊆ Ω)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hφ0 : ∀ r, r < a₀ ∨ b₀ < r → φ r = 0)
    (hK : measureTheoreticBoundary T ∩ {x | a₀ ≤ ‖x‖ ∧ ‖x‖ ≤ b₀} ⊆ V) :
    Integrable (fun x ↦ sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2)) (μ.restrict V) ∧
    Integrable (fun x ↦ sqNormSecondFundamentalForm F x * deriv φ ‖x‖ ^ 2) (μ.restrict V) ∧
    2 * ∫ x in V, sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2) ∂μ ≤
      ∫ x in V, sqNormSecondFundamentalForm F x * deriv φ ‖x‖ ^ 2 ∂μ := by
  have hfin : IsFiniteMeasure (μ.restrict V) :=
    IsSmoothBoundaryChart.isFiniteMeasure_restrict hp hVΩ
  have hKc : IsCompact (measureTheoreticBoundary T ∩ {x : Space d | a₀ ≤ ‖x‖ ∧ ‖x‖ ≤ b₀}) := by
    refine (isCompact_closedBall (0 : Space d) b₀).of_isClosed_subset ?_ ?_
    · exact (isClosed_measureTheoreticBoundary T).inter
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const))
    · intro x hx
      rw [mem_closedBall, dist_zero_right]
      exact hx.2.2
  obtain ⟨η, hη, -, hη1, hηV, hηc⟩ := exists_contDiff_eventually_one_tsupport_subset hKc h.isOpen hK
  have hSc : IsCompact (tsupport η) := hηc
  have hφlow : ∀ r, r < a₀ → φ r = 0 := fun r hr ↦ hφ0 r (Or.inl hr)
  have hφloc : ∀ r, r < a₀ ∨ b₀ < r → φ =ᶠ[𝓝 r] fun _ ↦ 0 := by
    intro r hr
    rcases hr with hr | hr
    · filter_upwards [Iio_mem_nhds hr] with s hs
      exact hφ0 s (Or.inl hs)
    · filter_upwards [Ioi_mem_nhds hr] with s hs
      exact hφ0 s (Or.inr hs)
  have hdφ0 : ∀ r, r < a₀ ∨ b₀ < r → deriv φ r = 0 := fun r hr ↦ by
    rw [(hφloc r hr).deriv_eq, deriv_const]
  set Φ : Space d → ℝ := fun x ↦ φ ‖x‖ with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_comp_norm_of_eq_zero hφ ha₀ hφlow
  have hH : ∀ z ∈ V, F z = 0 → meanCurvature F z = 0 := fun z hz hFz ↦
    h.meanCurvature_eq_zero hT hp hmin hVΩ hz hFz
  have hgood : ∀ᵐ x ∂μ.restrict V, x ∈ V ∧ F x = 0 ∧
      (η =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) ∨ (Φ =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) ∧ deriv φ ‖x‖ = 0)) := by
    filter_upwards [ae_restrict_mem h.isOpen.measurableSet, h.ae_restrict_eq_zero hp hVΩ]
      with x hxV hFx
    refine ⟨hxV, hFx, ?_⟩
    by_cases hr : a₀ ≤ ‖x‖ ∧ ‖x‖ ≤ b₀
    · exact Or.inl (hη1 x ⟨h.mem_measureTheoreticBoundary hxV hFx, hr⟩)
    · have hr' : ‖x‖ < a₀ ∨ b₀ < ‖x‖ := by
        by_contra hc
        rw [not_or, not_lt, not_lt] at hc
        exact hr hc
      exact Or.inr ⟨(continuous_norm.continuousAt (x := x)).eventually (hφloc _ hr'),
        hdφ0 _ hr'⟩
  -- membership in the compact support of `η` or vanishing
  have hmemS : ∀ x, η x = 1 → x ∈ tsupport η := fun x hx ↦
    subset_tsupport _ (by rw [Function.mem_support, hx]; exact one_ne_zero)
  have hcontA : ContinuousOn (sqNormSecondFundamentalForm F) V :=
    h.contDiffOn_sqNormSecondFundamentalForm.continuousOn
  have hcontq : Continuous (fun x : Space d ↦ φ ‖x‖ ^ 2 / ‖x‖ ^ 2) :=
    continuous_sq_div_norm_sq hφ ha₀ hφlow
  have hcontdφ : Continuous (fun x : Space d ↦ deriv φ ‖x‖) :=
    (hφ.continuous_deriv (by simp)).comp continuous_norm
  have hcontδΦ : ContinuousOn (tangentialGradient F Φ) V :=
    h.continuousOn_tangentialGradient (hΦ.of_le (by simp))
  -- integrability of the final integrands
  have hintG : Integrable (fun x ↦ sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2))
      (μ.restrict V) := by
    refine integrable_of_ae_mem_or_eq_zero h.isOpen (hcontA.mul hcontq.continuousOn) hSc hηV ?_
    filter_upwards [hgood] with x hx
    rcases hx.2.2 with h1 | h1
    · exact Or.inl (hmemS x h1.eq_of_nhds)
    · right
      simp only [show φ ‖x‖ = 0 from h1.1.eq_of_nhds]
      ring
  have hintH : Integrable (fun x ↦ sqNormSecondFundamentalForm F x * deriv φ ‖x‖ ^ 2)
      (μ.restrict V) := by
    refine integrable_of_ae_mem_or_eq_zero h.isOpen (hcontA.mul (hcontdφ.pow 2).continuousOn)
      hSc hηV ?_
    filter_upwards [hgood] with x hx
    rcases hx.2.2 with h1 | h1
    · exact Or.inl (hmemS x h1.eq_of_nhds)
    · right
      rw [h1.2]
      ring
  have hintJ : Integrable (fun x : Space d ↦ deriv φ ‖x‖ ^ 2) (μ.restrict V) := by
    refine integrable_of_ae_mem_or_eq_zero h.isOpen (hcontdφ.pow 2).continuousOn hSc hηV ?_
    filter_upwards [hgood] with x hx
    rcases hx.2.2 with h1 | h1
    · exact Or.inl (hmemS x h1.eq_of_nhds)
    · right
      rw [h1.2]
      ring
  have hkey : ∀ ε : ℝ, 0 < ε →
      2 * ∫ x in V, sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2) ∂μ ≤
        ∫ x in V, sqNormSecondFundamentalForm F x * deriv φ ‖x‖ ^ 2 ∂μ +
          ε ^ 2 * ∫ x in V, deriv φ ‖x‖ ^ 2 ∂μ := by
    intro ε hε
    set c : Space d → ℝ := fun y ↦ Real.sqrt (sqNormSecondFundamentalForm F y + ε ^ 2) with hcdef
    have hc : ContDiffOn ℝ ∞ c V := contDiffOn_sqrt_sqNorm h hε
    have hcc : ∀ y, c y ^ 2 = sqNormSecondFundamentalForm F y + ε ^ 2 := fun y ↦
      Real.sq_sqrt (add_nonneg (sqNormSecondFundamentalForm_nonneg F y) (sq_nonneg ε))
    have hηΦ : ContDiff ℝ ∞ (fun y ↦ η y * Φ y) := hη.mul hΦ
    have hηΦ2 : ContDiff ℝ ∞ (fun y ↦ η y * Φ y ^ 2) := hη.mul (hΦ.pow 2)
    have hts1 : tsupport (fun y ↦ η y * Φ y) ⊆ V := tsupport_mul_subset_left.trans hηV
    have hts2 : tsupport (fun y ↦ η y * Φ y ^ 2) ⊆ V := tsupport_mul_subset_left.trans hηV
    set ζ : Space d → ℝ := fun y ↦ (η y * Φ y) • c y with hζdef
    set f : Space d → ℝ := fun y ↦ (η y * Φ y ^ 2) • c y with hfdef
    have hζ : ContDiff ℝ ∞ ζ :=
      contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen hc hηΦ hts1
    have hf : ContDiff ℝ ∞ f :=
      contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen hc hηΦ2 hts2
    have hηΦc : HasCompactSupport (fun y ↦ η y * Φ y) := hηc.mul_right
    have hηΦ2c : HasCompactSupport (fun y ↦ η y * Φ y ^ 2) := hηc.mul_right
    have hζc : HasCompactSupport ζ := hasCompactSupport_smul_left' hηΦc c
    have hfc : HasCompactSupport f := hasCompactSupport_smul_left' hηΦ2c c
    have hζV : tsupport ζ ⊆ V := (tsupport_smul_subset_left' _ c).trans hts1
    have hfV : tsupport f ⊆ V := (tsupport_smul_subset_left' _ c).trans hts2
    have hstab := h.stability_inequality hT hp hmin hVΩ (hζ.of_le (by simp)) hζc hζV
    have hibp := h.integral_inner_tangentialGradient_eq_neg hT hp hmin hVΩ (hf.of_le (by simp))
      hfc hfV (hc.of_le (by simp))
    have hpt : ∀ᵐ x ∂μ.restrict V,
        ζ x ^ 2 * sqNormSecondFundamentalForm F x =
          (sqNormSecondFundamentalForm F x + ε ^ 2) * Φ x ^ 2 * sqNormSecondFundamentalForm F x ∧
        ‖tangentialGradient F ζ x‖ ^ 2 =
          inner ℝ (tangentialGradient F f x) (tangentialGradient F c x) +
            (sqNormSecondFundamentalForm F x + ε ^ 2) * ‖tangentialGradient F Φ x‖ ^ 2 ∧
        Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x / ‖x‖ ^ 2 -
            sqNormSecondFundamentalForm F x ^ 2) ≤ f x * tangentialLaplacian F c x ∧
        ‖tangentialGradient F Φ x‖ ^ 2 ≤ deriv φ ‖x‖ ^ 2 ∧
        (x ∈ tsupport η ∨ (Φ x = 0 ∧ tangentialGradient F Φ x = 0 ∧
          tangentialGradient F f x = 0 ∧ f x = 0)) := by
      filter_upwards [hgood] with x hx
      obtain ⟨hxV, hFx, hgerm⟩ := hx
      have hne := h.gradient_ne_zero x hxV
      have hg1 : (fun y ↦ η y * Φ y) =ᶠ[𝓝 x] Φ := by
        rcases hgerm with h1 | h1
        · filter_upwards [h1] with y hy
          rw [hy, one_mul]
        · filter_upwards [h1.1] with y hy
          rw [hy, mul_zero]
      have hg2 : (fun y ↦ η y * Φ y ^ 2) =ᶠ[𝓝 x] fun y ↦ Φ y ^ 2 := by
        rcases hgerm with h1 | h1
        · filter_upwards [h1] with y hy
          rw [hy, one_mul]
        · filter_upwards [h1.1] with y hy
          rw [hy]
          ring
      have hζg : ζ =ᶠ[𝓝 x] fun y ↦ Φ y * c y := by
        filter_upwards [hg1] with y hy
        show (η y * Φ y) • c y = Φ y * c y
        rw [smul_eq_mul, hy]
      have hfg : f =ᶠ[𝓝 x] fun y ↦ Φ y ^ 2 * c y := by
        filter_upwards [hg2] with y hy
        show (η y * Φ y ^ 2) • c y = Φ y ^ 2 * c y
        rw [smul_eq_mul, hy]
      have hdc : DifferentiableAt ℝ c x := h.differentiableAt_of_contDiffOn hxV hc (by simp)
      have hdΦ : DifferentiableAt ℝ Φ x := hΦ.contDiffAt.differentiableAt (by simp)
      have hdΦ2 : DifferentiableAt ℝ (fun y ↦ Φ y ^ 2) x := hdΦ.pow 2
      have hδζ : tangentialGradient F ζ x =
          Φ x • tangentialGradient F c x + c x • tangentialGradient F Φ x := by
        rw [(tangentialGradient_eventuallyEq F hζg).eq_of_nhds, tangentialGradient_mul F hdΦ hdc]
      have hδΦ2 : tangentialGradient F (fun y ↦ Φ y ^ 2) x =
          (2 * Φ x) • tangentialGradient F Φ x := by
        have hsq : (fun y ↦ Φ y ^ 2) = fun y ↦ Φ y * Φ y := funext fun y ↦ sq (Φ y)
        rw [hsq, tangentialGradient_mul F hdΦ hdΦ, ← add_smul, two_mul]
      have hδf : tangentialGradient F f x = Φ x ^ 2 • tangentialGradient F c x +
          c x • ((2 * Φ x) • tangentialGradient F Φ x) := by
        rw [(tangentialGradient_eventuallyEq F hfg).eq_of_nhds,
          tangentialGradient_mul F hdΦ2 hdc, hδΦ2]
      have hζx : ζ x = Φ x * c x := hζg.eq_of_nhds
      have hfx : f x = Φ x ^ 2 * c x := hfg.eq_of_nhds
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hζx, mul_pow, hcc]
        ring
      · rw [hδζ, hδf, ← hcc x, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          real_inner_comm (tangentialGradient F c x) (tangentialGradient F Φ x)]
        ring
      · rw [hfx]
        by_cases hΦx : Φ x = 0
        · rw [hΦx]
          simp
        · have hx0 : x ≠ 0 := by
            intro hx0
            apply hΦx
            rw [hΦdef]
            dsimp only
            rw [hx0, norm_zero]
            exact hφlow 0 ha₀
          have hlow := sqrt_mul_tangentialLaplacian_ge h hcone hH hxV hFx hx0 hε
          calc Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x / ‖x‖ ^ 2 -
                sqNormSecondFundamentalForm F x ^ 2)
              ≤ Φ x ^ 2 * (c x * tangentialLaplacian F c x) :=
                mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
            _ = Φ x ^ 2 * c x * tangentialLaplacian F c x := by ring
      · have h1 : ‖tangentialGradient F Φ x‖ ≤ |deriv φ ‖x‖| :=
          (norm_tangentialProj_le hne _).trans (norm_gradient_comp_norm_le hφ ha₀ hφlow x)
        calc ‖tangentialGradient F Φ x‖ ^ 2 ≤ |deriv φ ‖x‖| ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = deriv φ ‖x‖ ^ 2 := sq_abs _
      · rcases hgerm with h1 | h1
        · exact Or.inl (hmemS x h1.eq_of_nhds)
        · right
          have hf0 : f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
            filter_upwards [hfg, h1.1] with y hy hy'
            rw [hy, hy']
            ring
          have hδ0 : ∀ g : Space d → ℝ, g =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) →
              tangentialGradient F g x = 0 := fun g hg ↦ by
            rw [(tangentialGradient_eventuallyEq F hg).eq_of_nhds]
            simp [tangentialGradient, gradient]
          exact ⟨h1.1.eq_of_nhds, hδ0 Φ h1.1, hδ0 f hf0, hf0.eq_of_nhds⟩
    -- continuity and integrability
    have hcontδc : ContinuousOn (tangentialGradient F c) V :=
      (h.contDiffOn_tangentialGradient (n := 0) (hc.of_le (by simp))).continuousOn
    have hcontδf : ContinuousOn (tangentialGradient F f) V :=
      h.continuousOn_tangentialGradient (hf.of_le (by simp))
    have hcontΔc : ContinuousOn (tangentialLaplacian F c) V :=
      (h.contDiffOn_tangentialLaplacian hc).continuousOn
    have hcontΦ : Continuous Φ := hΦ.continuous
    have hintA : Integrable (fun x ↦ (sqNormSecondFundamentalForm F x + ε ^ 2) * Φ x ^ 2 *
        sqNormSecondFundamentalForm F x) (μ.restrict V) := by
      refine integrable_of_ae_mem_or_eq_zero h.isOpen
        (((hcontA.add continuousOn_const).mul (hcontΦ.pow 2).continuousOn).mul hcontA) hSc hηV ?_
      filter_upwards [hpt] with x hx
      rcases hx.2.2.2.2 with h1 | h1
      · exact Or.inl h1
      · right
        rw [h1.1]
        ring
    have hBeq : (fun x ↦ Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x / ‖x‖ ^ 2 -
        sqNormSecondFundamentalForm F x ^ 2)) = fun x ↦
          2 * sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2) -
            Φ x ^ 2 * sqNormSecondFundamentalForm F x ^ 2 := by
      funext x
      rw [hΦdef]
      ring
    have hintB : Integrable (fun x ↦ Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x / ‖x‖ ^ 2 -
        sqNormSecondFundamentalForm F x ^ 2)) (μ.restrict V) := by
      rw [hBeq]
      refine integrable_of_ae_mem_or_eq_zero h.isOpen
        (((continuousOn_const.mul hcontA).mul hcontq.continuousOn).sub
          ((hcontΦ.pow 2).continuousOn.mul (hcontA.pow 2))) hSc hηV ?_
      filter_upwards [hpt] with x hx
      rcases hx.2.2.2.2 with h1 | h1
      · exact Or.inl h1
      · right
        have h0 : φ ‖x‖ = 0 := h1.1
        rw [show Φ x = φ ‖x‖ from rfl, h0]
        ring
    have hintC : Integrable (fun x ↦ inner ℝ (tangentialGradient F f x)
        (tangentialGradient F c x)) (μ.restrict V) := by
      refine integrable_of_ae_mem_or_eq_zero h.isOpen (hcontδf.inner hcontδc) hSc hηV ?_
      filter_upwards [hpt] with x hx
      rcases hx.2.2.2.2 with h1 | h1
      · exact Or.inl h1
      · right
        rw [h1.2.2.1, inner_zero_left]
    have hintD : Integrable (fun x ↦ (sqNormSecondFundamentalForm F x + ε ^ 2) *
        ‖tangentialGradient F Φ x‖ ^ 2) (μ.restrict V) := by
      refine integrable_of_ae_mem_or_eq_zero h.isOpen
        ((hcontA.add continuousOn_const).mul (hcontδΦ.norm.pow 2)) hSc hηV ?_
      filter_upwards [hpt] with x hx
      rcases hx.2.2.2.2 with h1 | h1
      · exact Or.inl h1
      · right
        rw [h1.2.1, norm_zero]
        ring
    have hintE : Integrable (fun x ↦ f x * tangentialLaplacian F c x) (μ.restrict V) := by
      refine integrable_of_ae_mem_or_eq_zero h.isOpen (hf.continuous.continuousOn.mul hcontΔc)
        hSc hηV ?_
      filter_upwards [hpt] with x hx
      rcases hx.2.2.2.2 with h1 | h1
      · exact Or.inl h1
      · right
        rw [h1.2.2.2, zero_mul]
    have hintF : Integrable (fun x ↦ (sqNormSecondFundamentalForm F x + ε ^ 2) *
        deriv φ ‖x‖ ^ 2) (μ.restrict V) := by
      have := hintH.add (hintJ.const_mul (ε ^ 2))
      refine this.congr (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.add_apply]
      ring
    -- combine
    have h1 : ∫ x in V, ζ x ^ 2 * sqNormSecondFundamentalForm F x ∂μ =
        ∫ x in V, (sqNormSecondFundamentalForm F x + ε ^ 2) * Φ x ^ 2 *
          sqNormSecondFundamentalForm F x ∂μ :=
      integral_congr_ae (hpt.mono fun x hx ↦ hx.1)
    have h2 : ∫ x in V, ‖tangentialGradient F ζ x‖ ^ 2 ∂μ =
        (∫ x in V, inner ℝ (tangentialGradient F f x) (tangentialGradient F c x) ∂μ) +
          ∫ x in V, (sqNormSecondFundamentalForm F x + ε ^ 2) *
            ‖tangentialGradient F Φ x‖ ^ 2 ∂μ := by
      rw [← integral_add hintC hintD]
      exact integral_congr_ae (hpt.mono fun x hx ↦ hx.2.1)
    have h3 : ∫ x in V, Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x / ‖x‖ ^ 2 -
        sqNormSecondFundamentalForm F x ^ 2) ∂μ ≤
          ∫ x in V, f x * tangentialLaplacian F c x ∂μ :=
      integral_mono_ae hintB hintE (hpt.mono fun x hx ↦ hx.2.2.1)
    have h4 : ∫ x in V, (sqNormSecondFundamentalForm F x + ε ^ 2) *
        ‖tangentialGradient F Φ x‖ ^ 2 ∂μ ≤
          ∫ x in V, (sqNormSecondFundamentalForm F x + ε ^ 2) * deriv φ ‖x‖ ^ 2 ∂μ :=
      integral_mono_ae hintD hintF (hpt.mono fun x hx ↦ mul_le_mul_of_nonneg_left hx.2.2.2.1
        (add_nonneg (sqNormSecondFundamentalForm_nonneg F x) (sq_nonneg ε)))
    have h5 : ∫ x in V, 2 * (sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2)) ∂μ ≤
        ∫ x in V, ((sqNormSecondFundamentalForm F x + ε ^ 2) * Φ x ^ 2 *
          sqNormSecondFundamentalForm F x + Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x /
            ‖x‖ ^ 2 - sqNormSecondFundamentalForm F x ^ 2)) ∂μ := by
      refine integral_mono (hintG.const_mul 2) (hintA.add hintB) fun x ↦ ?_
      have ha := sqNormSecondFundamentalForm_nonneg F x
      have hq : 0 ≤ ε ^ 2 * Φ x ^ 2 * sqNormSecondFundamentalForm F x := by positivity
      have heq : (sqNormSecondFundamentalForm F x + ε ^ 2) * Φ x ^ 2 *
          sqNormSecondFundamentalForm F x + Φ x ^ 2 * (2 * sqNormSecondFundamentalForm F x /
            ‖x‖ ^ 2 - sqNormSecondFundamentalForm F x ^ 2) =
          2 * (sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2)) +
            ε ^ 2 * Φ x ^ 2 * sqNormSecondFundamentalForm F x := by
        rw [hΦdef]
        ring
      rw [heq]
      linarith
    have h6 : ∫ x in V, (sqNormSecondFundamentalForm F x + ε ^ 2) * deriv φ ‖x‖ ^ 2 ∂μ =
        ∫ x in V, sqNormSecondFundamentalForm F x * deriv φ ‖x‖ ^ 2 ∂μ +
          ε ^ 2 * ∫ x in V, deriv φ ‖x‖ ^ 2 ∂μ := by
      rw [← integral_const_mul, ← integral_add hintH (hintJ.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      ring
    rw [integral_add hintA hintB] at h5
    rw [integral_const_mul] at h5
    linarith
  -- `ε → 0`
  refine ⟨hintG, hintH, ?_⟩
  have hJnn : 0 ≤ ∫ x in V, deriv φ ‖x‖ ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set J := ∫ x in V, deriv φ ‖x‖ ^ 2 ∂μ
  have hε : 0 < Real.sqrt (δ / (J + 1)) := Real.sqrt_pos.mpr (div_pos hδ (by linarith))
  have h1 := hkey _ hε
  rw [Real.sq_sqrt (div_pos hδ (by linarith)).le] at h1
  have h2 : δ / (J + 1) * J ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith


/-- The stability inequality for a minimizing cone in the form `∫_V |A|² (2 φ²/|x|² - φ'²) dμ ≤ 0`. -/
theorem integral_radial_nonpos (hT : MeasurableSet T)
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ T ↔ a • x ∈ T)
    (hp : IsPerimeterPolarOn (EuclideanSpace.basisFun (Fin d) ℝ) T Ω μ ν)
    (hmin : IsPerimeterMinimizingIn (EuclideanSpace.basisFun (Fin d) ℝ) T Ω)
    (h : IsSmoothBoundaryChart T V F) (hVΩ : V ⊆ Ω)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hφ0 : ∀ r, r < a₀ ∨ b₀ < r → φ r = 0)
    (hK : measureTheoreticBoundary T ∩ {x | a₀ ≤ ‖x‖ ∧ ‖x‖ ≤ b₀} ⊆ V) :
    ∫ x in V, sqNormSecondFundamentalForm F x *
      (2 * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2) - deriv φ ‖x‖ ^ 2) ∂μ ≤ 0 := by
  obtain ⟨hG, hH, hle⟩ := integral_radial_le hT hcone hp hmin h hVΩ hφ ha₀ hφ0 hK
  have heq : (fun x ↦ sqNormSecondFundamentalForm F x *
      (2 * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2) - deriv φ ‖x‖ ^ 2)) = fun x ↦
        2 * (sqNormSecondFundamentalForm F x * (φ ‖x‖ ^ 2 / ‖x‖ ^ 2)) -
          sqNormSecondFundamentalForm F x * deriv φ ‖x‖ ^ 2 := by
    funext x
    ring
  rw [heq, integral_sub (hG.const_mul 2) hH, integral_const_mul]
  linarith

end Integral

end Simons

end SerrinEpigraph
