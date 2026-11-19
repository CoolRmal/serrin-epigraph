module

public import SerrinEpigraph.PerimeterVariation
public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.BVTranslation
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Smooth boundary charts of sets of finite perimeter

Ambient Euclidean calculus (Leon Simon's tangential-derivative formalism) on the regular part of
the boundary of a set of finite perimeter, together with the first-variation consequences for
perimeter minimizers (blueprint GR1 preliminaries).

## Main definitions
* `IsSmoothBoundaryChart E U F`: `U` is open, `F` is `C^∞` (`ContDiffOn ℝ ∞`) on `U` with
  `∇F ≠ 0` on `U`, and `E ∩ U = {F > 0} ∩ U` almost everywhere. The boundary piece is
  `M = U ∩ {F = 0}`.
* `chartNormal F = |∇F|⁻¹ ∇F` (unit normal pointing into `E`), `tangentialProj F = I - ν ⊗ ν`,
  `tangentialGradient F f = P ∇f`, `tangentialDivergence F X = div X - ⟪ν, DX ν⟫`,
  `meanCurvature F = div ν`, `secondFundamentalForm F = P Dν P`,
  `sqNormSecondFundamentalForm F = tr (Aᵀ A)`, `tangentialLaplacian F g = div_M (δ g)`.
  The divergence-type quantities are basis free (`LinearMap.trace`).
* `IsPerimeterPolarOn b E Ω μ ν`: `ν` is a `μ`-integrable unit field on the open set `Ω` with
  `-∫_E div X = ∫_Ω ⟪X, ν⟫ dμ` for compactly supported `C¹` fields `X` in `Ω`
  (constructed by `exists_isPerimeterPolarOn`).
* `IsPerimeterMinimizingIn b E Ω`: minimality against compact perturbations in `Ω`
  (from `IsLocalPerimeterMinimizer.isPerimeterMinimizingIn`).

## Main results
* Shape operator: `IsSmoothBoundaryChart.fderiv_chartNormal_apply` (`Dν w = |∇F|⁻¹ P D²F w`),
  `inner_chartNormal_fderiv_chartNormal` (`⟪ν, Dν w⟫ = 0`), `inner_secondFundamentalForm_comm`,
  `sqNormSecondFundamentalForm_eq_trace_sq` (`|A|² = tr (Dν)²`),
  `sqNormSecondFundamentalForm_eq_sum_sub` (`|A|² = ∑ ‖Dν bᵢ‖² - ‖Dν ν‖²`),
  `meanCurvature_eq_trace_secondFundamentalForm` (`H = tr A`).
* `tangentialGradient_eq_zero_of_eq_zero_on_level`: if `f` vanishes on `M` then `δ f = 0` on `M`.
* Perimeter identification: `IsSmoothBoundaryChart.ae_restrict_eq_zero` (the perimeter measure
  restricted to `U` is concentrated on `M`), `ae_restrict_eq_chartNormal` (its polar vector is
  `∇F/|∇F|`), `measure_ball_pos` (every point of `M` lies in the support).
* First variation on charts of minimizers: `integral_tangentialDivergence_eq_zero`,
  `meanCurvature_eq_zero` (`H = 0` at every point of `M`), and the integration by parts formula
  `integral_inner_tangentialGradient_eq_neg` (`∫ ⟪δf, δg⟫ dμ = -∫ f Δ_M g dμ`).

The stability inequality (GR1) is proved in `SerrinEpigraph.SecondVariation`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff CompactlySupported ENNReal

namespace SerrinEpigraph

/-! ### Definitions -/

/-- A smooth boundary chart of `E` on the open set `U`: `F` is smooth on `U` with nonvanishing
gradient, and `E` agrees almost everywhere on `U` with the superlevel set `{F > 0}`. The smoothness
order is `∞` (`C^∞`, not analytic). -/
structure IsSmoothBoundaryChart {d : ℕ} (E U : Set (Space d)) (F : Space d → ℝ) : Prop where
  isOpen : IsOpen U
  contDiffOn : ContDiffOn ℝ ∞ F U
  gradient_ne_zero : ∀ y ∈ U, gradient F y ≠ 0
  ae_mem_iff : ∀ᵐ y ∂volume.restrict U, y ∈ E ↔ 0 < F y

/-- The unit normal field `ν = ∇F / |∇F|`; it points into `{F > 0}`. -/
def chartNormal {d : ℕ} (F : Space d → ℝ) (y : Space d) : Space d :=
  ‖gradient F y‖⁻¹ • gradient F y

/-- The tangential projection `P = I - ν ⊗ ν`. -/
def tangentialProj {d : ℕ} (F : Space d → ℝ) (y : Space d) : Space d →L[ℝ] Space d :=
  ContinuousLinearMap.id ℝ (Space d) -
    (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y)

/-- The tangential gradient `δ f = P ∇f`. -/
def tangentialGradient {d : ℕ} (F f : Space d → ℝ) (y : Space d) : Space d :=
  tangentialProj F y (gradient f y)

/-- The tangential divergence `div_M X = div X - ⟪ν, DX ν⟫`. -/
def tangentialDivergence {d : ℕ} (F : Space d → ℝ) (X : Space d → Space d) (y : Space d) : ℝ :=
  LinearMap.trace ℝ (Space d) (fderiv ℝ X y).toLinearMap -
    inner ℝ (chartNormal F y) (fderiv ℝ X y (chartNormal F y))

/-- The mean curvature `H = div ν`. -/
def meanCurvature {d : ℕ} (F : Space d → ℝ) (y : Space d) : ℝ :=
  LinearMap.trace ℝ (Space d) (fderiv ℝ (chartNormal F) y).toLinearMap

/-- The second fundamental form `A = P Dν P`, as an endomorphism of `Space d`. -/
def secondFundamentalForm {d : ℕ} (F : Space d → ℝ) (y : Space d) : Space d →L[ℝ] Space d :=
  tangentialProj F y ∘L fderiv ℝ (chartNormal F) y ∘L tangentialProj F y

/-- The squared Hilbert-Schmidt norm `|A|² = tr (Aᵀ A)` of the second fundamental form. -/
def sqNormSecondFundamentalForm {d : ℕ} (F : Space d → ℝ) (y : Space d) : ℝ :=
  LinearMap.trace ℝ (Space d)
    ((secondFundamentalForm F y).adjoint ∘L secondFundamentalForm F y).toLinearMap

/-- The tangential (Laplace-Beltrami) Laplacian `Δ_M g = div_M (δ g)`. -/
def tangentialLaplacian {d : ℕ} (F g : Space d → ℝ) (y : Space d) : ℝ :=
  tangentialDivergence F (tangentialGradient F g) y

/-! ### Pointwise linear algebra of the normal and the tangential projection -/

section Pointwise

variable {d : ℕ} {F : Space d → ℝ} {y : Space d}

theorem tangentialProj_apply (F : Space d → ℝ) (y v : Space d) :
    tangentialProj F y v = v - inner ℝ (chartNormal F y) v • chartNormal F y := by
  simp [tangentialProj]

theorem norm_chartNormal (hy : gradient F y ≠ 0) : ‖chartNormal F y‖ = 1 := by
  rw [chartNormal, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

theorem inner_chartNormal_self (hy : gradient F y ≠ 0) :
    inner ℝ (chartNormal F y) (chartNormal F y) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_chartNormal hy, one_pow]

theorem gradient_eq_norm_smul_chartNormal (hy : gradient F y ≠ 0) :
    gradient F y = ‖gradient F y‖ • chartNormal F y := by
  rw [chartNormal, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

theorem inner_chartNormal_gradient :
    inner ℝ (chartNormal F y) (gradient F y) = ‖gradient F y‖ := by
  by_cases hy : gradient F y = 0
  · simp [hy]
  · rw [chartNormal, real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy), one_mul]

theorem inner_chartNormal_tangentialProj (hy : gradient F y ≠ 0) (v : Space d) :
    inner ℝ (chartNormal F y) (tangentialProj F y v) = 0 := by
  rw [tangentialProj_apply, inner_sub_right, real_inner_smul_right, inner_chartNormal_self hy,
    mul_one, sub_self]

theorem inner_tangentialProj_chartNormal (hy : gradient F y ≠ 0) (v : Space d) :
    inner ℝ (tangentialProj F y v) (chartNormal F y) = 0 := by
  rw [real_inner_comm, inner_chartNormal_tangentialProj hy]

theorem inner_gradient_tangentialProj (hy : gradient F y ≠ 0) (v : Space d) :
    inner ℝ (gradient F y) (tangentialProj F y v) = 0 := by
  rw [gradient_eq_norm_smul_chartNormal hy, real_inner_smul_left,
    inner_chartNormal_tangentialProj hy, mul_zero]

theorem inner_tangentialProj_left (F : Space d → ℝ) (y u w : Space d) :
    inner ℝ (tangentialProj F y u) w = inner ℝ u (tangentialProj F y w) := by
  simp only [tangentialProj_apply, inner_sub_left, inner_sub_right, real_inner_smul_right,
    real_inner_comm]
  ring

theorem tangentialProj_tangentialProj (hy : gradient F y ≠ 0) (v : Space d) :
    tangentialProj F y (tangentialProj F y v) = tangentialProj F y v := by
  rw [tangentialProj_apply (v := tangentialProj F y v), inner_chartNormal_tangentialProj hy,
    zero_smul, sub_zero]

theorem tangentialProj_chartNormal (hy : gradient F y ≠ 0) :
    tangentialProj F y (chartNormal F y) = 0 := by
  rw [tangentialProj_apply, inner_chartNormal_self hy, one_smul, sub_self]

theorem tangentialProj_eq_self_of_inner_eq_zero {v : Space d}
    (hv : inner ℝ (chartNormal F y) v = 0) : tangentialProj F y v = v := by
  rw [tangentialProj_apply, hv, zero_smul, sub_zero]

theorem adjoint_tangentialProj (F : Space d → ℝ) (y : Space d) :
    (tangentialProj F y).adjoint = tangentialProj F y := by
  exact ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    fun u w ↦ inner_tangentialProj_left F y u w).symm

theorem norm_sq_tangentialProj (hy : gradient F y ≠ 0) (v : Space d) :
    ‖tangentialProj F y v‖ ^ 2 = ‖v‖ ^ 2 - inner ℝ (chartNormal F y) v ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_tangentialProj_left,
    tangentialProj_tangentialProj hy, tangentialProj_apply, inner_sub_right,
    real_inner_smul_right, real_inner_comm v (chartNormal F y)]
  ring

theorem norm_tangentialProj_le (hy : gradient F y ≠ 0) (v : Space d) :
    ‖tangentialProj F y v‖ ≤ ‖v‖ := by
  have h := norm_sq_tangentialProj hy v
  have h2 : ‖tangentialProj F y v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg (inner ℝ (chartNormal F y) v)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem inner_tangentialProj_tangentialProj (hy : gradient F y ≠ 0) (u w : Space d) :
    inner ℝ (tangentialProj F y u) (tangentialProj F y w) = inner ℝ u (tangentialProj F y w) := by
  rw [inner_tangentialProj_left, tangentialProj_tangentialProj hy]

end Pointwise

/-! ### Functions vanishing on the level set have vanishing tangential gradient -/

/-- **Key lemma.** Let `F` and `f` be `C¹` on an open set `U`, let `y ∈ U` with `F y = 0` and
`∇F(y) ≠ 0`, and suppose `f` vanishes on the level set `U ∩ {F = 0}`. Then the tangential gradient
`δ f (y) = P ∇f (y)` vanishes, i.e. `∇f(y)` is parallel to `∇F(y)`. -/
theorem tangentialGradient_eq_zero_of_eq_zero_on_level {d : ℕ} {F f : Space d → ℝ}
    {U : Set (Space d)} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (hf : ContDiffOn ℝ 1 f U)
    (hzero : ∀ z ∈ U, F z = 0 → f z = 0) {y : Space d} (hyU : y ∈ U) (hy : F y = 0)
    (hne : gradient F y ≠ 0) : tangentialGradient F f y = 0 := by
  have hFs : HasStrictFDerivAt F (fderiv ℝ F y) y :=
    (hF.contDiffAt (hU.mem_nhds hyU)).hasStrictFDerivAt one_ne_zero
  have hfs : HasStrictFDerivAt f (fderiv ℝ f y) y :=
    (hf.contDiffAt (hU.mem_nhds hyU)).hasStrictFDerivAt one_ne_zero
  -- vectors tangent to the level set are annihilated by `Df(y)`
  have hker : ∀ v : Space d, fderiv ℝ F y v = 0 → fderiv ℝ f y v = 0 := by
    intro v hFv
    by_contra hfv
    have hnn : fderiv ℝ F y (gradient F y) = ‖gradient F y‖ ^ 2 := by
      rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    have hn0 : ‖gradient F y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
    have hsurj : ((fderiv ℝ F y).prod (fderiv ℝ f y) : Space d →ₗ[ℝ] ℝ × ℝ).range = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun pq ↦ ?_
      set α : ℝ := pq.1 / ‖gradient F y‖ ^ 2 with hα
      set β : ℝ := (pq.2 - α * fderiv ℝ f y (gradient F y)) / fderiv ℝ f y v with hβ
      refine ⟨α • gradient F y + β • v, ?_⟩
      show ((fderiv ℝ F y).prod (fderiv ℝ f y)) (α • gradient F y + β • v) = pq
      rw [ContinuousLinearMap.prod_apply]
      refine Prod.ext ?_ ?_
      · show fderiv ℝ F y (α • gradient F y + β • v) = pq.1
        rw [map_add, map_smul, map_smul, hnn, hFv, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
          hα]
        field_simp
      · show fderiv ℝ f y (α • gradient F y + β • v) = pq.2
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hβ]
        field_simp
        ring
    have hmap := (hFs.prodMk hfs).map_nhds_eq_of_surj hsurj
    have hGy : (F y, f y) = ((0 : ℝ), (0 : ℝ)) := by rw [hy, hzero y hyU hy]
    have himg : (fun z ↦ (F z, f z)) '' U ∈ 𝓝 ((0 : ℝ), (0 : ℝ)) := by
      rw [← hGy, ← hmap]
      exact image_mem_map (hU.mem_nhds hyU)
    have htend : Tendsto (fun s : ℝ ↦ ((0 : ℝ), s)) (𝓝[≠] 0) (𝓝 ((0 : ℝ), (0 : ℝ))) :=
      ((continuous_const.prodMk continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨s, hs, hs0⟩ := ((htend.eventually himg).and self_mem_nhdsWithin).exists
    obtain ⟨z, hzU, hz⟩ := hs
    have hz1 : F z = 0 := congrArg Prod.fst hz
    have hz2 : f z = s := congrArg Prod.snd hz
    exact hs0 (hz2 ▸ hzero z hzU hz1)
  -- the tangential gradient is itself tangent, so it is orthogonal to `∇f`
  have hFτ : fderiv ℝ F y (tangentialGradient F f y) = 0 := by
    rw [← inner_gradient_left, tangentialGradient, inner_gradient_tangentialProj hne]
  have hfτ := hker _ hFτ
  have hsq : ‖tangentialGradient F f y‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, tangentialGradient, inner_tangentialProj_tangentialProj hne,
      inner_gradient_left]
    exact hfτ
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-! ### Calculus of the normal field on a chart -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

theorem contDiffOn_gradient (h : IsSmoothBoundaryChart E U F) :
    ContDiffOn ℝ ∞ (gradient F) U :=
  (toDual ℝ (Space d)).symm.contDiff.comp_contDiffOn
    (h.contDiffOn.fderiv_of_isOpen h.isOpen (m := ∞) (by simp))

theorem contDiffOn_chartNormal (h : IsSmoothBoundaryChart E U F) :
    ContDiffOn ℝ ∞ (chartNormal F) U := by
  have hn : ContDiffOn ℝ ∞ (fun x ↦ ‖gradient F x‖) U :=
    h.contDiffOn_gradient.norm ℝ h.gradient_ne_zero
  have hinv : ContDiffOn ℝ ∞ (fun x ↦ ‖gradient F x‖⁻¹) U :=
    hn.inv fun x hx ↦ norm_ne_zero_iff.mpr (h.gradient_ne_zero x hx)
  exact hinv.smul h.contDiffOn_gradient

theorem contDiffAt (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) : ContDiffAt ℝ ∞ F y :=
  h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)

theorem contDiffAt_gradient (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    ContDiffAt ℝ ∞ (gradient F) y :=
  h.contDiffOn_gradient.contDiffAt (h.isOpen.mem_nhds hy)

theorem contDiffAt_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    ContDiffAt ℝ ∞ (chartNormal F) y :=
  h.contDiffOn_chartNormal.contDiffAt (h.isOpen.mem_nhds hy)

theorem differentiableAt_gradient (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    DifferentiableAt ℝ (gradient F) y :=
  (h.contDiffAt_gradient hy).differentiableAt (by simp)

theorem differentiableAt_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    DifferentiableAt ℝ (chartNormal F) y :=
  (h.contDiffAt_chartNormal hy).differentiableAt (by simp)

/-- The Hessian operator `D(∇F)` is symmetric. -/
theorem inner_hessian_comm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (u w : Space d) :
    inner ℝ (fderiv ℝ (gradient F) y u) w = inner ℝ u (fderiv ℝ (gradient F) y w) := by
  have hF := h.contDiffAt hy
  have hsymm := hF.isSymmSndFDerivAt (by simp)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hG := (h.differentiableAt_gradient hy).hasFDerivAt
  -- derivative of `x ↦ ⟪∇F x, v⟫ = DF x v`, computed in two ways
  have key (v : Space d) (z : Space d) :
      inner ℝ (fderiv ℝ (gradient F) y z) v = fderiv ℝ (fderiv ℝ F) y z v := by
    have h1 : HasFDerivAt (fun x ↦ inner ℝ v (gradient F x))
        ((innerSL ℝ v).comp (fderiv ℝ (gradient F) y)) y :=
      (innerSL ℝ v).hasFDerivAt.comp y hG
    have h2 : HasFDerivAt (fun x ↦ fderiv ℝ F x v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ F) y)) y :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hD1.hasFDerivAt
    have hfun : (fun x ↦ inner ℝ v (gradient F x)) = fun x ↦ fderiv ℝ F x v := by
      funext x
      rw [real_inner_comm, inner_gradient_left]
    rw [hfun] at h1
    have he := congrArg (fun L : Space d →L[ℝ] ℝ ↦ L z) (h1.unique h2)
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.apply_apply] at he
    rw [real_inner_comm]
    exact he
  rw [key w u, real_inner_comm, key u w]
  exact hsymm u w

/-- The normal derivative is tangential: `⟪ν, Dν w⟫ = 0`. -/
theorem inner_chartNormal_fderiv_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    inner ℝ (chartNormal F y) (fderiv ℝ (chartNormal F) y w) = 0 := by
  have hd := (h.differentiableAt_chartNormal hy).hasFDerivAt.norm_sq
  have hev : (fun x ↦ ‖chartNormal F x‖ ^ 2) =ᶠ[𝓝 y] fun _ ↦ (1 : ℝ) := by
    filter_upwards [h.isOpen.mem_nhds hy] with x hx
    rw [norm_chartNormal (h.gradient_ne_zero x hx), one_pow]
  have h0 : HasFDerivAt (fun x ↦ ‖chartNormal F x‖ ^ 2) (0 : Space d →L[ℝ] ℝ) y :=
    (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hev
  have he := congrArg (fun L : Space d →L[ℝ] ℝ ↦ L w) (hd.unique h0)
  have he' : 2 * inner ℝ (chartNormal F y) (fderiv ℝ (chartNormal F) y w) = 0 := by
    simpa using he
  linarith

/-- Explicit formula `Dν w = |∇F|⁻¹ P (D²F w)`. -/
theorem fderiv_chartNormal_apply (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (w : Space d) :
    fderiv ℝ (chartNormal F) y w =
      ‖gradient F y‖⁻¹ • tangentialProj F y (fderiv ℝ (gradient F) y w) := by
  have hne := h.gradient_ne_zero y hy
  have hnorm : ‖gradient F y‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hG := (h.differentiableAt_gradient hy).hasFDerivAt
  have hs : DifferentiableAt ℝ (fun x ↦ ‖gradient F x‖⁻¹) y :=
    ((h.differentiableAt_gradient hy).norm ℝ hne).inv hnorm
  have hsmul := hs.hasFDerivAt.smul hG
  have hfun : ((fun x ↦ ‖gradient F x‖⁻¹) • gradient F) = chartNormal F := rfl
  rw [hfun] at hsmul
  have hval : fderiv ℝ (chartNormal F) y w =
      ‖gradient F y‖⁻¹ • fderiv ℝ (gradient F) y w +
        fderiv ℝ (fun x ↦ ‖gradient F x‖⁻¹) y w • gradient F y := by
    rw [hsmul.fderiv]
    simp
  set c := fderiv ℝ (fun x ↦ ‖gradient F x‖⁻¹) y w
  have horth := h.inner_chartNormal_fderiv_chartNormal hy w
  rw [hval, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_chartNormal_gradient] at horth
  have hcG : c • gradient F y = (-(‖gradient F y‖⁻¹ *
      inner ℝ (chartNormal F y) (fderiv ℝ (gradient F) y w))) • chartNormal F y := by
    have h1 : c * ‖gradient F y‖ =
        -(‖gradient F y‖⁻¹ * inner ℝ (chartNormal F y) (fderiv ℝ (gradient F) y w)) := by
      linarith
    calc c • gradient F y = c • (‖gradient F y‖ • chartNormal F y) := by
          rw [← gradient_eq_norm_smul_chartNormal hne]
      _ = (c * ‖gradient F y‖) • chartNormal F y := by rw [smul_smul]
      _ = _ := by rw [h1]
  rw [hval, hcG, tangentialProj_apply, smul_sub, smul_smul, neg_smul, ← sub_eq_add_neg]

theorem tangentialProj_fderiv_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    tangentialProj F y (fderiv ℝ (chartNormal F) y w) = fderiv ℝ (chartNormal F) y w :=
  tangentialProj_eq_self_of_inner_eq_zero (h.inner_chartNormal_fderiv_chartNormal hy w)

/-- Symmetry of the shape operator on tangent vectors. -/
theorem inner_fderiv_chartNormal_tangentialProj_comm (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (u w : Space d) :
    inner ℝ (fderiv ℝ (chartNormal F) y (tangentialProj F y u)) (tangentialProj F y w) =
      inner ℝ (tangentialProj F y u) (fderiv ℝ (chartNormal F) y (tangentialProj F y w)) := by
  have hne := h.gradient_ne_zero y hy
  rw [h.fderiv_chartNormal_apply hy, h.fderiv_chartNormal_apply hy, real_inner_smul_left,
    real_inner_smul_right, inner_tangentialProj_left, tangentialProj_tangentialProj hne,
    ← inner_tangentialProj_left F y (tangentialProj F y u), tangentialProj_tangentialProj hne,
    h.inner_hessian_comm hy, inner_tangentialProj_left]

theorem secondFundamentalForm_apply (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    secondFundamentalForm F y w = fderiv ℝ (chartNormal F) y (tangentialProj F y w) := by
  simp only [secondFundamentalForm, ContinuousLinearMap.comp_apply]
  exact h.tangentialProj_fderiv_chartNormal hy _

/-- The second fundamental form is self-adjoint. -/
theorem inner_secondFundamentalForm_comm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (u w : Space d) :
    inner ℝ (secondFundamentalForm F y u) w = inner ℝ u (secondFundamentalForm F y w) := by
  have hne := h.gradient_ne_zero y hy
  have hl : inner ℝ (secondFundamentalForm F y u) w =
      inner ℝ (secondFundamentalForm F y u) (tangentialProj F y w) := by
    simp only [secondFundamentalForm, ContinuousLinearMap.comp_apply]
    rw [inner_tangentialProj_tangentialProj hne, inner_tangentialProj_left]
  rw [hl, h.secondFundamentalForm_apply hy, h.inner_fderiv_chartNormal_tangentialProj_comm hy,
    ← h.secondFundamentalForm_apply hy, inner_tangentialProj_left]
  congr 1
  simp only [secondFundamentalForm, ContinuousLinearMap.comp_apply,
    tangentialProj_tangentialProj hne]

theorem adjoint_secondFundamentalForm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    (secondFundamentalForm F y).adjoint = secondFundamentalForm F y :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    fun u w ↦ h.inner_secondFundamentalForm_comm hy u w).symm

/-- Chart version of `tangentialGradient_eq_zero_of_eq_zero_on_level`: a `C¹` function vanishing
on `M = U ∩ {F = 0}` has vanishing tangential gradient on `M`. -/
theorem tangentialGradient_eq_zero_of_eq_zero_on_level (h : IsSmoothBoundaryChart E U F)
    {f : Space d → ℝ} (hf : ContDiffOn ℝ 1 f U) (hzero : ∀ z ∈ U, F z = 0 → f z = 0)
    (hyU : y ∈ U) (hy : F y = 0) : tangentialGradient F f y = 0 :=
  SerrinEpigraph.tangentialGradient_eq_zero_of_eq_zero_on_level h.isOpen
    (h.contDiffOn.of_le (by simp)) hf hzero hyU hy (h.gradient_ne_zero y hyU)

end IsSmoothBoundaryChart

/-! ### Trace identities -/

section Trace

variable {d : ℕ}

theorem trace_clm_comp_comm (S T : Space d →L[ℝ] Space d) :
    LinearMap.trace ℝ (Space d) (S ∘L T).toLinearMap =
      LinearMap.trace ℝ (Space d) (T ∘L S).toLinearMap := by
  have h1 : (S ∘L T).toLinearMap = S.toLinearMap ∘ₗ T.toLinearMap := rfl
  have h2 : (T ∘L S).toLinearMap = T.toLinearMap ∘ₗ S.toLinearMap := rfl
  rw [h1, h2, LinearMap.trace_comp_comm']

theorem trace_clm_add (S T : Space d →L[ℝ] Space d) :
    LinearMap.trace ℝ (Space d) (S + T).toLinearMap =
      LinearMap.trace ℝ (Space d) S.toLinearMap + LinearMap.trace ℝ (Space d) T.toLinearMap := by
  have h1 : (S + T).toLinearMap = S.toLinearMap + T.toLinearMap := rfl
  rw [h1, map_add]

theorem trace_clm_smul (c : ℝ) (T : Space d →L[ℝ] Space d) :
    LinearMap.trace ℝ (Space d) (c • T).toLinearMap =
      c * LinearMap.trace ℝ (Space d) T.toLinearMap := by
  have h1 : (c • T).toLinearMap = c • T.toLinearMap := rfl
  rw [h1, map_smul, smul_eq_mul]

theorem trace_clm_smulRight (φ : Space d →L[ℝ] ℝ) (v : Space d) :
    LinearMap.trace ℝ (Space d) (φ.smulRight v).toLinearMap = φ v := by
  rw [ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight]
  rfl

/-- `tr (T ∘ (v ⊗ v)) = ⟪v, T v⟫`. -/
theorem trace_comp_rankOne (T : Space d →L[ℝ] Space d) (v : Space d) :
    LinearMap.trace ℝ (Space d) (T ∘L (innerSL ℝ v).smulRight v).toLinearMap =
      inner ℝ v (T v) := by
  have h1 : (T ∘L (innerSL ℝ v).smulRight v) = ((innerSL ℝ v).smulRight (T v)) := by
    ext1 w
    simp
  rw [h1, trace_clm_smulRight, innerSL_apply_apply]

/-- `tr (Tᵀ T) = ∑ ‖T bᵢ‖²` in any orthonormal basis. -/
theorem trace_adjoint_comp_self_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Space d)) (T : Space d →L[ℝ] Space d) :
    LinearMap.trace ℝ (Space d) (T.adjoint ∘L T).toLinearMap = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change inner ℝ (b i) (T.adjoint (T (b i))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem sqNormSecondFundamentalForm_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Space d)) (F : Space d → ℝ) (y : Space d) :
    sqNormSecondFundamentalForm F y = ∑ i, ‖secondFundamentalForm F y (b i)‖ ^ 2 :=
  trace_adjoint_comp_self_eq_sum b _

theorem sqNormSecondFundamentalForm_nonneg (F : Space d → ℝ) (y : Space d) :
    0 ≤ sqNormSecondFundamentalForm F y := by
  rw [sqNormSecondFundamentalForm_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ)]
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _

theorem trace_adjoint_comp_aux (B P : Space d →L[ℝ] Space d) (hP : P.adjoint = P)
    (hPP : P ∘L P = P) :
    LinearMap.trace ℝ (Space d) ((B ∘L P).adjoint ∘L (B ∘L P)).toLinearMap =
      LinearMap.trace ℝ (Space d) (B.adjoint ∘L (B ∘L P)).toLinearMap := by
  calc LinearMap.trace ℝ (Space d) ((B ∘L P).adjoint ∘L (B ∘L P)).toLinearMap
      = LinearMap.trace ℝ (Space d) (P ∘L (B.adjoint ∘L (B ∘L P))).toLinearMap := by
        rw [ContinuousLinearMap.adjoint_comp, hP, ContinuousLinearMap.comp_assoc]
    _ = LinearMap.trace ℝ (Space d) ((B.adjoint ∘L (B ∘L P)) ∘L P).toLinearMap :=
        trace_clm_comp_comm _ _
    _ = LinearMap.trace ℝ (Space d) (B.adjoint ∘L (B ∘L P)).toLinearMap := by
        rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hPP]

end Trace

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

private theorem id_eq_tangentialProj_add (F : Space d → ℝ) (y : Space d) :
    tangentialProj F y + (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y) =
      ContinuousLinearMap.id ℝ (Space d) := by
  simp [tangentialProj]

private theorem tangentialProj_comp_fderiv (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    tangentialProj F y ∘L fderiv ℝ (chartNormal F) y = fderiv ℝ (chartNormal F) y := by
  ext1 w
  exact h.tangentialProj_fderiv_chartNormal hy w

private theorem rankOne_comp_fderiv (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y) ∘L fderiv ℝ (chartNormal F) y =
      0 := by
  ext1 w
  simp [h.inner_chartNormal_fderiv_chartNormal hy w]

theorem secondFundamentalForm_eq_comp (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    secondFundamentalForm F y = fderiv ℝ (chartNormal F) y ∘L tangentialProj F y := by
  rw [secondFundamentalForm, ← ContinuousLinearMap.comp_assoc, h.tangentialProj_comp_fderiv hy]

/-- `|A|² = tr ((Dν)²)`. -/
theorem sqNormSecondFundamentalForm_eq_trace_sq (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) :
    sqNormSecondFundamentalForm F y =
      LinearMap.trace ℝ (Space d)
        (fderiv ℝ (chartNormal F) y ∘L fderiv ℝ (chartNormal F) y).toLinearMap := by
  set B := fderiv ℝ (chartNormal F) y
  set P := tangentialProj F y
  set Q := (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y)
  have hsplit : B ∘L B = B ∘L (B ∘L P) + B ∘L (B ∘L Q) := by
    rw [← ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_add,
      id_eq_tangentialProj_add F y, ContinuousLinearMap.comp_id]
  have hQ : LinearMap.trace ℝ (Space d) (B ∘L (B ∘L Q)).toLinearMap = 0 := by
    rw [trace_clm_comp_comm, ContinuousLinearMap.comp_assoc, h.rankOne_comp_fderiv hy,
      ContinuousLinearMap.comp_zero]
    simp
  have hP : B ∘L (B ∘L P) = secondFundamentalForm F y ∘L secondFundamentalForm F y := by
    rw [h.secondFundamentalForm_eq_comp hy, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc P B P, h.tangentialProj_comp_fderiv hy]
  rw [hsplit, trace_clm_add, hQ, add_zero, hP, sqNormSecondFundamentalForm,
    h.adjoint_secondFundamentalForm hy]

/-- `tr ((Dν)ᵀ Dν) = |A|² + |Dν ν|²`, i.e. `|A|² = ‖Dν‖²_HS - |Dν ν|²`. -/
theorem trace_adjoint_comp_fderiv_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    LinearMap.trace ℝ (Space d)
        ((fderiv ℝ (chartNormal F) y).adjoint ∘L fderiv ℝ (chartNormal F) y).toLinearMap =
      sqNormSecondFundamentalForm F y +
        ‖fderiv ℝ (chartNormal F) y (chartNormal F y)‖ ^ 2 := by
  set B := fderiv ℝ (chartNormal F) y
  set P := tangentialProj F y
  set Q := (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y)
  have hne := h.gradient_ne_zero y hy
  have hPP : P ∘L P = P := by
    ext1 w
    exact tangentialProj_tangentialProj hne w
  have hsplit : B.adjoint ∘L B = B.adjoint ∘L (B ∘L P) + B.adjoint ∘L (B ∘L Q) := by
    rw [← ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_add,
      id_eq_tangentialProj_add F y, ContinuousLinearMap.comp_id]
  have hQ : LinearMap.trace ℝ (Space d) (B.adjoint ∘L (B ∘L Q)).toLinearMap = ‖B (chartNormal F y)‖ ^ 2 := by
    rw [← ContinuousLinearMap.comp_assoc, trace_comp_rankOne, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hP : LinearMap.trace ℝ (Space d) (B.adjoint ∘L (B ∘L P)).toLinearMap =
      sqNormSecondFundamentalForm F y := by
    rw [sqNormSecondFundamentalForm, h.secondFundamentalForm_eq_comp hy]
    exact (trace_adjoint_comp_aux B P (adjoint_tangentialProj F y) hPP).symm
  rw [hsplit, trace_clm_add, hQ, hP]

/-- `|A|² = ∑ ‖Dν bᵢ‖² - ‖Dν ν‖²` in any orthonormal basis. -/
theorem sqNormSecondFundamentalForm_eq_sum_sub {ι : Type*} [Fintype ι]
    (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (b : OrthonormalBasis ι ℝ (Space d)) :
    sqNormSecondFundamentalForm F y =
      ∑ i, ‖fderiv ℝ (chartNormal F) y (b i)‖ ^ 2 -
        ‖fderiv ℝ (chartNormal F) y (chartNormal F y)‖ ^ 2 := by
  rw [← trace_adjoint_comp_self_eq_sum b, h.trace_adjoint_comp_fderiv_chartNormal hy]
  ring

/-- The mean curvature is the trace of the second fundamental form. -/
theorem meanCurvature_eq_trace_secondFundamentalForm (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) :
    meanCurvature F y = LinearMap.trace ℝ (Space d) (secondFundamentalForm F y).toLinearMap := by
  have hsplit : fderiv ℝ (chartNormal F) y =
      fderiv ℝ (chartNormal F) y ∘L tangentialProj F y +
        fderiv ℝ (chartNormal F) y ∘L
          (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y) := by
    rw [← ContinuousLinearMap.comp_add, id_eq_tangentialProj_add F y, ContinuousLinearMap.comp_id]
  rw [meanCurvature, hsplit, trace_clm_add, trace_comp_rankOne,
    h.inner_chartNormal_fderiv_chartNormal hy, add_zero, h.secondFundamentalForm_eq_comp hy]

end IsSmoothBoundaryChart

/-! ### Tangential divergence of products -/

section ProductRules

variable {d : ℕ} {F : Space d → ℝ} {y : Space d}

theorem tangentialDivergence_fun_smul {f : Space d → ℝ} {X : Space d → Space d}
    (hf : DifferentiableAt ℝ f y) (hX : DifferentiableAt ℝ X y) :
    tangentialDivergence F (fun x ↦ f x • X x) y =
      f y * tangentialDivergence F X y + fderiv ℝ f y (X y) -
        fderiv ℝ f y (chartNormal F y) * inner ℝ (chartNormal F y) (X y) := by
  have hd : fderiv ℝ (fun x ↦ f x • X x) y =
      f y • fderiv ℝ X y + (fderiv ℝ f y).smulRight (X y) :=
    (hf.hasFDerivAt.smul hX.hasFDerivAt).fderiv
  rw [tangentialDivergence, tangentialDivergence, hd, trace_clm_add, trace_clm_smul,
    trace_clm_smulRight]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, real_inner_smul_right]
  ring

theorem IsSmoothBoundaryChart.tangentialDivergence_smul_chartNormal {E U : Set (Space d)}
    (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) {ζ : Space d → ℝ}
    (hζ : DifferentiableAt ℝ ζ y) :
    tangentialDivergence F (fun x ↦ ζ x • chartNormal F x) y = ζ y * meanCurvature F y := by
  rw [tangentialDivergence_fun_smul hζ (h.differentiableAt_chartNormal hy), tangentialDivergence,
    h.inner_chartNormal_fderiv_chartNormal hy, sub_zero, inner_chartNormal_self
    (h.gradient_ne_zero y hy), mul_one, meanCurvature]
  ring

end ProductRules

/-! ### Cut-off, continuity and integration helpers -/

section Helpers

variable {d : ℕ}

/-- A function continuous on an open set and vanishing off a closed subset is continuous. -/
theorem continuous_of_continuousOn_of_eq_zero {Y : Type*} [TopologicalSpace Y] [Zero Y]
    {g : Space d → Y} {U K : Set (Space d)} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hg : ContinuousOn g U) (h0 : ∀ x, x ∉ K → g x = 0) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : x ∈ U
  · exact hg.continuousAt (hU.mem_nhds hx)
  · have hxK : x ∉ K := fun h ↦ hx (hKU h)
    have hev : g =ᶠ[𝓝 x] fun _ ↦ (0 : Y) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with z hz
      exact h0 z hz
    rw [continuousAt_congr hev]
    exact continuousAt_const

/-- Cutting off a field that is `Cⁿ` on an open set by a `Cⁿ` function supported inside it. -/
theorem contDiff_smul_of_tsupport_subset_of_contDiffOn {n : ℕ∞ω} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {Y : Space d → G} {g : Space d → ℝ}
    {U : Set (Space d)} (hU : IsOpen U) (hY : ContDiffOn ℝ n Y U) (hg : ContDiff ℝ n g)
    (hs : tsupport g ⊆ U) : ContDiff ℝ n (fun x ↦ g x • Y x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hg.contDiffAt.smul (hY.contDiffAt (hU.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : G))).congr_of_eventuallyEq
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun hx' ↦ hx (hs hx'))
    filter_upwards [hz] with z hz'
    simp only [Pi.zero_apply] at hz'
    simp only [hz', zero_smul]

theorem tsupport_smul_subset_left' {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Space d → ℝ) (Y : Space d → G) : tsupport (fun x ↦ g x • Y x) ⊆ tsupport g :=
  closure_mono (Function.support_smul_subset_left g Y)

theorem hasCompactSupport_smul_left' {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : Space d → ℝ} (hg : HasCompactSupport g) (Y : Space d → G) :
    HasCompactSupport (fun x ↦ g x • Y x) :=
  hg.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left' g Y)

theorem integrable_of_continuousOn_of_support_subset {G : Type*} [NormedAddCommGroup G]
    {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ] {g : Space d → G} {K : Set (Space d)}
    (hK : IsCompact K) (hg : ContinuousOn g K) (hs : Function.support g ⊆ K) : Integrable g μ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp (hg.integrableOn_compact hK)

/-- Divergence integration by parts against a function that is only `C¹` near the support of
the compactly supported field. -/
theorem integral_mul_fieldDivergence_eq_neg (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {u : Space d → ℝ} {X : Space d → Space d} {U : Set (Space d)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXU : tsupport X ⊆ U) :
    ∫ x, u x * fieldDivergence b X x = -∫ x, fderiv ℝ u x (X x) := by
  let ψ : Fin d → Space d → ℝ := fun i x ↦ inner ℝ (b i) (X x)
  have hψ (i : Fin d) : ContDiff ℝ 1 (ψ i) := (innerSL ℝ (b i)).contDiff.comp hX
  have hψs (i : Fin d) : tsupport (ψ i) ⊆ tsupport X :=
    tsupport_comp_subset (by simp : inner ℝ (b i) (0 : Space d) = 0) X
  have hψc (i : Fin d) : HasCompactSupport (ψ i) :=
    hXc.of_isClosed_subset (isClosed_tsupport _) (hψs i)
  have hdψ (i : Fin d) (x : Space d) :
      fderiv ℝ (ψ i) x (b i) = inner ℝ (b i) (fderiv ℝ X x (b i)) := by
    have he := (innerSL ℝ (b i)).hasFDerivAt.comp x (hX.differentiable one_ne_zero x).hasFDerivAt
    exact congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (b i)) he.fderiv
  have hK := hXc
  have hcont_u : ContinuousOn u (tsupport X) := hu.continuousOn.mono hXU
  have hcont_du : ContinuousOn (fun x ↦ fderiv ℝ u x) (tsupport X) :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).mono hXU
  have hint1 (i : Fin d) : Integrable (fun x ↦ u x * fderiv ℝ (ψ i) x (b i)) := by
    apply integrable_of_continuousOn_of_support_subset hK
      (hcont_u.mul (((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
    exact (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (b i)).trans (hψs i)))
  have hint2 (i : Fin d) : Integrable (fun x ↦ fderiv ℝ u x (b i) * ψ i x) := by
    apply integrable_of_continuousOn_of_support_subset hK
      ((hcont_du.clm_apply continuousOn_const).mul (hψ i).continuous.continuousOn)
    exact (Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans (hψs i))
  have hibp (i : Fin d) := integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := volume) hU hu
    (hψ i) (hψc i) ((hψs i).trans hXU) (b i)
  have hlhs : (fun x ↦ u x * fieldDivergence b X x) =
      fun x ↦ ∑ i, u x * fderiv ℝ (ψ i) x (b i) := by
    funext x
    simp only [fieldDivergence, Finset.mul_sum, hdψ]
  have hrhs : (fun x ↦ fderiv ℝ u x (X x)) = fun x ↦ ∑ i, fderiv ℝ u x (b i) * ψ i x := by
    funext x
    have hX' : X x = ∑ i, inner ℝ (b i) (X x) • b i := (b.sum_repr' (X x)).symm
    conv_lhs => rw [hX']
    simp only [map_sum, map_smul, smul_eq_mul, ψ]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [hlhs, hrhs, integral_finsetSum _ fun i _ ↦ hint1 i,
    integral_finsetSum _ fun i _ ↦ hint2 i, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hibp i

end Helpers

/-! ### Smoothed indicator of `{F > 0}` and the boundary pairing -/

section Pairing

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ}

private theorem deriv_smoothTransition_nonneg (z : ℝ) : 0 ≤ deriv Real.smoothTransition z :=
  Real.smoothTransition.monotone.deriv_nonneg

private theorem deriv_smoothTransition_of_one_lt {z : ℝ} (hz : 1 < z) :
    deriv Real.smoothTransition z = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 z] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact Real.smoothTransition.one_of_one_le (le_of_lt hw)
  rw [hev.deriv_eq]
  simp

private theorem deriv_smoothTransition_of_neg {z : ℝ} (hz : z < 0) :
    deriv Real.smoothTransition z = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hz] with w hw
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hw)
  rw [hev.deriv_eq]
  simp

/-- The boundary pairing `-∫_E div X` is the limit of `∫ hₙ'(F) ⟪∇F, X⟫` for the smoothed
indicators `hₙ = smoothTransition ((n + 1) ·)` of `{F > 0}`. -/
theorem IsSmoothBoundaryChart.tendsto_boundaryPairing (h : IsSmoothBoundaryChart E U F)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {X : Space d → Space d} (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) (hXU : tsupport X ⊆ U) :
    Tendsto (fun n : ℕ ↦ ∫ x, ((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * F x) *
        inner ℝ (gradient F x) (X x)) atTop
      (𝓝 (-(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b X x))) := by
  let u : ℕ → Space d → ℝ := fun n x ↦ Real.smoothTransition (((n : ℝ) + 1) * F x)
  have hF1 : ContDiffOn ℝ 1 F U := h.contDiffOn.of_le (by simp)
  have hu (n : ℕ) : ContDiffOn ℝ 1 (u n) U :=
    Real.smoothTransition.contDiff.comp_contDiffOn (contDiffOn_const.mul hF1)
  have hdiv_cont : Continuous (fieldDivergence b X) := fieldDivergence_continuous b hX
  have hdiv0 (x : Space d) (hx : x ∉ tsupport X) : fieldDivergence b X x = 0 :=
    fieldDivergence_zero_of_notMem_tsupport b X hx
  -- integration by parts for each smoothed indicator
  have hibp (n : ℕ) : ∫ x, ((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * F x) *
      inner ℝ (gradient F x) (X x) = -∫ x, u n x * fieldDivergence b X x := by
    rw [integral_mul_fieldDivergence_eq_neg b h.isOpen (hu n) hX hXc hXU, neg_neg]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    by_cases hxU : x ∈ U
    · have hFd : HasFDerivAt F (fderiv ℝ F x) x :=
        ((h.contDiffAt hxU).differentiableAt (by simp)).hasFDerivAt
      have hd : HasFDerivAt (u n) (deriv Real.smoothTransition (((n : ℝ) + 1) * F x) •
          (((n : ℝ) + 1) • fderiv ℝ F x)) x :=
        (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _
          |>.hasDerivAt.comp_hasFDerivAt x (hFd.const_smul ((n : ℝ) + 1))
      rw [hd.fderiv]
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, inner_gradient_left]
      ring
    · have hX0 : X x = 0 := image_eq_zero_of_notMem_tsupport fun hx ↦ hxU (hXU hx)
      simp [hX0]
  -- dominated convergence for the smoothed indicators
  have hae : ∀ᵐ x ∂volume, x ∈ U → (x ∈ E ↔ 0 < F x) :=
    (ae_restrict_iff' h.isOpen.measurableSet).mp h.ae_mem_iff
  have hlim : Tendsto (fun n ↦ ∫ x, u n x * fieldDivergence b X x) atTop
      (𝓝 (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b X x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖fieldDivergence b X x‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      apply continuous_of_continuousOn_of_eq_zero h.isOpen (isClosed_tsupport X) hXU
      · exact (hu n).continuousOn.mul hdiv_cont.continuousOn
      · intro x hx
        rw [hdiv0 x hx, mul_zero]
    · exact (hdiv_cont.integrable_of_hasCompactSupport
        (hXc.of_isClosed_subset (isClosed_tsupport _) (by
          apply closure_minimal _ (isClosed_tsupport X)
          intro x hx
          by_contra hxX
          exact hx (hdiv0 x hxX)))).norm
    · intro n
      refine Eventually.of_forall fun x ↦ ?_
      rw [norm_mul]
      have h1 : ‖u n x‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      nlinarith [norm_nonneg (fieldDivergence b X x), norm_nonneg (u n x)]
    · filter_upwards [hae] with x hx
      by_cases hxX : x ∈ tsupport X
      · have hxU := hXU hxX
        have hiff := hx hxU
        apply Tendsto.mul_const
        by_cases hFx : 0 < F x
        · have hxE : x ∈ E := hiff.mpr hFx
          rw [indicator_of_mem hxE]
          apply tendsto_const_nhds.congr'
          obtain ⟨N, hN⟩ := exists_nat_gt (1 / F x)
          filter_upwards [eventually_ge_atTop N] with n hn
          symm
          apply Real.smoothTransition.one_of_one_le
          have h1 : 1 / F x < (n : ℝ) + 1 := by
            have : (N : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          rw [div_lt_iff₀ hFx] at h1
          linarith
        · have hxE : x ∉ E := fun hxE ↦ hFx (hiff.mp hxE)
          rw [indicator_of_notMem hxE]
          apply tendsto_const_nhds.congr'
          refine Eventually.of_forall fun n ↦ ?_
          symm
          apply Real.smoothTransition.zero_of_nonpos
          have : 0 ≤ (n : ℝ) + 1 := by positivity
          nlinarith [not_lt.mp hFx]
      · simp only [hdiv0 x hxX, mul_zero]
        exact tendsto_const_nhds
  simp_rw [hibp]
  exact hlim.neg

/-- Tangential fields have zero boundary pairing. -/
theorem IsSmoothBoundaryChart.integral_indicator_fieldDivergence_eq_zero_of_tangent
    (h : IsSmoothBoundaryChart E U F) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {X : Space d → Space d} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXU : tsupport X ⊆ U) (htan : ∀ x ∈ U, inner ℝ (gradient F x) (X x) = 0) :
    ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b X x = 0 := by
  have ht := h.tendsto_boundaryPairing b hX hXc hXU
  have hzero : (fun n : ℕ ↦ ∫ x, ((n : ℝ) + 1) *
      deriv Real.smoothTransition (((n : ℝ) + 1) * F x) * inner ℝ (gradient F x) (X x)) =
      fun _ ↦ 0 := by
    funext n
    apply integral_eq_zero_of_ae
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hxU : x ∈ U
    · simp [htan x hxU]
    · have hX0 : X x = 0 := image_eq_zero_of_notMem_tsupport fun hx ↦ hxU (hXU hx)
      simp [hX0]
  rw [hzero] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

/-- Fields supported away from the level set `{F = 0}` have zero boundary pairing. -/
theorem IsSmoothBoundaryChart.integral_indicator_fieldDivergence_eq_zero_of_ne_zero
    (h : IsSmoothBoundaryChart E U F) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {X : Space d → Space d} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXU : tsupport X ⊆ U) (hF0 : ∀ x ∈ tsupport X, F x ≠ 0) :
    ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b X x = 0 := by
  have ht := h.tendsto_boundaryPairing b hX hXc hXU
  -- a positive lower bound for `|F|` on the support
  obtain ⟨c, hc, hcF⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ tsupport X, c ≤ |F x| := by
    rcases (tsupport X).eq_empty_or_nonempty with hempty | hne
    · exact ⟨1, one_pos, by simp [hempty]⟩
    · have hcont : ContinuousOn (fun x ↦ |F x|) (tsupport X) :=
        (h.contDiffOn.continuousOn.mono hXU).abs
      obtain ⟨x₀, hx₀, hmin⟩ := hXc.exists_isMinOn hne hcont
      exact ⟨|F x₀|, abs_pos.mpr (hF0 x₀ hx₀), fun x hx ↦ hmin hx⟩
  have hev : (fun n : ℕ ↦ ∫ x, ((n : ℝ) + 1) *
      deriv Real.smoothTransition (((n : ℝ) + 1) * F x) * inner ℝ (gradient F x) (X x)) =ᶠ[atTop]
      fun _ ↦ 0 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply integral_eq_zero_of_ae
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hxX : x ∈ tsupport X
    · have hcx := hcF x hxX
      have hn1 : 1 < ((n : ℝ) + 1) * c := by
        have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
        have h2 : 1 / c < (n : ℝ) + 1 := by linarith
        rwa [div_lt_iff₀ hc] at h2
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hd : deriv Real.smoothTransition (((n : ℝ) + 1) * F x) = 0 := by
        rcases le_or_gt 0 (F x) with hFx | hFx
        · apply deriv_smoothTransition_of_one_lt
          rw [abs_of_nonneg hFx] at hcx
          nlinarith
        · apply deriv_smoothTransition_of_neg
          nlinarith
      simp [hd]
    · have hX0 : X x = 0 := image_eq_zero_of_notMem_tsupport hxX
      simp [hX0]
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) ht
  linarith

/-- The inward normal has a nonnegative boundary pairing. -/
theorem IsSmoothBoundaryChart.integral_indicator_fieldDivergence_smul_chartNormal_nonpos
    (h : IsSmoothBoundaryChart E U F) (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
      fieldDivergence b (fun x ↦ φ x • chartNormal F x) x ≤ 0 := by
  have hX : ContDiff ℝ 1 (fun x ↦ φ x • chartNormal F x) :=
    contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen
      (h.contDiffOn_chartNormal.of_le (by simp)) hφ hφU
  have ht := h.tendsto_boundaryPairing b hX (hasCompactSupport_smul_left' hφc _)
    ((tsupport_smul_subset_left' _ _).trans hφU)
  have hnonneg : ∀ n : ℕ, 0 ≤ ∫ x, ((n : ℝ) + 1) *
      deriv Real.smoothTransition (((n : ℝ) + 1) * F x) *
        inner ℝ (gradient F x) (φ x • chartNormal F x) := by
    intro n
    apply integral_nonneg
    intro x
    dsimp only [Pi.zero_apply]
    rw [real_inner_smul_right, real_inner_comm, inner_chartNormal_gradient]
    have := deriv_smoothTransition_nonneg (((n : ℝ) + 1) * F x)
    have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have := hφ0 x
    positivity
  have := ge_of_tendsto' ht hnonneg
  linarith

end Pairing

/-! ### Nonnegativity from smooth tests -/

/-- A function whose integrals against all nonnegative smooth bumps supported in the open set `U`
are nonnegative is almost everywhere nonnegative on `U`. -/
theorem ae_nonneg_of_integral_contDiff_mul_nonneg {d : ℕ} {ρ : Measure (Space d)}
    [IsFiniteMeasure ρ] {U : Set (Space d)} (hU : IsOpen U) {f : Space d → ℝ}
    (hf : IntegrableOn f U ρ)
    (h : ∀ g : Space d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      (∀ x, 0 ≤ g x) → 0 ≤ ∫ x, g x * f x ∂ρ) :
    ∀ᵐ x ∂ρ, x ∈ U → 0 ≤ f x := by
  set f' : Space d → ℝ := U.indicator f with hf'def
  have hf'i : Integrable f' ρ := hf.integrable_indicator hU.measurableSet
  -- nonnegativity of the integrals over compact subsets of `U`
  have hK : ∀ K, IsCompact K → K ⊆ U → 0 ≤ ∫ x in K, f' x ∂ρ := by
    intro K hKc hKU
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · simp [hKe]
    obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
    let r : ℕ → ℝ := fun n ↦ δ / ((n : ℝ) + 2)
    have hr_pos (n : ℕ) : 0 < r n := by positivity
    have hr_le (n : ℕ) : r n ≤ δ := by
      simp only [r]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hr_tend : Tendsto r atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [r, div_eq_mul_inv] using h1.inv_tendsto_atTop.const_mul δ
    have hg (n : ℕ) : ∃ g : Space d → ℝ, ContDiff ℝ (((⊤ : ℕ∞) : ℕ∞ω)) g ∧
        Set.range g ⊆ Icc 0 1 ∧ Function.support g = thickening (r n) K ∧
          ∀ x, x ∈ K ↔ g x = 1 :=
      exists_contDiff_support_eq_eq_one_iff isOpen_thickening hKc.isClosed
        (self_subset_thickening (hr_pos n) K)
    choose g hgs hgr hgsupp hgone using hg
    have hg01 (n : ℕ) (x : Space d) : 0 ≤ g n x ∧ g n x ≤ 1 :=
      hgr n (Set.mem_range_self x)
    have htsupp (n : ℕ) : tsupport (g n) ⊆ cthickening δ K := by
      change closure (Function.support (g n)) ⊆ _
      rw [hgsupp n]
      exact (closure_thickening_subset_cthickening _ _).trans (cthickening_mono (hr_le n) K)
    have hgc (n : ℕ) : HasCompactSupport (g n) :=
      (hKc.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) (htsupp n)
    have hint_eq (n : ℕ) : ∫ x, g n x * f x ∂ρ = ∫ x, g n x * f' x ∂ρ := by
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      by_cases hxU : x ∈ U
      · rw [hf'def, indicator_of_mem hxU]
      · have hg0 : g n x = 0 := image_eq_zero_of_notMem_tsupport
          fun hx ↦ hxU (hδU (htsupp n hx))
        rw [hg0, zero_mul, zero_mul]
    have hnn (n : ℕ) : 0 ≤ ∫ x, g n x * f' x ∂ρ := by
      rw [← hint_eq n]
      exact h (g n) (hgs n) (hgc n) ((htsupp n).trans hδU) fun x ↦ (hg01 n x).1
    have hlim : Tendsto (fun n ↦ ∫ x, g n x * f' x ∂ρ) atTop (𝓝 (∫ x, K.indicator f' x ∂ρ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f' x‖)
      · exact fun n ↦ (hgs n).continuous.aestronglyMeasurable.mul hf'i.aestronglyMeasurable
      · exact hf'i.norm
      · intro n
        refine Eventually.of_forall fun x ↦ ?_
        rw [norm_mul, Real.norm_of_nonneg (hg01 n x).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (hg01 n x).2
      · refine Eventually.of_forall fun x ↦ ?_
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK]
          apply tendsto_const_nhds.congr'
          refine Eventually.of_forall fun n ↦ ?_
          simp only [(hgone n x).mp hxK, one_mul]
        · rw [indicator_of_notMem hxK]
          have hpos : 0 < infDist x K := (hKc.isClosed.notMem_iff_infDist_pos hKne).mp hxK
          apply tendsto_const_nhds.congr'
          filter_upwards [hr_tend.eventually (gt_mem_nhds hpos)] with n hn
          have hxt : x ∉ thickening (r n) K := by
            rw [mem_thickening_iff_infDist_lt hKne]
            exact not_lt.mpr hn.le
          have hg0 : g n x = 0 := by
            rw [← Function.notMem_support, hgsupp n]
            exact hxt
          simp only [hg0, zero_mul]
    rw [← integral_indicator hKc.measurableSet]
    exact ge_of_tendsto' hlim hnn
  -- pass to a strongly measurable representative and use inner regularity
  have hmeas := hf'i.aestronglyMeasurable
  set f'' := hmeas.mk f'
  have hf''eq : f' =ᵐ[ρ] f'' := hmeas.ae_eq_mk
  have hf''m : StronglyMeasurable f'' := hmeas.stronglyMeasurable_mk
  set A : Set (Space d) := U ∩ {x | f'' x < 0}
  have hAm : MeasurableSet A :=
    hU.measurableSet.inter (measurableSet_lt hf''m.measurable measurable_const)
  have hA0 : ρ A = 0 := by
    by_contra hne
    obtain ⟨K, hKA, hKc, hKpos⟩ :=
      hAm.exists_lt_isCompact_of_ne_top (measure_ne_top ρ A) (pos_iff_ne_zero.mpr hne)
    have h1 := hK K hKc (hKA.trans inter_subset_left)
    have h2 : ∫ x in K, f' x ∂ρ = ∫ x in K, f'' x ∂ρ :=
      integral_congr_ae (ae_restrict_of_ae hf''eq)
    have hint'' : Integrable (fun x ↦ -f'' x) (ρ.restrict K) :=
      ((hf'i.congr hf''eq).neg).integrableOn
    have h3 : 0 < ∫ x in K, -f'' x ∂ρ := by
      rw [integral_pos_iff_support_of_nonneg_ae _ hint'']
      · calc (0 : ℝ≥0∞) < ρ K := hKpos
          _ = ρ.restrict K K := (Measure.restrict_apply_self _ _).symm
          _ ≤ ρ.restrict K (Function.support fun x ↦ -f'' x) := by
            apply measure_mono
            intro x hx
            have hx' : f'' x < 0 := (hKA hx).2
            simp only [Function.mem_support, ne_eq, neg_eq_zero]
            exact hx'.ne
      · filter_upwards [ae_restrict_mem hKc.measurableSet] with x hx
        have hx' : f'' x < 0 := (hKA hx).2
        simp only [Pi.zero_apply]
        linarith
    rw [integral_neg] at h3
    linarith
  have hAae : ∀ᵐ x ∂ρ, x ∉ A := by
    rw [ae_iff]
    simpa using hA0
  filter_upwards [hf''eq, hAae] with x hx hxA hxU
  have h1 : ¬ f'' x < 0 := fun hlt ↦ hxA ⟨hxU, hlt⟩
  have h2 : f' x = f x := by rw [hf'def, indicator_of_mem hxU]
  rw [← h2, hx]
  exact not_lt.mp h1

/-! ### Perimeter measures and polar vectors -/

/-- `(μ, ν)` represent the distributional gradient of `1_E` on the open set `Ω`:
`ν` is a `μ`-integrable unit vector field on `Ω` and `-∫_E div X = ∫_Ω ⟪X, ν⟫ dμ` for every
compactly supported `C¹` field `X` with `tsupport X ⊆ Ω`. -/
structure IsPerimeterPolarOn {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (E Ω : Set (Space d)) (μ : Measure (Space d)) (ν : Space d → Space d) : Prop where
  isOpen : IsOpen Ω
  integrable : Integrable ν (μ.restrict Ω)
  norm_eq_one : ∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1
  pairing_eq : ∀ X : C_c(Space d, Space d), ContDiff ℝ 1 (X : Space d → Space d) →
    tsupport X ⊆ Ω →
    -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b X x) =
      ∫ x, inner ℝ (X x) (ν x) ∂μ.restrict Ω

namespace IsPerimeterPolarOn

variable {d : ℕ} {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
  {μ : Measure (Space d)} {ν : Space d → Space d}

theorem pairing (hp : IsPerimeterPolarOn b E Ω μ ν) {X : Space d → Space d}
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b X x) =
      ∫ x, inner ℝ (X x) (ν x) ∂μ.restrict Ω :=
  hp.pairing_eq ⟨⟨X, hX.continuous⟩, hXc⟩ hX hXΩ

theorem isFiniteMeasure (hp : IsPerimeterPolarOn b E Ω μ ν) : IsFiniteMeasure (μ.restrict Ω) := by
  constructor
  have heq : ∫⁻ _, (1 : ℝ≥0∞) ∂(μ.restrict Ω) = ∫⁻ x, ‖ν x‖ₑ ∂(μ.restrict Ω) := by
    apply lintegral_congr_ae
    filter_upwards [hp.norm_eq_one] with x hx
    simp [← ofReal_norm, hx]
  rw [lintegral_const, one_mul] at heq
  exact heq ▸ hp.integrable.2

/-- Restriction of a polar representation to a smaller open set. -/
theorem mono (hp : IsPerimeterPolarOn b E Ω μ ν) {Ω' : Set (Space d)} (hΩ' : IsOpen Ω')
    (hsub : Ω' ⊆ Ω) : IsPerimeterPolarOn b E Ω' μ ν where
  isOpen := hΩ'
  integrable := hp.integrable.mono_measure (Measure.restrict_mono hsub le_rfl)
  norm_eq_one := ae_restrict_of_ae_restrict_of_subset hsub hp.norm_eq_one
  pairing_eq X hX hXΩ' := by
    rw [hp.pairing_eq X hX (hXΩ'.trans hsub)]
    have h1 : (∫ x, inner ℝ (X x) (ν x) ∂μ.restrict Ω) =
        ∫ x in Ω', inner ℝ (X x) (ν x) ∂μ.restrict Ω := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : X x = 0 := image_eq_zero_of_notMem_tsupport fun hh ↦ hx (hXΩ' hh)
      simp [hz]
    rw [h1, Measure.restrict_restrict hΩ'.measurableSet, inter_eq_left.mpr hsub]

end IsPerimeterPolarOn

/-- Every open set in which `E` has finite perimeter carries a finite perimeter measure, concentrated
on that set, with a unit polar vector representing the distributional gradient of `1_E`. -/
theorem exists_isPerimeterPolarOn {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ (μ : Measure (Space d)) (ν : Space d → Space d), IsFiniteMeasure μ ∧ μ Ωᶜ = 0 ∧
      (∀ V, IsOpen V → V ⊆ Ω → μ V = variationalPerimeter b E V) ∧
      IsPerimeterPolarOn b E Ω μ ν := by
  obtain ⟨μ, ν, hfin, -, huniv, hopen, hν, hunit, hdist⟩ :=
    exists_localized_perimeter_polar_measure b hE hP
  have hW : μ Ω = μ univ := by rw [hopen _ hΩ subset_rfl, huniv]
  have hcompl : μ Ωᶜ = 0 := by
    have hsum := measure_add_measure_compl (μ := μ) hΩ.measurableSet
    rw [hW] at hsum
    have hfin' : μ univ ≠ ⊤ := measure_ne_top μ univ
    exact (ENNReal.add_right_inj hfin').mp (hsum.trans (add_zero _).symm)
  have hself : μ.restrict Ω = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hcompl)
  refine ⟨μ, ν, hfin, hcompl, hopen, ⟨hΩ, ?_, ?_, ?_⟩⟩
  · rw [hself]
    exact hν
  · rw [hself]
    exact hunit
  · intro X hX hXΩ
    rw [hself]
    exact hdist X hX hXΩ

/-- A global perimeter Radon measure (e.g. `perimeterRadonMeasure`) has a polar representation on
every open set of finite perimeter. -/
theorem exists_isPerimeterPolarOn_of_perimeter_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)} (hE : MeasurableSet E)
    (hΩ : IsOpen Ω) (hP : variationalPerimeter b E Ω ≠ ⊤) (μ : Measure (Space d))
    [IsLocallyFiniteMeasure μ] (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U) :
    ∃ ν : Space d → Space d, IsPerimeterPolarOn b E Ω μ ν := by
  obtain ⟨ν, h1, h2, h3⟩ := exists_local_polar_for_perimeter_measure b hE hΩ hP μ hμ
  exact ⟨ν, ⟨hΩ, h1, h2, h3⟩⟩

/-! ### Identification of the perimeter measure on a chart -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E U Ω : Set (Space d)}
  {F : Space d → ℝ} {μ : Measure (Space d)} {ν : Space d → Space d}

/-- On a chart, the perimeter measure is concentrated on the level set `M = U ∩ {F = 0}`. -/
theorem ae_restrict_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hp : IsPerimeterPolarOn b E Ω μ ν) (hUΩ : U ⊆ Ω) : ∀ᵐ x ∂μ.restrict U, F x = 0 := by
  have := hp.isFiniteMeasure
  set V : Set (Space d) := U ∩ F ⁻¹' {0}ᶜ
  have hV : IsOpen V :=
    h.contDiffOn.continuousOn.isOpen_inter_preimage h.isOpen isOpen_compl_singleton
  have hVU : V ⊆ U := inter_subset_left
  have hzero : ∀ᵐ x ∂μ.restrict Ω, x ∈ V → ν x = 0 := by
    apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hp.integrable.integrableOn.locallyIntegrableOn
    intro g hg hgc hgV
    have hint : Integrable (fun x ↦ g x • ν x) (μ.restrict Ω) :=
      hp.integrable.smul_of_top_right (hg.continuous.memLp_top_of_hasCompactSupport hgc _)
    apply ext_inner_left ℝ
    intro w
    rw [inner_zero_right, ← integral_inner hint]
    have hX : ContDiff ℝ 1 (fun x ↦ g x • w) := (hg.of_le (by simp)).smul contDiff_const
    have hXc : HasCompactSupport (fun x ↦ g x • w) := hasCompactSupport_smul_left' hgc _
    have hXV : tsupport (fun x ↦ g x • w) ⊆ V := (tsupport_smul_subset_left' _ _).trans hgV
    have hpair := hp.pairing hX hXc ((hXV.trans hVU).trans hUΩ)
    rw [h.integral_indicator_fieldDivergence_eq_zero_of_ne_zero b hX hXc (hXV.trans hVU)
      (fun x hx ↦ (hXV hx).2), neg_zero] at hpair
    rw [hpair]
    congr 1
    funext x
    rw [real_inner_smul_left, real_inner_smul_right]
  have hnotV : ∀ᵐ x ∂μ.restrict Ω, x ∉ V := by
    filter_upwards [hzero, hp.norm_eq_one] with x hx h1 hxV
    rw [hx hxV, norm_zero] at h1
    exact zero_ne_one h1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hUΩ hnotV,
    ae_restrict_mem h.isOpen.measurableSet] with x hx hxU
  by_contra hF
  exact hx ⟨hxU, hF⟩

/-- On a chart, the polar vector of the perimeter measure is the inward unit normal `∇F/|∇F|`. -/
theorem ae_restrict_eq_chartNormal (h : IsSmoothBoundaryChart E U F)
    (hp : IsPerimeterPolarOn b E Ω μ ν) (hUΩ : U ⊆ Ω) :
    ∀ᵐ x ∂μ.restrict U, ν x = chartNormal F x := by
  have := hp.isFiniteMeasure
  have hN : ContDiffOn ℝ ∞ (chartNormal F) U := h.contDiffOn_chartNormal
  have hNmeas : AEStronglyMeasurable (chartNormal F) ((μ.restrict Ω).restrict U) :=
    hN.continuousOn.aestronglyMeasurable h.isOpen.measurableSet
  have hνmeas : AEStronglyMeasurable ν ((μ.restrict Ω).restrict U) :=
    hp.integrable.aestronglyMeasurable.restrict
  -- the tangential part of `ν` vanishes
  let f : Space d → Space d := fun x ↦ ν x - inner ℝ (chartNormal F x) (ν x) • chartNormal F x
  have hf_eq (x : Space d) : f x = tangentialProj F x (ν x) :=
    (tangentialProj_apply F x (ν x)).symm
  have hfmeas : AEStronglyMeasurable f ((μ.restrict Ω).restrict U) :=
    hνmeas.sub ((hNmeas.inner (𝕜 := ℝ) hνmeas).smul hNmeas)
  have hfint : IntegrableOn f U (μ.restrict Ω) := by
    refine (hp.integrable.restrict (s := U)).norm.mono' hfmeas ?_
    filter_upwards [ae_restrict_mem h.isOpen.measurableSet] with x hx
    rw [hf_eq]
    exact norm_tangentialProj_le (h.gradient_ne_zero x hx) _
  have htan : ∀ᵐ x ∂μ.restrict Ω, x ∈ U → f x = 0 := by
    apply h.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint.locallyIntegrableOn
    intro g hg hgc hgU
    have hint : Integrable (fun x ↦ g x • f x) (μ.restrict Ω) := by
      have h1 : IntegrableOn (fun x ↦ g x • f x) U (μ.restrict Ω) :=
        hfint.smul_of_top_right (hg.continuous.memLp_top_of_hasCompactSupport hgc _)
      refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
      intro x hx
      exact hgU (subset_tsupport _ (Function.support_smul_subset_left _ _ hx))
    apply ext_inner_left ℝ
    intro w
    rw [inner_zero_right, ← integral_inner hint]
    let Y : Space d → Space d := fun x ↦ tangentialProj F x w
    have hYeq : Y = fun x ↦ w - inner ℝ (chartNormal F x) w • chartNormal F x := by
      funext x
      exact tangentialProj_apply F x w
    have hY : ContDiffOn ℝ ∞ Y U := by
      rw [hYeq]
      exact contDiffOn_const.sub ((hN.inner ℝ contDiffOn_const).smul hN)
    have hX : ContDiff ℝ 1 (fun x ↦ g x • Y x) :=
      contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen (hY.of_le (by simp))
        (hg.of_le (by simp)) hgU
    have hXc : HasCompactSupport (fun x ↦ g x • Y x) := hasCompactSupport_smul_left' hgc _
    have hXU : tsupport (fun x ↦ g x • Y x) ⊆ U := (tsupport_smul_subset_left' _ _).trans hgU
    have hpair := hp.pairing hX hXc (hXU.trans hUΩ)
    rw [h.integral_indicator_fieldDivergence_eq_zero_of_tangent b hX hXc hXU
      (fun x hx ↦ by
        rw [real_inner_smul_right, inner_gradient_tangentialProj (h.gradient_ne_zero x hx),
          mul_zero]), neg_zero] at hpair
    rw [hpair]
    congr 1
    funext x
    rw [real_inner_smul_left, real_inner_smul_right, hf_eq, inner_tangentialProj_left]
  -- the normal component is nonnegative
  let s : Space d → ℝ := fun x ↦ inner ℝ (chartNormal F x) (ν x)
  have hsint : IntegrableOn s U (μ.restrict Ω) := by
    refine (hp.integrable.restrict (s := U)).norm.mono' (hNmeas.inner (𝕜 := ℝ) hνmeas) ?_
    filter_upwards [ae_restrict_mem h.isOpen.measurableSet] with x hx
    calc ‖s x‖ ≤ ‖chartNormal F x‖ * ‖ν x‖ := norm_inner_le_norm _ _
      _ = ‖ν x‖ := by rw [norm_chartNormal (h.gradient_ne_zero x hx), one_mul]
  have hpos : ∀ᵐ x ∂μ.restrict Ω, x ∈ U → 0 ≤ s x := by
    apply ae_nonneg_of_integral_contDiff_mul_nonneg h.isOpen hsint
    intro g hg hgc hgU hg0
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
    have hX : ContDiff ℝ 1 (fun x ↦ g x • chartNormal F x) :=
      contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen (hN.of_le (by simp)) hg1 hgU
    have hpair := hp.pairing hX (hasCompactSupport_smul_left' hgc _)
      ((tsupport_smul_subset_left' _ _).trans (hgU.trans hUΩ))
    have hle := h.integral_indicator_fieldDivergence_smul_chartNormal_nonpos b hg1 hgc hgU hg0
    have heq : ∫ x, g x * s x ∂μ.restrict Ω =
        ∫ x, inner ℝ (g x • chartNormal F x) (ν x) ∂μ.restrict Ω := by
      congr 1
      funext x
      rw [real_inner_smul_left]
    linarith
  -- conclusion
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hUΩ htan,
    ae_restrict_of_ae_restrict_of_subset hUΩ hpos,
    ae_restrict_of_ae_restrict_of_subset hUΩ hp.norm_eq_one,
    ae_restrict_mem h.isOpen.measurableSet] with x h1 h2 h3 hxU
  have hne := h.gradient_ne_zero x hxU
  have hν : ν x = s x • chartNormal F x := by
    have := h1 hxU
    simp only [f, sub_eq_zero] at this
    exact this
  have hs1 : |s x| = 1 := by
    rw [hν, norm_smul, norm_chartNormal hne, mul_one, Real.norm_eq_abs] at h3
    exact h3
  have hs : s x = 1 := by
    rw [abs_of_nonneg (h2 hxU)] at hs1
    exact hs1
  rw [hν, hs, one_smul]

/-- Every point of the level set `M = U ∩ {F = 0}` lies in the support of the perimeter measure
restricted to the chart. -/
theorem measure_ball_pos (h : IsSmoothBoundaryChart E U F) (hE : MeasurableSet E)
    (hp : IsPerimeterPolarOn b E Ω μ ν) (hUΩ : U ⊆ Ω) {y : Space d} (hyU : y ∈ U)
    (hy : F y = 0) {r : ℝ} (hr : 0 < r) : 0 < μ.restrict U (ball y r) := by
  have hne := h.gradient_ne_zero y hyU
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      exact absurd (Subsingleton.elim (gradient F y) 0) hne
    · exact hd0
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp h.isOpen y hyU
  set r₁ := min r ε with hr₁def
  have hr₁ : 0 < r₁ := lt_min hr hε
  have hr₁U : ball y r₁ ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hεU
  by_contra hzero
  have hzero' : μ.restrict U (ball y r) = 0 := le_antisymm (not_lt.mp hzero) bot_le
  have hμ1 : μ (ball y r₁) = 0 := by
    have h1 : μ (ball y r₁) = μ.restrict U (ball y r₁) := by
      rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hr₁U]
    rw [h1]
    exact measure_mono_null (ball_subset_ball (min_le_left _ _)) hzero'
  -- the perimeter of `E` vanishes in the small ball
  have hP0 : variationalPerimeter b E (ball y r₁) = 0 := by
    refine le_antisymm ?_ zero_le
    unfold variationalPerimeter
    refine iSup_le fun X ↦ iSup_le fun hX ↦ iSup_le fun hXc ↦ iSup_le fun hXs ↦
      iSup_le fun _ ↦ ?_
    have hpair := hp.pairing hX hXc (hXs.trans (hr₁U.trans hUΩ))
    have hnull : μ.restrict Ω (ball y r₁) = 0 :=
      le_antisymm ((Measure.restrict_apply_le _ _).trans hμ1.le) bot_le
    have hint0 : ∫ x, inner ℝ (X x) (ν x) ∂μ.restrict Ω = 0 := by
      apply integral_eq_zero_of_ae
      have hae : ∀ᵐ x ∂μ.restrict Ω, x ∉ ball y r₁ := by
        rw [ae_iff]
        simp only [not_not, Set.ofPred_mem_eq]
        exact hnull
      filter_upwards [hae] with x hx
      have hX0 : X x = 0 := image_eq_zero_of_notMem_tsupport fun hh ↦ hx (hXs hh)
      simp [hX0]
    rw [hint0, neg_eq_zero] at hpair
    rw [hpair, norm_zero, ENNReal.ofReal_zero]
  -- translate to the origin
  set E' : Set (Space d) := (fun z : Space d ↦ y + z) ⁻¹' E
  have hE' : MeasurableSet E' := hE.preimage (measurable_const_add y)
  have hP0' : variationalPerimeter b E' (ball 0 r₁) = 0 := by
    have h1 := variationalPerimeter_preimage_add_smul_ball hd b E y 0 (r := 1) (ρ := r₁) one_pos
    simp only [one_smul, smul_zero, add_zero, one_mul] at h1
    rw [h1, hP0, mul_zero]
  -- the line through `y` in the normal direction crosses the level set transversally
  set e := chartNormal F y with he
  have he1 : ‖e‖ = 1 := norm_chartNormal hne
  have hFd : HasFDerivAt F (fderiv ℝ F y) y :=
    ((h.contDiffAt hyU).differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ F (y + t • e)) (fderiv ℝ F y e) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ y + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
    exact hFd.comp_hasDerivAt_of_eq 0 h1 (by simp)
  have hslope_pos : 0 < fderiv ℝ F y e := by
    rw [← inner_gradient_left, real_inner_comm, he, inner_chartNormal_gradient]
    exact norm_pos_iff.mpr hne
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < t⁻¹ * F (y + t • e) := by
    have ht := hasDerivAt_iff_tendsto_slope.mp hline
    filter_upwards [ht.eventually (lt_mem_nhds hslope_pos)] with t htl
    simpa [slope, hy] using htl
  obtain ⟨δ, hδ, hδt⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  set t₀ := min (δ / 2) (r₁ / 8) with ht₀def
  have ht₀ : 0 < t₀ := lt_min (by positivity) (by positivity)
  have ht₀δ : t₀ < δ := (min_le_left _ _).trans_lt (by linarith)
  have ht₀r : t₀ ≤ r₁ / 8 := min_le_right _ _
  have hFp : 0 < F (y + t₀ • e) := by
    have h1 := hδt (y := t₀) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht₀]; exact ht₀δ)
      ht₀.ne'
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr ht₀)).mp h1
  have hFq : F (y + (-t₀) • e) < 0 := by
    have h1 := hδt (y := -t₀) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht₀]; exact ht₀δ)
      (neg_ne_zero.mpr ht₀.ne')
    have hneg : (-t₀)⁻¹ < 0 := inv_lt_zero.mpr (neg_lt_zero.mpr ht₀)
    by_contra hcon
    have := mul_nonpos_of_nonpos_of_nonneg hneg.le (not_lt.mp hcon)
    linarith
  -- neighbourhoods of the two crossing points
  have hnorm_t (t : ℝ) : ‖t • e‖ = |t| := by rw [norm_smul, he1, mul_one, Real.norm_eq_abs]
  have hpU : y + t₀ • e ∈ U := by
    apply hr₁U
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm_t, abs_of_pos ht₀]
    linarith
  have hqU : y + (-t₀) • e ∈ U := by
    apply hr₁U
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm_t, abs_neg, abs_of_pos ht₀]
    linarith
  have hcont_p : ContinuousAt F (y + t₀ • e) :=
    h.contDiffOn.continuousOn.continuousAt (h.isOpen.mem_nhds hpU)
  have hcont_q : ContinuousAt F (y + (-t₀) • e) :=
    h.contDiffOn.continuousOn.continuousAt (h.isOpen.mem_nhds hqU)
  obtain ⟨εp, hεp, hεpF⟩ := Metric.eventually_nhds_iff.mp (hcont_p.eventually (lt_mem_nhds hFp))
  obtain ⟨εq, hεq, hεqF⟩ := Metric.eventually_nhds_iff.mp (hcont_q.eventually (gt_mem_nhds hFq))
  set ε₃ := min (min εp εq) (r₁ / 8) with hε₃def
  have hε₃ : 0 < ε₃ := lt_min (lt_min hεp hεq) (by positivity)
  set x₀ : Space d := t₀ • e
  set z : Space d := (-(2 * t₀)) • e
  have hz : ‖z‖ = 2 * t₀ := by rw [hnorm_t, abs_neg, abs_of_pos (by positivity)]
  set W := ball x₀ ε₃
  have hWsub : W ⊆ closedBall (0 : Space d) (r₁ / 4) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖x - x₀‖ < ε₃ := by rwa [mem_ball, dist_eq_norm] at hx
    have h2 : ‖x₀‖ = t₀ := by rw [hnorm_t, abs_of_pos ht₀]
    have h3 : ε₃ ≤ r₁ / 8 := min_le_right _ _
    calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ ≤ r₁ / 4 := by linarith
  have hWE : ∀ x ∈ W, 0 < F (y + x) ∧ F (y + (x + z)) < 0 ∧ y + x ∈ U ∧ y + (x + z) ∈ U := by
    intro x hx
    have h1 : ‖x - x₀‖ < ε₃ := by rwa [mem_ball, dist_eq_norm] at hx
    have hx₀ : ‖x₀‖ = t₀ := by rw [hnorm_t, abs_of_pos ht₀]
    have hxn : ‖x‖ ≤ r₁ / 4 := by
      have := hWsub hx
      rwa [mem_closedBall, dist_zero_right] at this
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply hεpF
      rw [dist_eq_norm, add_sub_add_left_eq_sub]
      exact h1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    · apply hεqF
      have : y + (x + z) - (y + (-t₀) • e) = x - x₀ := by
        simp only [z, x₀, neg_smul]
        rw [show (2 * t₀) • e = t₀ • e + t₀ • e by rw [two_mul, add_smul]]
        abel
      rw [dist_eq_norm, this]
      exact h1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    · apply hr₁U
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith
    · apply hr₁U
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      calc ‖x + z‖ ≤ ‖x‖ + ‖z‖ := norm_add_le _ _
        _ < r₁ := by rw [hz]; linarith
  -- the translation estimate forces the indicator difference to vanish, a contradiction
  have hzr : r₁ / 4 + ‖z‖ < r₁ := by rw [hz]; linarith
  have htrans := integral_phase_translation_le_perimeter_bound b hE' z hzr le_rfl
    (by rw [hP0', ENNReal.ofReal_zero])
  rw [mul_zero] at htrans
  set g : Space d → ℝ := fun x ↦ ‖E'.indicator (fun _ ↦ (1 : ℝ)) (x + z) -
    E'.indicator (fun _ ↦ (1 : ℝ)) x‖ with hgdef
  have hgm : Measurable g := by
    have h1 : Measurable (E'.indicator fun _ ↦ (1 : ℝ)) := measurable_const.indicator hE'
    exact ((h1.comp (measurable_add_const z)).sub h1).norm
  have hgle : ∀ x, g x ≤ 1 := by
    intro x
    simp only [hgdef]
    by_cases h1 : x + z ∈ E' <;> by_cases h2 : x ∈ E' <;> simp [h1, h2]
  have hgint : IntegrableOn g (closedBall (0 : Space d) (r₁ / 4)) := by
    refine Integrable.mono'
      ((continuousOn_const (c := (1 : ℝ))).integrableOn_compact (isCompact_closedBall 0 _))
      hgm.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hgle x
  have hae : ∀ᵐ x ∂volume, x ∈ U → (x ∈ E ↔ 0 < F x) :=
    (ae_restrict_iff' h.isOpen.measurableSet).mp h.ae_mem_iff
  have hae1 : ∀ᵐ x ∂volume, y + x ∈ U → (y + x ∈ E ↔ 0 < F (y + x)) :=
    (measurePreserving_add_left volume y).quasiMeasurePreserving.ae hae
  have hae2 : ∀ᵐ x ∂volume, (y + z) + x ∈ U → ((y + z) + x ∈ E ↔ 0 < F ((y + z) + x)) :=
    (measurePreserving_add_left volume (y + z)).quasiMeasurePreserving.ae hae
  have hgW : ∀ᵐ x ∂volume.restrict W, g x = 1 := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hae1,
      ae_restrict_of_ae hae2] with x hxW h1 h2
    obtain ⟨hFx, hFxz, hxU, hxzU⟩ := hWE x hxW
    have hyz : (y + z) + x = y + (x + z) := by abel
    rw [hyz] at h2
    have hmem1 : x ∈ E' := (h1 hxU).mpr hFx
    have hmem2 : x + z ∉ E' := fun hh ↦ (lt_asymm hFxz) ((h2 hxzU).mp hh)
    simp [hgdef, hmem1, hmem2]
  have hlow : volume.real W ≤ ∫ x in closedBall (0 : Space d) (r₁ / 4), g x := by
    calc volume.real W = ∫ x in W, (1 : ℝ) := by rw [setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ x in W, g x := (integral_congr_ae hgW).symm
      _ ≤ ∫ x in closedBall (0 : Space d) (r₁ / 4), g x :=
        setIntegral_mono_set hgint (Eventually.of_forall fun x ↦ norm_nonneg _)
          (Eventually.of_forall hWsub)
  have hWpos : 0 < volume.real W := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hε₃).ne' measure_ball_lt_top.ne
  linarith

end IsSmoothBoundaryChart

/-! ### First variation on a chart: vanishing mean curvature and integration by parts -/

/-- Minimality of `E` against compact perturbations inside the open set `Ω`, in the form used by
`perimeter_first_variation_eq_zero`. -/
def IsPerimeterMinimizingIn {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (E Ω : Set (Space d)) : Prop :=
  ∀ D, MeasurableSet D →
    (∃ K, IsCompact K ∧ K ⊆ Ω ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
    variationalPerimeter b E Ω ≤ variationalPerimeter b D Ω

theorem IsLocalPerimeterMinimizer.isPerimeterMinimizingIn {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω₀ Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω₀) (hΩ : IsOpen Ω) (hsub : Ω ⊆ Ω₀) :
    IsPerimeterMinimizingIn b E Ω :=
  fun D hD ⟨K, hK, hKΩ, hED⟩ ↦ h.minimizes Ω D K hΩ hsub hD hK hKΩ hED

namespace IsSmoothBoundaryChart

variable {d : ℕ} {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E U Ω : Set (Space d)}
  {F : Space d → ℝ} {μ : Measure (Space d)} {ν : Space d → Space d}

theorem meanCurvature_eq_fieldDivergence (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (F : Space d → ℝ) (y : Space d) :
    meanCurvature F y = fieldDivergence b (chartNormal F) y :=
  (fieldDivergence_eq_trace b _ y).symm

theorem continuousOn_meanCurvature (h : IsSmoothBoundaryChart E U F) :
    ContinuousOn (meanCurvature F) U := by
  have hfun : meanCurvature F = fieldDivergence (EuclideanSpace.basisFun (Fin d) ℝ)
      (chartNormal F) := funext (meanCurvature_eq_fieldDivergence _ F)
  rw [hfun]
  have hD : ContinuousOn (fderiv ℝ (chartNormal F)) U :=
    h.contDiffOn_chartNormal.continuousOn_fderiv_of_isOpen h.isOpen (by simp)
  exact continuousOn_finsetSum _ fun i _ ↦ continuousOn_const.inner
    (hD.clm_apply continuousOn_const)

theorem isFiniteMeasure_restrict (hp : IsPerimeterPolarOn b E Ω μ ν) (hUΩ : U ⊆ Ω) :
    IsFiniteMeasure (μ.restrict U) := by
  have := hp.isFiniteMeasure
  have h1 : μ.restrict U = (μ.restrict Ω).restrict U := by
    rw [Measure.restrict_restrict' hp.isOpen.measurableSet, inter_eq_left.mpr hUΩ]
  rw [h1]
  infer_instance

/-- First variation on a chart: for a perimeter minimizer, `∫_M div_M X dμ = 0` for every
compactly supported `C¹` field `X` with support in the chart. -/
theorem integral_tangentialDivergence_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hE : MeasurableSet E) (hp : IsPerimeterPolarOn b E Ω μ ν) (hmin : IsPerimeterMinimizingIn b E Ω)
    (hUΩ : U ⊆ Ω) {X : Space d → Space d} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXU : tsupport X ⊆ U) :
    ∫ x in U, tangentialDivergence F X x ∂μ = 0 := by
  have hfv := perimeter_first_variation_eq_zero b hE hp.isOpen hmin μ hp.integrable
    hp.norm_eq_one hp.pairing_eq hX hXc (hXU.trans hUΩ)
  set G : Space d → ℝ := fun x ↦ fieldDivergence b X x - inner ℝ (ν x) (fderiv ℝ X x (ν x))
  have hG0 : ∀ x, x ∉ U → G x = 0 := by
    intro x hx
    have hxX : x ∉ tsupport X := fun hh ↦ hx (hXU hh)
    simp [G, fieldDivergence, fderiv_of_notMem_tsupport ℝ hxX]
  have h1 : ∫ x, G x ∂μ.restrict Ω = ∫ x in U, G x ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx ↦ hG0 x hx),
      Measure.restrict_restrict' hp.isOpen.measurableSet, inter_eq_left.mpr hUΩ]
  rw [h1] at hfv
  rw [← hfv]
  refine integral_congr_ae ?_
  filter_upwards [h.ae_restrict_eq_chartNormal hp hUΩ] with x hx
  simp only [G, tangentialDivergence, hx, fieldDivergence_eq_trace]

/-- On a chart of a perimeter minimizer the mean curvature vanishes `μ`-almost everywhere. -/
theorem ae_meanCurvature_eq_zero (h : IsSmoothBoundaryChart E U F) (hE : MeasurableSet E)
    (hp : IsPerimeterPolarOn b E Ω μ ν) (hmin : IsPerimeterMinimizingIn b E Ω) (hUΩ : U ⊆ Ω) :
    ∀ᵐ x ∂μ.restrict U, meanCurvature F x = 0 := by
  have := isFiniteMeasure_restrict hp hUΩ
  have hloc : LocallyIntegrableOn (meanCurvature F) U (μ.restrict U) :=
    h.continuousOn_meanCurvature.locallyIntegrableOn h.isOpen.measurableSet
  have hzero := h.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [hzero, ae_restrict_mem h.isOpen.measurableSet] with x hx hxU
    exact hx hxU
  intro g hg hgc hgU
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hX : ContDiff ℝ 1 (fun x ↦ g x • chartNormal F x) :=
    contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen
      (h.contDiffOn_chartNormal.of_le (by simp)) hg1 hgU
  have hfv := h.integral_tangentialDivergence_eq_zero hE hp hmin hUΩ hX
    (hasCompactSupport_smul_left' hgc _) ((tsupport_smul_subset_left' _ _).trans hgU)
  rw [← hfv]
  refine setIntegral_congr_fun h.isOpen.measurableSet fun x hx ↦ ?_
  rw [h.tangentialDivergence_smul_chartNormal hx (hg1.differentiable one_ne_zero x), smul_eq_mul]

/-- **Minimal ⇒ `H = 0`.** On a chart of a perimeter minimizer the mean curvature `div ν`
vanishes at every point of the level set `M = U ∩ {F = 0}`. -/
theorem meanCurvature_eq_zero (h : IsSmoothBoundaryChart E U F) (hE : MeasurableSet E)
    (hp : IsPerimeterPolarOn b E Ω μ ν) (hmin : IsPerimeterMinimizingIn b E Ω) (hUΩ : U ⊆ Ω)
    {y : Space d} (hyU : y ∈ U) (hy : F y = 0) : meanCurvature F y = 0 := by
  by_contra hH
  have hcont : ContinuousAt (meanCurvature F) y :=
    h.continuousOn_meanCurvature.continuousAt (h.isOpen.mem_nhds hyU)
  obtain ⟨r, hr, hrH⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hH)
  have hnull : μ.restrict U (ball y r) = 0 := by
    apply measure_mono_null _ (ae_iff.mp (h.ae_meanCurvature_eq_zero hE hp hmin hUΩ))
    intro x hx
    exact hrH (mem_ball.mp hx)
  exact (h.measure_ball_pos hE hp hUΩ hyU hy hr).ne' hnull

theorem contDiffOn_tangentialGradient (h : IsSmoothBoundaryChart E U F) {g : Space d → ℝ}
    {n : ℕ} (hg : ContDiffOn ℝ (n + 1) g U) : ContDiffOn ℝ n (tangentialGradient F g) U := by
  have hG : ContDiffOn ℝ n (gradient g) U :=
    (toDual ℝ (Space d)).symm.contDiff.comp_contDiffOn (hg.fderiv_of_isOpen h.isOpen le_rfl)
  have hN : ContDiffOn ℝ n (chartNormal F) U :=
    h.contDiffOn_chartNormal.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hfun : tangentialGradient F g =
      fun x ↦ gradient g x - inner ℝ (chartNormal F x) (gradient g x) • chartNormal F x := by
    funext x
    exact tangentialProj_apply F x _
  rw [hfun]
  exact hG.sub ((hN.inner ℝ hG).smul hN)

theorem continuousOn_tangentialDivergence (h : IsSmoothBoundaryChart E U F)
    {Y : Space d → Space d} (hY : ContDiffOn ℝ 1 Y U) :
    ContinuousOn (tangentialDivergence F Y) U := by
  have hD : ContinuousOn (fderiv ℝ Y) U := hY.continuousOn_fderiv_of_isOpen h.isOpen le_rfl
  have hN : ContinuousOn (chartNormal F) U := h.contDiffOn_chartNormal.continuousOn
  have hfun : tangentialDivergence F Y = fun x ↦
      fieldDivergence (EuclideanSpace.basisFun (Fin d) ℝ) Y x -
        inner ℝ (chartNormal F x) (fderiv ℝ Y x (chartNormal F x)) := by
    funext x
    rw [tangentialDivergence, fieldDivergence_eq_trace]
  rw [hfun]
  refine (continuousOn_finsetSum _ fun i _ ↦ continuousOn_const.inner
    (hD.clm_apply continuousOn_const)).sub (hN.inner (hD.clm_apply hN))

/-- **Integration by parts on `M`.** For a perimeter minimizer with a smooth chart, a compactly
supported `C¹` function `f` and a `C²` function `g` on the chart,
`∫_M ⟪δf, δg⟫ dμ = -∫_M f Δ_M g dμ`. -/
theorem integral_inner_tangentialGradient_eq_neg (h : IsSmoothBoundaryChart E U F)
    (hE : MeasurableSet E) (hp : IsPerimeterPolarOn b E Ω μ ν)
    (hmin : IsPerimeterMinimizingIn b E Ω) (hUΩ : U ⊆ Ω) {f g : Space d → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hg : ContDiffOn ℝ 2 g U) :
    ∫ x in U, inner ℝ (tangentialGradient F f x) (tangentialGradient F g x) ∂μ =
      -∫ x in U, f x * tangentialLaplacian F g x ∂μ := by
  have := isFiniteMeasure_restrict hp hUΩ
  have hδg : ContDiffOn ℝ 1 (tangentialGradient F g) U :=
    h.contDiffOn_tangentialGradient (n := 1) (hg.of_le (by norm_num))
  have hX : ContDiff ℝ 1 (fun x ↦ f x • tangentialGradient F g x) :=
    contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen hδg hf hfU
  have hfv := h.integral_tangentialDivergence_eq_zero hE hp hmin hUΩ hX
    (hasCompactSupport_smul_left' hfc _) ((tsupport_smul_subset_left' _ _).trans hfU)
  -- pointwise product rule on the chart
  have hpt : ∀ x ∈ U, tangentialDivergence F (fun x ↦ f x • tangentialGradient F g x) x =
      f x * tangentialLaplacian F g x +
        inner ℝ (tangentialGradient F f x) (tangentialGradient F g x) := by
    intro x hx
    have hne := h.gradient_ne_zero x hx
    rw [tangentialDivergence_fun_smul (hf.differentiable one_ne_zero x)
      ((hδg.differentiableOn one_ne_zero x hx).differentiableAt (h.isOpen.mem_nhds hx)),
      tangentialGradient, inner_chartNormal_tangentialProj hne, mul_zero, sub_zero,
      tangentialLaplacian, ← inner_gradient_left, tangentialGradient,
      inner_tangentialProj_tangentialProj hne, ← tangentialGradient]
  -- continuity and integrability of the two terms
  have hdf : ∀ x, x ∉ tsupport f → gradient f x = 0 := by
    intro x hx
    simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hcont1 : Continuous fun x ↦ f x * tangentialLaplacian F g x := by
    apply continuous_of_continuousOn_of_eq_zero h.isOpen (isClosed_tsupport f) hfU
    · exact hf.continuous.continuousOn.mul (h.continuousOn_tangentialDivergence hδg)
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hcont2 : Continuous fun x ↦
      inner ℝ (tangentialGradient F f x) (tangentialGradient F g x) := by
    apply continuous_of_continuousOn_of_eq_zero h.isOpen (isClosed_tsupport f) hfU
    · have hgf : Continuous (gradient f) :=
        (toDual ℝ (Space d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
      have hN : ContinuousOn (chartNormal F) U := h.contDiffOn_chartNormal.continuousOn
      have hδf : ContinuousOn (tangentialGradient F f) U := by
        have hfun : tangentialGradient F f = fun x ↦
            gradient f x - inner ℝ (chartNormal F x) (gradient f x) • chartNormal F x := by
          funext x
          exact tangentialProj_apply F x _
        rw [hfun]
        exact hgf.continuousOn.sub ((hN.inner (𝕜 := ℝ) hgf.continuousOn).smul hN)
      exact hδf.inner hδg.continuousOn
    · intro x hx
      simp [tangentialGradient, hdf x hx]
  have hc1 : HasCompactSupport fun x ↦ f x * tangentialLaplacian F g x :=
    hfc.mul_right
  have hc2 : HasCompactSupport fun x ↦
      inner ℝ (tangentialGradient F f x) (tangentialGradient F g x) := by
    apply hfc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra hxf
    apply hx
    simp [tangentialGradient, hdf x hxf]
  have hint1 := hcont1.integrable_of_hasCompactSupport (μ := μ.restrict U) hc1
  have hint2 := hcont2.integrable_of_hasCompactSupport (μ := μ.restrict U) hc2
  have hsum : ∫ x in U, tangentialDivergence F (fun x ↦ f x • tangentialGradient F g x) x ∂μ =
      ∫ x in U, f x * tangentialLaplacian F g x ∂μ +
        ∫ x in U, inner ℝ (tangentialGradient F f x) (tangentialGradient F g x) ∂μ := by
    rw [← integral_add hint1 hint2]
    exact setIntegral_congr_fun h.isOpen.measurableSet hpt
  rw [hfv] at hsum
  linarith

end IsSmoothBoundaryChart

end SerrinEpigraph
