module

public import SerrinEpigraph.SecondVariation

/-!
# Commutator, Codazzi, Jacobi and Simons identities on smooth boundary charts

Ambient second-order calculus (Leon Simon's tangential-derivative formalism) on a smooth boundary
chart `(E, U, F)`, with `ν = ∇F/|∇F|`, `P = I - ν ⊗ ν`, `δ = P ∇` and `A = P Dν P` as in
`SerrinEpigraph.SmoothBoundaryChart`. All identities hold pointwise on the chart (on every level set
of `F`); they are specialized to the boundary piece `M = U ∩ {F = 0}` under the hypothesis
`H = 0` on `M`, which `IsSmoothBoundaryChart.meanCurvature_eq_zero` provides for perimeter minimizers.

## Main definitions
* `tangentialHessian F f y = D(δ f)(y) ∘ P`, with entries `⟪bⱼ, Q_f bᵢ⟫ = δᵢ δⱼ f` and
  `Δ_M f = tr Q_f` (`tangentialLaplacian_eq_trace_tangentialHessian`).
* `derivSecondFundamentalForm F y w z = D(x ↦ A(x) z)(P w)`, the ambient tangential derivative of `A`.
* `sqNormCovDerivSecondFundamentalForm F y = |∇_M A|² = ∑ₖ ∑ᵢ ‖P ((δ_{bₖ} A)(P bᵢ))‖²`.

## Main results
* Commutator formula `inner_tangentialHessian_sub`:
  `δᵢ δⱼ f - δⱼ δᵢ f = νᵢ (A δf)ⱼ - νⱼ (A δf)ᵢ`; `tangentialGradient_inner_chartNormal`
  (`δ ⟪ν, w⟫ = A w`); Codazzi `fderiv_inner_secondFundamentalForm_comm`.
* Jacobi: `tangentialLaplacian_inner_chartNormal` (`Δ_M ⟪ν, e⟫ = ⟪δH, e⟫ - |A|² ⟪ν, e⟫` on the chart),
  `tangentialLaplacian_inner_chartNormal_eq_neg` (`Δ_M ⟪ν, e⟫ = -|A|² ⟪ν, e⟫` on `M`), and the weak
  form for minimizers `integral_inner_tangentialGradient_inner_chartNormal`.
* Product/linearity rules (`tangentialLaplacian_mul`, `tangentialLaplacian_sum`, ...), the
  commutation `tangentialLaplacian_inner_tangentialGradient` of `Δ_M` with `δ`, and the Bochner
  formula `tangentialLaplacian_norm_sq_tangentialGradient`.
* `sum_norm_sq_derivSecondFundamentalForm`: ambient versus covariant derivative of `A`.
* **Simons' identity** `tangentialLaplacian_sqNormSecondFundamentalForm`:
  `½ Δ_M |A|² = |∇_M A|² - |A|⁴` on `M`.
* **Kato inequality** `norm_sq_tangentialGradient_sqNormSecondFundamentalForm_le`
  (`‖δ|A|²‖² ≤ 4 |A|² |∇_M A|²`) and `norm_sq_tangentialGradient_sqrt_sqNormSecondFundamentalForm_le`
  (`|δ|A||² ≤ |∇_M A|²` where `|A| > 0`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff

namespace SerrinEpigraph

/-! ### Hessians of general functions -/

section Hessian

variable {d : ℕ}

theorem differentiableAt_gradient_of_contDiffAt {f : Space d → ℝ} {y : Space d}
    (hf : ContDiffAt ℝ 2 f y) : DifferentiableAt ℝ (gradient f) y := by
  have h1 : ContDiffAt ℝ 1 (fun x ↦ (toDual ℝ (Space d)).symm (fderiv ℝ f x)) y :=
    (toDual ℝ (Space d)).symm.contDiff.contDiffAt.comp y (hf.fderiv_right (m := 1) (by norm_num))
  exact h1.differentiableAt (by simp)

/-- The Hessian operator `D(∇f)` of a `C²` function is symmetric. -/
theorem inner_fderiv_gradient_comm {f : Space d → ℝ} {y : Space d} (hf : ContDiffAt ℝ 2 f y)
    (u w : Space d) :
    inner ℝ (fderiv ℝ (gradient f) y u) w = inner ℝ u (fderiv ℝ (gradient f) y w) := by
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hG := (differentiableAt_gradient_of_contDiffAt hf).hasFDerivAt
  have key (v : Space d) (z : Space d) :
      inner ℝ (fderiv ℝ (gradient f) y z) v = fderiv ℝ (fderiv ℝ f) y z v := by
    have h1 : HasFDerivAt (fun x ↦ inner ℝ v (gradient f x))
        ((innerSL ℝ v).comp (fderiv ℝ (gradient f) y)) y :=
      (innerSL ℝ v).hasFDerivAt.comp y hG
    have h2 : HasFDerivAt (fun x ↦ fderiv ℝ f x v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) y)) y :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hD1.hasFDerivAt
    have hfun : (fun x ↦ inner ℝ v (gradient f x)) = fun x ↦ fderiv ℝ f x v := by
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

end Hessian

/-! ### The tangential Hessian and the commutator formula -/

/-- The tangential Hessian `Q_f = D(δ f) ∘ P`: its entries `⟪bⱼ, Q_f bᵢ⟫` are the iterated
tangential derivatives `δᵢ δⱼ f`. -/
def tangentialHessian {d : ℕ} (F f : Space d → ℝ) (y : Space d) : Space d →L[ℝ] Space d :=
  fderiv ℝ (tangentialGradient F f) y ∘L tangentialProj F y

/-- `Δ_M f = tr Q_f`. -/
theorem tangentialLaplacian_eq_trace_tangentialHessian {d : ℕ} (F f : Space d → ℝ)
    (y : Space d) :
    tangentialLaplacian F f y =
      LinearMap.trace ℝ (Space d) (tangentialHessian F f y).toLinearMap := by
  have hP : tangentialProj F y = ContinuousLinearMap.id ℝ (Space d) -
      (innerSL ℝ (chartNormal F y)).smulRight (chartNormal F y) := rfl
  rw [tangentialHessian, hP, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
    trace_clm_sub, trace_comp_rankOne]
  rfl

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

theorem contDiffOn_meanCurvature (h : IsSmoothBoundaryChart E U F) :
    ContDiffOn ℝ ∞ (meanCurvature F) U := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hfun : meanCurvature F = fun x ↦ ∑ i, inner ℝ (b i) (fderiv ℝ (chartNormal F) x (b i)) :=
    funext fun x ↦ meanCurvature_eq_fieldDivergence b F x
  rw [hfun]
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (chartNormal F)) U :=
    h.contDiffOn_chartNormal.fderiv_of_isOpen h.isOpen (m := ∞) (by simp)
  exact ContDiffOn.sum fun i _ ↦ contDiffOn_const.inner ℝ (hD.clm_apply contDiffOn_const)

theorem contDiffOn_inner_chartNormal (h : IsSmoothBoundaryChart E U F) (w : Space d) :
    ContDiffOn ℝ ∞ (fun x ↦ inner ℝ (chartNormal F x) w) U :=
  h.contDiffOn_chartNormal.inner ℝ contDiffOn_const

/-- Derivative of the tangential gradient:
`D(δ f) w = P (D²f w) - ⟪Dν w, ∇f⟫ ν - ⟪ν, ∇f⟫ Dν w`. -/
theorem fderiv_tangentialGradient_apply (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {f : Space d → ℝ} (hf : ContDiffAt ℝ 2 f y) (w : Space d) :
    fderiv ℝ (tangentialGradient F f) y w =
      tangentialProj F y (fderiv ℝ (gradient f) y w) -
        inner ℝ (fderiv ℝ (chartNormal F) y w) (gradient f y) • chartNormal F y -
          inner ℝ (chartNormal F y) (gradient f y) • fderiv ℝ (chartNormal F) y w := by
  have hG := (differentiableAt_gradient_of_contDiffAt hf).hasFDerivAt
  have hN := (h.differentiableAt_chartNormal hy).hasFDerivAt
  have hfun : tangentialGradient F f =
      gradient f - (fun x ↦ inner ℝ (chartNormal F x) (gradient f x)) • chartNormal F :=
    funext fun x ↦ tangentialProj_apply F x _
  have hd := hG.sub ((hN.inner ℝ hG).smul hN)
  rw [hfun, hd.fderiv]
  simp only [FunLike.coe_sub, Pi.sub_apply, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, tangentialProj_apply, add_smul]
  abel

theorem tangentialHessian_apply (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {f : Space d → ℝ} (hf : ContDiffAt ℝ 2 f y) (w : Space d) :
    tangentialHessian F f y w =
      tangentialProj F y (fderiv ℝ (gradient f) y (tangentialProj F y w)) -
        inner ℝ (secondFundamentalForm F y w) (gradient f y) • chartNormal F y -
          inner ℝ (chartNormal F y) (gradient f y) • secondFundamentalForm F y w := by
  rw [tangentialHessian, ContinuousLinearMap.comp_apply, h.fderiv_tangentialGradient_apply hy hf,
    ← h.secondFundamentalForm_apply hy]

theorem secondFundamentalForm_tangentialProj (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    secondFundamentalForm F y (tangentialProj F y w) = secondFundamentalForm F y w := by
  rw [h.secondFundamentalForm_apply hy, h.secondFundamentalForm_apply hy,
    tangentialProj_tangentialProj (h.gradient_ne_zero y hy)]

theorem secondFundamentalForm_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    secondFundamentalForm F y (chartNormal F y) = 0 := by
  rw [h.secondFundamentalForm_apply hy, tangentialProj_chartNormal (h.gradient_ne_zero y hy),
    map_zero]

theorem inner_chartNormal_secondFundamentalForm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) : inner ℝ (chartNormal F y) (secondFundamentalForm F y w) = 0 := by
  rw [h.secondFundamentalForm_apply hy]
  exact h.inner_chartNormal_fderiv_chartNormal hy _

/-- **Commutator formula.** For a `C²` function `f`,
`⟪w', Q_f w⟫ - ⟪w, Q_f w'⟫ = ⟪ν, w⟫ ⟪w', A δf⟫ - ⟪ν, w'⟫ ⟪w, A δf⟫`; in coordinates
`δᵢ δⱼ f - δⱼ δᵢ f = νᵢ (A δf)ⱼ - νⱼ (A δf)ᵢ`. -/
theorem inner_tangentialHessian_sub (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {f : Space d → ℝ} (hf : ContDiffAt ℝ 2 f y) (w w' : Space d) :
    inner ℝ w' (tangentialHessian F f y w) - inner ℝ w (tangentialHessian F f y w') =
      inner ℝ (chartNormal F y) w *
          inner ℝ w' (secondFundamentalForm F y (tangentialGradient F f y)) -
        inner ℝ (chartNormal F y) w' *
          inner ℝ w (secondFundamentalForm F y (tangentialGradient F f y)) := by
  have hne := h.gradient_ne_zero y hy
  have hAg (z : Space d) : inner ℝ (secondFundamentalForm F y z) (gradient f y) =
      inner ℝ z (secondFundamentalForm F y (tangentialGradient F f y)) := by
    rw [h.inner_secondFundamentalForm_comm hy, tangentialGradient,
      h.secondFundamentalForm_tangentialProj hy]
  have hHs : inner ℝ w' (tangentialProj F y (fderiv ℝ (gradient f) y (tangentialProj F y w))) =
      inner ℝ w (tangentialProj F y (fderiv ℝ (gradient f) y (tangentialProj F y w'))) := by
    rw [← inner_tangentialProj_left, ← inner_tangentialProj_left,
      ← inner_fderiv_gradient_comm hf, real_inner_comm]
  have hAs : inner ℝ w' (secondFundamentalForm F y w) =
      inner ℝ w (secondFundamentalForm F y w') := by
    rw [← h.inner_secondFundamentalForm_comm hy, real_inner_comm]
  rw [h.tangentialHessian_apply hy hf, h.tangentialHessian_apply hy hf]
  simp only [inner_sub_right, real_inner_smul_right, hAg]
  rw [hHs, hAs, real_inner_comm w' (chartNormal F y), real_inner_comm w (chartNormal F y)]
  ring

/-- The tangential gradient of a normal component: `δ ⟪ν, w⟫ = A w`. -/
theorem tangentialGradient_inner_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) w) y = secondFundamentalForm F y w := by
  have hN := (h.differentiableAt_chartNormal hy).hasFDerivAt
  have hu : HasFDerivAt (fun x ↦ inner ℝ (chartNormal F x) w)
      ((fderivInnerCLM ℝ (chartNormal F y, w)).comp
        ((fderiv ℝ (chartNormal F) y).prod (0 : Space d →L[ℝ] Space d))) y :=
    hN.inner ℝ (hasFDerivAt_const w y)
  apply ext_inner_right ℝ
  intro z
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left, hu.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, fderivInnerCLM_apply, inner_zero_right, zero_add]
  rw [← h.secondFundamentalForm_apply hy, h.inner_secondFundamentalForm_comm hy, real_inner_comm]

theorem differentiableAt_tangentialGradient (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {g : Space d → ℝ} (hg : ContDiffOn ℝ 2 g U) :
    DifferentiableAt ℝ (tangentialGradient F g) y :=
  ((h.contDiffOn_tangentialGradient (n := 1) hg).differentiableOn one_ne_zero y hy).differentiableAt
    (h.isOpen.mem_nhds hy)

theorem fderiv_inner_tangentialGradient (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {g : Space d → ℝ} (hg : ContDiffOn ℝ 2 g U) (c v : Space d) :
    fderiv ℝ (fun x ↦ inner ℝ c (tangentialGradient F g x)) y v =
      inner ℝ c (fderiv ℝ (tangentialGradient F g) y v) := by
  have hd := (innerSL ℝ c).hasFDerivAt.comp y (h.differentiableAt_tangentialGradient hy hg).hasFDerivAt
  rw [show (fun x ↦ inner ℝ c (tangentialGradient F g x)) =
      (innerSL ℝ c) ∘ tangentialGradient F g from rfl, hd.fderiv]
  rfl

theorem tangentialHessian_apply_of_inner_eq_zero (F f : Space d → ℝ) (y : Space d)
    {v : Space d} (hv : inner ℝ (chartNormal F y) v = 0) :
    tangentialHessian F f y v = fderiv ℝ (tangentialGradient F f) y v := by
  rw [tangentialHessian, ContinuousLinearMap.comp_apply, tangentialProj_eq_self_of_inner_eq_zero hv]

/-- **Codazzi equation.** For `w, z'` tangent at `y`,
`D⟪z', A z⟫ (w) = D⟪w, A z⟫ (z')`; with the symmetry of `A` this says that `∇A` is totally
symmetric on tangent vectors. -/
theorem fderiv_inner_secondFundamentalForm_comm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {w z' : Space d} (hw : inner ℝ (chartNormal F y) w = 0)
    (hz' : inner ℝ (chartNormal F y) z' = 0) (z : Space d) :
    fderiv ℝ (fun x ↦ inner ℝ z' (secondFundamentalForm F x z)) y w =
      fderiv ℝ (fun x ↦ inner ℝ w (secondFundamentalForm F x z)) y z' := by
  have hu2 : ContDiffOn ℝ 2 (fun x ↦ inner ℝ (chartNormal F x) z) U :=
    (h.contDiffOn_inner_chartNormal z).of_le (by simp)
  have huAt : ContDiffAt ℝ 2 (fun x ↦ inner ℝ (chartNormal F x) z) y :=
    hu2.contDiffAt (h.isOpen.mem_nhds hy)
  have heq (c : Space d) : (fun x ↦ inner ℝ c (secondFundamentalForm F x z)) =ᶠ[𝓝 y]
      fun x ↦ inner ℝ c (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) z) x) := by
    filter_upwards [h.isOpen.mem_nhds hy] with x hx
    rw [h.tangentialGradient_inner_chartNormal hx]
  rw [(heq z').fderiv_eq, (heq w).fderiv_eq, h.fderiv_inner_tangentialGradient hy hu2,
    h.fderiv_inner_tangentialGradient hy hu2,
    ← tangentialHessian_apply_of_inner_eq_zero F _ y hw,
    ← tangentialHessian_apply_of_inner_eq_zero F _ y hz']
  have hc := h.inner_tangentialHessian_sub hy huAt w z'
  rw [hw, hz', zero_mul, zero_mul, sub_zero] at hc
  linarith

/-- The second fundamental form satisfies `∑ᵢ ⟪bᵢ, A (A bᵢ)⟫ = |A|²`. -/
theorem sum_inner_secondFundamentalForm_sq (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space d)) :
    ∑ i, inner ℝ (b i) (secondFundamentalForm F y (secondFundamentalForm F y (b i))) =
      sqNormSecondFundamentalForm F y := by
  rw [sqNormSecondFundamentalForm, h.adjoint_secondFundamentalForm hy,
    LinearMap.trace_eq_sum_inner _ b]
  rfl

theorem sum_inner_secondFundamentalForm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space d)) :
    ∑ i, inner ℝ (b i) (secondFundamentalForm F y (b i)) = meanCurvature F y := by
  rw [h.meanCurvature_eq_trace_secondFundamentalForm hy, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- **Jacobi identity for the normal** (on the whole chart):
`Δ_M ⟪ν, e⟫ = ⟪δH, e⟫ - |A|² ⟪ν, e⟫`. -/
theorem tangentialLaplacian_inner_chartNormal (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (e : Space d) :
    tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) e) y =
      inner ℝ (tangentialGradient F (meanCurvature F) y) e -
        sqNormSecondFundamentalForm F y * inner ℝ (chartNormal F y) e := by
  have hne := h.gradient_ne_zero y hy
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hu2 : ContDiffOn ℝ 2 (fun x ↦ inner ℝ (chartNormal F x) e) U :=
    (h.contDiffOn_inner_chartNormal e).of_le (by simp)
  have hν2 (i : Fin d) : ContDiffOn ℝ 2 (fun x ↦ inner ℝ (chartNormal F x) (b i)) U :=
    (h.contDiffOn_inner_chartNormal (b i)).of_le (by simp)
  have hνAt (i : Fin d) : ContDiffAt ℝ 2 (fun x ↦ inner ℝ (chartNormal F x) (b i)) y :=
    (hν2 i).contDiffAt (h.isOpen.mem_nhds hy)
  -- step A: exchange the roles of `e` and `bᵢ`
  have hA (i : Fin d) :
      inner ℝ (b i) (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) e) y (b i)) =
        inner ℝ e (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y (b i)) := by
    have heq : (fun x ↦ inner ℝ (b i)
          (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) e) x)) =ᶠ[𝓝 y]
        fun x ↦ inner ℝ e (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) x) := by
      filter_upwards [h.isOpen.mem_nhds hy] with x hx
      rw [h.tangentialGradient_inner_chartNormal hx, h.tangentialGradient_inner_chartNormal hx,
        ← h.inner_secondFundamentalForm_comm hx, real_inner_comm]
    simp only [tangentialHessian, ContinuousLinearMap.comp_apply]
    rw [← h.fderiv_inner_tangentialGradient hy hu2, heq.fderiv_eq,
      h.fderiv_inner_tangentialGradient hy (hν2 i)]
  -- step B: the commutator formula for the components `νᵢ`
  have hB (i : Fin d) :
      inner ℝ e (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y (b i)) =
        inner ℝ (b i) (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y e) +
          inner ℝ (chartNormal F y) (b i) *
            inner ℝ e (secondFundamentalForm F y (secondFundamentalForm F y (b i))) -
          inner ℝ (chartNormal F y) e *
            inner ℝ (b i) (secondFundamentalForm F y (secondFundamentalForm F y (b i))) := by
    have hc := h.inner_tangentialHessian_sub hy (hνAt i) (b i) e
    rw [h.tangentialGradient_inner_chartNormal hy] at hc
    linarith
  -- step C: the trace of the commuted terms is the tangential derivative of `H`
  have hC : ∑ i, inner ℝ (b i)
      (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y e) =
        inner ℝ (tangentialGradient F (meanCurvature F) y) e := by
    have hterm (i : Fin d) : inner ℝ (b i)
        (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y e) =
          fderiv ℝ (fun x ↦ inner ℝ (b i)
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) x)) y
              (tangentialProj F y e) := by
      rw [h.fderiv_inner_tangentialGradient hy (hν2 i)]
      rfl
    have hdiff (i : Fin d) : HasFDerivAt (fun x ↦ inner ℝ (b i)
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) x))
          ((innerSL ℝ (b i)).comp (fderiv ℝ
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y)) y :=
      (innerSL ℝ (b i)).hasFDerivAt.comp y
        (h.differentiableAt_tangentialGradient hy (hν2 i)).hasFDerivAt
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hdiff i
    have hH : (fun x ↦ ∑ i ∈ Finset.univ, inner ℝ (b i)
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) x)) =ᶠ[𝓝 y]
          meanCurvature F := by
      filter_upwards [h.isOpen.mem_nhds hy] with x hx
      simp only [h.tangentialGradient_inner_chartNormal hx]
      exact h.sum_inner_secondFundamentalForm hx b
    have hHd : HasFDerivAt (meanCurvature F) (∑ i ∈ Finset.univ, (innerSL ℝ (b i)).comp (fderiv ℝ
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y)) y :=
      hsum.congr_of_eventuallyEq hH.symm
    calc ∑ i, inner ℝ (b i)
          (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y e)
        = ∑ i, ((innerSL ℝ (b i)).comp (fderiv ℝ
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y))
              (tangentialProj F y e) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hterm i, (hdiff i).fderiv]
      _ = (∑ i ∈ Finset.univ, (innerSL ℝ (b i)).comp (fderiv ℝ
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y))
              (tangentialProj F y e) := by
          rw [sum_apply]
      _ = fderiv ℝ (meanCurvature F) y (tangentialProj F y e) := by rw [hHd.fderiv]
      _ = inner ℝ (tangentialGradient F (meanCurvature F) y) e := by
          rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left]
  -- step D: the normal terms cancel since `A ν = 0`
  have hD : ∑ i, inner ℝ (chartNormal F y) (b i) *
      inner ℝ e (secondFundamentalForm F y (secondFundamentalForm F y (b i))) = 0 := by
    have h1 : ∑ i, inner ℝ (chartNormal F y) (b i) *
        inner ℝ e (secondFundamentalForm F y (secondFundamentalForm F y (b i))) =
          inner ℝ e (secondFundamentalForm F y (secondFundamentalForm F y
            (∑ i, inner ℝ (b i) (chartNormal F y) • b i))) := by
      simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, real_inner_comm]
    rw [h1, b.sum_repr', h.secondFundamentalForm_chartNormal hy, map_zero, inner_zero_right]
  -- assemble
  rw [tangentialLaplacian_eq_trace_tangentialHessian, LinearMap.trace_eq_sum_inner _ b]
  change ∑ i, inner ℝ (b i)
      (tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) e) y (b i)) = _
  simp_rw [hA, hB]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hC, hD, ← Finset.mul_sum,
    h.sum_inner_secondFundamentalForm_sq hy b]
  ring

/-- **Jacobi identity on the minimal boundary.** If the mean curvature vanishes on
`M = U ∩ {F = 0}`, then at every point of `M`, `Δ_M ⟪ν, e⟫ = -|A|² ⟪ν, e⟫`. -/
theorem tangentialLaplacian_inner_chartNormal_eq_neg (h : IsSmoothBoundaryChart E U F)
    (hH : ∀ z ∈ U, F z = 0 → meanCurvature F z = 0) (hy : y ∈ U) (hFy : F y = 0)
    (e : Space d) :
    tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) e) y =
      -(sqNormSecondFundamentalForm F y * inner ℝ (chartNormal F y) e) := by
  rw [h.tangentialLaplacian_inner_chartNormal hy,
    h.tangentialGradient_eq_zero_of_eq_zero_on_level (h.contDiffOn_meanCurvature.of_le (by simp))
      hH hy hFy, inner_zero_left, zero_sub]

end IsSmoothBoundaryChart

/-! ### The weak Jacobi equation for perimeter minimizers -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E U Ω : Set (Space d)}
  {F : Space d → ℝ} {μ : Measure (Space d)} {ν : Space d → Space d}

/-- **Weak Jacobi equation.** For a perimeter minimizer with a smooth chart and every `C¹`
function `ζ` compactly supported in the chart,
`∫_M ⟪δζ, δ⟪ν, e⟫⟫ dμ = ∫_M ζ |A|² ⟪ν, e⟫ dμ`. -/
theorem integral_inner_tangentialGradient_inner_chartNormal (h : IsSmoothBoundaryChart E U F)
    (hE : MeasurableSet E) (hp : IsPerimeterPolarOn b E Ω μ ν)
    (hmin : IsPerimeterMinimizingIn b E Ω) (hUΩ : U ⊆ Ω) {ζ : Space d → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) (e : Space d) :
    ∫ x in U, inner ℝ (tangentialGradient F ζ x)
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) e) x) ∂μ =
      ∫ x in U, ζ x * sqNormSecondFundamentalForm F x * inner ℝ (chartNormal F x) e ∂μ := by
  have hu2 : ContDiffOn ℝ 2 (fun x ↦ inner ℝ (chartNormal F x) e) U :=
    (h.contDiffOn_inner_chartNormal e).of_le (by simp)
  rw [h.integral_inner_tangentialGradient_eq_neg hE hp hmin hUΩ hζ hζc hζU hu2, ← integral_neg]
  refine integral_congr_ae ?_
  have hH : ∀ z ∈ U, F z = 0 → meanCurvature F z = 0 :=
    fun z hz hFz ↦ h.meanCurvature_eq_zero hE hp hmin hUΩ hz hFz
  filter_upwards [h.ae_restrict_eq_zero hp hUΩ, ae_restrict_mem h.isOpen.measurableSet]
    with x hFx hxU
  rw [h.tangentialLaplacian_inner_chartNormal_eq_neg hH hxU hFx]
  ring

end IsSmoothBoundaryChart

/-! ### Algebra of the tangential gradient and Laplacian -/

section TangentialAlgebra

variable {d : ℕ}

theorem tangentialGradient_eventuallyEq (F : Space d → ℝ) {f g : Space d → ℝ} {y : Space d}
    (heq : f =ᶠ[𝓝 y] g) : tangentialGradient F f =ᶠ[𝓝 y] tangentialGradient F g := by
  filter_upwards [heq.eventuallyEq_nhds] with x hx
  simp only [tangentialGradient, gradient, hx.fderiv_eq]

theorem tangentialLaplacian_congr (F : Space d → ℝ) {f g : Space d → ℝ} {y : Space d}
    (heq : f =ᶠ[𝓝 y] g) : tangentialLaplacian F f y = tangentialLaplacian F g y := by
  simp only [tangentialLaplacian, tangentialDivergence,
    (tangentialGradient_eventuallyEq F heq).fderiv_eq]

theorem tangentialDivergence_congr (F : Space d → ℝ) {X Y : Space d → Space d} {y : Space d}
    (heq : X =ᶠ[𝓝 y] Y) : tangentialDivergence F X y = tangentialDivergence F Y y := by
  simp only [tangentialDivergence, heq.fderiv_eq]

theorem tangentialGradient_sum (F : Space d → ℝ) {ι : Type*} (s : Finset ι)
    {φ : ι → Space d → ℝ} {x : Space d} (hφ : ∀ i ∈ s, DifferentiableAt ℝ (φ i) x) :
    tangentialGradient F (fun x ↦ ∑ i ∈ s, φ i x) x = ∑ i ∈ s, tangentialGradient F (φ i) x := by
  apply ext_inner_right ℝ
  intro z
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left,
    (HasFDerivAt.fun_sum fun i hi ↦ (hφ i hi).hasFDerivAt).fderiv, sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left]

theorem tangentialGradient_mul (F : Space d → ℝ) {φ ψ : Space d → ℝ} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    tangentialGradient F (fun x ↦ φ x * ψ x) x =
      φ x • tangentialGradient F ψ x + ψ x • tangentialGradient F φ x := by
  apply ext_inner_right ℝ
  intro z
  have hd : HasFDerivAt (fun x ↦ φ x * ψ x) (φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x) x :=
    hφ.hasFDerivAt.mul hψ.hasFDerivAt
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left, hd.fderiv,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, tangentialGradient,
    tangentialGradient, inner_tangentialProj_left, inner_tangentialProj_left, inner_gradient_left,
    inner_gradient_left]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem tangentialGradient_const_mul (F : Space d → ℝ) (a : ℝ) {φ : Space d → ℝ} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) :
    tangentialGradient F (fun x ↦ a * φ x) x = a • tangentialGradient F φ x := by
  rw [tangentialGradient_mul F (differentiableAt_const a) hφ]
  have h0 : tangentialGradient F (fun _ ↦ a) x = 0 := by
    simp [tangentialGradient, gradient]
  rw [h0, smul_zero, add_zero]

theorem tangentialDivergence_add (F : Space d → ℝ) {X Y : Space d → Space d} {y : Space d}
    (hX : DifferentiableAt ℝ X y) (hY : DifferentiableAt ℝ Y y) :
    tangentialDivergence F (fun x ↦ X x + Y x) y =
      tangentialDivergence F X y + tangentialDivergence F Y y := by
  have hd : fderiv ℝ (fun x ↦ X x + Y x) y = fderiv ℝ X y + fderiv ℝ Y y :=
    (hX.hasFDerivAt.add hY.hasFDerivAt).fderiv
  rw [tangentialDivergence, tangentialDivergence, tangentialDivergence, hd, trace_clm_add]
  simp only [FunLike.coe_add, Pi.add_apply, inner_add_right]
  ring

end TangentialAlgebra

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

theorem contDiffOn_tangentialGradient_smooth (h : IsSmoothBoundaryChart E U F)
    {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (tangentialGradient F f) U := by
  have hG : ContDiffOn ℝ ∞ (gradient f) U :=
    (toDual ℝ (Space d)).symm.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen h.isOpen (m := ∞) (by simp))
  have hN := h.contDiffOn_chartNormal
  have hfun : tangentialGradient F f = fun x ↦
      gradient f x - inner ℝ (chartNormal F x) (gradient f x) • chartNormal F x :=
    funext fun x ↦ tangentialProj_apply F x _
  rw [hfun]
  exact hG.sub ((hN.inner ℝ hG).smul hN)

theorem contDiffOn_tangentialDivergence_smooth (h : IsSmoothBoundaryChart E U F)
    {X : Space d → Space d} (hX : ContDiffOn ℝ ∞ X U) :
    ContDiffOn ℝ ∞ (tangentialDivergence F X) U := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ X) U := hX.fderiv_of_isOpen h.isOpen (m := ∞) (by simp)
  have hN := h.contDiffOn_chartNormal
  have hfun : tangentialDivergence F X = fun x ↦
      (∑ i, inner ℝ (b i) (fderiv ℝ X x (b i))) -
        inner ℝ (chartNormal F x) (fderiv ℝ X x (chartNormal F x)) := by
    funext x
    rw [tangentialDivergence, ← fieldDivergence_eq_trace b]
    rfl
  rw [hfun]
  exact (ContDiffOn.sum fun i _ ↦ contDiffOn_const.inner ℝ (hD.clm_apply contDiffOn_const)).sub
    (hN.inner ℝ (hD.clm_apply hN))

theorem contDiffOn_tangentialLaplacian (h : IsSmoothBoundaryChart E U F) {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (tangentialLaplacian F f) U :=
  h.contDiffOn_tangentialDivergence_smooth (h.contDiffOn_tangentialGradient_smooth hf)

theorem differentiableAt_of_contDiffOn (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space d → G}
    {n : ℕ∞ω} (hf : ContDiffOn ℝ n f U) (hn : n ≠ 0) : DifferentiableAt ℝ f y :=
  (hf.differentiableOn hn y hy).differentiableAt (h.isOpen.mem_nhds hy)

/-- Linearity of `Δ_M` over finite sums. -/
theorem tangentialLaplacian_sum (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) {ι : Type*}
    (s : Finset ι) {φ : ι → Space d → ℝ} (hφ : ∀ i ∈ s, ContDiffOn ℝ 2 (φ i) U) :
    tangentialLaplacian F (fun x ↦ ∑ i ∈ s, φ i x) y = ∑ i ∈ s, tangentialLaplacian F (φ i) y := by
  have heq : tangentialGradient F (fun x ↦ ∑ i ∈ s, φ i x) =ᶠ[𝓝 y]
      fun x ↦ ∑ i ∈ s, tangentialGradient F (φ i) x := by
    filter_upwards [h.isOpen.mem_nhds hy] with x hx
    exact tangentialGradient_sum F s fun i hi ↦
      h.differentiableAt_of_contDiffOn hx (hφ i hi) (by simp)
  have hd : HasFDerivAt (fun x ↦ ∑ i ∈ s, tangentialGradient F (φ i) x)
      (∑ i ∈ s, fderiv ℝ (tangentialGradient F (φ i)) y) y :=
    HasFDerivAt.fun_sum fun i hi ↦ (h.differentiableAt_tangentialGradient hy (hφ i hi)).hasFDerivAt
  simp only [tangentialLaplacian, tangentialDivergence, heq.fderiv_eq, hd.fderiv,
    ContinuousLinearMap.toLinearMap_sum, map_sum, sum_apply, inner_sum, Finset.sum_sub_distrib]

theorem tangentialLaplacian_const_mul (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (a : ℝ)
    {φ : Space d → ℝ} (hφ : ContDiffOn ℝ 2 φ U) :
    tangentialLaplacian F (fun x ↦ a * φ x) y = a * tangentialLaplacian F φ y := by
  have heq : tangentialGradient F (fun x ↦ a * φ x) =ᶠ[𝓝 y]
      fun x ↦ a • tangentialGradient F φ x := by
    filter_upwards [h.isOpen.mem_nhds hy] with x hx
    exact tangentialGradient_const_mul F a (h.differentiableAt_of_contDiffOn hx hφ (by simp))
  have hd : HasFDerivAt (fun x ↦ a • tangentialGradient F φ x)
      (a • fderiv ℝ (tangentialGradient F φ) y) y :=
    (h.differentiableAt_tangentialGradient hy hφ).hasFDerivAt.const_smul a
  rw [tangentialLaplacian, tangentialDivergence_congr F heq, tangentialDivergence, hd.fderiv,
    trace_clm_smul, tangentialLaplacian, tangentialDivergence]
  simp only [FunLike.coe_smul, Pi.smul_apply, real_inner_smul_right]
  ring

/-- Product rule `Δ_M (φ ψ) = φ Δ_M ψ + ψ Δ_M φ + 2 ⟪δφ, δψ⟫`. -/
theorem tangentialLaplacian_mul (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {φ ψ : Space d → ℝ} (hφ : ContDiffOn ℝ 2 φ U) (hψ : ContDiffOn ℝ 2 ψ U) :
    tangentialLaplacian F (fun x ↦ φ x * ψ x) y =
      φ y * tangentialLaplacian F ψ y + ψ y * tangentialLaplacian F φ y +
        2 * inner ℝ (tangentialGradient F φ y) (tangentialGradient F ψ y) := by
  have hne := h.gradient_ne_zero y hy
  have heq : tangentialGradient F (fun x ↦ φ x * ψ x) =ᶠ[𝓝 y]
      fun x ↦ φ x • tangentialGradient F ψ x + ψ x • tangentialGradient F φ x := by
    filter_upwards [h.isOpen.mem_nhds hy] with x hx
    exact tangentialGradient_mul F (h.differentiableAt_of_contDiffOn hx hφ (by simp))
      (h.differentiableAt_of_contDiffOn hx hψ (by simp))
  have hφd := h.differentiableAt_of_contDiffOn hy hφ (by simp)
  have hψd := h.differentiableAt_of_contDiffOn hy hψ (by simp)
  have hδφ := h.differentiableAt_tangentialGradient hy hφ
  have hδψ := h.differentiableAt_tangentialGradient hy hψ
  have hcross (f g : Space d → ℝ) :
      fderiv ℝ f y (tangentialGradient F g y) =
        inner ℝ (tangentialGradient F f y) (tangentialGradient F g y) := by
    rw [← inner_gradient_left, tangentialGradient, tangentialGradient,
      inner_tangentialProj_tangentialProj hne, real_inner_comm, inner_tangentialProj_left,
      real_inner_comm]
  have hX1 : DifferentiableAt ℝ (fun x ↦ φ x • tangentialGradient F ψ x) y := hφd.smul hδψ
  have hX2 : DifferentiableAt ℝ (fun x ↦ ψ x • tangentialGradient F φ x) y := hψd.smul hδφ
  rw [tangentialLaplacian, tangentialDivergence_congr F heq,
    tangentialDivergence_add F hX1 hX2,
    tangentialDivergence_fun_smul hφd hδψ, tangentialDivergence_fun_smul hψd hδφ, tangentialGradient,
    inner_chartNormal_tangentialProj hne, tangentialGradient, inner_chartNormal_tangentialProj hne,
    ← tangentialGradient, ← tangentialGradient, hcross, hcross, ← tangentialLaplacian,
    ← tangentialLaplacian, real_inner_comm (tangentialGradient F ψ y)]
  ring

/-- `⟪c, δ ⟪w, δ f⟫⟫ = ⟪w, Q_f c⟫`: the iterated tangential derivatives are the entries of the
tangential Hessian. -/
theorem inner_tangentialGradient_inner_tangentialGradient (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) {f : Space d → ℝ} (hf : ContDiffOn ℝ 2 f U) (c w : Space d) :
    inner ℝ c (tangentialGradient F (fun x ↦ inner ℝ w (tangentialGradient F f x)) y) =
      inner ℝ w (tangentialHessian F f y c) := by
  rw [tangentialGradient, ← inner_tangentialProj_left, real_inner_comm, inner_gradient_left,
    h.fderiv_inner_tangentialGradient hy hf]
  rfl

/-- The normal component of the tangential Hessian: `⟪ν, Q_f z⟫ = -⟪z, A δf⟫`. -/
theorem inner_chartNormal_tangentialHessian (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    {f : Space d → ℝ} (hf : ContDiffAt ℝ 2 f y) (z : Space d) :
    inner ℝ (chartNormal F y) (tangentialHessian F f y z) =
      -inner ℝ z (secondFundamentalForm F y (tangentialGradient F f y)) := by
  have hne := h.gradient_ne_zero y hy
  rw [h.tangentialHessian_apply hy hf, inner_sub_right, inner_sub_right,
    inner_chartNormal_tangentialProj hne, real_inner_smul_right, real_inner_smul_right,
    inner_chartNormal_self hne, h.inner_chartNormal_secondFundamentalForm hy,
    h.inner_secondFundamentalForm_comm hy, tangentialGradient,
    h.secondFundamentalForm_tangentialProj hy]
  ring

theorem fderiv_tangentialProj_eq_inner (F φ : Space d → ℝ) (y w : Space d) :
    fderiv ℝ φ y (tangentialProj F y w) = inner ℝ (tangentialGradient F φ y) w := by
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left]

/-- **Commuting `Δ_M` with `δ`.** For a smooth `f` on the chart and a vector `c` tangent at `y`,
`Δ_M ⟪c, δf⟫ = ⟪c, δ(Δ_M f)⟫ + H ⟪c, A δf⟫ - 2 ⟪c, A (A δf)⟫`. -/
theorem tangentialLaplacian_inner_tangentialGradient (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f U) {c : Space d}
    (hc : inner ℝ (chartNormal F y) c = 0) :
    tangentialLaplacian F (fun x ↦ inner ℝ c (tangentialGradient F f x)) y =
      inner ℝ c (tangentialGradient F (tangentialLaplacian F f) y) +
        meanCurvature F y * inner ℝ c (secondFundamentalForm F y (tangentialGradient F f y)) -
          2 * inner ℝ c (secondFundamentalForm F y
            (secondFundamentalForm F y (tangentialGradient F f y))) := by
  have hne := h.gradient_ne_zero y hy
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hU := h.isOpen.mem_nhds hy
  have hf2 : ContDiffOn ℝ 2 f U := hf.of_le (by simp)
  have hg : ContDiffOn ℝ ∞ (tangentialGradient F f) U := h.contDiffOn_tangentialGradient_smooth hf
  have hgk (w : Space d) : ContDiffOn ℝ ∞ (fun x ↦ inner ℝ w (tangentialGradient F f x)) U :=
    contDiffOn_const.inner ℝ hg
  have hgk2 (w : Space d) : ContDiffOn ℝ 2 (fun x ↦ inner ℝ w (tangentialGradient F f x)) U :=
    (hgk w).of_le (by simp)
  have hn (w : Space d) : ContDiffOn ℝ ∞ (fun x ↦ inner ℝ (chartNormal F x) w) U :=
    h.contDiffOn_inner_chartNormal w
  have hδn (w : Space d) : ContDiffOn ℝ ∞
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) w)) U :=
    h.contDiffOn_tangentialGradient_smooth (hn w)
  -- differentiability at `y`
  have dg : DifferentiableAt ℝ (tangentialGradient F f) y :=
    h.differentiableAt_of_contDiffOn hy hg (by simp)
  have dn (w : Space d) : DifferentiableAt ℝ (fun x ↦ inner ℝ (chartNormal F x) w) y :=
    h.differentiableAt_of_contDiffOn hy (hn w) (by simp)
  have dδn (w : Space d) : DifferentiableAt ℝ
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) w)) y :=
    h.differentiableAt_of_contDiffOn hy (hδn w) (by simp)
  have dδg (w : Space d) : DifferentiableAt ℝ
      (tangentialGradient F (fun x ↦ inner ℝ w (tangentialGradient F f x))) y :=
    h.differentiableAt_tangentialGradient hy (hgk2 w)
  have dpair (w : Space d) : DifferentiableAt ℝ (fun x ↦ inner ℝ
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) w) x)
      (tangentialGradient F f x)) y := (dδn w).inner ℝ dg
  -- the commuted expression (★), valid on the chart
  have hstar (k : Fin d) : (fun x ↦ inner ℝ (b k)
      (tangentialGradient F (fun x ↦ inner ℝ c (tangentialGradient F f x)) x)) =ᶠ[𝓝 y]
      fun x ↦ inner ℝ c (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) x) +
        inner ℝ (chartNormal F x) (b k) * inner ℝ
          (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
          (tangentialGradient F f x) -
        inner ℝ (chartNormal F x) c * inner ℝ
          (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b k)) x)
          (tangentialGradient F f x) := by
    filter_upwards [hU] with x hx
    have hfx : ContDiffAt ℝ 2 f x := hf2.contDiffAt (h.isOpen.mem_nhds hx)
    have h1 := h.inner_tangentialGradient_inner_tangentialGradient hx hf2 (b k) c
    have h2 := h.inner_tangentialGradient_inner_tangentialGradient hx hf2 c (b k)
    have h3 := h.inner_tangentialHessian_sub hx hfx (b k) c
    rw [h.tangentialGradient_inner_chartNormal hx, h.tangentialGradient_inner_chartNormal hx,
      h.inner_secondFundamentalForm_comm hx, h.inner_secondFundamentalForm_comm hx, h1, h2]
    linarith
  -- derivative of the right-hand side of (★) in the direction `P bₖ`
  have hderiv (k : Fin d) : fderiv ℝ (fun x ↦ inner ℝ (b k)
      (tangentialGradient F (fun x ↦ inner ℝ c (tangentialGradient F f x)) x)) y
        (tangentialProj F y (b k)) =
      inner ℝ c (tangentialHessian F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y (b k)) +
        (inner ℝ (chartNormal F y) (b k) * fderiv ℝ (fun x ↦ inner ℝ
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
            (tangentialGradient F f x)) y (tangentialProj F y (b k)) +
          inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) y)
            (tangentialGradient F f y) * inner ℝ (secondFundamentalForm F y (b k)) (b k)) -
        inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b k)) y)
            (tangentialGradient F f y) * inner ℝ (secondFundamentalForm F y c) (b k) := by
    rw [(hstar k).fderiv_eq]
    have dT1 : DifferentiableAt ℝ (fun x ↦ inner ℝ c
        (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) x)) y :=
      (differentiableAt_const c).inner ℝ (dδg (b k))
    have dT2 : DifferentiableAt ℝ (fun x ↦ inner ℝ (chartNormal F x) (b k) * inner ℝ
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
        (tangentialGradient F f x)) y := (dn (b k)).mul (dpair c)
    have dT3 : DifferentiableAt ℝ (fun x ↦ inner ℝ (chartNormal F x) c * inner ℝ
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b k)) x)
        (tangentialGradient F f x)) y := (dn c).mul (dpair (b k))
    have dT12 : DifferentiableAt ℝ (fun x ↦ inner ℝ c
        (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) x) +
        inner ℝ (chartNormal F x) (b k) * inner ℝ
          (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
          (tangentialGradient F f x)) y := dT1.add dT2
    rw [fderiv_fun_sub dT12 dT3, fderiv_fun_add dT1 dT2,
      fderiv_fun_mul (dn (b k)) (dpair c), fderiv_fun_mul (dn c) (dpair (b k))]
    simp only [FunLike.coe_sub, FunLike.coe_add, FunLike.coe_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [h.fderiv_inner_tangentialGradient hy (hgk2 (b k)), fderiv_tangentialProj_eq_inner,
      fderiv_tangentialProj_eq_inner, fderiv_tangentialProj_eq_inner,
      fderiv_tangentialProj_eq_inner,
      h.tangentialGradient_inner_chartNormal hy, h.tangentialGradient_inner_chartNormal hy, hc,
      zero_mul, zero_add]
    rw [tangentialHessian, ContinuousLinearMap.comp_apply]
  -- sum over `k`
  have hT1 : ∑ k, inner ℝ c
      (tangentialHessian F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y (b k)) =
        inner ℝ c (tangentialGradient F (tangentialLaplacian F f) y) -
          inner ℝ c (secondFundamentalForm F y
            (secondFundamentalForm F y (tangentialGradient F f y))) := by
    -- the commutator formula for each component `⟪bₖ, δf⟫`
    have hcomm (k : Fin d) : inner ℝ c
        (tangentialHessian F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y (b k)) =
          inner ℝ (b k)
            (tangentialHessian F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y c) +
          inner ℝ (chartNormal F y) (b k) * inner ℝ (secondFundamentalForm F y c)
            (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y) := by
      have hcx := h.inner_tangentialHessian_sub hy
        ((hgk2 (b k)).contDiffAt hU) (b k) c
      rw [hc, zero_mul, sub_zero, ← h.inner_secondFundamentalForm_comm hy] at hcx
      linarith
    simp_rw [hcomm]
    rw [Finset.sum_add_distrib]
    -- the trace part is the derivative of `Δ_M f`
    have hA : ∑ k, inner ℝ (b k)
        (tangentialHessian F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y c) =
          inner ℝ c (tangentialGradient F (tangentialLaplacian F f) y) := by
      have hterm (k : Fin d) : inner ℝ (b k)
          (tangentialHessian F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y c) =
            ((innerSL ℝ (b k)).comp (fderiv ℝ (tangentialGradient F
              (fun x ↦ inner ℝ (b k) (tangentialGradient F f x))) y)) (tangentialProj F y c) := by
        rw [tangentialHessian, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          innerSL_apply_apply]
      have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ ↦
        (innerSL ℝ (b k)).hasFDerivAt.comp y (dδg (b k)).hasFDerivAt
      have hL : (fun x ↦ ∑ k ∈ Finset.univ, inner ℝ (b k)
          (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) x)) =ᶠ[𝓝 y]
            tangentialLaplacian F f := by
        filter_upwards [hU] with x hx
        rw [tangentialLaplacian_eq_trace_tangentialHessian, LinearMap.trace_eq_sum_inner _ b]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [h.inner_tangentialGradient_inner_tangentialGradient hx hf2 (b k) (b k)]
        rfl
      have hLd := hsum.congr_of_eventuallyEq hL.symm
      simp_rw [hterm]
      rw [← sum_apply, ← hLd.fderiv, fderiv_tangentialProj_eq_inner, real_inner_comm]
    -- the normal part is `-⟪c, A² δf⟫`
    have hB : ∑ k, inner ℝ (chartNormal F y) (b k) * inner ℝ (secondFundamentalForm F y c)
        (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y) =
          -inner ℝ c (secondFundamentalForm F y
            (secondFundamentalForm F y (tangentialGradient F f y))) := by
      have hterm (k : Fin d) : inner ℝ (secondFundamentalForm F y c)
          (tangentialGradient F (fun x ↦ inner ℝ (b k) (tangentialGradient F f x)) y) =
            inner ℝ (b k) (tangentialHessian F f y (secondFundamentalForm F y c)) :=
        h.inner_tangentialGradient_inner_tangentialGradient hy hf2 _ (b k)
      simp_rw [hterm]
      rw [b.sum_inner_mul_inner, h.inner_chartNormal_tangentialHessian hy (hf2.contDiffAt hU),
        h.inner_secondFundamentalForm_comm hy]
    rw [hA, hB]
    ring
  have hT2 : ∑ k, inner ℝ (chartNormal F y) (b k) * fderiv ℝ (fun x ↦ inner ℝ
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
      (tangentialGradient F f x)) y (tangentialProj F y (b k)) = 0 := by
    have h1 : ∑ k, inner ℝ (chartNormal F y) (b k) * fderiv ℝ (fun x ↦ inner ℝ
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
        (tangentialGradient F f x)) y (tangentialProj F y (b k)) =
          fderiv ℝ (fun x ↦ inner ℝ
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) x)
            (tangentialGradient F f x)) y (tangentialProj F y
              (∑ k, inner ℝ (b k) (chartNormal F y) • b k)) := by
      simp only [map_sum, map_smul, smul_eq_mul, real_inner_comm]
    rw [h1, b.sum_repr', tangentialProj_chartNormal hne, map_zero]
  have hT3 : ∑ k, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) c) y)
      (tangentialGradient F f y) * inner ℝ (secondFundamentalForm F y (b k)) (b k) =
        meanCurvature F y * inner ℝ c (secondFundamentalForm F y (tangentialGradient F f y)) := by
    rw [← Finset.mul_sum, h.tangentialGradient_inner_chartNormal hy,
      h.inner_secondFundamentalForm_comm hy, ← h.sum_inner_secondFundamentalForm hy b]
    simp only [real_inner_comm (b _)]
    ring
  have hT4 : ∑ k, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b k)) y)
      (tangentialGradient F f y) * inner ℝ (secondFundamentalForm F y c) (b k) =
        inner ℝ c (secondFundamentalForm F y
          (secondFundamentalForm F y (tangentialGradient F f y))) := by
    have hterm (k : Fin d) : inner ℝ
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b k)) y)
        (tangentialGradient F f y) * inner ℝ (secondFundamentalForm F y c) (b k) =
          inner ℝ (secondFundamentalForm F y c) (b k) *
            inner ℝ (b k) (secondFundamentalForm F y (tangentialGradient F f y)) := by
      rw [h.tangentialGradient_inner_chartNormal hy, h.inner_secondFundamentalForm_comm hy]
      ring
    simp_rw [hterm]
    rw [b.sum_inner_mul_inner, h.inner_secondFundamentalForm_comm hy]
  -- assemble
  rw [tangentialLaplacian_eq_trace_tangentialHessian, LinearMap.trace_eq_sum_inner _ b]
  have hQ (k : Fin d) : inner ℝ (b k)
      ((tangentialHessian F (fun x ↦ inner ℝ c (tangentialGradient F f x)) y).toLinearMap
        (b k)) =
      fderiv ℝ (fun x ↦ inner ℝ (b k)
        (tangentialGradient F (fun x ↦ inner ℝ c (tangentialGradient F f x)) x)) y
          (tangentialProj F y (b k)) := by
    rw [h.fderiv_inner_tangentialGradient hy (hgk2 c)]
    rfl
  simp_rw [hQ, hderiv]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hT1, hT2, hT3, hT4]
  ring

theorem norm_sq_eq_sum_inner_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space d))
    (v : Space d) : ‖v‖ ^ 2 = ∑ i, inner ℝ (b i) v ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner v v]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, sq]

/-- **Bochner formula** (ambient form) on a chart: for smooth `f`,
`½ Δ_M ‖δf‖² = ∑ₖ ‖Q_f bₖ‖² + ⟪δf, δ(Δ_M f)⟫ + H ⟪δf, A δf⟫ - 2 ⟪δf, A (A δf)⟫`. -/
theorem tangentialLaplacian_norm_sq_tangentialGradient (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    tangentialLaplacian F (fun x ↦ ‖tangentialGradient F f x‖ ^ 2) y / 2 =
      (∑ k, ‖tangentialHessian F f y (EuclideanSpace.basisFun (Fin d) ℝ k)‖ ^ 2) +
        inner ℝ (tangentialGradient F f y) (tangentialGradient F (tangentialLaplacian F f) y) +
        meanCurvature F y * inner ℝ (tangentialGradient F f y)
          (secondFundamentalForm F y (tangentialGradient F f y)) -
        2 * inner ℝ (tangentialGradient F f y)
          (secondFundamentalForm F y (secondFundamentalForm F y (tangentialGradient F f y))) := by
  have hne := h.gradient_ne_zero y hy
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hf2 : ContDiffOn ℝ 2 f U := hf.of_le (by simp)
  have hg : ContDiffOn ℝ ∞ (tangentialGradient F f) U := h.contDiffOn_tangentialGradient_smooth hf
  have hgj (j : Fin d) : ContDiffOn ℝ 2 (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) U :=
    (contDiffOn_const.inner ℝ hg).of_le (by simp)
  -- `‖δf‖² = ∑ⱼ ⟪bⱼ, δf⟫²`
  have hsq : (fun x ↦ ‖tangentialGradient F f x‖ ^ 2) = fun x ↦ ∑ j,
      inner ℝ (b j) (tangentialGradient F f x) * inner ℝ (b j) (tangentialGradient F f x) := by
    funext x
    rw [norm_sq_eq_sum_inner_sq b]
    simp only [sq]
  rw [hsq, h.tangentialLaplacian_sum hy _ fun j _ ↦ (hgj j).mul (hgj j)]
  simp_rw [h.tangentialLaplacian_mul hy (hgj _) (hgj _)]
  -- the Laplacian term is the commuted component `⟪δf(y), δf⟫`
  have hlap : ∑ j, inner ℝ (b j) (tangentialGradient F f y) *
      tangentialLaplacian F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y =
        tangentialLaplacian F (fun x ↦ inner ℝ (tangentialGradient F f y)
          (tangentialGradient F f x)) y := by
    have hfun : (fun x ↦ inner ℝ (tangentialGradient F f y) (tangentialGradient F f x)) =
        fun x ↦ ∑ j, inner ℝ (b j) (tangentialGradient F f y) *
          inner ℝ (b j) (tangentialGradient F f x) := by
      funext x
      rw [← b.sum_inner_mul_inner]
      simp only [real_inner_comm (b _) (tangentialGradient F f y)]
    rw [hfun, h.tangentialLaplacian_sum hy _ fun j _ ↦ contDiffOn_const.mul (hgj j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [h.tangentialLaplacian_const_mul hy _ (hgj j)]
  -- the gradient term is the Hilbert-Schmidt norm of the tangential Hessian
  have hhess : ∑ j, inner ℝ (tangentialGradient F
        (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y)
      (tangentialGradient F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y) =
        ∑ k, ‖tangentialHessian F f y (b k)‖ ^ 2 := by
    have h1 (j : Fin d) : inner ℝ (tangentialGradient F
          (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y)
        (tangentialGradient F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y) =
          ∑ k, inner ℝ (b j) (tangentialHessian F f y (b k)) ^ 2 := by
      rw [real_inner_self_eq_norm_sq, norm_sq_eq_sum_inner_sq b]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [h.inner_tangentialGradient_inner_tangentialGradient hy hf2]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [norm_sq_eq_sum_inner_sq b]
  have hsplit : ∑ j, (inner ℝ (b j) (tangentialGradient F f y) *
        tangentialLaplacian F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y +
      inner ℝ (b j) (tangentialGradient F f y) *
        tangentialLaplacian F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y +
      2 * inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y)
        (tangentialGradient F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y)) =
      2 * (∑ j, inner ℝ (b j) (tangentialGradient F f y) *
        tangentialLaplacian F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y) +
      2 * ∑ j, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y)
        (tangentialGradient F (fun x ↦ inner ℝ (b j) (tangentialGradient F f x)) y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit, hlap, hhess, h.tangentialLaplacian_inner_tangentialGradient hy hf
    (c := tangentialGradient F f y) (inner_chartNormal_tangentialProj hne _)]
  ring

end IsSmoothBoundaryChart

/-! ### The covariant derivative of the second fundamental form and Simons' identity -/

/-- The tangential derivative of the second fundamental form applied to a fixed vector `z`:
`(δ_w A) z = D(x ↦ A(x) z)(P w)`. -/
def derivSecondFundamentalForm {d : ℕ} (F : Space d → ℝ) (y w z : Space d) : Space d :=
  fderiv ℝ (fun x ↦ secondFundamentalForm F x z) y (tangentialProj F y w)

/-- `|∇_M A|² = ∑ₖ ∑ᵢ ‖P ((δ_{bₖ} A)(P bᵢ))‖²`: the sum of squares of the tangential derivatives
of the tangential components of the second fundamental form (all slots projected to the tangent
space), i.e. the squared norm of the covariant derivative `∇_M A`. -/
def sqNormCovDerivSecondFundamentalForm {d : ℕ} (F : Space d → ℝ) (y : Space d) : ℝ :=
  ∑ k, ∑ i, ‖tangentialProj F y (derivSecondFundamentalForm F y (EuclideanSpace.basisFun (Fin d) ℝ k)
    (tangentialProj F y (EuclideanSpace.basisFun (Fin d) ℝ i)))‖ ^ 2

section TangentialAlgebra

variable {d : ℕ}

theorem tangentialGradient_sub (F : Space d → ℝ) {φ ψ : Space d → ℝ} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    tangentialGradient F (fun x ↦ φ x - ψ x) x =
      tangentialGradient F φ x - tangentialGradient F ψ x := by
  apply ext_inner_right ℝ
  intro z
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left,
    fderiv_fun_sub hφ hψ, inner_sub_left, tangentialGradient, tangentialGradient,
    inner_tangentialProj_left, inner_tangentialProj_left, inner_gradient_left, inner_gradient_left]
  rfl

end TangentialAlgebra

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

theorem secondFundamentalForm_apply_eventuallyEq (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (z : Space d) : (fun x ↦ secondFundamentalForm F x z) =ᶠ[𝓝 y]
      tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) z) := by
  filter_upwards [h.isOpen.mem_nhds hy] with x hx
  rw [h.tangentialGradient_inner_chartNormal hx]

theorem differentiableAt_secondFundamentalForm_apply (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (z : Space d) : DifferentiableAt ℝ (fun x ↦ secondFundamentalForm F x z) y :=
  (h.differentiableAt_tangentialGradient hy
    ((h.contDiffOn_inner_chartNormal z).of_le (by simp))).congr_of_eventuallyEq
      (h.secondFundamentalForm_apply_eventuallyEq hy z)

theorem derivSecondFundamentalForm_eq_tangentialHessian (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (w z : Space d) :
    derivSecondFundamentalForm F y w z =
      tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) z) y w := by
  rw [derivSecondFundamentalForm, (h.secondFundamentalForm_apply_eventuallyEq hy z).fderiv_eq]
  rfl

theorem inner_derivSecondFundamentalForm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (c w z : Space d) :
    inner ℝ c (derivSecondFundamentalForm F y w z) =
      fderiv ℝ (fun x ↦ inner ℝ c (secondFundamentalForm F x z)) y (tangentialProj F y w) := by
  have hd := (innerSL ℝ c).hasFDerivAt.comp y
    (h.differentiableAt_secondFundamentalForm_apply hy z).hasFDerivAt
  rw [show (fun x ↦ inner ℝ c (secondFundamentalForm F x z)) =
      (innerSL ℝ c) ∘ fun x ↦ secondFundamentalForm F x z from rfl, hd.fderiv]
  rfl

/-- Symmetry of the derivative of `A` in its last two slots. -/
theorem inner_derivSecondFundamentalForm_comm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w u v : Space d) :
    inner ℝ u (derivSecondFundamentalForm F y w v) =
      inner ℝ v (derivSecondFundamentalForm F y w u) := by
  rw [h.inner_derivSecondFundamentalForm hy, h.inner_derivSecondFundamentalForm hy]
  have heq : (fun x ↦ inner ℝ u (secondFundamentalForm F x v)) =ᶠ[𝓝 y]
      fun x ↦ inner ℝ v (secondFundamentalForm F x u) := by
    filter_upwards [h.isOpen.mem_nhds hy] with x hx
    rw [← h.inner_secondFundamentalForm_comm hx, real_inner_comm]
  rw [heq.fderiv_eq]

/-- Normal component: `⟪ν, (δ_w A) z⟫ = -⟪A w, A z⟫`. -/
theorem inner_chartNormal_derivSecondFundamentalForm (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (w z : Space d) :
    inner ℝ (chartNormal F y) (derivSecondFundamentalForm F y w z) =
      -inner ℝ (secondFundamentalForm F y w) (secondFundamentalForm F y z) := by
  rw [h.derivSecondFundamentalForm_eq_tangentialHessian hy,
    h.inner_chartNormal_tangentialHessian hy
      (((h.contDiffOn_inner_chartNormal z).of_le (by simp)).contDiffAt (h.isOpen.mem_nhds hy)),
    h.tangentialGradient_inner_chartNormal hy, h.inner_secondFundamentalForm_comm hy]

theorem derivSecondFundamentalForm_add (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w z₁ z₂ : Space d) :
    derivSecondFundamentalForm F y w (z₁ + z₂) =
      derivSecondFundamentalForm F y w z₁ + derivSecondFundamentalForm F y w z₂ := by
  have hfun : (fun x ↦ secondFundamentalForm F x (z₁ + z₂)) =
      fun x ↦ secondFundamentalForm F x z₁ + secondFundamentalForm F x z₂ :=
    funext fun x ↦ map_add _ _ _
  rw [derivSecondFundamentalForm, hfun, fderiv_fun_add
    (h.differentiableAt_secondFundamentalForm_apply hy z₁)
    (h.differentiableAt_secondFundamentalForm_apply hy z₂)]
  rfl

theorem derivSecondFundamentalForm_smul (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w z : Space d) (a : ℝ) :
    derivSecondFundamentalForm F y w (a • z) = a • derivSecondFundamentalForm F y w z := by
  have hfun : (fun x ↦ secondFundamentalForm F x (a • z)) =
      fun x ↦ a • secondFundamentalForm F x z :=
    funext fun x ↦ map_smul _ _ _
  have hd : HasFDerivAt (fun x ↦ a • secondFundamentalForm F x z)
      (a • fderiv ℝ (fun x ↦ secondFundamentalForm F x z) y) y :=
    (h.differentiableAt_secondFundamentalForm_apply hy z).hasFDerivAt.const_smul a
  rw [derivSecondFundamentalForm, hfun, hd.fderiv]
  rfl

/-- `P ((δ_w A) ν) = -A (A w)`. -/
theorem tangentialProj_derivSecondFundamentalForm_chartNormal (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (w : Space d) :
    tangentialProj F y (derivSecondFundamentalForm F y w (chartNormal F y)) =
      -secondFundamentalForm F y (secondFundamentalForm F y w) := by
  apply ext_inner_left ℝ
  intro z
  have key : inner ℝ (secondFundamentalForm F y w) (secondFundamentalForm F y z) =
      inner ℝ z (secondFundamentalForm F y (secondFundamentalForm F y w)) := by
    rw [← h.inner_secondFundamentalForm_comm hy z, real_inner_comm]
  rw [← inner_tangentialProj_left, h.inner_derivSecondFundamentalForm_comm hy,
    h.inner_chartNormal_derivSecondFundamentalForm hy, h.secondFundamentalForm_tangentialProj hy,
    inner_neg_right, key]

/-- Decomposition of the ambient derivative of `A` into its covariant part and the normal parts:
`∑ᵢ ‖(δ_w A) bᵢ‖² = ∑ᵢ ‖P ((δ_w A)(P bᵢ))‖² + 2 ‖A (A w)‖²`. -/
theorem sum_norm_sq_derivSecondFundamentalForm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    ∑ i, ‖derivSecondFundamentalForm F y w (EuclideanSpace.basisFun (Fin d) ℝ i)‖ ^ 2 =
      ∑ i, ‖tangentialProj F y (derivSecondFundamentalForm F y w
        (tangentialProj F y (EuclideanSpace.basisFun (Fin d) ℝ i)))‖ ^ 2 +
        2 * ‖secondFundamentalForm F y (secondFundamentalForm F y w)‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hne := h.gradient_ne_zero y hy
  have hD0 : derivSecondFundamentalForm F y w 0 = 0 := by
    have h0 := h.derivSecondFundamentalForm_smul hy w (0 : Space d) 0
    rwa [zero_smul, zero_smul] at h0
  -- the linear map `z ↦ P (D (P z))`
  let L : Space d →ₗ[ℝ] Space d :=
    { toFun := fun z ↦ tangentialProj F y (derivSecondFundamentalForm F y w (tangentialProj F y z))
      map_add' := fun z₁ z₂ ↦ by
        simp only [map_add, h.derivSecondFundamentalForm_add hy]
      map_smul' := fun c z ↦ by
        simp only [map_smul, h.derivSecondFundamentalForm_smul hy, RingHom.id_apply] }
  have hL (z : Space d) : L z =
      tangentialProj F y (derivSecondFundamentalForm F y w (tangentialProj F y z)) := rfl
  have hDb (i : Fin d) : derivSecondFundamentalForm F y w (b i) =
      derivSecondFundamentalForm F y w (tangentialProj F y (b i)) +
        inner ℝ (chartNormal F y) (b i) • derivSecondFundamentalForm F y w (chartNormal F y) := by
    have hb : b i = tangentialProj F y (b i) + inner ℝ (chartNormal F y) (b i) • chartNormal F y := by
      rw [tangentialProj_apply]
      abel
    conv_lhs => rw [hb]
    rw [h.derivSecondFundamentalForm_add hy, h.derivSecondFundamentalForm_smul hy]
  have hnorm (i : Fin d) : ‖derivSecondFundamentalForm F y w (b i)‖ ^ 2 =
      ‖tangentialProj F y (derivSecondFundamentalForm F y w (b i))‖ ^ 2 +
        inner ℝ (b i) (secondFundamentalForm F y (secondFundamentalForm F y w)) ^ 2 := by
    have key : inner ℝ (secondFundamentalForm F y w) (secondFundamentalForm F y (b i)) =
        inner ℝ (b i) (secondFundamentalForm F y (secondFundamentalForm F y w)) := by
      rw [← h.inner_secondFundamentalForm_comm hy (b i), real_inner_comm]
    rw [norm_sq_tangentialProj hne, h.inner_chartNormal_derivSecondFundamentalForm hy, key]
    ring
  have hPD (i : Fin d) : tangentialProj F y (derivSecondFundamentalForm F y w (b i)) =
      L (b i) - inner ℝ (chartNormal F y) (b i) •
        secondFundamentalForm F y (secondFundamentalForm F y w) := by
    rw [hDb, map_add, map_smul, h.tangentialProj_derivSecondFundamentalForm_chartNormal hy, hL,
      smul_neg, ← sub_eq_add_neg]
  have hLν : ∑ i, inner ℝ (chartNormal F y) (b i) • L (b i) = 0 := by
    have h1 : ∑ i, inner ℝ (chartNormal F y) (b i) • L (b i) =
        L (∑ i, inner ℝ (chartNormal F y) (b i) • b i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ (map_smul L _ _).symm
    have h2 : ∑ i, inner ℝ (chartNormal F y) (b i) • b i = chartNormal F y :=
      (Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]).trans (b.sum_repr' _)
    rw [h1, h2, hL, tangentialProj_chartNormal hne, hD0, map_zero]
  have hν1 : ∑ i, inner ℝ (chartNormal F y) (b i) ^ 2 = 1 := by
    have h1 := norm_sq_eq_sum_inner_sq b (chartNormal F y)
    rw [norm_chartNormal hne, one_pow] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
  have hcross : ∑ i, inner ℝ (chartNormal F y) (b i) *
      inner ℝ (L (b i)) (secondFundamentalForm F y (secondFundamentalForm F y w)) = 0 := by
    have h1 : ∑ i, inner ℝ (chartNormal F y) (b i) *
        inner ℝ (L (b i)) (secondFundamentalForm F y (secondFundamentalForm F y w)) =
          inner ℝ (∑ i, inner ℝ (chartNormal F y) (b i) • L (b i))
            (secondFundamentalForm F y (secondFundamentalForm F y w)) := by
      rw [sum_inner]
      simp only [real_inner_smul_left]
    rw [h1, hLν, inner_zero_left]
  have ha := norm_sq_eq_sum_inner_sq b (secondFundamentalForm F y (secondFundamentalForm F y w))
  calc ∑ i, ‖derivSecondFundamentalForm F y w (b i)‖ ^ 2
      = ∑ i, (‖L (b i)‖ ^ 2 - 2 * (inner ℝ (chartNormal F y) (b i) *
          inner ℝ (L (b i)) (secondFundamentalForm F y (secondFundamentalForm F y w))) +
          inner ℝ (chartNormal F y) (b i) ^ 2 *
            ‖secondFundamentalForm F y (secondFundamentalForm F y w)‖ ^ 2 +
          inner ℝ (b i) (secondFundamentalForm F y (secondFundamentalForm F y w)) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hnorm, hPD, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
          real_inner_smul_right]
    _ = ∑ i, ‖L (b i)‖ ^ 2 - 2 * ∑ i, inner ℝ (chartNormal F y) (b i) *
            inner ℝ (L (b i)) (secondFundamentalForm F y (secondFundamentalForm F y w)) +
          (∑ i, inner ℝ (chartNormal F y) (b i) ^ 2) *
            ‖secondFundamentalForm F y (secondFundamentalForm F y w)‖ ^ 2 +
          ∑ i, inner ℝ (b i) (secondFundamentalForm F y (secondFundamentalForm F y w)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
        rw [hcross, hν1, ← ha]
        simp only [hL]
        ring

theorem sqNormSecondFundamentalForm_eventuallyEq (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    sqNormSecondFundamentalForm F =ᶠ[𝓝 y] fun x ↦ ∑ i, ‖tangentialGradient F
      (fun x ↦ inner ℝ (chartNormal F x) (EuclideanSpace.basisFun (Fin d) ℝ i)) x‖ ^ 2 := by
  filter_upwards [h.isOpen.mem_nhds hy] with x hx
  rw [sqNormSecondFundamentalForm_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h.tangentialGradient_inner_chartNormal hx]

theorem contDiffOn_sqNormSecondFundamentalForm (h : IsSmoothBoundaryChart E U F) :
    ContDiffOn ℝ ∞ (sqNormSecondFundamentalForm F) U := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hs : ContDiffOn ℝ ∞ (fun x ↦ ∑ i, ‖tangentialGradient F
      (fun x ↦ inner ℝ (chartNormal F x) (b i)) x‖ ^ 2) U :=
    ContDiffOn.sum fun i _ ↦ (h.contDiffOn_tangentialGradient_smooth
      (h.contDiffOn_inner_chartNormal (b i))).norm_sq (𝕜 := ℝ)
  refine hs.congr fun x hx ↦ ?_
  rw [sqNormSecondFundamentalForm_eq_sum b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h.tangentialGradient_inner_chartNormal hx]

/-- **Simons' identity.** If the mean curvature vanishes on `M = U ∩ {F = 0}`, then at every point
of `M`, `½ Δ_M |A|² = |∇_M A|² - |A|⁴`. -/
theorem tangentialLaplacian_sqNormSecondFundamentalForm (h : IsSmoothBoundaryChart E U F)
    (hH : ∀ z ∈ U, F z = 0 → meanCurvature F z = 0) (hy : y ∈ U) (hFy : F y = 0) :
    tangentialLaplacian F (sqNormSecondFundamentalForm F) y / 2 =
      sqNormCovDerivSecondFundamentalForm F y - sqNormSecondFundamentalForm F y ^ 2 := by
  have hne := h.gradient_ne_zero y hy
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hU := h.isOpen.mem_nhds hy
  have hn (i : Fin d) : ContDiffOn ℝ ∞ (fun x ↦ inner ℝ (chartNormal F x) (b i)) U :=
    h.contDiffOn_inner_chartNormal (b i)
  have hδn (i : Fin d) : ContDiffOn ℝ ∞
      (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i))) U :=
    h.contDiffOn_tangentialGradient_smooth (hn i)
  have hsq2 (i : Fin d) : ContDiffOn ℝ 2 (fun x ↦ ‖tangentialGradient F
      (fun x ↦ inner ℝ (chartNormal F x) (b i)) x‖ ^ 2) U :=
    ((hδn i).norm_sq (𝕜 := ℝ)).of_le (by simp)
  have hHy : meanCurvature F y = 0 := hH y hy hFy
  have hAν : secondFundamentalForm F y (chartNormal F y) = 0 := h.secondFundamentalForm_chartNormal hy
  rw [tangentialLaplacian_congr F (h.sqNormSecondFundamentalForm_eventuallyEq hy),
    h.tangentialLaplacian_sum hy _ fun i _ ↦ hsq2 i, Finset.sum_div]
  simp_rw [h.tangentialLaplacian_norm_sq_tangentialGradient hy (hn _), hHy, zero_mul, add_zero]
  -- the Hessian terms give the covariant derivative plus normal corrections
  have hP1 : ∑ i, ∑ k, ‖tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y (b k)‖ ^ 2 =
      sqNormCovDerivSecondFundamentalForm F y +
        2 * ∑ k, ‖secondFundamentalForm F y (secondFundamentalForm F y (b k))‖ ^ 2 := by
    simp_rw [← h.derivSecondFundamentalForm_eq_tangentialHessian hy]
    rw [Finset.sum_comm, show b = EuclideanSpace.basisFun (Fin d) ℝ from rfl]
    simp_rw [h.sum_norm_sq_derivSecondFundamentalForm hy]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  -- the cubic terms
  have hP2 : ∑ i, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
      (secondFundamentalForm F y (secondFundamentalForm F y
        (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y))) =
        ∑ k, ‖secondFundamentalForm F y (secondFundamentalForm F y (b k))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h.tangentialGradient_inner_chartNormal hy, ← h.inner_secondFundamentalForm_comm hy,
      real_inner_self_eq_norm_sq]
  -- the Laplacian terms use the Jacobi identity
  have hP3 : ∑ i, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
      (tangentialGradient F (tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y) =
        -sqNormSecondFundamentalForm F y ^ 2 := by
    have hδH : ContDiffOn ℝ ∞ (tangentialGradient F (meanCurvature F)) U :=
      h.contDiffOn_tangentialGradient_smooth h.contDiffOn_meanCurvature
    have hδHz : ∀ z ∈ U, F z = 0 → tangentialGradient F (meanCurvature F) z = 0 := fun z hz hFz ↦
      h.tangentialGradient_eq_zero_of_eq_zero_on_level (h.contDiffOn_meanCurvature.of_le (by simp))
        hH hz hFz
    have hsqd : DifferentiableAt ℝ (sqNormSecondFundamentalForm F) y :=
      h.differentiableAt_of_contDiffOn hy h.contDiffOn_sqNormSecondFundamentalForm (by simp)
    have hterm (i : Fin d) :
        tangentialGradient F (tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y =
          -(sqNormSecondFundamentalForm F y •
              tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y +
            inner ℝ (chartNormal F y) (b i) •
              tangentialGradient F (sqNormSecondFundamentalForm F) y) := by
      have heq : tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) =ᶠ[𝓝 y]
          fun x ↦ inner ℝ (tangentialGradient F (meanCurvature F) x) (b i) -
            sqNormSecondFundamentalForm F x * inner ℝ (chartNormal F x) (b i) := by
        filter_upwards [hU] with x hx
        rw [h.tangentialLaplacian_inner_chartNormal hx]
      have hc1 : ContDiffOn ℝ ∞ (fun x ↦ inner ℝ (tangentialGradient F (meanCurvature F) x) (b i))
          U := hδH.inner ℝ contDiffOn_const
      have hd1 : DifferentiableAt ℝ
          (fun x ↦ inner ℝ (tangentialGradient F (meanCurvature F) x) (b i)) y :=
        h.differentiableAt_of_contDiffOn hy hc1 (by simp)
      have hdn : DifferentiableAt ℝ (fun x ↦ inner ℝ (chartNormal F x) (b i)) y :=
        h.differentiableAt_of_contDiffOn hy (hn i) (by simp)
      have hzero : tangentialGradient F
          (fun x ↦ inner ℝ (tangentialGradient F (meanCurvature F) x) (b i)) y = 0 :=
        h.tangentialGradient_eq_zero_of_eq_zero_on_level (hc1.of_le (by simp))
          (fun z hz hFz ↦ by rw [hδHz z hz hFz, inner_zero_left]) hy hFy
      have hdm : DifferentiableAt ℝ
          (fun x ↦ sqNormSecondFundamentalForm F x * inner ℝ (chartNormal F x) (b i)) y :=
        hsqd.mul hdn
      rw [(tangentialGradient_eventuallyEq F heq).eq_of_nhds,
        tangentialGradient_sub F hd1 hdm, hzero,
        tangentialGradient_mul F hsqd hdn, zero_sub]
    simp_rw [hterm]
    have hsum1 : ∑ i, ‖tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y‖ ^ 2 =
        sqNormSecondFundamentalForm F y := by
      rw [sqNormSecondFundamentalForm_eq_sum b]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [h.tangentialGradient_inner_chartNormal hy]
    have hsum2 : ∑ i, inner ℝ (chartNormal F y) (b i) *
        inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
          (tangentialGradient F (sqNormSecondFundamentalForm F) y) = 0 := by
      have h1 : ∑ i, inner ℝ (chartNormal F y) (b i) *
          inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
            (tangentialGradient F (sqNormSecondFundamentalForm F) y) =
            inner ℝ (secondFundamentalForm F y
              (∑ i, inner ℝ (chartNormal F y) (b i) • b i))
              (tangentialGradient F (sqNormSecondFundamentalForm F) y) := by
        rw [map_sum, sum_inner]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_smul, real_inner_smul_left, h.tangentialGradient_inner_chartNormal hy]
      have h2 : ∑ i, inner ℝ (chartNormal F y) (b i) • b i = chartNormal F y :=
        (Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]).trans (b.sum_repr' _)
      rw [h1, h2, hAν, inner_zero_left]
    have hexp : ∑ i, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
        (-(sqNormSecondFundamentalForm F y •
            tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y +
          inner ℝ (chartNormal F y) (b i) •
            tangentialGradient F (sqNormSecondFundamentalForm F) y)) =
        -(sqNormSecondFundamentalForm F y *
            ∑ i, ‖tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y‖ ^ 2) -
          ∑ i, inner ℝ (chartNormal F y) (b i) *
            inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
              (tangentialGradient F (sqNormSecondFundamentalForm F) y) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [inner_neg_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    rw [hexp, hsum1, hsum2]
    ring
  have hsplit : ∑ i, (∑ k, ‖tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y
        (b k)‖ ^ 2 +
      inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
        (tangentialGradient F (tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y) -
      2 * inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
        (secondFundamentalForm F y (secondFundamentalForm F y
          (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)))) =
      (∑ i, ∑ k, ‖tangentialHessian F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y (b k)‖ ^ 2) +
        (∑ i, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
          (tangentialGradient F
            (tangentialLaplacian F (fun x ↦ inner ℝ (chartNormal F x) (b i))) y)) -
        2 * ∑ i, inner ℝ (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y)
          (secondFundamentalForm F y (secondFundamentalForm F y
            (tangentialGradient F (fun x ↦ inner ℝ (chartNormal F x) (b i)) y))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hsplit, hP1, hP2, hP3]
  ring

end IsSmoothBoundaryChart

/-! ### The Kato inequality -/

section Kato

variable {d : ℕ}

/-- Cauchy-Schwarz for finite sums of inner products. -/
theorem sq_sum_inner_le {ι : Type*} (s : Finset ι) (u v : ι → Space d) :
    (∑ i ∈ s, inner ℝ (u i) (v i)) ^ 2 ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h1 : |∑ i ∈ s, inner ℝ (u i) (v i)| ≤ ∑ i ∈ s, ‖u i‖ * ‖v i‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ ↦ abs_real_inner_le_norm _ _)
  calc (∑ i ∈ s, inner ℝ (u i) (v i)) ^ 2 ≤ (∑ i ∈ s, ‖u i‖ * ‖v i‖) ^ 2 :=
        sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    _ ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * ∑ i ∈ s, ‖v i‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq s _ _

theorem inner_tangentialGradient_norm_sq (F : Space d → ℝ) {g : Space d → Space d} {y : Space d}
    (hg : DifferentiableAt ℝ g y) (c : Space d) :
    inner ℝ c (tangentialGradient F (fun x ↦ ‖g x‖ ^ 2) y) =
      2 * inner ℝ (g y) (fderiv ℝ g y (tangentialProj F y c)) := by
  rw [real_inner_comm, ← IsSmoothBoundaryChart.fderiv_tangentialProj_eq_inner,
    hg.hasFDerivAt.norm_sq.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    nsmul_eq_mul, Nat.cast_ofNat]

end Kato

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

/-- Only the covariant part of `δ_w A` pairs with `A`:
`∑ᵢ ⟪A bᵢ, (δ_w A) bᵢ⟫ = ∑ᵢ ⟪A bᵢ, P ((δ_w A)(P bᵢ))⟫`. -/
theorem sum_inner_derivSecondFundamentalForm (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (w : Space d) :
    ∑ i, inner ℝ (secondFundamentalForm F y (EuclideanSpace.basisFun (Fin d) ℝ i))
        (derivSecondFundamentalForm F y w (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      ∑ i, inner ℝ (secondFundamentalForm F y (EuclideanSpace.basisFun (Fin d) ℝ i))
        (tangentialProj F y (derivSecondFundamentalForm F y w
          (tangentialProj F y (EuclideanSpace.basisFun (Fin d) ℝ i)))) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hne := h.gradient_ne_zero y hy
  have hDb (i : Fin d) : derivSecondFundamentalForm F y w (b i) =
      derivSecondFundamentalForm F y w (tangentialProj F y (b i)) +
        inner ℝ (chartNormal F y) (b i) • derivSecondFundamentalForm F y w (chartNormal F y) := by
    have hb : b i = tangentialProj F y (b i) + inner ℝ (chartNormal F y) (b i) • chartNormal F y := by
      rw [tangentialProj_apply]
      abel
    conv_lhs => rw [hb]
    rw [h.derivSecondFundamentalForm_add hy, h.derivSecondFundamentalForm_smul hy]
  have htan (z v : Space d) : inner ℝ (secondFundamentalForm F y z) v =
      inner ℝ (secondFundamentalForm F y z) (tangentialProj F y v) := by
    rw [← inner_tangentialProj_left, tangentialProj_eq_self_of_inner_eq_zero
      (h.inner_chartNormal_secondFundamentalForm hy z)]
  have hnormal : ∑ i, inner ℝ (chartNormal F y) (b i) * inner ℝ (secondFundamentalForm F y (b i))
      (derivSecondFundamentalForm F y w (chartNormal F y)) = 0 := by
    have h1 : ∑ i, inner ℝ (chartNormal F y) (b i) * inner ℝ (secondFundamentalForm F y (b i))
        (derivSecondFundamentalForm F y w (chartNormal F y)) =
          inner ℝ (secondFundamentalForm F y (∑ i, inner ℝ (chartNormal F y) (b i) • b i))
            (derivSecondFundamentalForm F y w (chartNormal F y)) := by
      rw [map_sum, sum_inner]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, real_inner_smul_left]
    have h2 : ∑ i, inner ℝ (chartNormal F y) (b i) • b i = chartNormal F y :=
      (Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]).trans (b.sum_repr' _)
    rw [h1, h2, h.secondFundamentalForm_chartNormal hy, inner_zero_left]
  calc ∑ i, inner ℝ (secondFundamentalForm F y (b i)) (derivSecondFundamentalForm F y w (b i))
      = ∑ i, (inner ℝ (secondFundamentalForm F y (b i))
          (tangentialProj F y (derivSecondFundamentalForm F y w (tangentialProj F y (b i)))) +
        inner ℝ (chartNormal F y) (b i) * inner ℝ (secondFundamentalForm F y (b i))
          (derivSecondFundamentalForm F y w (chartNormal F y))) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hDb, inner_add_right, real_inner_smul_right, htan _
          (derivSecondFundamentalForm F y w (tangentialProj F y (b i)))]
    _ = _ := by rw [Finset.sum_add_distrib, hnormal, add_zero]

/-- **Kato inequality** (squared form): `‖δ|A|²‖² ≤ 4 |A|² |∇_M A|²`, valid on the whole chart. -/
theorem norm_sq_tangentialGradient_sqNormSecondFundamentalForm_le
    (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    ‖tangentialGradient F (sqNormSecondFundamentalForm F) y‖ ^ 2 ≤
      4 * sqNormSecondFundamentalForm F y * sqNormCovDerivSecondFundamentalForm F y := by
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
  have hcomp (k : Fin d) : inner ℝ (b k) (tangentialGradient F (sqNormSecondFundamentalForm F) y) =
      2 * ∑ i, inner ℝ (secondFundamentalForm F y (b i))
        (tangentialProj F y (derivSecondFundamentalForm F y (b k) (tangentialProj F y (b i)))) := by
    rw [hδ, inner_sum, ← h.sum_inner_derivSecondFundamentalForm hy (b k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_tangentialGradient_norm_sq F (hdδn i), h.tangentialGradient_inner_chartNormal hy,
      h.derivSecondFundamentalForm_eq_tangentialHessian hy]
    rfl
  have hA : ∑ i, ‖secondFundamentalForm F y (b i)‖ ^ 2 = sqNormSecondFundamentalForm F y :=
    (sqNormSecondFundamentalForm_eq_sum b F y).symm
  rw [norm_sq_eq_sum_inner_sq b, sqNormCovDerivSecondFundamentalForm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rw [hcomp k]
  have hcs := sq_sum_inner_le Finset.univ (fun i ↦ secondFundamentalForm F y (b i))
    (fun i ↦ tangentialProj F y (derivSecondFundamentalForm F y (b k) (tangentialProj F y (b i))))
  rw [hA] at hcs
  have : (2 * ∑ i, inner ℝ (secondFundamentalForm F y (b i))
      (tangentialProj F y (derivSecondFundamentalForm F y (b k) (tangentialProj F y (b i))))) ^ 2 =
      4 * (∑ i, inner ℝ (secondFundamentalForm F y (b i))
        (tangentialProj F y (derivSecondFundamentalForm F y (b k) (tangentialProj F y (b i))))) ^ 2 :=
    by ring
  rw [this]
  calc 4 * (∑ i, inner ℝ (secondFundamentalForm F y (b i))
        (tangentialProj F y (derivSecondFundamentalForm F y (b k) (tangentialProj F y (b i))))) ^ 2
      ≤ 4 * (sqNormSecondFundamentalForm F y * ∑ i, ‖tangentialProj F y
          (derivSecondFundamentalForm F y (b k) (tangentialProj F y (b i)))‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- **Kato inequality** `|δ|A|| ≤ |∇_M A|` at points where `|A| > 0`. -/
theorem norm_sq_tangentialGradient_sqrt_sqNormSecondFundamentalForm_le
    (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (hpos : 0 < sqNormSecondFundamentalForm F y) :
    ‖tangentialGradient F (fun x ↦ Real.sqrt (sqNormSecondFundamentalForm F x)) y‖ ^ 2 ≤
      sqNormCovDerivSecondFundamentalForm F y := by
  have hsd : DifferentiableAt ℝ (sqNormSecondFundamentalForm F) y :=
    h.differentiableAt_of_contDiffOn hy h.contDiffOn_sqNormSecondFundamentalForm (by simp)
  have hd : HasFDerivAt (fun x ↦ Real.sqrt (sqNormSecondFundamentalForm F x))
      ((1 / (2 * Real.sqrt (sqNormSecondFundamentalForm F y))) •
        fderiv ℝ (sqNormSecondFundamentalForm F) y) y :=
    (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt y hsd.hasFDerivAt
  have hgrad : tangentialGradient F (fun x ↦ Real.sqrt (sqNormSecondFundamentalForm F x)) y =
      (1 / (2 * Real.sqrt (sqNormSecondFundamentalForm F y))) •
        tangentialGradient F (sqNormSecondFundamentalForm F) y := by
    apply ext_inner_right ℝ
    intro z
    rw [real_inner_smul_left, ← fderiv_tangentialProj_eq_inner, ← fderiv_tangentialProj_eq_inner,
      hd.fderiv]
    rfl
  have hkato := h.norm_sq_tangentialGradient_sqNormSecondFundamentalForm_le hy
  have hsqrt : Real.sqrt (sqNormSecondFundamentalForm F y) ^ 2 = sqNormSecondFundamentalForm F y :=
    Real.sq_sqrt hpos.le
  have hspos : 0 < Real.sqrt (sqNormSecondFundamentalForm F y) := Real.sqrt_pos.mpr hpos
  have hs0 : sqNormSecondFundamentalForm F y ≠ 0 := hpos.ne'
  rw [hgrad, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow, mul_pow, hsqrt]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [hkato]

end IsSmoothBoundaryChart

end SerrinEpigraph
