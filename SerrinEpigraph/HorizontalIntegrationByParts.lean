module

public import SerrinEpigraph.AlignedFluxVertical

/-!
# Horizontal integration by parts against Lipschitz functions

For a globally Lipschitz function `F` and a compactly supported `C¹` vector field `ζ`,
`∫ ⟪ζ, ∇F⟫ = -∫ (div ζ) F` (`integral_inner_gradient_eq_neg_integral_fieldDivergence_mul`).
On `Space (m + 1)`, the same holds for the horizontal part of the gradient tested against
`ψ(t) ζ(y)`: `∫ ψ(t) ⟪ζ(y), ∇_y F⟫ = -∫ ψ(t) (div ζ)(y) F`
(`integral_mul_inner_horizontal_gradient_eq_neg`). Both follow from the one-direction
integration by parts `integral_fderiv_apply_mul_eq_neg_of_lipschitz`, applied to the coordinates
of the test field in the standard basis.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

/-- Integration by parts for a globally Lipschitz function against a finite family of compactly
supported `C¹` test functions, each paired with its own direction. -/
private theorem integral_sum_mul_fderiv_eq_neg_of_lipschitz_aux {d : ℕ} {ι : Type*}
    [Fintype ι] {F : Space d → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {θ : ι → Space d → ℝ}
    (hθ : ∀ i, ContDiff ℝ 1 (θ i)) (hθc : ∀ i, HasCompactSupport (θ i)) (v : ι → Space d) :
    ∫ y, ∑ i, θ i y * fderiv ℝ F y (v i) = -∫ y, F y * ∑ i, fderiv ℝ (θ i) y (v i) := by
  have hint₁ : ∀ i, Integrable (fun y ↦ θ i y * fderiv ℝ F y (v i)) := by
    intro i
    refine ((hθ i).continuous.integrable_of_hasCompactSupport (hθc i)).mul_bdd
      (c := K * ‖v i‖) (measurable_fderiv_apply_const ℝ F (v i)).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    exact ((fderiv ℝ F y).le_opNorm (v i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  have hint₂ : ∀ i, Integrable (fun y ↦ F y * fderiv ℝ (θ i) y (v i)) := by
    intro i
    have hcont : Continuous (fun y ↦ fderiv ℝ (θ i) y (v i)) :=
      ((hθ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hF.continuous.mul hcont).integrable_of_hasCompactSupport
      ((hθc i).fderiv_apply ℝ (v i)).mul_left
  rw [integral_finsetSum _ fun i _ ↦ hint₁ i]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ hint₂ i, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_fderiv_apply_mul_eq_neg_of_lipschitz hF (hθ i) (hθc i) (v i)]
  congr 1
  funext y
  ring

/-- **Integration by parts against a Lipschitz function.** For a globally Lipschitz `F` and a
compactly supported `C¹` vector field `ζ`, `∫ ⟪ζ, ∇F⟫ = -∫ (div ζ) F`. -/
theorem integral_inner_gradient_eq_neg_integral_fieldDivergence_mul {d : ℕ}
    {F : Space d → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {ζ : Space d → Space d}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) :
    ∫ y, inner ℝ (ζ y) (gradient F y) =
      -∫ y, fieldDivergence (EuclideanSpace.basisFun (Fin d) ℝ) ζ y * F y := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  have hθ : ∀ i, ContDiff ℝ 1 (fun y ↦ inner ℝ (ζ y) (b i)) := fun i ↦
    hζ.inner ℝ contDiff_const
  have hθc : ∀ i, HasCompactSupport (fun y ↦ inner ℝ (ζ y) (b i)) := fun i ↦
    hζc.comp_left (g := fun w ↦ inner ℝ w (b i)) (inner_zero_left _)
  have hl : ∀ y, inner ℝ (ζ y) (gradient F y) =
      ∑ i, inner ℝ (ζ y) (b i) * fderiv ℝ F y (b i) := by
    intro y
    rw [← b.sum_inner_mul_inner (ζ y) (gradient F y)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm (gradient F y) (b i), inner_gradient_left]
  have hr : ∀ y, fieldDivergence b ζ y * F y =
      F y * ∑ i, fderiv ℝ (fun y ↦ inner ℝ (ζ y) (b i)) y (b i) := by
    intro y
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [fderiv_inner_apply ℝ (hζ.differentiable one_ne_zero y) (differentiableAt_const _),
      fderiv_const_apply, zero_apply, inner_zero_right, zero_add, real_inner_comm]
  simp_rw [hl, hr]
  exact integral_sum_mul_fderiv_eq_neg_of_lipschitz_aux hF hθ hθc fun i ↦ b i

/-- **Horizontal integration by parts against a Lipschitz function.** For a globally Lipschitz
`F` on `Space (m + 1)`, a compactly supported `C¹` horizontal field `ζ` and a compactly
supported `C¹` vertical profile `ψ`, `∫ ψ(t) ⟪ζ(y), ∇_y F⟫ = -∫ ψ(t) (div ζ)(y) F`. -/
theorem integral_mul_inner_horizontal_gradient_eq_neg {m : ℕ} {F : Space (m + 1) → ℝ}
    {K : ℝ≥0} (hF : LipschitzWith K F) {ζ : Space m → Space m} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (horizontal (gradient F z)) =
      -∫ z, ψ (z (Fin.last m)) *
        fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ (horizontal z) * F z := by
  set b := EuclideanSpace.basisFun (Fin m) ℝ
  set θ : Fin m → Space (m + 1) → ℝ :=
    fun i z ↦ ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (b i)
  have hθ : ∀ i, ContDiff ℝ 1 (θ i) := fun i ↦
    (hψ.comp contDiff_last).mul ((hζ.comp contDiff_horizontal).inner ℝ contDiff_const)
  have hθc : ∀ i, HasCompactSupport (θ i) := by
    intro i
    obtain ⟨r₁, hr₁⟩ := hζc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨r₂, hr₂⟩ := hψc.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space (m + 1)) (r₁ + r₂))
      fun z hz ↦ ?_
    rw [mem_closedBall_zero_iff, not_le] at hz
    by_cases h₁ : horizontal z ∈ tsupport ζ
    · have h₂ : z (Fin.last m) ∉ tsupport ψ := fun h₂ ↦ by
        have e₁ := mem_closedBall_zero_iff.mp (hr₁ h₁)
        have e₂ := mem_closedBall_zero_iff.mp (hr₂ h₂)
        rw [Real.norm_eq_abs] at e₂
        linarith [norm_le_norm_horizontal_add_abs_last z]
      simp [θ, image_eq_zero_of_notMem_tsupport h₂]
    · simp [θ, image_eq_zero_of_notMem_tsupport h₁]
  have hderiv : ∀ i z, fderiv ℝ (θ i) z (point (b i) 0) =
      ψ (z (Fin.last m)) * inner ℝ (b i) (fderiv ℝ ζ (horizontal z) (b i)) := by
    intro i z
    have hlast : HasFDerivAt (fun z : Space (m + 1) ↦ z (Fin.last m))
        (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ) z :=
      (EuclideanSpace.proj (Fin.last m) : Space (m + 1) →L[ℝ] ℝ).hasFDerivAt
    have hψd : HasFDerivAt (fun z : Space (m + 1) ↦ ψ (z (Fin.last m)))
        ((fderiv ℝ ψ (z (Fin.last m))).comp (EuclideanSpace.proj (Fin.last m))) z :=
      (hψ.differentiable one_ne_zero _).hasFDerivAt.comp z hlast
    have hζd : HasFDerivAt (fun z : Space (m + 1) ↦ ζ (horizontal z))
        ((fderiv ℝ ζ (horizontal z)).comp horizontalContinuousLinearMap) z :=
      (hζ.differentiable one_ne_zero _).hasFDerivAt.comp z
        horizontalContinuousLinearMap.hasFDerivAt
    rw [(hψd.fun_mul (hζd.inner ℝ (hasFDerivAt_const (b i) z))).fderiv]
    simp [horizontalContinuousLinearMap_apply, real_inner_comm]
  have hl : ∀ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (horizontal (gradient F z)) =
      ∑ i, θ i z * fderiv ℝ F z (point (b i) 0) := by
    intro z
    rw [← b.sum_inner_mul_inner (ζ (horizontal z)) (horizontal (gradient F z)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← inner_gradient_left, inner_point_zero_right,
      real_inner_comm (horizontal (gradient F z)) (b i), mul_assoc]
  have hr : ∀ z, ψ (z (Fin.last m)) * fieldDivergence b ζ (horizontal z) * F z =
      F z * ∑ i, fderiv ℝ (θ i) z (point (b i) 0) := by
    intro z
    simp_rw [hderiv, ← Finset.mul_sum]
    unfold fieldDivergence
    ring
  simp_rw [hl, hr]
  exact integral_sum_mul_fderiv_eq_neg_of_lipschitz_aux hF hθ hθc fun i ↦ point (b i) 0

end SerrinEpigraph
