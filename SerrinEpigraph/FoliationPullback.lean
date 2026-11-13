module

public import SerrinEpigraph.FoliationEquation
public import SerrinEpigraph.VectorIntegrationByParts

/-!
# The foliation gradient along a comparison function
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Horizontal projection as a continuous linear map. -/
@[expose] def horizontalContinuousLinearMap : Space (m + 1) →L[ℝ] Space m :=
  LinearMap.toContinuousLinearMap
    { toFun := horizontal
      map_add' := by intro x y; ext i; simp [horizontal]
      map_smul' := by intro c x; ext i; simp [horizontal] }

/-- The gradient field evaluated at the levels of a comparison function. -/
@[expose] def RigidityHypotheses.comparisonField (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (v : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    Space (m + 1) := hr.levelGradient h (horizontal x, v x)

/-- A continuously differentiable comparison function gives a continuously differentiable field. -/
theorem RigidityHypotheses.comparisonField_contDiffOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {v : Space (m + 1) → ℝ} {Ω : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hval : ∀ x ∈ Ω, v x ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffOn ℝ 1 (hr.comparisonField h v) Ω := by
  intro x hx
  have hc := hr.levelGradient_contDiffAt h (p := (horizontal x, v x)) (hval x hx)
  exact (hc.comp x (horizontalContinuousLinearMap.contDiff.contDiffAt.prodMk
    (hv.contDiffAt (hΩ.mem_nhds hx)))).contDiffWithinAt

/-- The comparison field obeys the chain rule in both horizontal position and solution level. -/
theorem RigidityHypotheses.comparisonField_fderiv_apply (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {v : Space (m + 1) → ℝ} {x : Space (m + 1)}
    (hv : DifferentiableAt ℝ v x) (hs : v x ∈ Set.Ioo (0 : ℝ) 1) (w : Space (m + 1)) :
    fderiv ℝ (hr.comparisonField h v) x w =
      fderiv ℝ (hr.levelGradient h) (horizontal x, v x) (horizontal w, fderiv ℝ v x w) := by
  have hc := ((hr.levelGradient_contDiffAt h hs).differentiableAt
    (by norm_num)).hasFDerivAt.comp x
    (horizontalContinuousLinearMap.hasFDerivAt.prodMk hv.hasFDerivAt)
  exact congrArg (fun L : Space (m + 1) →L[ℝ] Space (m + 1) ↦ L w) hc.fderiv

/-- The comparison field divergence equals the reaction plus the level-variation correction. -/
theorem RigidityHypotheses.comparisonField_trace (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {v : Space (m + 1) → ℝ} {x : Space (m + 1)}
    (hv : DifferentiableAt ℝ v x) (hs : v x ∈ Set.Ioo (0 : ℝ) 1)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space (m + 1))) :
    (∑ i, inner ℝ (fderiv ℝ (hr.comparisonField h v) x (b i)) (b i)) =
      -f (v x) + inner ℝ (fderiv ℝ (hr.levelGradient h) (horizontal x, v x) (0, 1))
        (gradient v x - hr.comparisonField h v x) := by
  let p := (horizontal x, v x)
  let D := fderiv ℝ (hr.levelGradient h) p
  have he (i : ι) : inner ℝ (fderiv ℝ (hr.comparisonField h v) x (b i)) (b i) =
      inner ℝ (D (horizontal (b i), 0)) (b i) +
        inner ℝ (gradient v x) (b i) * inner ℝ (D (0, 1)) (b i) := by
    rw [hr.comparisonField_fderiv_apply h hv hs]
    have hp : (horizontal (b i), fderiv ℝ v x (b i)) =
        (horizontal (b i), 0) + (fderiv ℝ v x (b i)) • (0, 1) := by simp
    rw [hp, map_add, map_smul, inner_add_left, real_inner_smul_left, inner_gradient_left]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hparse : (∑ i, inner ℝ (gradient v x) (b i) * inner ℝ (D (0, 1)) (b i)) =
      inner ℝ (D (0, 1)) (gradient v x) := by
    simpa only [real_inner_comm, mul_comm] using
      b.sum_inner_mul_inner (gradient v x) (D (0, 1))
  rw [hparse, inner_sub_right]
  have hpde := hr.levelGradient_equation h (p := p) hs b
  change (∑ i, inner ℝ (D (horizontal (b i), 0)) (b i)) +
    inner ℝ (D (0, 1)) (hr.comparisonField h v x) = -f (v x) at hpde
  change _ = -f (v x) + (inner ℝ (D (0, 1)) (gradient v x) -
    inner ℝ (D (0, 1)) (hr.comparisonField h v x))
  linarith

/-- The comparison field satisfies the integrated calibration identity for compact tests. -/
theorem RigidityHypotheses.comparisonField_integral (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {v φ : Space (m + 1) → ℝ} {Ω : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hval : ∀ x ∈ Ω, v x ∈ Set.Ioo (0 : ℝ) 1)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    (∫ x, inner ℝ (hr.comparisonField h v x) (gradient φ x)) =
      ∫ x, (f (v x) -
        inner ℝ (fderiv ℝ (hr.levelGradient h) (horizontal x, v x) (0, 1))
          (gradient v x - hr.comparisonField h v x)) * φ x := by
  let b := stdOrthonormalBasis ℝ (Space (m + 1))
  rw [integral_inner_field_gradient hΩ
    (hr.comparisonField_contDiffOn h hΩ hv hval) hφ hφc hsub b, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [hr.comparisonField_trace h
      ((hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)) (hval x hx) b]
    ring
  · have hz : φ x = 0 := Function.notMem_support.mp
      (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
    simp [hz]

end SerrinEpigraph
