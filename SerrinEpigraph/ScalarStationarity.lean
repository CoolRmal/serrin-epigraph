module

public import SerrinEpigraph.BoundaryWeakInequality

/-!
# Scalar stationarity across the free boundary

Multiplying the equation by the solution removes the boundary flux. This gives
the scalar energy identity needed for strong gradient compactness and the Weiss
formula without an unsupported smoothness assumption at the interface.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- Product divergence for the scalar variation of the solution. -/
theorem Hypotheses.fieldDivergence_scalar_flux
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (hφ : ContDiff ℝ 1 φ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    fieldDivergence basis (fun y ↦ (φ y * u y) • gradient u y) x =
      φ x * (‖gradient u x‖ ^ 2 - u x * f (u x)) +
        u x * inner ℝ (gradient u x) (gradient φ x) := by
  have hu := h.solution_contDiffOn.contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hud := hu.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp x
      (hu.fderiv_right (m := 1) (by norm_num))).differentiableAt (by norm_num)
  rw [fieldDivergence_fun_smul basis (φ := fun y ↦ φ y * u y)
      ((hφ.differentiable_one x).mul hud) hg,
    gradient_mul_at (hφ.differentiable_one x) hud]
  have hlap := h.laplacian_eq_sum_gradient_derivative hx basis
  simp_rw [real_inner_comm] at hlap
  change (Δ u) x = fieldDivergence basis (gradient u) x at hlap
  have heq : (Δ u) x = -f (u x) := by linarith [h.equation x hx]
  rw [← hlap, heq]
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (gradient φ x) (gradient u x)]
  ring

/-- The Dirichlet trace cancels the boundary term in the scalar energy identity. -/
theorem RigidityHypotheses.integral_epigraph_scalar_stationarity
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x in epigraph g, φ x * (‖gradient u x‖ ^ 2 - u x * f (u x)) +
      u x * inner ℝ (gradient u x) (gradient φ x)) = 0 := by
  let p := gradientWithin u (closure (epigraph g))
  let F := fun x ↦ (φ x * u x) • gradient u x
  let Fbar := fun x ↦ (φ x * u x) • p x
  let D := fun x ↦ φ x * (‖p x‖ ^ 2 - u x * f (u x)) +
    u x * inner ℝ (p x) (gradient φ x)
  let basis := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hgrad : ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
      (h.solution_contDiffOn.fderiv_of_isOpen hΩ (by norm_num))
  have hF : ContDiffOn ℝ 1 F (epigraph g) :=
    (hφ.contDiffOn.mul (h.solution_contDiffOn.of_le (by norm_num))).smul hgrad
  have hcF : HasCompactSupport F := hc.mul_right.smul_right
  have hu := h.solution_contDiffOn_closure.continuousOn
  have hbar : ContinuousOn Fbar (closure (epigraph g)) :=
    (hφ.continuous.continuousOn.mul hu).smul h.closed_gradient_continuousOn
  have hcbar : HasCompactSupport Fbar := hc.mul_right.smul_right
  have heq : EqOn Fbar F (epigraph g) := by
    intro x hx
    simp only [Fbar, F, p, h.closed_gradient_eq hx]
  have hD : ContinuousOn D (closure (epigraph g)) := by
    have hf := h.reaction_contDiffOn.continuousOn.comp hu
      (fun x hx ↦ (hr.solution_mem_Icc_closure h hx).1)
    have hφgrad : Continuous (gradient φ) :=
      (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
    exact (hφ.continuous.continuousOn.mul
      ((h.closed_gradient_continuousOn.norm.pow 2).sub (hu.mul hf))).add
      (hu.mul (h.closed_gradient_continuousOn.inner hφgrad.continuousOn))
  have hcD : HasCompactSupport D := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    apply hx
    simp [D, gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn]
  have hdiv : EqOn (fieldDivergence basis F) D (epigraph g) := by
    intro x hx
    simpa only [D, p, h.closed_gradient_eq hx] using
      h.fieldDivergence_scalar_flux basis hφ hx
  have hGauss := integral_epigraph_divergence_of_continuous_trace basis h.graph_contDiff
    hF hcF hbar hcbar heq hD hcD hdiv
  have hzero : (∫ x in epigraph g, D x) = 0 := by
    rw [hGauss]
    simp [Fbar, h.dirichlet]
  rw [← hzero]
  apply setIntegral_congr_fun hΩ.measurableSet
  intro x hx
  simp only [D, p, h.closed_gradient_eq hx]

/-- Scalar stationarity is valid globally for the zero extension. -/
theorem RigidityHypotheses.integral_zeroExtension_scalar_stationarity
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x * (‖gradient (zeroExtension g u) x‖ ^ 2 -
      zeroExtension g u x * f (zeroExtension g u x)) +
      zeroExtension g u x * inner ℝ (gradient (zeroExtension g u) x) (gradient φ x)) = 0 := by
  have he : (fun x ↦ φ x * (‖gradient (zeroExtension g u) x‖ ^ 2 -
        zeroExtension g u x * f (zeroExtension g u x)) +
        zeroExtension g u x * inner ℝ (gradient (zeroExtension g u) x) (gradient φ x)) =
      (epigraph g).indicator (fun x ↦ φ x * (‖gradient u x‖ ^ 2 - u x * f (u x)) +
        u x * inner ℝ (gradient u x) (gradient φ x)) := by
    funext x
    by_cases hx : x ∈ epigraph g
    · simp only [indicator_of_mem hx, h.gradient_zeroExtension hx, zeroExtension_of_mem hx]
    · simp [indicator_of_notMem hx, h.gradient_zeroExtension_of_notMem hx,
        zeroExtension_of_notMem hx]
  rw [he, integral_indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
  exact hr.integral_epigraph_scalar_stationarity h hφ hc

end SerrinEpigraph
