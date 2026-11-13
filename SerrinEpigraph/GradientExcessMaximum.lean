module

public import SerrinEpigraph.GradientExcess
public import SerrinEpigraph.WeakViscosity
public import SerrinEpigraph.StressStationarity

/-!
# Local maximum tests for the gradient excess
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The excess evaluated using the gradient within the closed epigraph. -/
@[expose] def closedGradientExcess (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (f : ℝ → ℝ) (ε : ℝ) (x : Space (m + 1)) : ℝ :=
  ‖gradientWithin u (closure (epigraph g)) x‖ ^ 2 / 2 -
    normalizedPotential f (u x) + ε * u x ^ 2

/-- The excess extends continuously to the closed epigraph. -/
theorem RigidityHypotheses.closedGradientExcess_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (ε : ℝ) :
    ContinuousOn (closedGradientExcess g u f ε) (closure (epigraph g)) := by
  have hu := h.solution_contDiffOn_closure.continuousOn
  have hW := h.normalizedPotential_continuousOn.comp hu
    (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
  exact (((h.closed_gradient_continuousOn.norm.pow 2).div_const 2).sub hW).add
    (continuousOn_const.mul (hu.pow 2))

/-- The closed and interior excesses agree throughout the open epigraph. -/
theorem Hypotheses.closedGradientExcess_eq (h : Hypotheses g u f κ) (ε : ℝ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    closedGradientExcess g u f ε x = gradientExcess u f ε x := by
  simp only [closedGradientExcess, gradientExcess, h.closed_gradient_eq hx]

/-- The boundary energy identity forces zero excess on the whole graph. -/
theorem RigidityHypotheses.closedGradientExcess_boundary_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (ε : ℝ) (y : Space m) :
    closedGradientExcess g u f ε (point y (g y)) = 0 := by
  have hκ := hr.kappa_sq_eq_twice_potential h
  simp only [closedGradientExcess, h.dirichlet y, h.boundary_gradient_eq y,
    norm_smul, norm_outwardNormal, mul_one, norm_neg, Real.norm_eq_abs, sq_abs,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  linarith

/-- The perturbed excess satisfies its differential inequality at every smooth upper test. -/
theorem RigidityHypotheses.gradientExcess_upper_test_inequality
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {ε : ℝ} (hε : 0 ≤ ε)
    {ψ : Space (m + 1) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g)
    (hmax : IsLocalMax (fun y ↦ gradientExcess u f ε y - ψ y) x) :
    ‖gradient ψ x‖ ^ 2 + 2 * ε * ‖gradient u x‖ ^ 4 ≤
      ‖gradient u x‖ ^ 2 * (Δ ψ) x + 2 * (f (u x) + 2 * ε * u x) *
        inner ℝ (gradient u x) (gradient ψ x) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hp : ContinuousOn (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hF : ContinuousOn (fun y ↦ f (u y)) (epigraph g) :=
    h.reaction_contDiffOn.continuousOn.comp hu.continuousOn (fun y hy ↦ (h.positive y hy).le)
  have hS : ContinuousOn (fun y ↦ hessianSquare b u y - f (u y) ^ 2 +
      2 * ε * ‖gradient u y‖ ^ 2 - 2 * ε * u y * f (u y)) (epigraph g) :=
    (((h.hessianSquare_continuousOn b).sub (hF.pow 2)).add
      (continuousOn_const.mul (hp.norm.pow 2))).sub
        ((continuousOn_const.mul hu.continuousOn).mul hF)
  have hweak (φ : Space (m + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ epigraph g) :
      (∫ y, inner ℝ (gradient (gradientExcess u f ε) y) (gradient φ y)) =
        -(∫ y, (hessianSquare b u y - f (u y) ^ 2 +
          2 * ε * ‖gradient u y‖ ^ 2 - 2 * ε * u y * f (u y)) * φ y) := by
    rw [h.weak_gradientExcess_identity b ε hφ hc hs, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y ↦ by dsimp only; ring)
  have htest := weak_laplacian_le_at_upper_test hΩ (h.gradientExcess_contDiffOn ε)
    hS hweak hψ hx hmax
  have hder := hmax.fderiv_eq_zero
  rw [fderiv_fun_sub
    (((h.gradientExcess_contDiffOn ε).differentiableOn_one x hx).differentiableAt
      (hΩ.mem_nhds hx)) (hψ.differentiable (by norm_num) x), sub_eq_zero] at hder
  have hgrad : gradient (gradientExcess u f ε) x = gradient ψ x := by
    simp only [gradient, hder]
  have hh := hr.gradientExcess_differential_inequality h b hε hx
  rw [hgrad] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left htest (sq_nonneg _)) le_rfl)

/-- An interior local maximum of the positively perturbed excess cannot exceed its perturbation. -/
theorem RigidityHypotheses.gradientExcess_le_of_isLocalMax
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {ε : ℝ} (hε : 0 < ε)
    {x : Space (m + 1)} (hx : x ∈ epigraph g)
    (hmax : IsLocalMax (gradientExcess u f ε) x) : gradientExcess u f ε x ≤ ε := by
  have ht := hr.gradientExcess_upper_test_inequality h b hε.le
    (ψ := fun _ ↦ (0 : ℝ)) contDiff_const hx (by simpa only [sub_zero] using hmax)
  have hg0 : gradient (fun _ : Space (m + 1) ↦ (0 : ℝ)) x = 0 := by simp [gradient]
  simp only [hg0, norm_zero, zero_pow (by norm_num : 2 ≠ 0), laplacian_const, Pi.zero_apply,
    mul_zero, inner_zero_right, add_zero, zero_add] at ht
  have hgn : ‖gradient u x‖ = 0 := by
    have hpow : ‖gradient u x‖ ^ 4 = 0 := by
      nlinarith [pow_nonneg (norm_nonneg (gradient u x)) 4]
    exact eq_zero_of_pow_eq_zero hpow
  have hu : 0 < u x := h.positive x hx
  have hu1 : u x < 1 := hr.solution_lt_one x hx
  have hW := hr.normalizedPotential_nonneg h ⟨hu.le, hu1.le⟩
  have hu2 : u x ^ 2 ≤ 1 := by nlinarith
  have hεu := mul_le_mul_of_nonneg_left hu2 hε.le
  dsimp only [gradientExcess]
  rw [hgn]
  nlinarith

end SerrinEpigraph
