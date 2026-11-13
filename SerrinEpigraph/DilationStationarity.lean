module

public import SerrinEpigraph.StressStationarity

/-!
# Localized dilation identity for the phase energy
-/

public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace SerrinEpigraph

/-- The derivative of a localized dilation consists of the scalar identity and
the rank-one cutoff derivative. -/
theorem fderiv_localized_dilation {d : ℕ} {φ : Space d → ℝ}
    {x : Space d} (hφ : DifferentiableAt ℝ φ x) (c v : Space d) :
    fderiv ℝ (fun y ↦ φ y • (y - c)) x v =
      φ x • v + fderiv ℝ φ x v • (x - c) := by
  have hd := hφ.hasFDerivAt.smul ((hasFDerivAt_id x).sub_const c)
  change HasFDerivAt (fun y ↦ φ y • (y - c)) _ x at hd
  rw [hd.fderiv]
  simp

/-- The divergence of a localized dilation is dimension times the cutoff plus
its radial derivative. -/
theorem divergence_localized_dilation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {φ : Space d → ℝ}
    {x : Space d} (hφ : DifferentiableAt ℝ φ x) (c : Space d) :
    fieldDivergence b (fun y ↦ φ y • (y - c)) x =
      (d : ℝ) * φ x + fderiv ℝ φ x (x - c) := by
  unfold fieldDivergence
  simp_rw [fderiv_localized_dilation hφ, inner_add_right, real_inner_smul_right]
  rw [Finset.sum_add_distrib]
  have hsum := sum_inner_mul_linear b (fderiv ℝ φ x) (x - c)
  simp_rw [mul_comm (fderiv ℝ φ x _)]
  rw [hsum]
  simp

/-- Stationarity tested against a compactly localized dilation gives the weak
Pohozaev identity without imposing any smoothness on spherical intersections. -/
theorem RigidityHypotheses.integral_dilation_stationarity
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (c : Space (m + 1)) :
    (∫ x in epigraph g,
      (((m + 1 : ℝ) - 2) / 2 * ‖gradient u x‖ ^ 2 +
        (m + 1 : ℝ) * normalizedPotential f (u x)) * φ x +
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * fderiv ℝ φ x (x - c) -
      inner ℝ (gradient u x) (x - c) * fderiv ℝ φ x (gradient u x)) = 0 := by
  let X := fun x ↦ φ x • (x - c)
  have hX : ContDiff ℝ 1 X := hφ.smul (contDiff_id.sub contDiff_const)
  have hXc : HasCompactSupport X := hc.smul_right
  have he := hr.integral_stress_stationarity h basis hX hXc
  rw [← he]
  apply setIntegral_congr_fun (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  intro x _
  dsimp only [X]
  rw [divergence_localized_dilation basis (hφ.differentiable_one x),
    fderiv_localized_dilation (hφ.differentiable_one x)]
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    Nat.cast_add, Nat.cast_one]
  ring

end SerrinEpigraph
