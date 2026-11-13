module

public import SerrinEpigraph.UnitShellVolume
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Energy under spatial rescaling
-/

public section

open MeasureTheory Metric
open scoped Pointwise

namespace SerrinEpigraph

noncomputable section

/-- The phase energy with interface thickness equal to the inverse spatial scale. -/
@[expose] def rescaledPhaseEnergyDensity {d : ℕ} (f : ℝ → ℝ) (R : ℝ)
    (v : Space d → ℝ) (x : Space d) : ℝ :=
  {x | 0 < v x}.indicator
    (fun x ↦ ‖gradient v x‖ ^ 2 / (2 * R) + R * normalizedPotential f (v x)) x

/-- Spatial dilation multiplies the gradient by its scale. -/
theorem gradient_comp_dilation {d : ℕ} (U : Space d → ℝ) (R : ℝ) (x : Space d) :
    gradient (fun y ↦ U (R • y)) x = R • gradient U (R • x) := by
  simp only [gradient, fderiv_comp_smul, map_smul]

/-- The rescaled density is the original density multiplied by the spatial scale. -/
theorem rescaledPhaseEnergyDensity_dilation {d : ℕ} (f : ℝ → ℝ)
    (U : Space d → ℝ) {R : ℝ} (hR : 0 < R) (x : Space d) :
    rescaledPhaseEnergyDensity f R (fun y ↦ U (R • y)) x =
      R * phaseEnergyDensity f 0 U (R • x) := by
  by_cases hx : 0 < U (R • x)
  · simp only [rescaledPhaseEnergyDensity, phaseEnergyDensity, Set.indicator_apply,
      Set.mem_ofPred_eq, hx, ite_true, gradient_comp_dilation, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, add_zero]
    field_simp
  · simp [rescaledPhaseEnergyDensity, phaseEnergyDensity, hx]

/-- Change of variables for the energy on a rescaled ball. -/
theorem integral_rescaledPhaseEnergyDensity {m : ℕ} (f : ℝ → ℝ)
    (U : Space (m + 1) → ℝ) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f R (fun y ↦ U (R • y)) x) =
      (R ^ m)⁻¹ * ∫ x in closedBall 0 (R * r), phaseEnergyDensity f 0 U x := by
  simp_rw [rescaledPhaseEnergyDensity_dilation f U hR]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume _ _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, pow_succ]
  field_simp

/-- Surface growth gives a scale-independent bound for the rescaled energy on each ball. -/
theorem RigidityHypotheses.rescaledPhaseEnergy_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 1 ≤ R * r →
      (∫ x in closedBall 0 r,
        rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) ≤
          C * r ^ m := by
  obtain ⟨C, hC, hbound⟩ := hr.phaseEnergy_surface_growth h
  refine ⟨C, hC, fun R r hR hRr ↦ ?_⟩
  rw [integral_rescaledPhaseEnergyDensity f _ hR r]
  have he := mul_le_mul_of_nonneg_left (hbound (R * r) hRr)
    (inv_nonneg.mpr (pow_nonneg hR.le m))
  calc
    _ ≤ (R ^ m)⁻¹ * (C * (R * r) ^ m) := he
    _ = C * r ^ m := by rw [mul_pow]; field_simp

end

end SerrinEpigraph
