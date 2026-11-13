module

public import SerrinEpigraph.ModicaBound
public import SerrinEpigraph.EnergyScaleMonotonicity

/-!
# Surface-scaled energy monotonicity from the original rigidity hypotheses
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Surface-scaled energy with any nonnegative decreasing radial profile is monotone. -/
theorem RigidityHypotheses.weighted_surface_energy_monotone
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hq0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ q s) (hqanti : Antitone q)
    (c : Space (m + 1)) :
    MonotoneOn (fun r ↦ r ^ (-(m : ℤ)) * ∫ x in epigraph g,
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * radialWeight q c r x) (Ioi 0) := by
  apply hr.weighted_energy_monotone_of_coefficient_nonneg h
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (-(m : ℤ)) _ hq hzero hq0 hqanti c
  intro x hx
  have hM := hr.modica_bound h hx
  simp only [Int.cast_neg, Int.cast_natCast]
  nlinarith

/-- Surface-scaled exact ball energy is monotone about every center, without an extra premise. -/
theorem RigidityHypotheses.surface_scaled_energy_monotone
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) :
    MonotoneOn (fun r ↦ r ^ (-(m : ℤ)) * ∫ x in closedBall c r,
      phaseEnergyDensity f 0 (zeroExtension g u) x) (Ioi 0) :=
  hr.surface_scaled_energy_monotone_of_modica h (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
    (fun _ hx ↦ hr.modica_bound h hx) c

end SerrinEpigraph
