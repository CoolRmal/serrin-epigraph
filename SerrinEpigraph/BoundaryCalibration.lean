module

public import SerrinEpigraph.PhaseEnergy
public import SerrinEpigraph.BoundaryGradient

/-!
# Calibration inequality including the zero phase

The energy offset is the measured boundary value, not an assumed normalization.
-/

public section

noncomputable section

open InnerProductSpace

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The closed calibration shifted to vanish on the zero phase. -/
@[expose] def RigidityHypotheses.boundaryCalibratedDensity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (y : Space m) (s : ℝ) (z : Space (m + 1)) : ℝ :=
  inner ℝ (hr.closedLevelGradient h (y, s)) z -
    ‖hr.closedLevelGradient h (y, s)‖ ^ 2 / 2 + normalizedPotential f s +
      (κ ^ 2 / 2 - normalizedPotential f 0)

/-- The shifted closed calibration vanishes at zero level and zero gradient. -/
theorem RigidityHypotheses.boundaryCalibratedDensity_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    hr.boundaryCalibratedDensity h y 0 0 = 0 := by
  simp only [boundaryCalibratedDensity, inner_zero_right,
    hr.norm_closedLevelGradient_zero h y]
  ring

/-- The calibration deficit is exactly half the squared gradient mismatch. -/
theorem RigidityHypotheses.boundaryCalibratedDensity_deficit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (y : Space m) (s : ℝ) (z : Space (m + 1)) :
    ‖z‖ ^ 2 / 2 + normalizedPotential f s +
        (κ ^ 2 / 2 - normalizedPotential f 0) - hr.boundaryCalibratedDensity h y s z =
      ‖hr.closedLevelGradient h (y, s) - z‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real]
  unfold boundaryCalibratedDensity
  ring

/-- The closed calibration bounds the phase energy of every nonnegative competitor. -/
theorem RigidityHypotheses.boundaryCalibratedDensity_le_phaseEnergy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : ∀ x, 0 ≤ v x) (x : Space (m + 1)) :
    hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x) ≤
      phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) v x := by
  by_cases hp : 0 < v x
  · rw [phaseEnergyDensity, Set.indicator_of_mem (s := {z | 0 < v z}) hp]
    have he := hr.boundaryCalibratedDensity_deficit h (horizontal x) (v x) (gradient v x)
    have hn := sq_nonneg ‖hr.closedLevelGradient h (horizontal x, v x) - gradient v x‖
    linarith
  · have hz : v x = 0 := le_antisymm (not_lt.mp hp) (hv x)
    have hmin : IsLocalMin v x := by
      filter_upwards with y
      simpa only [hz] using hv y
    have hg : gradient v x = 0 := by simp only [gradient, hmin.fderiv_eq_zero, map_zero]
    rw [hz, hg, hr.boundaryCalibratedDensity_zero h]
    simp only [phaseEnergyDensity, Set.indicator_of_notMem (s := {z | 0 < v z}) hp, le_refl]

/-- The zero extension attains equality, including outside its positive phase. -/
theorem RigidityHypotheses.boundaryCalibratedDensity_zeroExtension
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    hr.boundaryCalibratedDensity h (horizontal x) (zeroExtension g u x)
        (gradient (zeroExtension g u) x) =
      phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) (zeroExtension g u) x := by
  by_cases hx : x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff x).mpr hx
    rw [phaseEnergyDensity, Set.indicator_of_mem (s := {z | 0 < zeroExtension g u z}) hp,
      h.gradient_zeroExtension hx, zeroExtension_of_mem hx]
    unfold boundaryCalibratedDensity
    rw [hr.closedLevelGradient_eq h ⟨h.positive x hx, hr.solution_lt_one x hx⟩,
      hr.levelGradient_solution h hx, real_inner_self_eq_norm_sq]
    ring
  · have hp : ¬0 < zeroExtension g u x := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
    rw [phaseEnergyDensity, Set.indicator_of_notMem (s := {z | 0 < zeroExtension g u z}) hp,
      h.gradient_zeroExtension_of_notMem hx, zeroExtension_of_notMem hx,
      hr.boundaryCalibratedDensity_zero h]

end SerrinEpigraph
