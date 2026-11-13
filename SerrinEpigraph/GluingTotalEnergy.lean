module

public import SerrinEpigraph.GluingGradientEnergy
public import SerrinEpigraph.GluingPotentialEnergy

/-!
# Total rescaled energy of cutoff gluing
-/

public section

open Set

namespace SerrinEpigraph

/-- For a nonnegative function the totalized gradient vanishes on the zero phase,
so the kinetic term needs no phase indicator. -/
theorem rescaledPhaseEnergyDensity_eq_kinetic_add_potential {d : ℕ}
    (f : ℝ → ℝ) (R : ℝ) {v : Space d → ℝ} (hv : ∀ x, 0 ≤ v x) (x : Space d) :
    rescaledPhaseEnergyDensity f R v x =
      ‖gradient v x‖ ^ 2 / (2 * R) + R * phasePotentialDensity f v x := by
  by_cases hp : 0 < v x
  · simp [rescaledPhaseEnergyDensity, phasePotentialDensity, hp]
  · have hz : v x = 0 := le_antisymm (le_of_not_gt hp) (hv x)
    have hmin : IsLocalMin v x := by
      filter_upwards with y
      rw [hz]
      exact hv y
    have hg : gradient v x = 0 := by
      simp only [gradient, hmin.fderiv_eq_zero, map_zero]
    simp [rescaledPhaseEnergyDensity, phasePotentialDensity, hp, hg]

/-- The full diffuse energy of a glued competitor has controlled kinetic and potential
costs, including the mismatch terms at the zero phase. -/
theorem RigidityHypotheses.gluedCompetitor_rescaled_energy_le_ae
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ∀ᵐ x ∂MeasureTheory.volume,
      rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x ≤
        (1 + δ) * ((1 - η x) * (‖gradient U x‖ ^ 2 / (2 * R)) +
          η x * (‖gradient v x‖ ^ 2 / (2 * R))) +
        R * (normalizedPotential f 0 / normalizedPotential f (1 / 2)) *
          (phasePotentialDensity f U x + phasePotentialDensity f v x) +
        (1 + 1 / δ) * ‖v x - U x‖ ^ 2 * ‖gradient η x‖ ^ 2 / (2 * R) +
        4 * R * normalizedPotential f 0 * (v x - U x) ^ 2 := by
  filter_upwards [gluedCompetitor_kinetic_energy_le_ae hU hv hη hηval hδ hR] with x hx
  rw [rescaledPhaseEnergyDensity_eq_kinetic_add_potential f R
    (fun y ↦ (gluedCompetitor_mem_Icc hUval hvval hηval y).1)]
  have hp := mul_le_mul_of_nonneg_left
    (hr.gluedCompetitor_potential_le h hUval hvval hηval x) hR.le
  calc
    _ ≤ _ := add_le_add hx hp
    _ = _ := by ring

end SerrinEpigraph
