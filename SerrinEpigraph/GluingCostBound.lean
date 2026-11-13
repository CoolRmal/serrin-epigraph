module

public import SerrinEpigraph.GluingTransition

/-!
# A cutoff-independent majorant for transition energy
-/

public section

open Set

namespace SerrinEpigraph

/-- A uniform cutoff gradient bound turns gluing energy into a majorant depending
only on the input energies and their squared mismatch. -/
theorem RigidityHypotheses.gluedCompetitor_energy_cost_bound_ae
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1) {R G : ℝ} (hR : 0 < R)
    (hgrad : ∀ x, ‖gradient η x‖ ≤ G) :
    ∀ᵐ x ∂MeasureTheory.volume,
      rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x ≤
        max 2 (normalizedPotential f 0 / normalizedPotential f (1 / 2)) *
          (rescaledPhaseEnergyDensity f R U x + rescaledPhaseEnergyDensity f R v x) +
        (G ^ 2 / R + 4 * R * normalizedPotential f 0) * (v x - U x) ^ 2 := by
  filter_upwards [hr.gluedCompetitor_rescaled_energy_le_ae h hU hv hη hUval hvval hηval
    (show (0 : ℝ) < 1 by norm_num) hR] with x hx
  have hKU : 0 ≤ ‖gradient U x‖ ^ 2 / (2 * R) := by positivity
  have hKv : 0 ≤ ‖gradient v x‖ ^ 2 / (2 * R) := by positivity
  have hpnonneg : ∀ w : Space d → ℝ, (∀ y, w y ∈ Icc (0 : ℝ) 1) →
      0 ≤ phasePotentialDensity f w x := by
    intro w hw
    by_cases hp : 0 < w x
    · simpa [phasePotentialDensity, hp] using hr.normalizedPotential_nonneg h (hw x)
    · simp [phasePotentialDensity, hp]
  have hPU := hpnonneg U hUval
  have hPv := hpnonneg v hvval
  have hweight : (1 - η x) * (‖gradient U x‖ ^ 2 / (2 * R)) +
      η x * (‖gradient v x‖ ^ 2 / (2 * R)) ≤
      ‖gradient U x‖ ^ 2 / (2 * R) + ‖gradient v x‖ ^ 2 / (2 * R) := by
    nlinarith [mul_nonneg (hηval x).1 hKU,
      mul_nonneg (sub_nonneg.mpr (hηval x).2) hKv]
  have hkin := mul_le_mul_of_nonneg_right
    (le_max_left (2 : ℝ) (normalizedPotential f 0 / normalizedPotential f (1 / 2)))
    (add_nonneg hKU hKv)
  have hpot := mul_le_mul_of_nonneg_right
    (le_max_right (2 : ℝ) (normalizedPotential f 0 / normalizedPotential f (1 / 2)))
    (mul_nonneg hR.le (add_nonneg hPU hPv))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (hgrad x) 2
  have herr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg (v x - U x))) hR.le
  rw [rescaledPhaseEnergyDensity_eq_kinetic_add_potential f R (fun y ↦ (hUval y).1),
    rescaledPhaseEnergyDensity_eq_kinetic_add_potential f R (fun y ↦ (hvval y).1)]
  norm_num only [div_one, Real.norm_eq_abs, sq_abs] at hx
  have he : 2 * (v x - U x) ^ 2 * ‖gradient η x‖ ^ 2 / (2 * R) =
      (v x - U x) ^ 2 * ‖gradient η x‖ ^ 2 / R := by ring
  rw [he] at hx
  ring_nf at hx hweight hkin hpot herr ⊢
  linarith only [hx, hweight, hkin, hpot, herr]

/-- The explicit input-energy and mismatch majorant is needed only on the transition set. -/
theorem RigidityHypotheses.gluedCompetitor_localized_cost_bound_ae
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1) {R G : ℝ} (hR : 0 < R)
    (hgrad : ∀ x, ‖gradient η x‖ ≤ G) :
    ∀ᵐ x ∂MeasureTheory.volume,
      rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x ≤
        (1 - η x) * rescaledPhaseEnergyDensity f R U x +
        η x * rescaledPhaseEnergyDensity f R v x +
        {y | 0 < η y ∧ η y < 1}.indicator (fun y ↦
          max 2 (normalizedPotential f 0 / normalizedPotential f (1 / 2)) *
            (rescaledPhaseEnergyDensity f R U y + rescaledPhaseEnergyDensity f R v y) +
          (G ^ 2 / R + 4 * R * normalizedPotential f 0) * (v y - U y) ^ 2) x := by
  apply rescaledEnergy_glued_le_transition_bound_ae f R hU hv hη hηval
    (hr.rescaledPhaseEnergyDensity_nonneg h hR.le hUval)
    (hr.rescaledPhaseEnergyDensity_nonneg h hR.le hvval)
  filter_upwards [hr.gluedCompetitor_energy_cost_bound_ae h hU hv hη hUval hvval hηval
    hR hgrad] with x hx
  exact fun _ ↦ hx

end SerrinEpigraph
