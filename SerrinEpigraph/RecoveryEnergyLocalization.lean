module

public import SerrinEpigraph.GeometricRecoveryEnergy
public import SerrinEpigraph.GluingTransition
public import SerrinEpigraph.GluingCostIntegral

/-!
# Localization of recovery energy to the open transition layer
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- A normalized competitor has zero phase energy at either pure phase. -/
theorem rescaledPhaseEnergyDensity_eq_zero_of_endpoint {d : ℕ}
    (f : ℝ → ℝ) (R : ℝ) {v : Space d → ℝ} (hv : ∀ y, v y ∈ Icc (0 : ℝ) 1)
    {x : Space d} (hx : v x = 0 ∨ v x = 1) :
    rescaledPhaseEnergyDensity f R v x = 0 := by
  have hg := gradient_cutoff_eq_zero_of_endpoint hv hx
  rcases hx with hx | hx <;>
    simp [rescaledPhaseEnergyDensity, hx, hg, normalizedPotential_one]

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ} {ρ : Space d → ℝ} {x : Space d}

/-- Recovery energy vanishes outside the open transition layer, including its endpoints. -/
theorem RigidityHypotheses.geometricRecoveryProfile_energy_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    (hx : R * ρ x ∉ Ioo 0 (recoveryTravelTime f δ 1)) :
    rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x = 0 := by
  apply rescaledPhaseEnergyDensity_eq_zero_of_endpoint f R
    (hr.geometricRecoveryProfile_mem_Icc h hδ)
  by_cases hs : R * ρ x ≤ 0
  · exact Or.inl (hr.recoveryProfile_eq_zero h hδ hs)
  · have ht : recoveryTravelTime f δ 1 ≤ R * ρ x :=
      le_of_not_gt (fun ht ↦ hx ⟨lt_of_not_ge hs, ht⟩)
    exact Or.inr (hr.recoveryProfile_eq_one h hδ ht)

/-- The global density bound is supported precisely on the open transition layer. -/
theorem RigidityHypotheses.geometricRecoveryProfile_localized_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    (hρ : DifferentiableAt ℝ ρ x) (hg : ‖gradient ρ x‖ ≤ 1) :
    rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x ≤
      {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)}.indicator
        (fun y ↦ R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ y) + δ)) x := by
  by_cases hx : R * ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1)
  · simpa only [indicator_apply, mem_ofPred_eq, hx, ite_true] using
      hr.geometricRecoveryProfile_energy_le h hδ hR hρ hx hg
  · simp only [indicator_apply, mem_ofPred_eq, hx, ite_false,
      hr.geometricRecoveryProfile_energy_zero h hδ hx, le_refl]

/-- On compact sets, a one-Lipschitz coordinate bounds the energy by its transition-layer integral. -/
theorem RigidityHypotheses.geometricRecoveryProfile_integral_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    (hρ : LipschitzWith 1 ρ) {K : Set (Space d)} (hK : IsCompact K) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x) ≤
      ∫ x in K ∩ {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)},
        R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) := by
  have hv := hr.geometricRecoveryProfile_lipschitz h hδ (R := R) hρ
  have hval := hr.geometricRecoveryProfile_mem_Icc h hδ (R := R) (ρ := ρ)
  have hi := h.integrableOn_rescaledPhaseEnergy hv.locallyLipschitz hval R hK
  have hW := h.normalizedPotential_continuousOn.comp_continuous hv.continuous hval
  have hc : Continuous (fun x ↦
      R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)) :=
    continuous_const.mul ((continuous_const.mul hW).add continuous_const)
  have hS : MeasurableSet {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)} :=
    measurableSet_Ioo.preimage (continuous_const.mul hρ.continuous).measurable
  have hj := (hc.continuousOn.integrableOn_compact (μ := volume) hK).indicator hS
  have hb : ∀ᵐ x, rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x ≤
      {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)}.indicator
        (fun y ↦ R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ y) + δ)) x := by
    filter_upwards [ae_differentiableAt_of_locallyLipschitz hρ.locallyLipschitz] with x hx
    apply hr.geometricRecoveryProfile_localized_energy_le h hδ hR hx
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hρ
  have he := integral_mono_ae hi hj (ae_restrict_of_ae hb)
  rwa [setIntegral_indicator hS] at he

end SerrinEpigraph
