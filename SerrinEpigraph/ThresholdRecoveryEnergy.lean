module

public import SerrinEpigraph.ThresholdCoordinateGradient

/-!
# Energy bounds for variable-width threshold recovery
-/

public section

open Set

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- A coordinate gradient bound above one costs only its square in the
localized transition-density majorant. -/
theorem RigidityHypotheses.geometricRecovery_energy_le_mul_layer
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {ρ : Space d → ℝ} {x : Space d}
    (hρ : DifferentiableAt ℝ ρ x) {G : ℝ} (hG : 1 ≤ G)
    (hgrad : R * ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1) → ‖gradient ρ x‖ ≤ G) :
    rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x ≤
      G ^ 2 * recoveryLayerDensity f δ R (ρ x) := by
  have hs : R * ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1) ↔
      ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1 / R) := by
    simp only [mem_Ioo, lt_div_iff₀ hR, mul_comm R, mul_pos_iff_of_pos_right hR]
  by_cases ht : R * ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1)
  · have hq := hr.recoveryProfileCore_mem_Ioo h hδ ht
    have heq : geometricRecoveryProfile f δ R ρ x = recoveryProfileCore f δ (R * ρ x) :=
      recoveryProfile_eq_core ⟨ht.1.le, ht.2.le⟩
    have hp : 0 < geometricRecoveryProfile f δ R ρ x := by rw [heq]; exact hq.1
    have hw := hr.normalizedPotential_nonneg h
      (hr.geometricRecoveryProfile_mem_Icc h hδ (R := R) (ρ := ρ) x)
    have hsq : ‖gradient ρ x‖ ^ 2 ≤ G ^ 2 := by nlinarith [hgrad ht, norm_nonneg (gradient ρ x)]
    have hGsq : 1 ≤ G ^ 2 := by nlinarith
    rw [recoveryLayerDensity, indicator_of_mem (hs.mp ht)]
    simp only [rescaledPhaseEnergyDensity, indicator_apply, mem_ofPred_eq, hp, ite_true]
    rw [hr.gradient_geometricRecoveryProfile h hδ hρ ht, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR.le), mul_pow, mul_pow,
      Real.sq_sqrt (show 0 ≤ 2 *
        (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) by positivity)]
    have hkin : 2 * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) *
        R ^ 2 * ‖gradient ρ x‖ ^ 2 / (2 * R) =
        R * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) *
          ‖gradient ρ x‖ ^ 2 := by field_simp
    rw [hkin]
    have hk := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ R * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)
        by positivity)
    have hw' := mul_le_mul_of_nonneg_right hGsq (mul_nonneg hR.le hw)
    change _ ≤ G ^ 2 * (R * (2 * normalizedPotential f
      (geometricRecoveryProfile f δ R ρ x) + δ))
    nlinarith
  · rw [hr.geometricRecoveryProfile_energy_zero h hδ ht, recoveryLayerDensity,
      indicator_of_notMem (fun hh ↦ ht (hs.mpr hh)), mul_zero]

/-- Within the transition layer, the variable width changes the energy by
a factor tending to one as the prescribed scale tends to infinity. -/
theorem RigidityHypotheses.thresholdRecovery_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {φ a : Space d → ℝ} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) (ha : DifferentiableAt ℝ a x) (hpos : 0 < a x)
    (hgrad : ‖gradient φ x‖ ≤ a x) {C : ℝ} (hC : 0 ≤ C)
    (hrel : ‖gradient a x‖ / a x ≤ C) (t : ℝ) :
    rescaledPhaseEnergyDensity f R (thresholdRecovery f δ R φ a t) x ≤
      (1 + recoveryTravelTime f δ 1 * C / R) ^ 2 *
        recoveryLayerDensity f δ R (thresholdCoordinate φ a t x) := by
  have hρ : DifferentiableAt ℝ (thresholdCoordinate φ a t) x := by
    unfold thresholdCoordinate
    simp only [div_eq_mul_inv]
    exact (hφ.sub_const t).mul
      ((hasDerivAt_inv hpos.ne').comp_hasFDerivAt x ha.hasFDerivAt).differentiableAt
  have hG : 1 ≤ 1 + recoveryTravelTime f δ 1 * C / R := by
    have hT := hr.recoveryTravelTime_one_pos h hδ
    have hp : 0 ≤ recoveryTravelTime f δ 1 * C / R := by positivity
    linarith
  apply hr.geometricRecovery_energy_le_mul_layer h hδ hR hρ hG
  intro ht
  have hρpos : 0 < thresholdCoordinate φ a t x := (mul_pos_iff_of_pos_left hR).mp ht.1
  have hρle : ‖thresholdCoordinate φ a t x‖ ≤ recoveryTravelTime f δ 1 / R := by
    rw [Real.norm_of_nonneg hρpos.le]
    exact ((lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using ht.2)).le
  have hrelpos : 0 ≤ ‖gradient a x‖ / a x := div_nonneg (norm_nonneg _) hpos.le
  have he := mul_le_mul hρle hrel hrelpos
    (div_nonneg (hr.recoveryTravelTime_one_pos h hδ).le hR.le)
  have hg := norm_gradient_thresholdCoordinate_le hφ ha hpos hgrad t
  rw [div_mul_eq_mul_div] at he
  exact hg.trans (add_le_add le_rfl he)

end SerrinEpigraph
