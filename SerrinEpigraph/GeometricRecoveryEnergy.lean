module

public import SerrinEpigraph.GeometricRecoveryProfile

/-!
# Interior energy of geometric recovery profiles
-/

public section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- On the transition interval the extension agrees with its inverse-profile core. -/
theorem recoveryProfile_eq_core {t : ℝ} (ht : t ∈ Icc 0 (recoveryTravelTime f δ 1)) :
    recoveryProfile f δ t = recoveryProfileCore f δ t := by
  simp only [recoveryProfile, max_eq_left ht.1, min_eq_left ht.2]

/-- The extended profile obeys the transition ODE at every interior transition time. -/
theorem RigidityHypotheses.recoveryProfile_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Ioo 0 (recoveryTravelTime f δ 1)) :
    HasDerivAt (recoveryProfile f δ)
      (Real.sqrt (2 * (normalizedPotential f (recoveryProfile f δ t) + δ))) t := by
  rw [recoveryProfile_eq_core ⟨ht.1.le, ht.2.le⟩]
  apply (hr.recoveryProfileCore_hasDerivAt h hδ ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact recoveryProfile_eq_core ⟨hs.1.le, hs.2.le⟩

/-- The spatial gradient is the regularized speed times the scaled coordinate gradient. -/
theorem RigidityHypotheses.gradient_geometricRecoveryProfile
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {ρ : Space d → ℝ} {x : Space d} (hρ : DifferentiableAt ℝ ρ x)
    (ht : R * ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1)) :
    gradient (geometricRecoveryProfile f δ R ρ) x =
      (Real.sqrt (2 * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)) * R) •
        gradient ρ x := by
  have hd := (hr.recoveryProfile_hasDerivAt h hδ ht).comp_hasFDerivAt x
    (hρ.hasFDerivAt.const_mul R)
  have he : fderiv ℝ (geometricRecoveryProfile f δ R ρ) x =
      (Real.sqrt (2 * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)) * R) •
        fderiv ℝ ρ x := by
    change fderiv ℝ (fun y ↦ recoveryProfile f δ (R * ρ y)) x = _
    simpa only [Function.comp_def, geometricRecoveryProfile, smul_smul] using hd.fderiv
  simp only [gradient, he, map_smul]

/-- Coordinates of gradient norm at most one give the one-dimensional interior energy bound. -/
theorem RigidityHypotheses.geometricRecoveryProfile_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {ρ : Space d → ℝ} {x : Space d} (hρ : DifferentiableAt ℝ ρ x)
    (ht : R * ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1)) (hg : ‖gradient ρ x‖ ≤ 1) :
    rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x ≤
      R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) := by
  have hval := hr.recoveryProfileCore_mem_Ioo h hδ ht
  have heq : geometricRecoveryProfile f δ R ρ x = recoveryProfileCore f δ (R * ρ x) :=
    recoveryProfile_eq_core ⟨ht.1.le, ht.2.le⟩
  have hp : 0 < geometricRecoveryProfile f δ R ρ x := by rw [heq]; exact hval.1
  have hw := hr.normalizedPotential_nonneg h
    (hr.geometricRecoveryProfile_mem_Icc h hδ (R := R) (ρ := ρ) x)
  simp only [rescaledPhaseEnergyDensity, indicator_apply, mem_ofPred_eq, hp, ite_true]
  rw [hr.gradient_geometricRecoveryProfile h hδ hρ ht, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR.le), mul_pow, mul_pow,
    Real.sq_sqrt (show 0 ≤ 2 *
      (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) by positivity)]
  have hgsq : ‖gradient ρ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (gradient ρ x)]
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgsq
      (show 0 ≤ 2 * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) * R ^ 2
        by positivity)) (show 0 ≤ 2 * R by positivity)
  have he : (2 * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) * R ^ 2 * 1) /
      (2 * R) = R * (normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) := by
    field_simp
  rw [he] at hb
  linarith

end SerrinEpigraph
