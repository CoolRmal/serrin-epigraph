module

public import SerrinEpigraph.RecoveryLayerMass

/-!
# Sharp recovery bounds from domination of the distance distribution
-/

public section

open Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- A measure dominated by a multiple of length has layer integral bounded by that multiple
of the exact action. -/
theorem RigidityHypotheses.recoveryLayerDensity_integral_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {μ : Measure ℝ} {P : ℝ≥0} (hμ : μ ≤ (P : ℝ≥0∞) • volume) :
    (∫ s, recoveryLayerDensity f δ R s ∂μ) ≤ (P : ℝ) * recoveryActionPrimitive f δ 1 := by
  have hi := (hr.integrable_recoveryLayerDensity h hδ (R := R)).smul_measure_nnreal (c := P)
  have he := integral_mono_measure hμ
    (Filter.Eventually.of_forall (hr.recoveryLayerDensity_nonneg h hδ hR.le)) hi
  simpa only [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul,
    hr.integral_recoveryLayerDensity h hδ hR] using he

/-- Domination of the transition layer's coordinate distribution gives the sharp energy upper bound.
The geometric domination premise is separate from the analytic recovery construction. -/
theorem RigidityHypotheses.geometricRecoveryProfile_energy_le_of_map_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {ρ : Space d → ℝ} (hρ : LipschitzWith 1 ρ) {K : Set (Space d)} (hK : IsCompact K)
    {P : ℝ≥0}
    (hmap : Measure.map ρ (volume.restrict
      (K ∩ {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)})) ≤ (P : ℝ≥0∞) • volume) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x) ≤
      (P : ℝ) * recoveryActionPrimitive f δ 1 := by
  let S := K ∩ {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)}
  have hS : MeasurableSet S := hK.measurableSet.inter
    (measurableSet_Ioo.preimage (continuous_const.mul hρ.continuous).measurable)
  have hi := ((hr.integrable_recoveryLayerDensity h hδ (R := R)).smul_measure_nnreal
    (c := P)).mono_measure hmap
  have he := hr.recoveryLayerDensity_integral_le h hδ hR hmap
  rw [integral_map hρ.continuous.measurable.aemeasurable hi.aestronglyMeasurable] at he
  apply (hr.geometricRecoveryProfile_integral_energy_le h hδ hR hρ hK).trans
  have heq : (∫ x in S, R *
      (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)) =
      ∫ x in S, recoveryLayerDensity f δ R (ρ x) := by
    apply setIntegral_congr_fun hS
    intro x hx
    have hx' : ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1 / R) := by
      exact ⟨(mul_pos_iff_of_pos_left hR).mp hx.2.1,
        (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hx.2.2)⟩
    simp only [recoveryLayerDensity, indicator_of_mem hx', geometricRecoveryProfile]
  rw [heq]
  exact he

end SerrinEpigraph
