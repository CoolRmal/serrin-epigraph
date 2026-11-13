module

public import SerrinEpigraph.GraphRecoveryBound

/-!
# Recovery bounds requiring gradient control only on the integration region
-/

public section

open Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ} {ρ : Space d → ℝ}

/-- A smooth coordinate needs unit-gradient control only on the compact integration region. -/
theorem RigidityHypotheses.geometricRecoveryProfile_local_integral_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    (hρ : ContDiff ℝ 1 ρ) {K : Set (Space d)} (hK : IsCompact K)
    (hg : ∀ x ∈ K, ‖gradient ρ x‖ ≤ 1) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (geometricRecoveryProfile f δ R ρ) x) ≤
      ∫ x in K ∩ {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)},
        R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ) := by
  have hs : ContDiff ℝ 1 (fun x ↦ R * ρ x) := contDiff_const.mul hρ
  have hv : LocallyLipschitz (geometricRecoveryProfile f δ R ρ) :=
    (hr.recoveryProfile_lipschitz h hδ).locallyLipschitz.comp hs.locallyLipschitz
  have hval := hr.geometricRecoveryProfile_mem_Icc h hδ (R := R) (ρ := ρ)
  have hi := h.integrableOn_rescaledPhaseEnergy hv hval R hK
  have hW := h.normalizedPotential_continuousOn.comp_continuous hv.continuous hval
  have hc : Continuous (fun x ↦
      R * (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)) :=
    continuous_const.mul ((continuous_const.mul hW).add continuous_const)
  have hS : MeasurableSet {y | R * ρ y ∈ Ioo 0 (recoveryTravelTime f δ 1)} :=
    measurableSet_Ioo.preimage hs.continuous.measurable
  have hj := (hc.continuousOn.integrableOn_compact (μ := volume) hK).indicator hS
  have he := integral_mono_ae hi hj (ae_restrict_of_forall_mem hK.measurableSet
    (fun x hx ↦ hr.geometricRecoveryProfile_localized_energy_le h hδ hR
      (hρ.differentiable (by norm_num) x) (hg x hx)))
  rwa [setIntegral_indicator hS] at he

/-- Local gradient bounds and transition-coordinate measure domination give a sharp energy bound. -/
theorem RigidityHypotheses.geometricRecoveryProfile_local_energy_le_of_map_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    (hρ : ContDiff ℝ 1 ρ) {K : Set (Space d)} (hK : IsCompact K)
    (hg : ∀ x ∈ K, ‖gradient ρ x‖ ≤ 1) {P : ℝ≥0}
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
  apply (hr.geometricRecoveryProfile_local_integral_energy_le h hδ hR hρ hK hg).trans
  have heq : (∫ x in S, R *
      (2 * normalizedPotential f (geometricRecoveryProfile f δ R ρ x) + δ)) =
      ∫ x in S, recoveryLayerDensity f δ R (ρ x) := by
    apply setIntegral_congr_fun hS
    intro x hx
    have hx' : ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1 / R) :=
      ⟨(mul_pos_iff_of_pos_left hR).mp hx.2.1,
        (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hx.2.2)⟩
    simp only [recoveryLayerDensity, indicator_of_mem hx', geometricRecoveryProfile]
  rw [heq]
  exact he

/-- Smooth graph recovery needs slope control only above the integration region. -/
theorem RigidityHypotheses.graphRecovery_local_integral_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {L : ℝ} (hL : 0 < L)
    {A : Set (Space d)} (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    {K : Set (Space (d + 1))} (hK : IsCompact K) (hproj : ∀ x ∈ K, horizontal x ∈ A)
    (hslope : ∀ x ∈ K, 1 + ‖gradient b (horizontal x)‖ ^ 2 ≤ L ^ 2) :
    (∫ x in K, rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun y ↦ graphHeight b y / L)) x) ≤
      ((volume A).toReal * L) * recoveryActionPrimitive f δ 1 := by
  have hc : ContDiff ℝ 1 (graphHeight b) :=
    (PiLp.proj 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).contDiff.sub
      (hb.comp horizontalContinuousLinearMap.contDiff)
  have hn : ContDiff ℝ 1 (fun y ↦ graphHeight b y / L) := by
    simpa only [div_eq_mul_inv] using hc.mul contDiff_const
  let P : ℝ≥0 := ⟨(volume A).toReal * L, mul_nonneg ENNReal.toReal_nonneg hL.le⟩
  have hP : (P : ℝ≥0∞) = volume A * ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((volume A).toReal * L) = _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
  have hm := map_euclidean_graphHeight_volume_le hb.continuous.measurable hA
    (fun x (hx : x ∈ K ∩ {y | R * (graphHeight b y / L) ∈
      Ioo 0 (recoveryTravelTime f δ 1)}) ↦ hproj x hx.1) hL
  rw [← hP] at hm
  apply hr.geometricRecoveryProfile_local_energy_le_of_map_le h hδ hR hn hK _ hm
  intro x hx
  exact norm_gradient_normalizedGraphHeight_le
    (hb.differentiable (by norm_num) (horizontal x)) hL (hslope x hx)

end SerrinEpigraph
