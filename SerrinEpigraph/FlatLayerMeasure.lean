module

public import SerrinEpigraph.RecoveryMeasureBound

/-!
# Exact coordinate distributions and layer integrals in flat cylinders
-/

public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Projection of a flat cylinder gives cross-sectional volume times length. -/
theorem map_snd_cylinder_volume {d : ℕ} (A : Set (Space d)) (I : Set ℝ) :
    Measure.map Prod.snd (((volume : Measure (Space d)).prod volume).restrict (A ×ˢ I)) =
      volume A • volume.restrict I := by
  rw [← Measure.prod_restrict, Measure.map_snd_prod, Measure.restrict_apply_univ]

/-- Any subset of a flat cylinder has normal-coordinate distribution bounded by its base volume. -/
theorem map_snd_volume_le_of_subset_cylinder {d : ℕ} {A : Set (Space d)}
    {K : Set (Space d × ℝ)} (hK : K ⊆ A ×ˢ univ) :
    Measure.map Prod.snd (((volume : Measure (Space d)).prod volume).restrict K) ≤
      volume A • (volume : Measure ℝ) := by
  have he := Measure.map_mono
    (Measure.restrict_mono hK (le_refl ((volume : Measure (Space d)).prod volume))) measurable_snd
  simpa only [map_snd_cylinder_volume, Measure.restrict_univ] using he

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- The layer integral over a full flat cylinder is exactly base volume times action. -/
theorem RigidityHypotheses.integral_recoveryLayerDensity_cylinder
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {A : Set (Space d)} (hA : volume A ≠ ∞) :
    (∫ p in A ×ˢ (univ : Set ℝ), recoveryLayerDensity f δ R p.2
      ∂((volume : Measure (Space d)).prod volume)) =
      (volume A).toReal * recoveryActionPrimitive f δ 1 := by
  have hi := (hr.integrable_recoveryLayerDensity h hδ (R := R)).smul_measure hA
  have hm := map_snd_cylinder_volume A (univ : Set ℝ)
  rw [Measure.restrict_univ] at hm
  have him : Integrable (recoveryLayerDensity f δ R)
      (Measure.map Prod.snd (((volume : Measure (Space d)).prod volume).restrict (A ×ˢ univ))) := by
    rw [hm]
    exact hi
  rw [← integral_map measurable_snd.aemeasurable him.aestronglyMeasurable, hm,
    integral_smul_measure, hr.integral_recoveryLayerDensity h hδ hR, smul_eq_mul]

/-- The same sharp bound holds on arbitrary subsets of a flat cylinder. -/
theorem RigidityHypotheses.integral_recoveryLayerDensity_le_cylinder
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {A : Set (Space d)} (hA : volume A ≠ ∞) {K : Set (Space d × ℝ)}
    (hK : K ⊆ A ×ˢ univ) :
    (∫ p in K, recoveryLayerDensity f δ R p.2 ∂((volume : Measure (Space d)).prod volume)) ≤
      (volume A).toReal * recoveryActionPrimitive f δ 1 := by
  have hm := map_snd_volume_le_of_subset_cylinder hK
  have hi := (hr.integrable_recoveryLayerDensity h hδ (R := R)).smul_measure hA
  have him := hi.mono_measure hm
  have he := integral_mono_measure hm
    (Filter.Eventually.of_forall (hr.recoveryLayerDensity_nonneg h hδ hR.le)) hi
  rw [integral_map measurable_snd.aemeasurable him.aestronglyMeasurable,
    integral_smul_measure, hr.integral_recoveryLayerDensity h hδ hR, smul_eq_mul] at he
  exact he

end SerrinEpigraph
