module

public import SerrinEpigraph.GraphLayerMeasure

/-!
# Measure bounds after normalization of graph height
-/

public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Dividing a real coordinate by a positive scale multiplies its measure bound by that scale. -/
theorem map_div_le_smul_volume {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ} (hρ : Measurable ρ) {C : ℝ≥0∞}
    (hmap : Measure.map ρ μ ≤ C • volume) {L : ℝ} (hL : 0 < L) :
    Measure.map (fun x ↦ ρ x / L) μ ≤ (C * ENNReal.ofReal L) • volume := by
  have hs : Measurable (fun t : ℝ ↦ L⁻¹ * t) := measurable_const.mul measurable_id
  have he := Measure.map_mono hmap hs
  rw [Measure.map_map hs hρ, Measure.map_smul _ hs.aemeasurable,
    Real.map_volume_mul_left (inv_ne_zero hL.ne'), inv_inv, abs_of_pos hL, smul_smul] at he
  simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using he

/-- A normalized graph height has distribution bounded by normalization scale times base volume. -/
theorem map_normalizedGraphHeight_volume_le {d : ℕ} {b : Space d → ℝ} (hb : Measurable b)
    {A : Set (Space d)} (hA : MeasurableSet A) {K : Set (Space d × ℝ)}
    (hK : ∀ p ∈ K, p.1 ∈ A) {L : ℝ} (hL : 0 < L) :
    Measure.map (fun p : Space d × ℝ ↦ (-b p.1 + p.2) / L)
      (((volume : Measure (Space d)).prod volume).restrict K) ≤
      (volume A * ENNReal.ofReal L) • (volume : Measure ℝ) := by
  apply map_div_le_smul_volume _ (map_graphHeight_volume_le hb hA hK) hL
  exact (hb.comp measurable_fst).neg.add measurable_snd

/-- Normalized graph layers retain the sharp action bound with the normalization factor. -/
theorem RigidityHypotheses.integral_recoveryLayerDensity_normalizedGraph_le
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ R L : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {b : Space d → ℝ} (hb : Measurable b) {A : Set (Space d)}
    (hA : MeasurableSet A) (hfin : volume A ≠ ∞) {K : Set (Space d × ℝ)}
    (hK : ∀ p ∈ K, p.1 ∈ A) (hL : 0 < L) :
    (∫ p in K, recoveryLayerDensity f δ R ((-b p.1 + p.2) / L)
      ∂((volume : Measure (Space d)).prod volume)) ≤
      ((volume A).toReal * L) * recoveryActionPrimitive f δ 1 := by
  have hm := map_normalizedGraphHeight_volume_le hb hA hK hL
  have hi := (hr.integrable_recoveryLayerDensity h hδ (R := R)).smul_measure
    (show volume A * ENNReal.ofReal L ≠ ∞ from ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
  have him := hi.mono_measure hm
  have he := integral_mono_measure hm
    (Filter.Eventually.of_forall (hr.recoveryLayerDensity_nonneg h hδ hR.le)) hi
  have hc : Measurable (fun p : Space d × ℝ ↦ (-b p.1 + p.2) / L) :=
    ((hb.comp measurable_fst).neg.add measurable_snd).div_const L
  rw [integral_map hc.aemeasurable him.aestronglyMeasurable, integral_smul_measure,
    hr.integral_recoveryLayerDensity h hδ hR, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hL.le] at he
  exact he

end SerrinEpigraph
