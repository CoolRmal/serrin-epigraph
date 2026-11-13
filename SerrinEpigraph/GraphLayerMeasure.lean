module

public import SerrinEpigraph.FlatLayerMeasure
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Vertical graph coordinates preserve product volume
-/

public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Flattening a measurable graph by vertical translation preserves product Lebesgue measure. -/
theorem measurePreserving_graphFlatten {d : ℕ} {b : Space d → ℝ} (hb : Measurable b) :
    MeasurePreserving (fun p : Space d × ℝ ↦ (p.1, -b p.1 + p.2))
      ((volume : Measure (Space d)).prod volume) ((volume : Measure (Space d)).prod volume) := by
  exact (MeasurePreserving.id (volume : Measure (Space d))).skew_product
    ((hb.comp measurable_fst).neg.add measurable_snd)
    (Filter.Eventually.of_forall (fun x ↦ map_add_left_eq_self volume (-b x)))

/-- The vertical height distribution of a graph strip equals base volume times length. -/
theorem map_graphHeight_strip_volume {d : ℕ} {b : Space d → ℝ} (hb : Measurable b)
    {A : Set (Space d)} (hA : MeasurableSet A) {I : Set ℝ} (hI : MeasurableSet I) :
    Measure.map (fun p : Space d × ℝ ↦ -b p.1 + p.2)
      (((volume : Measure (Space d)).prod volume).restrict
        {p | p.1 ∈ A ∧ -b p.1 + p.2 ∈ I}) = volume A • volume.restrict I := by
  have hp := (measurePreserving_graphFlatten hb).restrict_preimage (hA.prod hI)
  have he := congrArg (Measure.map Prod.snd) hp.map_eq
  rw [Measure.map_map measurable_snd (measurePreserving_graphFlatten hb).measurable] at he
  have hs : (fun p : Space d × ℝ ↦ (p.1, -b p.1 + p.2)) ⁻¹' (A ×ˢ I) =
      {p | p.1 ∈ A ∧ -b p.1 + p.2 ∈ I} := by ext p; rfl
  simpa only [Function.comp_def, hs, map_snd_cylinder_volume] using he

/-- Any subset of a vertical graph cylinder satisfies the same height-measure bound. -/
theorem map_graphHeight_volume_le {d : ℕ} {b : Space d → ℝ} (hb : Measurable b)
    {A : Set (Space d)} (hA : MeasurableSet A) {K : Set (Space d × ℝ)}
    (hK : ∀ p ∈ K, p.1 ∈ A) :
    Measure.map (fun p : Space d × ℝ ↦ -b p.1 + p.2)
      (((volume : Measure (Space d)).prod volume).restrict K) ≤ volume A • (volume : Measure ℝ) := by
  have hs : K ⊆ {p : Space d × ℝ | p.1 ∈ A ∧ -b p.1 + p.2 ∈ (univ : Set ℝ)} :=
    fun p hp ↦ ⟨hK p hp, mem_univ _⟩
  have he := Measure.map_mono (Measure.restrict_mono hs
    (le_refl ((volume : Measure (Space d)).prod volume)))
    ((hb.comp measurable_fst).neg.add measurable_snd)
  simpa only [Pi.add_def, Pi.neg_def, Function.comp_def,
    map_graphHeight_strip_volume hb hA MeasurableSet.univ,
    Measure.restrict_univ] using he

/-- Vertical graph layers have the sharp action bound with the projected base volume. -/
theorem RigidityHypotheses.integral_recoveryLayerDensity_graph_le
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ R : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {b : Space d → ℝ} (hb : Measurable b) {A : Set (Space d)}
    (hA : MeasurableSet A) (hfin : volume A ≠ ∞) {K : Set (Space d × ℝ)}
    (hK : ∀ p ∈ K, p.1 ∈ A) :
    (∫ p in K, recoveryLayerDensity f δ R (-b p.1 + p.2)
      ∂((volume : Measure (Space d)).prod volume)) ≤
      (volume A).toReal * recoveryActionPrimitive f δ 1 := by
  have hm := map_graphHeight_volume_le hb hA hK
  have hi := (hr.integrable_recoveryLayerDensity h hδ (R := R)).smul_measure hfin
  have him := hi.mono_measure hm
  have he := integral_mono_measure hm
    (Filter.Eventually.of_forall (hr.recoveryLayerDensity_nonneg h hδ hR.le)) hi
  have hc : Measurable (fun p : Space d × ℝ ↦ -b p.1 + p.2) :=
    (hb.comp measurable_fst).neg.add measurable_snd
  rw [integral_map hc.aemeasurable
    him.aestronglyMeasurable, integral_smul_measure,
    hr.integral_recoveryLayerDensity h hδ hR, smul_eq_mul] at he
  exact he

end SerrinEpigraph
