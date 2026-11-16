module

public import SerrinEpigraph.MeasurablePhaseMollification

/-!
# A measurable representative with pointwise vertical order
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric ContinuousLinearMap
open scoped Topology Convolution

namespace SerrinEpigraph

/-- Points at which the smooth phase averages converge to one. -/
@[expose] def orderedPhaseRepresentative {d : ℕ} (E : Set (Space d)) : Set (Space d) :=
  {x | Tendsto (fun n ↦ mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x) atTop (𝓝 1)}

/-- The smooth-average representative is measurable. -/
theorem measurableSet_orderedPhaseRepresentative {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) : MeasurableSet (orderedPhaseRepresentative E) := by
  apply measurableSet_tendsto (𝓝 1)
  intro n
  have hc := mollify_contDiff_of_locallyIntegrable (locallyIntegrable_phaseIndicator hE) n
  exact hc.continuous.measurable

/-- Choosing the smooth-average representative changes the phase only on a null set. -/
theorem orderedPhaseRepresentative_ae_eq {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) : orderedPhaseRepresentative E =ᵐ[volume] E := by
  filter_upwards [mollify_tendsto_ae_of_locallyIntegrable
    (locallyIntegrable_phaseIndicator hE)] with x hx
  apply propext
  change Tendsto _ atTop (𝓝 1) ↔ x ∈ E
  constructor
  · intro hrep
    have he := tendsto_nhds_unique hx hrep
    by_contra hnot
    simp only [indicator_of_notMem hnot] at he
    norm_num at he
  · intro hxE
    simpa only [indicator_of_mem hxE] using hx

/-- Almost-everywhere inclusion under a translation gives pointwise order of every
smooth average, with no exceptional points. -/
theorem mollify_phaseIndicator_translation_le {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) {z : Space d}
    (hz : ∀ᵐ x ∂volume, x ∈ E → x + z ∈ E) (n : ℕ) (x : Space d) :
    mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x ≤
      mollify (E.indicator (fun _ ↦ (1 : ℝ))) n (x + z) := by
  have hi := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume) (lsmul ℝ ℝ)
      (averagingBump d n).continuous_normed (locallyIntegrable_phaseIndicator hE)
  apply integral_mono_ae (hi x) (hi (x + z))
  filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hz]
    with y hy
  simp only [lsmul_apply, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ ((averagingBump d n).nonneg_normed y)
  have he : x + z - y = x - y + z := by abel
  rw [he]
  by_cases hxE : x - y ∈ E
  · simp only [indicator_of_mem hxE, indicator_of_mem (hy hxE), le_refl]
  · simp only [indicator_of_notMem hxE]
    exact indicator_nonneg (fun _ _ ↦ zero_le_one) _

/-- The representative respects every translation that preserves the phase almost everywhere. -/
theorem orderedPhaseRepresentative_translation {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) {z : Space d}
    (hz : ∀ᵐ x ∂volume, x ∈ E → x + z ∈ E) {x : Space d}
    (hx : x ∈ orderedPhaseRepresentative E) : x + z ∈ orderedPhaseRepresentative E := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds
  · exact fun n ↦ mollify_phaseIndicator_translation_le hE hz n x
  · exact fun n ↦ (mollify_phaseIndicator_mem_Icc hE n (x + z)).2

/-- A vertically ordered phase has a Borel representative whose vertical order
holds simultaneously at every point and every nonnegative distance. -/
theorem orderedPhaseRepresentative_vertical {m : ℕ} {E : Set (Space (m + 1))}
    (hE : MeasurableSet E)
    (hvertical : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume,
      x ∈ E → x + t • verticalDirection m ∈ E) :
    ∀ (x : Space (m + 1)) (t : ℝ), 0 ≤ t →
      x ∈ orderedPhaseRepresentative E →
      x + t • verticalDirection m ∈ orderedPhaseRepresentative E := by
  intro x t ht hx
  exact orderedPhaseRepresentative_translation hE (hvertical t ht) hx

end SerrinEpigraph
