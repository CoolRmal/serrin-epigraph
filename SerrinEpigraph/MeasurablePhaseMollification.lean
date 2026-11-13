module

public import SerrinEpigraph.AsymptoticEnergyMass

/-!
# Smooth local approximations of arbitrary measurable phases
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution

namespace SerrinEpigraph

/-- Averaging smooths locally integrable functions without a continuity assumption. -/
theorem mollify_contDiff_of_locallyIntegrable {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyIntegrable v volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify v n) :=
  (averagingBump d n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (averagingBump d n).contDiff_normed hv

/-- The fixed averaging sequence converges almost everywhere for locally integrable functions. -/
theorem mollify_tendsto_ae_of_locallyIntegrable {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyIntegrable v volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n ↦ mollify v n x) atTop (𝓝 (v x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := averagingBump d) (K := 2) tendsto_one_div_add_atTop_nhds_zero_nat _ hv
  exact Eventually.of_forall (fun n ↦ by dsimp [averagingBump]; linarith)

/-- A constant upper bound survives convolution for every locally integrable function. -/
theorem mollify_le_of_locallyIntegrable {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyIntegrable v volume) {B : ℝ} (hb : ∀ x, v x ≤ B)
    (n : ℕ) (x : Space d) : mollify v n x ≤ B := by
  have he := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume) (lsmul ℝ ℝ) (averagingBump d n).continuous_normed hv
  have hc := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume) (lsmul ℝ ℝ) (averagingBump d n).continuous_normed
    (continuous_const (y := B)).locallyIntegrable
  have hm := convolution_mono_right (he x) (hc x) (averagingBump d n).nonneg_normed hb
  rw [(averagingBump d n).normed_convolution_eq_right
    (g := fun _ : Space d ↦ B) (fun _ _ ↦ rfl)] at hm
  exact hm

/-- The indicator of any measurable phase is locally integrable. -/
theorem locallyIntegrable_phaseIndicator {d : ℕ} {E : Set (Space d)} (hE : MeasurableSet E) :
    LocallyIntegrable (E.indicator (fun _ ↦ (1 : ℝ))) volume :=
  (continuous_const (y := (1 : ℝ))).locallyIntegrable.indicator hE

/-- Smooth averages of a measurable phase take values in the closed unit interval. -/
theorem mollify_phaseIndicator_mem_Icc {d : ℕ} {E : Set (Space d)} (hE : MeasurableSet E)
    (n : ℕ) (x : Space d) : mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨mollify_nonneg (fun y ↦ ?_) n x,
    mollify_le_of_locallyIntegrable (locallyIntegrable_phaseIndicator hE) (fun y ↦ ?_) n x⟩
  · by_cases hy : y ∈ E <;> simp [hy]
  · by_cases hy : y ∈ E <;> simp [hy]

/-- The same explicit smooth averages converge in integral norm on every compact set. -/
theorem mollify_phaseIndicator_integral_tendsto {d : ℕ} {E K : Set (Space d)}
    (hE : MeasurableSet E) (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K,
      ‖mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) := by
  have hloc := locallyIntegrable_phaseIndicator hE
  have hcont (n : ℕ) := (mollify_contDiff_of_locallyIntegrable hloc n).continuous
  have ht : Tendsto (fun n ↦ ∫ x in K,
      ‖mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 (∫ _x in K, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (2 : ℝ))
    · intro n
      exact (((hcont n).aestronglyMeasurable.sub
        (measurable_const.indicator hE).aestronglyMeasurable).norm).restrict
    · exact continuousOn_const.integrableOn_compact hK
    · intro n
      exact Eventually.of_forall (fun x ↦ by
        have hm := mollify_phaseIndicator_mem_Icc hE n x
        have hi : E.indicator (fun _ ↦ (1 : ℝ)) x ∈ Icc (0 : ℝ) 1 := by
          by_cases hx : x ∈ E <;> simp [hx]
        rw [norm_norm, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hm.1, hi.2], by linarith [hm.2, hi.1]⟩)
    · filter_upwards [ae_restrict_of_ae (mollify_tendsto_ae_of_locallyIntegrable hloc)] with x hx
      simpa only [sub_self, norm_zero] using
        (hx.sub (tendsto_const_nhds (x := E.indicator (fun _ ↦ (1 : ℝ)) x))).norm
  simpa only [integral_zero] using ht

end SerrinEpigraph
