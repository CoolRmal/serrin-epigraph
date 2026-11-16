module

public import SerrinEpigraph.PerimeterSmoothApproximation
public import SerrinEpigraph.TranslationIntegral

/-!
# Translation estimates for finite-perimeter phases

Smooth convolution and the original divergence definition give the translation estimate.
No boundary rectifiability or trace representation is assumed.
-/

public section

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The translation error of smooth phase averages converges on every compact set. -/
theorem mollify_phase_translation_integral_tendsto {d : ℕ} {E K : Set (Space d)}
    (hE : MeasurableSet E) (hK : IsCompact K) (z : Space d) :
    Tendsto (fun n ↦ ∫ x in K,
      ‖mollify (E.indicator (fun _ ↦ (1 : ℝ))) n (x + z) -
        mollify (E.indicator (fun _ ↦ (1 : ℝ))) n x‖) atTop
      (𝓝 (∫ x in K, ‖E.indicator (fun _ ↦ (1 : ℝ)) (x + z) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖)) := by
  have hloc := locallyIntegrable_phaseIndicator hE
  have ht := mollify_tendsto_ae_of_locallyIntegrable hloc
  have htz := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae ht
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (2 : ℝ))
  · intro n
    have hc := (mollify_contDiff_of_locallyIntegrable hloc n).continuous
    exact (((hc.comp (continuous_id.add continuous_const)).sub hc).norm.aestronglyMeasurable)
      |>.restrict
  · exact continuousOn_const.integrableOn_compact hK
  · intro n
    exact Eventually.of_forall fun x ↦ by
      have hx := mollify_phaseIndicator_mem_Icc hE n x
      have hz := mollify_phaseIndicator_mem_Icc hE n (x + z)
      rw [norm_norm, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hx.2, hz.1], by linarith [hz.2, hx.1]⟩
  · filter_upwards [ae_restrict_of_ae ht, ae_restrict_of_ae htz] with x hx hz
    exact (hz.sub hx).norm

/-- Local finite perimeter controls the integral translation error on an interior ball. -/
theorem integral_phase_translation_le_perimeter_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    (hE : MeasurableSet E) {r R B : ℝ} (z : Space d)
    (hrR : r + ‖z‖ < R) (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 R) ≤ ENNReal.ofReal B) :
    (∫ x in closedBall 0 r, ‖E.indicator (fun _ ↦ (1 : ℝ)) (x + z) -
      E.indicator (fun _ ↦ (1 : ℝ)) x‖) ≤ ‖z‖ * B := by
  apply le_of_tendsto (mollify_phase_translation_integral_tendsto hE
    (isCompact_closedBall 0 r) z)
  filter_upwards [eventually_integral_gradient_mollified_phase_closedBall_le b hE hrR hB hP]
    with n hn
  exact (integral_norm_translate_sub_le
    ((mollify_contDiff_of_locallyIntegrable (locallyIntegrable_phaseIndicator hE) n).of_le
      (by simp)) r z).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg z))

/-- Global finite perimeter and finite volume imply the sharp integral translation estimate. -/
theorem integral_phase_translation_le_global_perimeter_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    (hE : MeasurableSet E) (hEV : volume E ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hP : variationalPerimeter b E univ ≤ ENNReal.ofReal B) (z : Space d) :
    (∫ x, ‖E.indicator (fun _ ↦ (1 : ℝ)) (x + z) -
      E.indicator (fun _ ↦ (1 : ℝ)) x‖) ≤ ‖z‖ * B := by
  let S : ℕ → Set (Space d) := fun n ↦ closedBall 0 ((n : ℝ) + 1)
  have hS : (⋃ n, S n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change dist x 0 ≤ (n : ℝ) + 1
    rw [dist_zero_right]
    linarith
  have hi : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrableOn_const (C := (1 : ℝ)) hEV).integrable_indicator hE
  have hiz := (measurePreserving_add_right volume z).integrable_comp_of_integrable hi
  have ht := tendsto_setIntegral_of_monotone (fun n ↦ measurableSet_closedBall)
    (show Monotone S from fun n k hnk ↦ closedBall_subset_closedBall
      (add_le_add (Nat.cast_le.mpr hnk) le_rfl)) ((hiz.sub hi).norm.integrableOn)
  rw [hS, Measure.restrict_univ] at ht
  apply le_of_tendsto ht
  exact Eventually.of_forall fun n ↦ integral_phase_translation_le_perimeter_bound b hE z
    (show (n : ℝ) + 1 + ‖z‖ < (n : ℝ) + 1 + ‖z‖ + 1 by linarith) hB
    ((variationalPerimeter_mono b E (subset_univ _)).trans hP)

end SerrinEpigraph
