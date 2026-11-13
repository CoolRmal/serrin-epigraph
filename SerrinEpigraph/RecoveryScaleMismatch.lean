module

public import SerrinEpigraph.PartitionPotentialEnergy

/-!
# Quantitative mismatch of recovery profiles with different graph scales
-/

public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The potential-scale weighted difference of two graph recovery profiles. -/
@[expose] noncomputable def recoveryScaleMismatch (f : ℝ → ℝ) (δ R L M t : ℝ) : ℝ :=
  R * ‖recoveryProfile f δ (R * t / L) - recoveryProfile f δ (R * t / M)‖

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R L M : ℝ}

/-- Two positive graph scales differ only inside the larger transition layer. -/
theorem RigidityHypotheses.recoveryScaleMismatch_eq_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    {t : ℝ} (ht : t ∉ Ioo 0 (recoveryTravelTime f δ 1 * max L M / R)) :
    recoveryScaleMismatch f δ R L M t = 0 := by
  have hT := (hr.recoveryTravelTime_one_pos h hδ).le
  by_cases ht0 : t ≤ 0
  · simp [recoveryScaleMismatch, hr.recoveryProfile_eq_zero h hδ
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR.le ht0) hL.le),
      hr.recoveryProfile_eq_zero h hδ
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR.le ht0) hM.le)]
  · have ht' : recoveryTravelTime f δ 1 * max L M / R ≤ t := by
      exact le_of_not_gt (fun hlt ↦ ht ⟨lt_of_not_ge ht0, hlt⟩)
    have he := (div_le_iff₀ hR).mp ht'
    have ha : recoveryTravelTime f δ 1 ≤ R * t / L := by
      apply (le_div_iff₀ hL).mpr
      exact (mul_le_mul_of_nonneg_left (le_max_left L M) hT).trans (by nlinarith [he])
    have hb : recoveryTravelTime f δ 1 ≤ R * t / M := by
      apply (le_div_iff₀ hM).mpr
      exact (mul_le_mul_of_nonneg_left (le_max_right L M) hT).trans (by nlinarith [he])
    simp [recoveryScaleMismatch, hr.recoveryProfile_eq_one h hδ ha,
      hr.recoveryProfile_eq_one h hδ hb]

/-- A scale mismatch has a uniform amplitude bound on its thin supporting layer. -/
theorem RigidityHypotheses.recoveryScaleMismatch_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M) (t : ℝ) :
    recoveryScaleMismatch f δ R L M t ≤
      (Ioo 0 (recoveryTravelTime f δ 1 * max L M / R)).indicator
        (fun _ ↦ R * Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
          (recoveryTravelTime f δ 1 * max L M) * |L⁻¹ - M⁻¹|) t := by
  by_cases ht : t ∈ Ioo 0 (recoveryTravelTime f δ 1 * max L M / R)
  · rw [indicator_of_mem ht]
    have he := (hr.recoveryProfile_lipschitz h hδ).dist_le_mul (R * t / L) (R * t / M)
    rw [dist_eq_norm, Real.dist_eq] at he
    have hd : |R * t / L - R * t / M| = (R * t) * |L⁻¹ - M⁻¹| := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul,
        abs_of_nonneg (mul_nonneg hR.le ht.1.le)]
    rw [hd] at he
    have htR : R * t ≤ recoveryTravelTime f δ 1 * max L M := by
      have hh := (lt_div_iff₀ hR).mp ht.2
      nlinarith
    have he' := mul_le_mul_of_nonneg_left he hR.le
    change recoveryScaleMismatch f δ R L M t ≤ _ at he'
    calc
      _ ≤ R * (Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
          (R * t * |L⁻¹ - M⁻¹|)) := he'
      _ ≤ R * (Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
          ((recoveryTravelTime f δ 1 * max L M) * |L⁻¹ - M⁻¹|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htR (abs_nonneg _)) (Real.sqrt_nonneg _)) hR.le
      _ = _ := by ring
  · rw [indicator_of_notMem ht, hr.recoveryScaleMismatch_eq_zero h hδ hR hL hM ht]

/-- The scale-weighted mismatch is integrable, with a bound independent of the blow-down scale. -/
theorem RigidityHypotheses.integral_recoveryScaleMismatch_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M) :
    Integrable (recoveryScaleMismatch f δ R L M) ∧
      (∫ t, recoveryScaleMismatch f δ R L M t) ≤
        Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
          (recoveryTravelTime f δ 1 * max L M) ^ 2 * |L⁻¹ - M⁻¹| := by
  let a := recoveryTravelTime f δ 1 * max L M / R
  let C := R * Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
    (recoveryTravelTime f δ 1 * max L M) * |L⁻¹ - M⁻¹|
  have ha : 0 ≤ a := div_nonneg (mul_nonneg
    (hr.recoveryTravelTime_one_pos h hδ).le (hL.le.trans (le_max_left _ _))) hR.le
  have hi : Integrable ((Ioo 0 a).indicator (fun _ : ℝ ↦ C)) :=
    ((continuous_const.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc (a := (0 : ℝ)) (b := a))).mono_set Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo
  have hc : Continuous (recoveryScaleMismatch f δ R L M) := by
    unfold recoveryScaleMismatch
    exact continuous_const.mul (((hr.recoveryProfile_lipschitz h hδ).continuous.comp
      ((continuous_const.mul continuous_id).div_const L)).sub
      ((hr.recoveryProfile_lipschitz h hδ).continuous.comp
        ((continuous_const.mul continuous_id).div_const M))).norm
  have hn (t : ℝ) : 0 ≤ recoveryScaleMismatch f δ R L M t :=
    mul_nonneg hR.le (norm_nonneg _)
  have hb (t : ℝ) := hr.recoveryScaleMismatch_le h hδ hR hL hM t
  have hj := hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun t ↦ by
    rw [Real.norm_of_nonneg (hn t)]
    exact hb t))
  refine ⟨hj, (integral_mono hj hi (fun t ↦ hb t)).trans_eq ?_⟩
  rw [integral_indicator measurableSet_Ioo, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal ha, smul_eq_mul]
  dsimp [a, C]
  field_simp

/-- Integrating scale mismatch over a graph cylinder costs only its projected base volume. -/
theorem RigidityHypotheses.integral_recoveryScaleMismatch_graph_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    {d : ℕ} {b : Space d → ℝ} (hb : Measurable b) {A : Set (Space d)}
    (hA : MeasurableSet A) (hfin : volume A ≠ ∞) {K : Set (Space (d + 1))}
    (hK : ∀ x ∈ K, horizontal x ∈ A) :
    (∫ x in K, recoveryScaleMismatch f δ R L M (graphHeight b x)) ≤
      (volume A).toReal * (Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
        (recoveryTravelTime f δ 1 * max L M) ^ 2 * |L⁻¹ - M⁻¹|) := by
  have hm := map_euclidean_graphHeight_volume_le hb hA hK (show (0 : ℝ) < 1 by norm_num)
  simp only [div_one, ENNReal.ofReal_one, mul_one] at hm
  obtain ⟨hi, hbound⟩ := hr.integral_recoveryScaleMismatch_le h hδ hR hL hM
  have his := hi.smul_measure hfin
  have him := his.mono_measure hm
  have he := integral_mono_measure hm
    (Filter.Eventually.of_forall (fun t ↦ show 0 ≤ recoveryScaleMismatch f δ R L M t from
      mul_nonneg hR.le (norm_nonneg _))) his
  have hc : Measurable (graphHeight b) := by
    unfold graphHeight
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).continuous.measurable.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).continuous.measurable)
  rw [integral_map hc.aemeasurable him.aestronglyMeasurable,
    integral_smul_measure, smul_eq_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg)

end SerrinEpigraph
