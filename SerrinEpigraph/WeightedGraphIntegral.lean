module

public import SerrinEpigraph.PartitionTotalEnergy

/-!
# Exact weighted integration in graph coordinates
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- Horizontal position together with vertical graph height preserves Euclidean volume. -/
theorem measurePreserving_horizontal_graphHeight {d : ℕ} {b : Space d → ℝ}
    (hb : Measurable b) :
    MeasurePreserving (fun x : Space (d + 1) ↦ (horizontal x, graphHeight b x))
      volume ((volume : Measure (Space d)).prod volume) := by
  have he := (measurePreserving_graphFlatten hb).comp (measurePreserving_horizontal_last d)
  simpa only [Function.comp_def, graphHeight, sub_eq_neg_add] using he

/-- Integrable horizontal weights remain intact under graph flattening and vertical scaling. -/
theorem integral_weighted_graphHeight {d : ℕ} {b w : Space d → ℝ} (hb : Measurable b)
    (hw : Integrable w) {q : ℝ → ℝ} (hq : Integrable q) {L : ℝ} (hL : 0 < L) :
    Integrable (fun x : Space (d + 1) ↦ w (horizontal x) * q (graphHeight b x / L)) ∧
      (∫ x : Space (d + 1), w (horizontal x) * q (graphHeight b x / L)) =
        (∫ y, w y) * (L * ∫ t, q t) := by
  let Q : Space d × ℝ → ℝ := fun p ↦ w p.1 * q (p.2 / L)
  have hQ : Integrable Q ((volume : Measure (Space d)).prod volume) := hw.mul_prod (hq.comp_div hL.ne')
  have hp := measurePreserving_horizontal_graphHeight hb
  have hQmap : Integrable Q (Measure.map (fun x : Space (d + 1) ↦
      (horizontal x, graphHeight b x)) volume) := by rw [hp.map_eq]; exact hQ
  have hi := hQmap.comp_measurable hp.measurable
  refine ⟨hi, ?_⟩
  have he := integral_map hp.measurable.aemeasurable hQmap.aestronglyMeasurable
  rw [hp.map_eq] at he
  rw [← he]
  change (∫ p : Space d × ℝ, w p.1 * q (p.2 / L) ∂volume.prod volume) = _
  rw [integral_prod_mul w (fun t ↦ q (t / L)), Measure.integral_comp_div, abs_of_pos hL, smul_eq_mul]

/-- The exact weighted layer mass retains the base weight instead of counting its support volume. -/
theorem RigidityHypotheses.integral_weighted_recoveryLayer
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ R L : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) {b w : Space d → ℝ}
    (hb : Measurable b) (hw : Integrable w) :
    Integrable (fun x : Space (d + 1) ↦
      w (horizontal x) * recoveryLayerDensity f δ R (graphHeight b x / L)) ∧
      (∫ x : Space (d + 1),
        w (horizontal x) * recoveryLayerDensity f δ R (graphHeight b x / L)) =
        (∫ y, w y) * (L * recoveryActionPrimitive f δ 1) := by
  simpa only [hr.integral_recoveryLayerDensity h hδ hR] using
    integral_weighted_graphHeight hb hw (hr.integrable_recoveryLayerDensity h hδ (R := R)) hL

/-- A nonnegative base weight gives a sharp weighted recovery bound when its active
graph slopes are controlled by the patch scale. -/
theorem RigidityHypotheses.integral_weighted_graphRecovery_energy_le
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ R L : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) {b w : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) (hw : Continuous w) (hwi : Integrable w) (hwpos : ∀ y, 0 ≤ w y)
    (hslope : ∀ y, 0 < w y → 1 + ‖gradient b y‖ ^ 2 ≤ L ^ 2)
    {K : Set (Space (d + 1))} (hK : IsCompact K) :
    (∫ x in K, w (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x) ≤
        (∫ y, w y) * (L * recoveryActionPrimitive f δ 1) := by
  have hheight : ContDiff ℝ 1 (graphHeight b) := by
    unfold graphHeight
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).contDiff.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).contDiff)
  have hρ : ContDiff ℝ 1 (fun x ↦ graphHeight b x / L) := hheight.div_const L
  have hv : LocallyLipschitz (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) :=
    (hr.recoveryProfile_lipschitz h hδ).locallyLipschitz.comp
      (contDiff_const.mul hρ).locallyLipschitz
  have hval := hr.geometricRecoveryProfile_mem_Icc h hδ (R := R)
    (ρ := fun z ↦ graphHeight b z / L)
  have hwc : Continuous (fun x : Space (d + 1) ↦ w (horizontal x)) :=
    hw.comp (horizontalContinuousLinearMap (m := d)).continuous
  have hi : IntegrableOn (fun x ↦ w (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x) K := by
    simpa only [mul_comm] using IntegrableOn.mul_continuousOn
      (h.integrableOn_rescaledPhaseEnergy hv hval R hK) hwc.continuousOn hK
  obtain ⟨hil, heq⟩ := hr.integral_weighted_recoveryLayer h hδ hR hL hb.continuous.measurable hwi
  have hn (x : Space (d + 1)) : 0 ≤ w (horizontal x) *
      recoveryLayerDensity f δ R (graphHeight b x / L) :=
    mul_nonneg (hwpos _) (hr.recoveryLayerDensity_nonneg h hδ hR.le _)
  have hle (x : Space (d + 1)) : w (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x ≤
      w (horizontal x) * recoveryLayerDensity f δ R (graphHeight b x / L) := by
    rcases (hwpos (horizontal x)).eq_or_lt with hx | hx
    · simp [← hx]
    have hg := norm_gradient_normalizedGraphHeight_le (hb.differentiable one_ne_zero
      (horizontal x)) hL (hslope _ hx)
    have he := hr.geometricRecoveryProfile_localized_energy_le h hδ hR
      (hρ.differentiable one_ne_zero x) hg
    have hs : R * (graphHeight b x / L) ∈ Ioo 0 (recoveryTravelTime f δ 1) ↔
        graphHeight b x / L ∈ Ioo 0 (recoveryTravelTime f δ 1 / R) := by
      simp only [mem_Ioo, lt_div_iff₀ hR, mul_comm R, mul_pos_iff_of_pos_right hR]
    simp only [recoveryLayerDensity, indicator_apply, mem_ofPred_eq, hs,
      geometricRecoveryProfile] at he ⊢
    exact mul_le_mul_of_nonneg_left he hx.le
  exact ((integral_mono hi hil.integrableOn hle).trans
    (setIntegral_le_integral hil (Filter.Eventually.of_forall hn))).trans_eq heq

end SerrinEpigraph
