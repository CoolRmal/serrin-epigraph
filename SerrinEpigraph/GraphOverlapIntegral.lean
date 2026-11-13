module

public import SerrinEpigraph.PartitionOverlap

/-!
# Integrated common-layer errors on Euclidean graph cylinders
-/

public section

open Set MeasureTheory
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

/-- The scale factor in a constant layer density cancels its reciprocal thickness. -/
theorem integral_graphLayer_le {d : ℕ} {b : Space d → ℝ} (hb : Measurable b)
    {A : Set (Space d)} (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    {K : Set (Space (d + 1))} (hK : ∀ x ∈ K, horizontal x ∈ A)
    {R T D : ℝ} (hR : 0 < R) (hT : 0 ≤ T) (hD : 0 ≤ D) :
    IntegrableOn (fun x ↦ (Ioo 0 T).indicator (fun _ ↦ R * D) (R * graphHeight b x)) K ∧
      (∫ x in K, (Ioo 0 T).indicator (fun _ ↦ R * D) (R * graphHeight b x)) ≤
        (volume A).toReal * (T * D) := by
  let q : ℝ → ℝ := (Ioo 0 (T / R)).indicator (fun _ ↦ R * D)
  have hi : Integrable q :=
    ((continuous_const.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc (a := (0 : ℝ)) (b := T / R))).mono_set Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo
  have hmass : (∫ t, q t) = T * D := by
    rw [integral_indicator measurableSet_Ioo, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal (div_nonneg hT hR.le), smul_eq_mul]
    field_simp
  have hm := map_euclidean_graphHeight_volume_le hb hA hK (show (0 : ℝ) < 1 by norm_num)
  simp only [div_one, ENNReal.ofReal_one, mul_one] at hm
  have his := hi.smul_measure hfin
  have him := his.mono_measure hm
  have hc : Measurable (graphHeight b) := by
    unfold graphHeight
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).continuous.measurable.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).continuous.measurable)
  have heq (x : Space (d + 1)) : q (graphHeight b x) =
      (Ioo 0 T).indicator (fun _ ↦ R * D) (R * graphHeight b x) := by
    have he : R * graphHeight b x ∈ Ioo 0 T ↔ graphHeight b x ∈ Ioo 0 (T / R) := by
      simp only [mem_Ioo, lt_div_iff₀ hR, mul_comm R, mul_pos_iff_of_pos_right hR]
    simp only [q, indicator_apply, he]
  have hint := him.comp_measurable hc
  have hbound := integral_mono_measure hm (Filter.Eventually.of_forall (fun t ↦
    show 0 ≤ q t from indicator_nonneg (fun _ _ ↦ mul_nonneg hR.le hD) t)) his
  rw [integral_map hc.aemeasurable him.aestronglyMeasurable,
    integral_smul_measure, hmass, smul_eq_mul] at hbound
  simp only [Function.comp_def, heq] at hint hbound
  exact ⟨hint, hbound⟩

/-- The integrated potential defect of graph-profile gluing is uniformly bounded in R
and is proportional to inverse-scale oscillation on active overlaps. -/
theorem RigidityHypotheses.integral_partitionRecovery_potential_defect_le
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ δ R : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {C : ℝ≥0}
    (hW : LipschitzOnWith C (normalizedPotential f) (Icc 0 1))
    {b : Space d → ℝ} (hb : Continuous b) {η : ι → Space (d + 1) → ℝ}
    (hη : ∀ i, Continuous (η i)) (hpos : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) {L : ι → ℝ} {H ε : ℝ}
    (hL : ∀ i, 0 < L i) (hLH : ∀ i, L i ≤ H) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    {A : Set (Space d)} (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hproj : ∀ x ∈ K, horizontal x ∈ A) (hone : ∀ x ∈ K, ∑ i, η i x = 1)
    (hclose : ∀ x ∈ K, ∀ i j, 0 < η i x → 0 < η j x → |(L j)⁻¹ - (L i)⁻¹| ≤ ε) :
    let v := fun i x ↦ recoveryProfile f δ (R * graphHeight b x / L i)
    (∫ x in K, R * (normalizedPotential f (partitionRecovery η v x) -
      ∑ i, η i x * normalizedPotential f (v i x))) ≤
      (volume A).toReal * (C * Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
        (recoveryTravelTime f δ 1 * H) ^ 2 * ε) := by
  classical
  dsimp only
  let v := fun i x ↦ recoveryProfile f δ (R * graphHeight b x / L i)
  let T := recoveryTravelTime f δ 1 * H
  let D := (C : ℝ) * Real.sqrt (2 * (normalizedPotential f 0 + δ)) * T * ε
  have hT : 0 ≤ T := mul_nonneg (hr.recoveryTravelTime_one_pos h hδ).le hH
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (mul_nonneg C.coe_nonneg (Real.sqrt_nonneg _)) hT) hε
  have hheight : Continuous (graphHeight b) := by
    unfold graphHeight
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).continuous.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).continuous)
  have hv (i : ι) : Continuous (v i) :=
    (hr.recoveryProfile_lipschitz h hδ).continuous.comp
      ((continuous_const.mul hheight).div_const (L i))
  have hval (i : ι) (x : Space (d + 1)) : v i x ∈ Icc (0 : ℝ) 1 :=
    hr.recoveryProfile_mem_Icc h hδ _
  have hp : Continuous (partitionRecovery η v) :=
    continuous_finsetSum _ (fun i _ ↦ (hη i).mul (hv i))
  have hwv (i : ι) : Continuous (fun x ↦ normalizedPotential f (v i x)) :=
    h.normalizedPotential_continuousOn.comp_continuous (hv i) (hval i)
  have hwp : Continuous (fun x ↦ normalizedPotential f (partitionRecovery η v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hp
      (partitionRecovery_mem_Icc hpos hsum hval)
  have hi : IntegrableOn (fun x ↦ R * (normalizedPotential f (partitionRecovery η v x) -
      ∑ i, η i x * normalizedPotential f (v i x))) K :=
    (continuous_const.mul (hwp.sub
    (continuous_finsetSum _ (fun i _ ↦ (hη i).mul (hwv i))))).continuousOn.integrableOn_compact
      (μ := volume) hK
  obtain ⟨hil, hbound⟩ := integral_graphLayer_le hb.measurable hA hfin hproj hR hT hD
  have he := integral_mono_ae hi hil (ae_restrict_of_forall_mem hK.measurableSet (fun x hx ↦ by
    have hp := hr.partitionRecovery_potential_overlap_le h hδ hW
      (ρ := fun y ↦ R * graphHeight b y) (fun i ↦ hpos i x) (hone x hx) hL hLH (hclose x hx)
    change R * (normalizedPotential f (partitionRecovery η v x) -
      ∑ i, η i x * normalizedPotential f (v i x)) ≤
        (Ioo 0 T).indicator (fun _ ↦ R * D) (R * graphHeight b x)
    by_cases hs : R * graphHeight b x ∈ Ioo 0 T
    · rw [indicator_of_mem hs]
      rw [indicator_of_mem hs] at hp
      dsimp only [D]
      nlinarith [mul_le_mul_of_nonneg_left hp hR.le]
    · rw [indicator_of_notMem hs]
      rw [indicator_of_notMem hs] at hp
      simpa only [mul_zero] using mul_nonpos_of_nonneg_of_nonpos hR.le
        (sub_nonpos.mpr (by simpa only [mul_zero, add_zero] using hp))))
  apply he.trans (hbound.trans_eq _)
  dsimp [T, D]
  ring

end SerrinEpigraph
