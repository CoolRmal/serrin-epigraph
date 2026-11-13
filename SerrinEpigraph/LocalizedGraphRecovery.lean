module

public import SerrinEpigraph.GraphPerimeter

/-!
# Ambient cutoff localization of graph recovery energy
-/

public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- A Lipschitz ambient cutoff equal to one on the integration set can be moved
to the graph with an explicit error proportional to the transition thickness. -/
theorem RigidityHypotheses.integral_graphRecovery_energy_le_cutoff
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ}
    {κ δ R L : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L)
    {b w : Space d → ℝ} (hb : ContDiff ℝ 1 b) (hw : Continuous w)
    (hwc : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (hslope : ∀ y, 0 < w y → 1 + ‖gradient b y‖ ^ 2 ≤ L ^ 2)
    {χ : Space (d + 1) → ℝ} {M : ℝ≥0} (hχ : LipschitzWith M χ)
    (hχpos : ∀ x, 0 ≤ χ x) {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hχone : ∀ x ∈ K, 1 ≤ χ x) :
    (∫ x in K, w (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x) ≤
      (∫ y, w y * (χ (point y (b y)) + M * (recoveryTravelTime f δ 1 * L / R))) *
        (L * recoveryActionPrimitive f δ 1) := by
  let e : ℝ := M * (recoveryTravelTime f δ 1 * L / R)
  let w' := fun y ↦ w y * (χ (point y (b y)) + e)
  have he : 0 ≤ e := by
    exact mul_nonneg M.coe_nonneg
      (div_nonneg (mul_nonneg (hr.recoveryTravelTime_one_pos h hδ).le hL.le) hR.le)
  have hw' : Continuous w' := hw.mul
    ((hχ.continuous.comp (pointContinuousLinearMap.continuous.comp
      (continuous_id.prodMk hb.continuous))).add continuous_const)
  have hw'c : HasCompactSupport w' := hwc.mul_right
  have hw'pos (y : Space d) : 0 ≤ w' y := mul_nonneg (hwpos y) (add_nonneg (hχpos _) he)
  have hheight : ContDiff ℝ 1 (graphHeight b) := by
    unfold graphHeight
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).contDiff.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).contDiff)
  have hρ : ContDiff ℝ 1 (fun x ↦ graphHeight b x / L) := hheight.div_const L
  have hv : LocallyLipschitz (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) :=
    (hr.recoveryProfile_lipschitz h hδ).locallyLipschitz.comp
      (contDiff_const.mul hρ).locallyLipschitz
  have hi : IntegrableOn (fun x ↦ w (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x) K := by
    simpa only [mul_comm, Function.comp_def] using IntegrableOn.mul_continuousOn
      (h.integrableOn_rescaledPhaseEnergy hv (hr.geometricRecoveryProfile_mem_Icc h hδ) R hK)
      (hw.comp continuous_horizontal).continuousOn hK
  obtain ⟨hil, hel⟩ := hr.integral_weighted_recoveryLayer h hδ hR hL
    hb.continuous.measurable (hw'.integrable_of_hasCompactSupport hw'c)
  have hn (x : Space (d + 1)) : 0 ≤ w' (horizontal x) *
      recoveryLayerDensity f δ R (graphHeight b x / L) :=
    mul_nonneg (hw'pos _) (hr.recoveryLayerDensity_nonneg h hδ hR.le _)
  have hbound (x : Space (d + 1)) (hx : x ∈ K) :
      w (horizontal x) * rescaledPhaseEnergyDensity f R
        (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x ≤
      w' (horizontal x) * recoveryLayerDensity f δ R (graphHeight b x / L) := by
    rcases (hwpos (horizontal x)).eq_or_lt with hwx | hwx
    · simp only [w', ← hwx, zero_mul, le_refl]
    by_cases ht : R * (graphHeight b x / L) ∈ Ioo 0 (recoveryTravelTime f δ 1)
    · have hh : 0 < graphHeight b x :=
        (div_pos_iff_of_pos_right hL).mp ((mul_pos_iff_of_pos_left hR).mp ht.1)
      have hhi : graphHeight b x ≤ recoveryTravelTime f δ 1 * L / R := by
        apply (le_div_iff₀ hR).mpr
        have ht' : R * graphHeight b x < recoveryTravelTime f δ 1 * L :=
          (div_lt_iff₀ hL).mp (by simpa only [mul_div_assoc] using ht.2)
        nlinarith
      have hd : dist x (point (horizontal x) (b (horizontal x))) = |graphHeight b x| := by
        calc
          _ = dist (point (horizontal x) (x (Fin.last d)))
              (point (horizontal x) (b (horizontal x))) := by rw [point_horizontal_last]
          _ = _ := by rw [(isometry_point _).dist_eq, Real.dist_eq]; rfl
      have hc := hχ.dist_le_mul x (point (horizontal x) (b (horizontal x)))
      rw [hd, Real.dist_eq, abs_of_pos hh] at hc
      have hc' := (le_abs_self (χ x - χ (point (horizontal x) (b (horizontal x))))).trans hc
      have hwe : 1 ≤ χ (point (horizontal x) (b (horizontal x))) + e := by
        have he' := mul_le_mul_of_nonneg_left hhi M.coe_nonneg
        dsimp only [e]
        linarith [hχone x hx]
      have hge := hr.geometricRecoveryProfile_energy_le h hδ hR
        (hρ.differentiable one_ne_zero x) ht
        (norm_gradient_normalizedGraphHeight_le (hb.differentiable_one _) hL (hslope _ hwx))
      have ht' : graphHeight b x / L ∈ Ioo 0 (recoveryTravelTime f δ 1 / R) := by
        exact ⟨(mul_pos_iff_of_pos_left hR).mp ht.1,
          (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using ht.2)⟩
      have hle : rescaledPhaseEnergyDensity f R
          (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L)) x ≤
          recoveryLayerDensity f δ R (graphHeight b x / L) := by
        simpa only [recoveryLayerDensity, indicator_of_mem ht', geometricRecoveryProfile] using hge
      apply (mul_le_mul_of_nonneg_left hle hwx.le).trans
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hwx.le hwe) (hr.recoveryLayerDensity_nonneg h hδ hR.le _)
    · rw [hr.geometricRecoveryProfile_energy_zero h hδ ht, mul_zero]
      exact hn x
  exact ((setIntegral_mono_on hi hil.integrableOn hK.measurableSet hbound).trans
    (setIntegral_le_integral hil (Eventually.of_forall hn))).trans_eq hel

/-- Subunit graph partitions retain an arbitrary continuous nonnegative weight
in the area bound. -/
theorem sum_weighted_graphScale_le_cutoff_area {ι : Type*} [Fintype ι] {d : ℕ}
    {b z : Space d → ℝ} (hb : ContDiff ℝ 1 b) (hz : Continuous z) (hzpos : ∀ y, 0 ≤ z y)
    {w : ι → Space d → ℝ} (hw : ∀ i, Continuous (w i))
    (hwc : ∀ i, HasCompactSupport (w i)) (hpos : ∀ i y, 0 ≤ w i y)
    (hsum : ∀ y, ∑ i, w i y ≤ 1) {A : Set (Space d)} (hA : IsCompact A)
    (hsupp : ∀ i y, y ∉ A → w i y = 0) {L : ι → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hscale : ∀ i y, 0 < w i y → L i ≤ graphAreaDensity b y + ε) :
    (∑ i, (∫ y, w i y * z y) * L i) ≤
      ∫ y in A, z y * (graphAreaDensity b y + ε) := by
  classical
  have hi (i : ι) : Integrable (fun y ↦ (w i y * z y) * L i) :=
    (((hw i).mul hz).mul continuous_const).integrable_of_hasCompactSupport
      ((hwc i).mul_right.mul_right)
  have his : Integrable (fun y ↦ ∑ i, (w i y * z y) * L i) :=
    integrable_finsetSum _ (fun i _ ↦ hi i)
  have he : (∫ y in A, ∑ i, (w i y * z y) * L i) =
      ∑ i, (∫ y, w i y * z y) * L i := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by simp [hsupp _ y hy]),
      integral_finsetSum _ (fun i _ ↦ hi i)]
    simp only [integral_mul_const]
  rw [← he]
  apply setIntegral_mono_on his.integrableOn
    ((hz.mul ((continuous_graphAreaDensity hb).add continuous_const))
      |>.continuousOn.integrableOn_compact hA) hA.measurableSet
  intro y _
  calc
    (∑ i, (w i y * z y) * L i) ≤ ∑ i, w i y * (z y * (graphAreaDensity b y + ε)) := by
      apply Finset.sum_le_sum
      intro i _
      rcases (hpos i y).eq_or_lt with hi | hi
      · simp [← hi]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hscale i y hi) (mul_nonneg hi.le (hzpos y))
    _ ≤ z y * (graphAreaDensity b y + ε) := by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left
        (mul_nonneg (hzpos y) (add_nonneg (graphAreaDensity_pos b y).le hε)) (hsum y)

/-- The principal energy of a graph partition is controlled by the ambient
cutoff's trace on the graph, with a uniform transition-thickness error. -/
theorem RigidityHypotheses.sum_graphRecovery_energy_le_cutoff_area
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ δ R : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {w : ι → Space d → ℝ} (hw : ∀ i, Continuous (w i))
    (hwc : ∀ i, HasCompactSupport (w i)) (hpos : ∀ i y, 0 ≤ w i y)
    (hsum : ∀ y, ∑ i, w i y ≤ 1) {A : Set (Space d)} (hA : IsCompact A)
    (hsupp : ∀ i y, y ∉ A → w i y = 0) {L : ι → ℝ} {H ε : ℝ}
    (hL : ∀ i, 0 < L i) (hLH : ∀ i, L i ≤ H) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hscale : ∀ i y, 0 < w i y → L i ≤ graphAreaDensity b y + ε)
    (hslope : ∀ i y, 0 < w i y → 1 + ‖gradient b y‖ ^ 2 ≤ (L i) ^ 2)
    {χ : Space (d + 1) → ℝ} {M : ℝ≥0} (hχ : LipschitzWith M χ)
    (hχpos : ∀ x, 0 ≤ χ x) {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hχone : ∀ x ∈ K, 1 ≤ χ x) :
    (∑ i, ∫ x in K, w i (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L i)) x) ≤
      (∫ y in A, (χ (point y (b y)) + M * (recoveryTravelTime f δ 1 * H / R)) *
        (graphAreaDensity b y + ε)) * recoveryActionPrimitive f δ 1 := by
  let z := fun y ↦ χ (point y (b y)) + M * (recoveryTravelTime f δ 1 * H / R)
  have hz : Continuous z := (hχ.continuous.comp (pointContinuousLinearMap.continuous.comp
    (continuous_id.prodMk hb.continuous))).add continuous_const
  have hzpos (y : Space d) : 0 ≤ z y := add_nonneg (hχpos _)
    (mul_nonneg M.coe_nonneg (div_nonneg
      (mul_nonneg (hr.recoveryTravelTime_one_pos h hδ).le hH) hR.le))
  have ha : 0 ≤ recoveryActionPrimitive f δ 1 := by
    rw [← hr.integral_recoveryLayerDensity h hδ hR]
    exact integral_nonneg (hr.recoveryLayerDensity_nonneg h hδ hR.le)
  have hbnd (i : ι) : (∫ x in K, w i (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L i)) x) ≤
      (∫ y, w i y * z y) * (L i * recoveryActionPrimitive f δ 1) := by
    apply (hr.integral_graphRecovery_energy_le_cutoff h hδ hR (hL i) hb (hw i) (hwc i)
      (hpos i) (hslope i) hχ hχpos hK hχone).trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hL i).le ha)
    apply integral_mono
      (((hw i).mul ((hχ.continuous.comp (pointContinuousLinearMap.continuous.comp
        (continuous_id.prodMk hb.continuous))).add continuous_const))
        |>.integrable_of_hasCompactSupport (hwc i).mul_right)
      (((hw i).mul hz).integrable_of_hasCompactSupport (hwc i).mul_right)
    intro y
    apply mul_le_mul_of_nonneg_left _ (hpos i y)
    change χ (point y (b y)) + M * (recoveryTravelTime f δ 1 * L i / R) ≤
      χ (point y (b y)) + M * (recoveryTravelTime f δ 1 * H / R)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hLH i)
        (hr.recoveryTravelTime_one_pos h hδ).le) hR.le) M.coe_nonneg
  calc
    _ ≤ ∑ i, (∫ y, w i y * z y) * (L i * recoveryActionPrimitive f δ 1) :=
      Finset.sum_le_sum (fun i _ ↦ hbnd i)
    _ = (∑ i, (∫ y, w i y * z y) * L i) * recoveryActionPrimitive f δ 1 := by
      simp only [← mul_assoc, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_weighted_graphScale_le_cutoff_area hb hz hzpos hw hwc hpos hsum hA hsupp hε hscale) ha

/-- Expanding the localized area bound separates the two vanishing errors from
the cutoff-weighted area itself. -/
theorem integral_graph_cutoff_expansion {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {χ : Space (d + 1) → ℝ} (hχ : Continuous χ)
    {A : Set (Space d)} (hA : IsCompact A) (ε e : ℝ) :
    (∫ y in A, (χ (point y (b y)) + e) * (graphAreaDensity b y + ε)) =
      (∫ y in A, χ (point y (b y)) * graphAreaDensity b y) +
        ε * (∫ y in A, χ (point y (b y))) +
        e * ((∫ y in A, graphAreaDensity b y) + ε * (volume A).toReal) := by
  have hc : Continuous (fun y ↦ χ (point y (b y))) := hχ.comp
    (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous))
  have hiχ := hc.continuousOn.integrableOn_compact (μ := volume) hA
  have hia := (continuous_graphAreaDensity hb).continuousOn.integrableOn_compact (μ := volume) hA
  have hiχa : IntegrableOn (fun y ↦ χ (point y (b y)) * graphAreaDensity b y) A :=
    (hc.mul (continuous_graphAreaDensity hb)).continuousOn.integrableOn_compact hA
  have hie : IntegrableOn (fun _ : Space d ↦ ε) A :=
    continuous_const.continuousOn.integrableOn_compact hA
  have hi₁ : IntegrableOn (fun y ↦ χ (point y (b y)) * graphAreaDensity b y +
      ε * χ (point y (b y))) A := hiχa.add (hiχ.const_mul ε)
  have hi₂ : IntegrableOn (fun y ↦ e * (graphAreaDensity b y + ε)) A :=
    (hia.add hie).const_mul e
  calc
    _ = ∫ y in A, (χ (point y (b y)) * graphAreaDensity b y + ε * χ (point y (b y))) +
        e * (graphAreaDensity b y + ε) := by
      apply setIntegral_congr_fun hA.measurableSet
      intro y _
      dsimp only
      ring
    _ = _ := by
      rw [integral_add hi₁ hi₂,
        integral_add hiχa (hiχ.const_mul ε), integral_const_mul, integral_const_mul,
        integral_add hia hie, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]

end SerrinEpigraph
