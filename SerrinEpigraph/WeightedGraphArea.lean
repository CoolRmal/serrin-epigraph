module

public import SerrinEpigraph.WeightedGraphIntegral

/-!
# Summation of weighted recovery coefficients against graph area
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- Subunit partition weights sum local scale coefficients without overcounting graph area. -/
theorem sum_weighted_graphScale_le_area {ι : Type*} [Fintype ι] {d : ℕ}
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {w : ι → Space d → ℝ}
    (hw : ∀ i, Integrable (w i)) (hpos : ∀ i y, 0 ≤ w i y)
    (hsum : ∀ y, ∑ i, w i y ≤ 1) {A : Set (Space d)} (hA : IsCompact A)
    (hsupp : ∀ i y, y ∉ A → w i y = 0) {L : ι → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hscale : ∀ i y, 0 < w i y → L i ≤ graphAreaDensity b y + ε) :
    (∑ i, (∫ y, w i y) * L i) ≤ (∫ y in A, graphAreaDensity b y) + ε * (volume A).toReal := by
  classical
  have hi (i : ι) : Integrable (fun y ↦ w i y * L i) := (hw i).mul_const _
  have his : Integrable (fun y ↦ ∑ i, w i y * L i) := integrable_finsetSum _ (fun i _ ↦ hi i)
  have he : (∫ y in A, ∑ i, w i y * L i) = ∑ i, (∫ y, w i y) * L i := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by simp [hsupp _ y hy]),
      integral_finsetSum _ (fun i _ ↦ hi i)]
    simp only [integral_mul_const]
  have hj : IntegrableOn (fun y ↦ graphAreaDensity b y + ε) A :=
    ((continuous_graphAreaDensity hb).add continuous_const).continuousOn.integrableOn_compact hA
  have hbound := setIntegral_mono_on his.integrableOn hj hA.measurableSet (fun y _ ↦ by
    calc
      (∑ i, w i y * L i) ≤ ∑ i, w i y * (graphAreaDensity b y + ε) := by
        apply Finset.sum_le_sum
        intro i _
        rcases (hpos i y).eq_or_lt with hi | hi
        · simp [← hi]
        exact mul_le_mul_of_nonneg_left (hscale i y hi) hi.le
      _ ≤ graphAreaDensity b y + ε := by
        rw [← Finset.sum_mul]
        exact mul_le_of_le_one_left (add_nonneg (graphAreaDensity_pos b y).le hε) (hsum y))
  rw [he, integral_add ((continuous_graphAreaDensity hb).continuousOn.integrableOn_compact hA)
    (continuous_const.continuousOn.integrableOn_compact hA), integral_const] at hbound
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using hbound

/-- Summing the weighted local recovery energies yields graph area times the one-dimensional
action, with only the prescribed area-density error. -/
theorem RigidityHypotheses.sum_weighted_graphRecovery_energy_le_area
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ δ R : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {w : ι → Space d → ℝ} (hw : ∀ i, Continuous (w i)) (hwi : ∀ i, Integrable (w i))
    (hpos : ∀ i y, 0 ≤ w i y) (hsum : ∀ y, ∑ i, w i y ≤ 1)
    {A : Set (Space d)} (hA : IsCompact A) (hsupp : ∀ i y, y ∉ A → w i y = 0)
    {L : ι → ℝ} (hL : ∀ i, 0 < L i) {ε : ℝ} (hε : 0 ≤ ε)
    (hscale : ∀ i y, 0 < w i y → L i ≤ graphAreaDensity b y + ε)
    (hslope : ∀ i y, 0 < w i y → 1 + ‖gradient b y‖ ^ 2 ≤ (L i) ^ 2)
    {K : Set (Space (d + 1))} (hK : IsCompact K) :
    (∑ i, ∫ x in K, w i (horizontal x) * rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L i)) x) ≤
      ((∫ y in A, graphAreaDensity b y) + ε * (volume A).toReal) *
        recoveryActionPrimitive f δ 1 := by
  have ha : 0 ≤ recoveryActionPrimitive f δ 1 := by
    rw [← hr.integral_recoveryLayerDensity h hδ hR]
    exact integral_nonneg (hr.recoveryLayerDensity_nonneg h hδ hR.le)
  calc
    _ ≤ ∑ i, (∫ y, w i y) * (L i * recoveryActionPrimitive f δ 1) :=
      Finset.sum_le_sum (fun i _ ↦ hr.integral_weighted_graphRecovery_energy_le h hδ hR
        (hL i) hb (hw i) (hwi i) (hpos i) (hslope i) hK)
    _ = (∑ i, (∫ y, w i y) * L i) * recoveryActionPrimitive f δ 1 := by
      simp only [← mul_assoc, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_weighted_graphScale_le_area hb hwi hpos hsum hA hsupp hε hscale) ha

end SerrinEpigraph
