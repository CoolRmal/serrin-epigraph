module

public import SerrinEpigraph.EuclideanProductVolume

/-!
# Recovery energy bounds for graphs with controlled slope
-/

public section

open Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace SerrinEpigraph

/-- A globally controlled graph slope gives a one-Lipschitz normalized height coordinate. -/
theorem normalizedGraphHeight_lipschitz {d : ℕ} {b : Space d → ℝ}
    (hb : Differentiable ℝ b) {L : ℝ} (hL : 0 < L)
    (hslope : ∀ y, 1 + ‖gradient b y‖ ^ 2 ≤ L ^ 2) :
    LipschitzWith 1 (fun x : Space (d + 1) ↦ graphHeight b x / L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x
    have hd := (graphHeight_hasFDerivAt (hb (horizontal x))).const_mul L⁻¹
    simpa only [div_eq_inv_mul] using hd.differentiableAt
  · intro x
    change ‖fderiv ℝ (fun y ↦ graphHeight b y / L) x‖ ≤ (1 : ℝ)
    rw [← norm_gradient_eq_norm_fderiv]
    exact norm_gradient_normalizedGraphHeight_le (hb (horizontal x)) hL (hslope _)

/-- A graph recovery competitor has energy bounded by normalized projected area times action. -/
theorem RigidityHypotheses.graphRecovery_integral_energy_le
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ R L : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (hR : 0 < R)
    {b : Space d → ℝ} (hb : Differentiable ℝ b) (hL : 0 < L)
    (hslope : ∀ y, 1 + ‖gradient b y‖ ^ 2 ≤ L ^ 2)
    {A : Set (Space d)} (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    {K : Set (Space (d + 1))} (hK : IsCompact K) (hproj : ∀ x ∈ K, horizontal x ∈ A) :
    (∫ x in K, rescaledPhaseEnergyDensity f R
      (geometricRecoveryProfile f δ R (fun y ↦ graphHeight b y / L)) x) ≤
      ((volume A).toReal * L) * recoveryActionPrimitive f δ 1 := by
  let P : ℝ≥0 := ⟨(volume A).toReal * L, mul_nonneg ENNReal.toReal_nonneg hL.le⟩
  have hP : (P : ℝ≥0∞) = volume A * ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((volume A).toReal * L) = _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
  have hm := map_euclidean_graphHeight_volume_le hb.continuous.measurable hA
    (fun x (hx : x ∈ K ∩ {y | R * (graphHeight b y / L) ∈
      Ioo 0 (recoveryTravelTime f δ 1)}) ↦ hproj x hx.1) hL
  rw [← hP] at hm
  exact hr.geometricRecoveryProfile_energy_le_of_map_le h hδ hR
    (normalizedGraphHeight_lipschitz hb hL hslope) hK hm

/-- The graph recovery competitors converge locally to the epigraph indicator. -/
theorem RigidityHypotheses.graphRecovery_integral_limit
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ L : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {b : Space d → ℝ} (hb : Differentiable ℝ b) (hL : 0 < L)
    (hslope : ∀ y, 1 + ‖gradient b y‖ ^ 2 ≤ L ^ 2)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    (hwidth : Filter.Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 / R j)
      Filter.atTop (𝓝 0)) {K : Set (Space (d + 1))} (hK : IsCompact K) :
    Filter.Tendsto (fun j ↦ ∫ x in K,
      ‖geometricRecoveryProfile f (δ j) (R j) (fun y ↦ graphHeight b y / L) x -
        (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x‖) Filter.atTop (𝓝 0) := by
  have hset : {x : Space (d + 1) | 0 < graphHeight b x / L} = epigraph b := by
    ext x
    simp only [mem_ofPred_eq, div_pos_iff_of_pos_right hL, graphHeight, sub_pos, epigraph]
  have he := hr.geometricRecoveryProfile_integral_limit h hδ hR hwidth
    (normalizedGraphHeight_lipschitz hb hL hslope).continuous hK
  simpa only [hset] using he

end SerrinEpigraph
