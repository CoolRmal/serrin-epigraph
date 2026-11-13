module

public import SerrinEpigraph.GraphPerimeterLower
public import Mathlib.Topology.UrysohnsLemma

/-!
# Localized perimeter of C1 graph epigraphs
-/

public section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The area of every compact graph piece lying in an open test domain is
bounded by the epigraph perimeter in that domain. -/
theorem compact_graph_area_le_perimeter {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {Ω : Set (Space (d + 1))} (hΩ : IsOpen Ω)
    {K : Set (Space d)} (hK : IsCompact K) (hKΩ : ∀ y ∈ K, point y (b y) ∈ Ω) :
    ENNReal.ofReal (∫ y in K, graphAreaDensity b y) ≤
      variationalPerimeter basis (epigraph b) Ω := by
  have htrace : Continuous (fun y ↦ point y (b y)) :=
    pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous)
  obtain ⟨χ, hχK, hχc, hχs, hχval⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK.image htrace) hΩ
      (by rintro x ⟨y, hy, rfl⟩; exact hKΩ y hy)
  have hc : HasCompactSupport (fun y ↦ χ (point y (b y))) := by
    simpa only [add_zero] using hasCompactSupport_graph_section (b := b) hχc 0
  have hi : Integrable (fun y ↦ χ (point y (b y)) * graphAreaDensity b y) :=
    ((χ.continuous.comp htrace).mul (continuous_graphAreaDensity hb))
      |>.integrable_of_hasCompactSupport hc.mul_right
  have he : (∫ y in K, graphAreaDensity b y) =
      ∫ y in K, χ (point y (b y)) * graphAreaDensity b y := by
    apply setIntegral_congr_fun hK.measurableSet
    intro y hy
    dsimp only
    rw [hχK ⟨y, hy, rfl⟩]
    simp
  apply le_trans _ (weighted_graph_area_le_perimeter basis hb χ.continuous hχc hχval hχs)
  apply ENNReal.ofReal_le_ofReal
  rw [he]
  exact setIntegral_le_integral hi (Eventually.of_forall
    (fun y ↦ mul_nonneg (hχval _).1 (graphAreaDensity_pos b y).le))

/-- On every open ambient set, variational epigraph perimeter is exactly the
area integral over the portion of the C1 graph in that set, including infinite area. -/
theorem graph_perimeter_eq_area {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {Ω : Set (Space (d + 1))} (hΩ : IsOpen Ω) :
    variationalPerimeter basis (epigraph b) Ω =
      ∫⁻ y in {y | point y (b y) ∈ Ω}, ENNReal.ofReal (graphAreaDensity b y) := by
  have htrace : Continuous (fun y ↦ point y (b y)) :=
    pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous)
  have hU : IsOpen {y | point y (b y) ∈ Ω} := hΩ.preimage htrace
  apply le_antisymm
  · unfold variationalPerimeter
    refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
      iSup_le (fun hs ↦ iSup_le (fun hunit ↦ ?_)))))
    have hpair : (∫ x, (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence basis F x) = ∫ x in epigraph b, fieldDivergence basis F x := by
      rw [← integral_indicator (isOpen_epigraph hb.continuous).measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x ↦ by by_cases hx : x ∈ epigraph b <;> simp [hx])
    rw [hpair]
    apply le_trans (ENNReal.ofReal_le_ofReal
      (norm_integral_epigraph_divergence_le_graph_area basis hb hF hc))
    have hct : HasCompactSupport (fun y ↦ ‖F (point y (b y))‖) := by
      simpa only [add_zero] using hasCompactSupport_graph_section (b := b) hc.norm 0
    have hi : Integrable (fun y ↦ graphAreaDensity b y * ‖F (point y (b y))‖) :=
      ((continuous_graphAreaDensity hb).mul (hF.continuous.comp htrace).norm)
        |>.integrable_of_hasCompactSupport hct.mul_left
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall
      (fun y ↦ mul_nonneg (graphAreaDensity_pos b y).le (norm_nonneg _))),
      ← lintegral_indicator hU.measurableSet]
    apply lintegral_mono
    intro y
    by_cases hy : point y (b y) ∈ Ω
    · rw [indicator_of_mem (s := {y | point y (b y) ∈ Ω}) hy]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_right (graphAreaDensity_pos b y).le (hunit _))
    · have hz : F (point y (b y)) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx ↦ hy (hs hx))
      simp only [hz, norm_zero, mul_zero, ENNReal.ofReal_zero, zero_le]
  · let μ := volume.withDensity (fun y ↦ ENNReal.ofReal (graphAreaDensity b y))
    have : IsLocallyFiniteMeasure μ :=
      IsLocallyFiniteMeasure.withDensity_ofReal (continuous_graphAreaDensity hb)
    rw [← withDensity_apply _ hU.measurableSet]
    change μ {y | point y (b y) ∈ Ω} ≤ _
    rw [hU.measure_eq_iSup_isCompact μ]
    refine iSup_le (fun K ↦ iSup_le (fun hKU ↦ iSup_le (fun hK ↦ ?_)))
    change volume.withDensity (fun y ↦ ENNReal.ofReal (graphAreaDensity b y)) K ≤ _
    rw [withDensity_apply _ hK.measurableSet, ← ofReal_integral_eq_lintegral_ofReal
      ((continuous_graphAreaDensity hb).continuousOn.integrableOn_compact hK)
      (Eventually.of_forall (fun y ↦ (graphAreaDensity_pos b y).le))]
    exact compact_graph_area_le_perimeter basis hb hΩ hK hKU

end SerrinEpigraph
