module

public import SerrinEpigraph.UnitFieldApproximation

/-!
# Continuous normal tests for the lower graph perimeter bound
-/

public section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Continuous compact unit fields are admissible boundary-flux tests after
smooth approximation preserving the support and the unit bound. -/
theorem graph_flux_le_perimeter_of_continuous {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {F : Space (d + 1) → Space (d + 1)}
    (hF : Continuous F) (hc : HasCompactSupport F) (hunit : ∀ x, ‖F x‖ ≤ 1)
    {Ω : Set (Space (d + 1))} (hs : tsupport F ⊆ Ω) :
    ENNReal.ofReal ‖∫ y, inner ℝ (point (gradient b y) (-1)) (F (point y (b y)))‖ ≤
      variationalPerimeter basis (epigraph b) Ω := by
  obtain ⟨G, hG, hGunit, hGs, hGt⟩ := exists_contDiff_unit_field_approx hF hunit
  let A := horizontal '' tsupport F
  have hA : IsCompact A := hc.image continuous_horizontal
  have hnormal : Continuous (fun y ↦ point (gradient b y) (-1)) :=
    pointContinuousLinearMap.continuous.comp
      (((toDual ℝ (Space d)).symm.continuous.comp (hb.continuous_fderiv one_ne_zero)).prodMk
        continuous_const)
  have htrace : Continuous (fun y ↦ point y (b y)) :=
    pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous)
  have hout (y : Space d) (hy : y ∉ A) : point y (b y) ∉ tsupport F := by
    intro hh
    exact hy ⟨point y (b y), hh, horizontal_point _ _⟩
  have hzero (y : Space d) (hy : y ∉ A) : F (point y (b y)) = 0 :=
    image_eq_zero_of_notMem_tsupport (hout y hy)
  have hGzero (j : ℕ) (y : Space d) (hy : y ∉ A) : G j (point y (b y)) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh ↦ hout y hy (hGs j hh))
  have heG (j : ℕ) : (∫ y in A, inner ℝ (point (gradient b y) (-1)) (G j (point y (b y)))) =
      ∫ y, inner ℝ (point (gradient b y) (-1)) (G j (point y (b y))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hGzero j y hy, inner_zero_right]
  have heF : (∫ y in A, inner ℝ (point (gradient b y) (-1)) (F (point y (b y)))) =
      ∫ y, inner ℝ (point (gradient b y) (-1)) (F (point y (b y))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hzero y hy, inner_zero_right]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict A)
    (F := fun j y ↦ inner ℝ (point (gradient b y) (-1)) (G j (point y (b y))))
    (f := fun y ↦ inner ℝ (point (gradient b y) (-1)) (F (point y (b y))))
    (graphAreaDensity b)
    (fun j ↦ (hnormal.inner ((hG j).continuous.comp htrace)).aestronglyMeasurable)
    ((continuous_graphAreaDensity hb).continuousOn.integrableOn_compact hA)
    (fun j ↦ Eventually.of_forall (fun y ↦ by
      apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      rw [norm_graphNormal_eq_areaDensity]
      exact mul_le_of_le_one_right (graphAreaDensity_pos b y).le (hGunit j _)))
    (Eventually.of_forall (fun y ↦ tendsto_const_nhds.inner (hGt _)))
  simp only [heG, heF] at ht
  apply le_of_tendsto_of_tendsto (ENNReal.tendsto_ofReal ht.norm) tendsto_const_nhds
  apply Eventually.of_forall
  intro j
  dsimp only
  have hcG : HasCompactSupport (G j) := hc.of_isClosed_subset (isClosed_tsupport _) (hGs j)
  have hpair : (∫ x, (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x *
      fieldDivergence basis (G j) x) = ∫ x in epigraph b, fieldDivergence basis (G j) x := by
    rw [← integral_indicator (isOpen_epigraph hb.continuous).measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by by_cases hx : x ∈ epigraph b <;> simp [hx])
  rw [← integral_epigraph_divergence basis hb (hG j) hcG, ← hpair]
  unfold variationalPerimeter
  exact le_iSup_of_le (G j) (le_iSup_of_le (hG j) (le_iSup_of_le hcG
    (le_iSup_of_le ((hGs j).trans hs) (le_iSup_of_le (hGunit j) le_rfl))))

/-- Every continuous compact cutoff in the test domain gives its weighted graph
area as a lower bound on the variational perimeter, already for C1 graphs. -/
theorem weighted_graph_area_le_perimeter {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {χ : Space (d + 1) → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hχval : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {Ω : Set (Space (d + 1))} (hs : tsupport χ ⊆ Ω) :
    ENNReal.ofReal (∫ y, χ (point y (b y)) * graphAreaDensity b y) ≤
      variationalPerimeter basis (epigraph b) Ω := by
  have hn : Continuous (outwardNormal b) := by
    change Continuous (fun y ↦ (graphAreaDensity b y)⁻¹ • point (gradient b y) (-1))
    apply ((continuous_graphAreaDensity hb).inv₀ (fun y ↦ (graphAreaDensity_pos b y).ne')).smul
    exact pointContinuousLinearMap.continuous.comp
      (((toDual ℝ (Space d)).symm.continuous.comp (hb.continuous_fderiv one_ne_zero)).prodMk
        continuous_const)
  let F := fun x : Space (d + 1) ↦ χ x • outwardNormal b (horizontal x)
  have hF : Continuous F := hχ.smul (hn.comp continuous_horizontal)
  have hFs : tsupport F ⊆ tsupport χ := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp only [F, hz, zero_smul])
  have hFc : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport _) hFs
  have hunit (x : Space (d + 1)) : ‖F x‖ ≤ 1 := by
    simpa only [F, norm_smul, norm_outwardNormal, mul_one,
      Real.norm_of_nonneg (hχval x).1] using (hχval x).2
  have he (y : Space d) : inner ℝ (point (gradient b y) (-1)) (F (point y (b y))) =
      χ (point y (b y)) * graphAreaDensity b y := by
    simp only [F, horizontal_point]
    change inner ℝ (point (gradient b y) (-1))
      (χ (point y (b y)) • ((graphAreaDensity b y)⁻¹ • point (gradient b y) (-1))) = _
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_graphNormal_eq_areaDensity]
    field_simp [(graphAreaDensity_pos b y).ne']
  have hnonneg : 0 ≤ ∫ y, χ (point y (b y)) * graphAreaDensity b y :=
    integral_nonneg (fun y ↦ mul_nonneg (hχval _).1 (graphAreaDensity_pos b y).le)
  simpa only [he, Real.norm_of_nonneg hnonneg] using
    graph_flux_le_perimeter_of_continuous basis hb hF hFc hunit (hFs.trans hs)

end SerrinEpigraph
