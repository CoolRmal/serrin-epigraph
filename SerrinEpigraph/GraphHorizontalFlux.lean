module

public import SerrinEpigraph.GraphVerticalFlux

/-!
# Horizontal integration by parts over graph epigraphs
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Flattening an epigraph permits integration of horizontal sections first. -/
theorem integral_epigraph_eq_flat_sections {d : ℕ} {b : Space d → ℝ}
    (hb : Continuous b) {v : Space (d + 1) → ℝ} (hv : Measurable v)
    (hi : IntegrableOn v (epigraph b)) :
    (∫ x in epigraph b, v x) = ∫ t in Ioi (0 : ℝ), ∫ y, v (point y (b y + t)) := by
  let F := (epigraph b).indicator v
  let Q : Space d × ℝ → ℝ := fun p ↦ F (point p.1 (b p.1 + p.2))
  have hF : Measurable F := hv.indicator (isOpen_epigraph hb).measurableSet
  have hFi : Integrable F := (integrable_indicator_iff (isOpen_epigraph hb).measurableSet).mpr hi
  have hmapcont : Continuous (fun p : Space d × ℝ ↦ point p.1 (b p.1 + p.2)) :=
    pointContinuousLinearMap.continuous.comp
      (continuous_fst.prodMk ((hb.comp continuous_fst).add continuous_snd))
  have hQ : Measurable Q := hF.comp hmapcont.measurable
  have hp := measurePreserving_horizontal_graphHeight hb.measurable
  have hinv (x : Space (d + 1)) : point (horizontal x) (b (horizontal x) + graphHeight b x) = x := by
    have he : b (horizontal x) + graphHeight b x = x (Fin.last d) := by
      dsimp [graphHeight]; ring
    rw [he, point_horizontal_last]
  have hQi : Integrable Q ((volume : Measure (Space d)).prod volume) := by
    apply (hp.integrable_comp hQ.aestronglyMeasurable).mp
    simpa only [Function.comp_def, Q, hinv] using hFi
  have hmap := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable Q (Measure.map
      (fun x : Space (d + 1) ↦ (horizontal x, graphHeight b x)) volume) from
        hQ.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  have he : (∫ x, F x) = ∫ p, Q p ∂((volume : Measure (Space d)).prod volume) := by
    simpa only [Q, hinv] using hmap.symm
  rw [← integral_indicator (isOpen_epigraph hb).measurableSet]
  change (∫ x, F x) = _
  rw [he, integral_prod_symm _ hQi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t ↦ by
    dsimp only
    by_cases ht : 0 < t
    · rw [indicator_of_mem (s := Ioi (0 : ℝ)) ht]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y ↦ by
        have hm : point y (b y + t) ∈ epigraph b := by simp [epigraph, ht]
        exact indicator_of_mem hm _)
    · have hz : ∀ y, Q (y, t) = 0 := by
        intro y
        have hm : point y (b y + t) ∉ epigraph b := by simp [epigraph, ht]
        exact indicator_of_notMem hm _
      simp only [hz, integral_zero, indicator_of_notMem (s := Ioi (0 : ℝ)) ht])

/-- A fixed flattened graph section of a compact test function is compactly supported. -/
theorem hasCompactSupport_graph_section {d : ℕ} {b : Space d → ℝ}
    {φ : Space (d + 1) → ℝ} (hc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun y ↦ φ (point y (b y + t))) := by
  apply (hc.image continuous_horizontal).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (hc.image continuous_horizontal).isClosed
  intro y hy
  exact ⟨point y (b y + t), subset_tsupport φ hy, horizontal_point _ _⟩

/-- Every flattened graph section has zero integral horizontal derivative. -/
theorem integral_graph_section_fderiv_eq_zero {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {φ : Space (d + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (w : Space d) :
    (∫ y, fderiv ℝ (fun z ↦ φ (point z (b z + t))) y w) = 0 := by
  have hp : ContDiff ℝ 1 (fun y ↦ point y (b y + t)) :=
    pointContinuousLinearMap.contDiff.comp (contDiff_id.prodMk (hb.add contDiff_const))
  have hi := integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := volume)
    (u := fun _ : Space d ↦ (1 : ℝ)) isOpen_univ contDiffOn_const (hφ.comp hp)
    (hasCompactSupport_graph_section hc t) (subset_univ _) w
  simpa [Function.comp_def] using hi

/-- Horizontal flux through an epigraph equals the boundary trace weighted by
the corresponding graph derivative. -/
theorem integral_epigraph_horizontal_fderiv {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {φ : Space (d + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (w : Space d) :
    (∫ x in epigraph b, fderiv ℝ φ x (point w 0)) =
      ∫ y, φ (point y (b y)) * fderiv ℝ b y w := by
  let A := fun x : Space (d + 1) ↦ fderiv ℝ φ x (point w 0)
  let B := fun x : Space (d + 1) ↦ fderiv ℝ b (horizontal x) w * verticalDerivative φ x
  have hA : Continuous A := (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hB : Continuous B :=
    (((hb.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp continuous_horizontal).mul
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hsA : tsupport A ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ _
  have hsB : tsupport B ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    exact hx (by simp [B, verticalDerivative, fderiv_of_notMem_tsupport ℝ hn])
  have hiA : Integrable A := hA.integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) hsA)
  have hiB : Integrable B := hB.integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) hsB)
  have hder (t : ℝ) (y : Space d) :
      fderiv ℝ (fun z ↦ φ (point z (b z + t))) y w =
        A (point y (b y + t)) + B (point y (b y + t)) := by
    have hp := pointContinuousLinearMap.hasFDerivAt.comp y
      ((hasFDerivAt_id y).prodMk ((hb.differentiable_one y).hasFDerivAt.add_const t))
    have hd := (hφ.differentiable_one (point y (b y + t))).hasFDerivAt.comp y hp
    simp only [Function.comp_def, pointContinuousLinearMap_apply, id_eq] at hd
    rw [hd.fderiv]
    change fderiv ℝ φ (point y (b y + t)) (point w (fderiv ℝ b y w)) = _
    have he := point_add_vertical w 0 (fderiv ℝ b y w)
    rw [zero_add] at he
    rw [← he, map_add, map_smul]
    simp only [A, B, horizontal_point, verticalDerivative, smul_eq_mul]
  have hzero : (∫ x in epigraph b, A x + B x) = 0 := by
    rw [integral_epigraph_eq_flat_sections (v := fun x ↦ A x + B x)
      hb.continuous (hA.add hB).measurable
      (hiA.add hiB).integrableOn]
    simp_rw [← hder, integral_graph_section_fderiv_eq_zero hb hφ hc, integral_zero]
  have hvertical : (∫ x in epigraph b, B x) =
      -∫ y, φ (point y (b y)) * fderiv ℝ b y w := by
    rw [integral_epigraph_eq_integral_sections hb.continuous hB.measurable hiB.integrableOn]
    have he (y : Space d) : (∫ t in Ioi (b y), B (point y t)) =
        -(φ (point y (b y)) * fderiv ℝ b y w) := by
      simp only [B, horizontal_point]
      rw [integral_const_mul, integral_verticalDerivative_section hφ hc]
      ring
    simp_rw [he]
    exact integral_neg _
  rw [integral_add hiA.integrableOn hiB.integrableOn, hvertical] at hzero
  change (∫ x in epigraph b, A x) = _
  linarith

/-- The directional boundary flux formula combines the horizontal and vertical parts. -/
theorem integral_epigraph_fderiv {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {φ : Space (d + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (w : Space (d + 1)) :
    (∫ x in epigraph b, fderiv ℝ φ x w) =
      ∫ y, φ (point y (b y)) * (fderiv ℝ b y (horizontal w) - w (Fin.last d)) := by
  have htrace : Continuous (fun y ↦ φ (point y (b y))) := hφ.continuous.comp
    (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous))
  have hcTrace : HasCompactSupport (fun y ↦ φ (point y (b y))) := by
    simpa only [add_zero] using hasCompactSupport_graph_section (b := b) hc 0
  have hiTrace : Integrable (fun y ↦ φ (point y (b y))) :=
    htrace.integrable_of_hasCompactSupport hcTrace
  have hiWeight : Integrable (fun y ↦ φ (point y (b y)) * fderiv ℝ b y (horizontal w)) :=
    (htrace.mul ((hb.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport hcTrace.mul_right
  have hi (z : Space (d + 1)) : Integrable (fun x ↦ fderiv ℝ φ x z) :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ z))
  have hw : w = point (horizontal w) 0 + w (Fin.last d) • verticalDirection d := by
    rw [point_add_vertical, zero_add, point_horizontal_last]
  have he (x : Space (d + 1)) : fderiv ℝ φ x w =
      fderiv ℝ φ x (point (horizontal w) 0) + w (Fin.last d) * verticalDerivative φ x := by
    conv_lhs => rw [hw]
    simp only [map_add, map_smul, smul_eq_mul, verticalDerivative]
  have hiV : IntegrableOn (fun x ↦ w (Fin.last d) * verticalDerivative φ x) (epigraph b) :=
    ((hi (verticalDirection d)).const_mul _).integrableOn
  simp_rw [he, mul_sub]
  rw [integral_add (hi (point (horizontal w) 0)).integrableOn hiV,
    integral_const_mul, integral_epigraph_horizontal_fderiv hb hφ hc,
    integral_epigraph_verticalDerivative hb.continuous hφ hc,
    integral_sub hiWeight (hiTrace.mul_const _), integral_mul_const]
  ring

end SerrinEpigraph
