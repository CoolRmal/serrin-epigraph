module

public import SerrinEpigraph.OneSidedPhaseLimit
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vertical integration by parts over a graph epigraph
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- A vertical coordinate line is an isometric embedding. -/
theorem isometry_point {d : ℕ} (y : Space d) : Isometry (point y) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  have he : point y s - point y t = (s - t) • verticalDirection d := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point, verticalDirection]
  rw [dist_eq_norm, he, norm_smul, norm_verticalDirection, mul_one, dist_eq_norm]

/-- The vertical derivative of a compact C1 test function integrates to its
negative boundary trace on every vertical section of an epigraph. -/
theorem integral_verticalDerivative_section {d : ℕ} {φ : Space (d + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (y : Space d) (a : ℝ) :
    (∫ t in Ioi a, verticalDerivative φ (point y t)) = -φ (point y a) := by
  have hp : ContDiff ℝ 1 (point y) :=
    pointContinuousLinearMap.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hslice : HasCompactSupport (fun t ↦ φ (point y t)) :=
    hc.comp_isClosedEmbedding (isometry_point y).isClosedEmbedding
  have he (t : ℝ) : deriv (fun s ↦ φ (point y s)) t =
      verticalDerivative φ (point y t) := by
    have hd : HasDerivAt (point y) (verticalDirection d) t := by
      simpa only [point_add_vertical, zero_add, id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const (verticalDirection d)).const_add (point y 0)
    exact ((hφ.differentiable_one _).hasFDerivAt.comp_hasDerivAt t hd).deriv
  simpa only [Function.comp_def, he] using hslice.integral_Ioi_deriv_eq (hφ.comp hp) a

/-- Fubini in horizontal/vertical Euclidean coordinates, with graph truncation. -/
theorem integral_epigraph_eq_integral_sections {d : ℕ} {b : Space d → ℝ}
    (hb : Continuous b) {v : Space (d + 1) → ℝ} (hv : Measurable v)
    (hi : IntegrableOn v (epigraph b)) :
    (∫ x in epigraph b, v x) = ∫ y, ∫ t in Ioi (b y), v (point y t) := by
  let F := (epigraph b).indicator v
  let Q : Space d × ℝ → ℝ := fun p ↦ F (point p.1 p.2)
  have hF : Measurable F := hv.indicator (isOpen_epigraph hb).measurableSet
  have hFi : Integrable F := (integrable_indicator_iff (isOpen_epigraph hb).measurableSet).mpr hi
  have hQ : Measurable Q := hF.comp pointContinuousLinearMap.continuous.measurable
  have hp := measurePreserving_horizontal_last d
  have hQi : Integrable Q ((volume : Measure (Space d)).prod volume) := by
    apply (hp.integrable_comp hQ.aestronglyMeasurable).mp
    simpa only [Function.comp_def, Q, point_horizontal_last] using hFi
  have hmap := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable Q (Measure.map
      (fun x : Space (d + 1) ↦ (horizontal x, x (Fin.last d))) volume) from
        hQ.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  have he : (∫ x, F x) = ∫ p, Q p ∂((volume : Measure (Space d)).prod volume) := by
    simpa only [Q, point_horizontal_last] using hmap.symm
  rw [← integral_indicator (isOpen_epigraph hb).measurableSet]
  change (∫ x, F x) = _
  rw [he, integral_prod _ hQi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y ↦ by
    dsimp only
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t ↦ by
      simp only [Q, F, indicator_apply, epigraph, mem_ofPred_eq, horizontal_point, last_point,
        mem_Ioi]))

/-- Vertical integration by parts identifies the graph boundary trace exactly. -/
theorem integral_epigraph_verticalDerivative {d : ℕ} {b : Space d → ℝ}
    (hb : Continuous b) {φ : Space (d + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x in epigraph b, verticalDerivative φ x) = -∫ y, φ (point y (b y)) := by
  have hd : Continuous (verticalDerivative φ) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs : tsupport (verticalDerivative φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    exact hx (by simp [verticalDerivative, fderiv_of_notMem_tsupport ℝ hn])
  have hcompact : HasCompactSupport (verticalDerivative φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hs
  rw [integral_epigraph_eq_integral_sections hb hd.measurable
    (hd.integrable_of_hasCompactSupport hcompact).integrableOn]
  simp_rw [integral_verticalDerivative_section hφ hc]
  exact integral_neg _

end SerrinEpigraph
