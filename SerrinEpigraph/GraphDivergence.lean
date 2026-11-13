module

public import SerrinEpigraph.GraphHorizontalFlux

/-!
# Divergence theorem for C1 graph epigraphs
-/

public section

open Set MeasureTheory InnerProductSpace

namespace SerrinEpigraph

/-- Compact C1 vector fields have the exact outward boundary flux on a C1 epigraph.
The unnormalized normal includes the graph area factor. -/
theorem integral_epigraph_divergence {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {F : Space (d + 1) → Space (d + 1)}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    (∫ x in epigraph b, fieldDivergence basis F x) =
      ∫ y, inner ℝ (point (gradient b y) (-1)) (F (point y (b y))) := by
  let ψ := fun i x ↦ inner ℝ (basis i) (F x)
  have hψ (i : Fin (d + 1)) : ContDiff ℝ 1 (ψ i) :=
    (innerSL ℝ (basis i)).contDiff.comp hF
  have hcψ (i : Fin (d + 1)) : HasCompactSupport (ψ i) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (by simp : inner ℝ (basis i) (0 : Space (d + 1)) = 0) F)
  have hd (i : Fin (d + 1)) (x : Space (d + 1)) :
      fderiv ℝ (ψ i) x (basis i) = inner ℝ (basis i) (fderiv ℝ F x (basis i)) := by
    have he := (innerSL ℝ (basis i)).hasFDerivAt.comp x (hF.differentiable_one x).hasFDerivAt
    exact congrArg (fun L : Space (d + 1) →L[ℝ] ℝ ↦ L (basis i)) he.fderiv
  have hi (i : Fin (d + 1)) : IntegrableOn
      (fun x ↦ fderiv ℝ (ψ i) x (basis i)) (epigraph b) :=
    (((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport
        ((hcψ i).of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ _))
      |>.integrableOn
  have htrace (i : Fin (d + 1)) : Continuous (fun y ↦ ψ i (point y (b y))) :=
    (hψ i).continuous.comp
      (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous))
  have hcTrace (i : Fin (d + 1)) : HasCompactSupport (fun y ↦ ψ i (point y (b y))) := by
    simpa only [add_zero] using hasCompactSupport_graph_section (b := b) (hcψ i) 0
  have hiTrace (i : Fin (d + 1)) : Integrable (fun y ↦ ψ i (point y (b y)) *
      (fderiv ℝ b y (horizontal (basis i)) - basis i (Fin.last d))) :=
    ((htrace i).mul (((hb.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
      continuous_const)).integrable_of_hasCompactSupport (hcTrace i).mul_right
  have hnormal (y : Space d) (i : Fin (d + 1)) :
      fderiv ℝ b y (horizontal (basis i)) - basis i (Fin.last d) =
        inner ℝ (point (gradient b y) (-1)) (basis i) := by
    conv_rhs => rw [← point_horizontal_last (basis i)]
    simp only [inner_point_point, inner_gradient_left, neg_one_mul]
    ring
  have hsum (y : Space d) : (∑ i, ψ i (point y (b y)) *
      (fderiv ℝ b y (horizontal (basis i)) - basis i (Fin.last d))) =
        inner ℝ (point (gradient b y) (-1)) (F (point y (b y))) := by
    simp_rw [hnormal]
    simpa only [ψ, mul_comm] using basis.sum_inner_mul_inner
      (point (gradient b y) (-1)) (F (point y (b y)))
  unfold fieldDivergence
  simp_rw [← hd]
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [integral_epigraph_fderiv hb (hψ _) (hcψ _)]
  rw [← integral_finsetSum _ (fun i _ ↦ hiTrace i)]
  simp_rw [hsum]

/-- The unnormalized graph normal has norm equal to the graph area density. -/
theorem norm_graphNormal_eq_areaDensity {d : ℕ} (b : Space d → ℝ) (y : Space d) :
    ‖point (gradient b y) (-1)‖ = graphAreaDensity b y := by
  have hn : ‖point (gradient b y) (-1)‖ ^ 2 = ‖gradient b y‖ ^ 2 + 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
    ring
  nlinarith [graphAreaDensity_sq b y, graphAreaDensity_pos b y,
    norm_nonneg (point (gradient b y) (-1))]

/-- Divergence tests are bounded by graph area weighted by the boundary norm of
the field, so the upper bound is localized to the actual graph trace. -/
theorem norm_integral_epigraph_divergence_le_graph_area {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {F : Space (d + 1) → Space (d + 1)}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    ‖∫ x in epigraph b, fieldDivergence basis F x‖ ≤
      ∫ y, graphAreaDensity b y * ‖F (point y (b y))‖ := by
  rw [integral_epigraph_divergence basis hb hF hc]
  have htrace : Continuous (fun y ↦ F (point y (b y))) := hF.continuous.comp
    (pointContinuousLinearMap.continuous.comp (continuous_id.prodMk hb.continuous))
  have hct : HasCompactSupport (fun y ↦ ‖F (point y (b y))‖) := by
    simpa only [add_zero] using hasCompactSupport_graph_section (b := b) hc.norm 0
  have hi : Integrable (fun y ↦ graphAreaDensity b y * ‖F (point y (b y))‖) :=
    ((continuous_graphAreaDensity hb).mul htrace.norm).integrable_of_hasCompactSupport hct.mul_left
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y ↦ norm_nonneg _)) hi
  apply Filter.Eventually.of_forall
  intro y
  simpa only [norm_graphNormal_eq_areaDensity] using
    (norm_inner_le_norm (𝕜 := ℝ) (point (gradient b y) (-1)) (F (point y (b y))))

end SerrinEpigraph
