module

public import SerrinEpigraph.NormalizedGraphMeasure

/-!
# Euclidean gradient of normalized graph height
-/

public section

open InnerProductSpace

namespace SerrinEpigraph

/-- Vertical height above a graph in Euclidean coordinates. -/
@[expose] def graphHeight {d : ℕ} (b : Space d → ℝ) (x : Space (d + 1)) : ℝ :=
  x (Fin.last d) - b (horizontal x)

/-- The differential of graph height splits into its vertical and horizontal parts. -/
theorem graphHeight_hasFDerivAt {d : ℕ} {b : Space d → ℝ} {x : Space (d + 1)}
    (hb : DifferentiableAt ℝ b (horizontal x)) :
    HasFDerivAt (graphHeight b)
      (PiLp.proj 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d) -
        (fderiv ℝ b (horizontal x)).comp horizontalContinuousLinearMap) x := by
  exact (PiLp.proj 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).hasFDerivAt.sub
    (hb.hasFDerivAt.comp x horizontalContinuousLinearMap.hasFDerivAt)

/-- The Euclidean gradient has the horizontal graph gradient and a unit vertical component. -/
theorem gradient_graphHeight {d : ℕ} {b : Space d → ℝ} {x : Space (d + 1)}
    (hb : DifferentiableAt ℝ b (horizontal x)) :
    gradient (graphHeight b) x = point (-gradient b (horizontal x)) 1 := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, (graphHeight_hasFDerivAt hb).fderiv]
  conv_rhs => rw [← point_horizontal_last w]
  simp only [inner_point_point, inner_neg_left, inner_gradient_left, one_mul,
    sub_apply, ContinuousLinearMap.comp_apply]
  change w (Fin.last d) - fderiv ℝ b (horizontal x) (horizontal w) =
    -fderiv ℝ b (horizontal x) (horizontal w) + w (Fin.last d)
  ring

/-- Graph height has the exact Euclidean squared gradient norm. -/
theorem norm_gradient_graphHeight_sq {d : ℕ} {b : Space d → ℝ} {x : Space (d + 1)}
    (hb : DifferentiableAt ℝ b (horizontal x)) :
    ‖gradient (graphHeight b) x‖ ^ 2 = 1 + ‖gradient b (horizontal x)‖ ^ 2 := by
  rw [gradient_graphHeight hb, ← real_inner_self_eq_norm_sq, inner_point_point,
    real_inner_self_eq_norm_sq, norm_neg]
  ring

/-- Dividing height by an upper bound for its gradient yields a unit-gradient coordinate. -/
theorem norm_gradient_normalizedGraphHeight_le {d : ℕ} {b : Space d → ℝ}
    {x : Space (d + 1)} (hb : DifferentiableAt ℝ b (horizontal x)) {L : ℝ} (hL : 0 < L)
    (hbound : 1 + ‖gradient b (horizontal x)‖ ^ 2 ≤ L ^ 2) :
    ‖gradient (fun y ↦ graphHeight b y / L) x‖ ≤ 1 := by
  have hd := (graphHeight_hasFDerivAt hb).const_mul L⁻¹
  have he : fderiv ℝ (fun y ↦ graphHeight b y / L) x =
      L⁻¹ • fderiv ℝ (graphHeight b) x := by
    simpa only [div_eq_inv_mul, (graphHeight_hasFDerivAt hb).fderiv] using hd.fderiv
  have hn : ‖gradient (graphHeight b) x‖ ≤ L := by
    have hh := norm_gradient_graphHeight_sq hb
    nlinarith [norm_nonneg (gradient (graphHeight b) x)]
  simp only [gradient, he, map_smul, norm_smul, norm_inv,
    Real.norm_of_nonneg hL.le]
  change L⁻¹ * ‖gradient (graphHeight b) x‖ ≤ 1
  rw [← div_eq_inv_mul, div_le_one hL]
  exact hn

end SerrinEpigraph
