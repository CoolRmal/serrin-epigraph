module

public import SerrinEpigraph.MeasurablePhaseMollification

/-!
# Moving averaging from a measurable phase to its test functions
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution

namespace SerrinEpigraph

/-- Fubini transfers scalar averaging to translated compact test functions. -/
theorem integral_mollify_mul_eq_average_tests {d : ℕ} {v ψ : Space d → ℝ}
    (hv : Measurable v) {B : ℝ} (hB : ∀ x, ‖v x‖ ≤ B)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (n : ℕ) :
    (∫ x, mollify v n x * ψ x) = ∫ y, (averagingBump d n).normed volume y *
      ∫ x, v x * ψ (x + y) := by
  let K := (averagingBump d n).normed volume
  let F : Space d → Space d → ℝ := fun x y ↦ K y * v (x - y) * ψ x
  have hi : Integrable F.uncurry (volume.prod volume) := by
    have hh := ((hψ.integrable_of_hasCompactSupport (μ := volume) hc).mul_prod
      ((averagingBump d n).integrable_normed (μ := volume))).mul_bdd
      (hv.comp (continuous_fst.sub continuous_snd).measurable).aestronglyMeasurable
      (Eventually.of_forall (fun p ↦ hB (p.1 - p.2)))
    apply hh.congr
    exact Eventually.of_forall (fun p ↦ by
      dsimp only [F, K, Function.uncurry, Function.comp_def, Pi.sub_apply]
      ring)
  calc
    _ = ∫ x, ∫ y, F x y := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x ↦ by
        dsimp only [F]
        rw [integral_mul_const]
        rfl)
    _ = ∫ y, ∫ x, F x y := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun y ↦ ?_)
      change (∫ x, F x y) = K y * (∫ x, v x * ψ (x + y))
      have he := integral_add_right_eq_self (μ := volume) (fun x ↦ v (x - y) * ψ x) y
      simp only [add_sub_cancel_right] at he
      calc
        (∫ x, F x y) = K y * ∫ x, v (x - y) * ψ x := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Eventually.of_forall (fun x ↦ by dsimp only [F]; ring)
        _ = K y * ∫ x, v x * ψ (x + y) := congrArg (fun z ↦ K y * z) he.symm

/-- Translating a C1 vector field translates its divergence. -/
theorem fieldDivergence_translate {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F : Space d → Space d}
    (hF : ContDiff ℝ 1 F) (y x : Space d) :
    fieldDivergence b (fun z ↦ F (z + y)) x = fieldDivergence b F (x + y) := by
  have hd := ((hF.differentiable_one (x + y)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).add_const y)
  have he : fderiv ℝ (fun z ↦ F (z + y)) x = fderiv ℝ F (x + y) := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using hd.fderiv
  simp only [fieldDivergence, he]

/-- A translated field supported in a ball is supported in the ball enlarged by the shift. -/
theorem tsupport_translate_subset_ball {d : ℕ} {F : Space d → Space d}
    {r ρ : ℝ} (hs : tsupport F ⊆ ball 0 r) {y : Space d} (hy : ‖y‖ ≤ ρ) :
    tsupport (fun x ↦ F (x + y)) ⊆ ball 0 (r + ρ) := by
  have ht := tsupport_comp_subset_preimage F (continuous_id.add (continuous_const (y := y)))
  intro x hx
  have hxy : x + y ∈ tsupport F := ht hx
  have hn : ‖x + y‖ < r := by simpa only [mem_ball, dist_zero_right] using hs hxy
  rw [mem_ball, dist_zero_right]
  calc
    ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
    _ < r + ρ := add_lt_add_of_lt_of_le hn hy

end SerrinEpigraph
