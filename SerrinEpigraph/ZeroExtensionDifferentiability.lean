module

public import SerrinEpigraph.ZeroExtensionRegularity
public import SerrinEpigraph.BoundaryGradient
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Almost-everywhere differentiation of the zero extension
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Filter Metric
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Rademacher's theorem on a countable compact cover gives almost-everywhere differentiability. -/
theorem Hypotheses.zeroExtension_ae_differentiableAt (h : Hypotheses g u f κ) :
    ∀ᵐ x, DifferentiableAt ℝ (zeroExtension g u) x := by
  have he (n : ℕ) : ∀ᵐ x, x ∈ closedBall (0 : Space (m + 1)) (n + 1) →
      DifferentiableWithinAt ℝ (zeroExtension g u) (closedBall 0 (n + 1)) x := by
    obtain ⟨C, hC⟩ := h.zeroExtension_lipschitzOn_compact (isCompact_closedBall 0 (n + 1))
    exact hC.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr he] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hb : x ∈ ball (0 : Space (m + 1)) (n + 1) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  exact (hx n (ball_subset_closedBall hb)).differentiableAt (closedBall_mem_nhds_of_mem hb)

/-- The totalized gradient is zero wherever the nonnegative extension vanishes. -/
theorem Hypotheses.gradient_zeroExtension_of_notMem (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∉ epigraph g) : gradient (zeroExtension g u) x = 0 := by
  have hmin : IsLocalMin (zeroExtension g u) x := by
    filter_upwards with y
    rw [zeroExtension_of_notMem hx]
    exact h.zeroExtension_nonneg y
  simp only [gradient, hmin.fderiv_eq_zero, map_zero]

/-- The totalized gradient of the zero extension is exactly the interior gradient extended by zero. -/
theorem Hypotheses.gradient_zeroExtension_eq_indicator (h : Hypotheses g u f κ) :
    gradient (zeroExtension g u) = (epigraph g).indicator (gradient u) := by
  funext x
  by_cases hx : x ∈ epigraph g
  · rw [h.gradient_zeroExtension hx, Set.indicator_of_mem hx]
  · rw [h.gradient_zeroExtension_of_notMem hx, Set.indicator_of_notMem hx]

/-- The extension and original function agree on the entire closed epigraph. -/
theorem Hypotheses.zeroExtension_eqOn_closure (h : Hypotheses g u f κ) :
    Set.EqOn (zeroExtension g u) u (closure (epigraph g)) := by
  intro x hx
  by_cases hxi : x ∈ epigraph g
  · exact zeroExtension_of_mem hxi
  · have hfront : x ∈ frontier (epigraph g) :=
      ⟨hx, fun hi ↦ hxi (interior_subset hi)⟩
    rw [zeroExtension_of_notMem hxi, h.solution_zero_frontier hfront]

/-- The nonzero boundary slope prevents differentiability of the zero extension on the graph. -/
theorem Hypotheses.zeroExtension_not_differentiableAt_boundary
    (h : Hypotheses g u f κ) (y : Space m) :
    ¬DifferentiableAt ℝ (zeroExtension g u) (point y (g y)) := by
  intro hd
  have hx := point_mem_closure_epigraph (le_refl (g y))
  have hout : point y (g y) ∉ epigraph g := by simp [epigraph]
  have hmin : IsLocalMin (zeroExtension g u) (point y (g y)) := by
    filter_upwards with x
    rw [zeroExtension_of_notMem hout]
    exact h.zeroExtension_nonneg x
  have hzero := hmin.fderiv_eq_zero
  have he : HasFDerivWithinAt u (0 : Space (m + 1) →L[ℝ] ℝ) (closure (epigraph g)) (point y (g y)) := by
    have hdu := hd.hasFDerivAt.hasFDerivWithinAt (s := closure (epigraph g))
    rw [hzero] at hdu
    exact hdu.congr h.zeroExtension_eqOn_closure.symm (h.zeroExtension_eqOn_closure hx).symm
  have hf := he.fderivWithin
    ((uniqueDiffOn_closure_epigraph h.graph_contDiff.differentiable_one) _ hx)
  have hn := h.neumann y
  rw [hf, zero_apply] at hn
  linarith [h.kappa_pos]

/-- The boundary is a null set, as it is contained in the Rademacher exceptional set. -/
theorem Hypotheses.frontier_epigraph_null (h : Hypotheses g u f κ) :
    volume (frontier (epigraph g)) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [h.zeroExtension_ae_differentiableAt] with x hx hfront
  have he : g (horizontal x) = x (Fin.last m) := by
    simpa only [frontier_epigraph h.graph_contDiff.continuous, Set.mem_ofPred_eq] using hfront
  have hp : point (horizontal x) (g (horizontal x)) = x := by
    rw [he, point_horizontal_last]
  apply h.zeroExtension_not_differentiableAt_boundary (horizontal x)
  rwa [hp]

end SerrinEpigraph
