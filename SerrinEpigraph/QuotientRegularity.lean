module

public import SerrinEpigraph.Quotient
public import SerrinEpigraph.Boundary
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Continuity and local integrability of the negative quotient
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

private theorem point_graph_eq_of_mem_closure_not_mem_epigraph
    (hg : Continuous g) {x : Space (m + 1)}
    (hx : x ∈ closure (epigraph g)) (hxi : x ∉ epigraph g) :
    point (horizontal x) (g (horizontal x)) = x := by
  have hle : g (horizontal x) ≤ x (Fin.last m) := by
    simpa only [closure_epigraph hg, Set.mem_ofPred_eq] using hx
  have heq : g (horizontal x) = x (Fin.last m) := le_antisymm hle (le_of_not_gt hxi)
  rw [heq, point_horizontal_last]

/-- The totalized quotient is zero on the graph because its denominator is zero there. -/
theorem negativeQuotient_eq_zero_of_mem_closure_not_mem_epigraph (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ closure (epigraph g)) (hxi : x ∉ epigraph g) :
    negativeQuotient u x = 0 := by
  have heq := point_graph_eq_of_mem_closure_not_mem_epigraph h.graph_contDiff.continuous hx hxi
  have hu : u x = 0 := by
    rw [← heq]
    exact h.dirichlet _
  simp [negativeQuotient, hu]

/-- Near every graph point the negative quotient vanishes on the whole closed epigraph. -/
theorem exists_ball_negativeQuotient_eq_zero (h : Hypotheses g u f κ) (y : Space m) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ closure (epigraph g) ∩ Metric.ball (point y (g y)) ε,
      negativeQuotient u x = 0 := by
  obtain ⟨ε, hε, hpos⟩ := exists_ball_verticalDerivative_pos h y
  refine ⟨ε, hε, fun x hx ↦ ?_⟩
  by_cases hxi : x ∈ epigraph g
  · exact (negativeQuotient_eq_zero_iff (h.positive x hxi)).2 (hpos x ⟨hxi, hx.2⟩).le
  · exact negativeQuotient_eq_zero_of_mem_closure_not_mem_epigraph h hx.1 hxi

theorem continuousOn_negativeQuotient_epigraph (h : Hypotheses g u f κ) :
    ContinuousOn (negativeQuotient u) (epigraph g) := by
  have hd := h.solution_contDiffOn.continuousOn_fderiv_of_isOpen
    (isOpen_epigraph h.graph_contDiff.continuous) (by norm_num)
  have hv : ContinuousOn (verticalDerivative u) (epigraph g) := hd.clm_apply continuousOn_const
  exact (hv.neg.div h.solution_contDiffOn.continuousOn
    (fun x hx ↦ (h.positive x hx).ne')).sup continuousOn_const

/-- The negative quotient extends continuously to the boundary with value zero. -/
theorem continuousOn_negativeQuotient_closure (h : Hypotheses g u f κ) :
    ContinuousOn (negativeQuotient u) (closure (epigraph g)) := by
  intro x hx
  by_cases hxi : x ∈ epigraph g
  · exact ((continuousOn_negativeQuotient_epigraph h).continuousAt
      ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hxi)).continuousWithinAt
  · have heq := point_graph_eq_of_mem_closure_not_mem_epigraph h.graph_contDiff.continuous hx hxi
    rw [← heq]
    obtain ⟨ε, hε, hzero⟩ := exists_ball_negativeQuotient_eq_zero h (horizontal x)
    apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq_of_mem ?_
      (point_mem_closure_epigraph (le_refl _))
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Metric.ball_mem_nhds (point (horizontal x) (g (horizontal x))) hε]
      with z hz hzc
    exact hzero z ⟨hzc, hz⟩

/-- Every weighted quotient moment is integrable on a compact truncation of the closed epigraph. -/
theorem integrableOn_sq_mul_negativeQuotient_pow_closure_inter_closedBall
    (h : Hypotheses g u f κ) (k : ℕ) (R : ℝ) :
    IntegrableOn (fun x ↦ u x ^ 2 * negativeQuotient u x ^ k)
      (closure (epigraph g) ∩ Metric.closedBall 0 R) := by
  have hc := (h.solution_contDiffOn_closure.continuousOn.pow 2).mul
    ((continuousOn_negativeQuotient_closure h).pow k)
  exact (hc.mono Set.inter_subset_left).integrableOn_compact
    ((isCompact_closedBall 0 R).inter_left isClosed_closure)

/-- Every weighted quotient moment used in the estimates is integrable on a ball truncation. -/
theorem integrableOn_sq_mul_negativeQuotient_pow_epigraph_inter_ball
    (h : Hypotheses g u f κ) (k : ℕ) (R : ℝ) :
    IntegrableOn (fun x ↦ u x ^ 2 * negativeQuotient u x ^ k)
      (epigraph g ∩ Metric.ball 0 R) := by
  exact (integrableOn_sq_mul_negativeQuotient_pow_closure_inter_closedBall h k R).mono_set
    (Set.inter_subset_inter subset_closure Metric.ball_subset_closedBall)

end SerrinEpigraph
