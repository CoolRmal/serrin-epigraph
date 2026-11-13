module

public import SerrinEpigraph.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local finiteness of the squared mass

Continuity up to the boundary makes the squared mass on every bounded truncation integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}

/-- The squared solution is integrable on every compact truncation of the closed epigraph. -/
theorem integrableOn_sq_closure_inter_closedBall
    (hu : ContinuousOn u (closure (epigraph g))) (R : ℝ) :
    IntegrableOn (fun x ↦ u x ^ 2) (closure (epigraph g) ∩ Metric.closedBall 0 R) := by
  exact ((hu.pow 2).mono Set.inter_subset_left).integrableOn_compact
    ((isCompact_closedBall 0 R).inter_left isClosed_closure)

/-- The squared mass defining the growth hypothesis is an integral of an integrable function. -/
theorem integrableOn_sq_epigraph_inter_ball
    (hu : ContinuousOn u (closure (epigraph g))) (R : ℝ) :
    IntegrableOn (fun x ↦ u x ^ 2) (epigraph g ∩ Metric.ball 0 R) := by
  exact (integrableOn_sq_closure_inter_closedBall hu R).mono_set
    (Set.inter_subset_inter subset_closure Metric.ball_subset_closedBall)

theorem squareMass_nonneg (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (R : ℝ) :
    0 ≤ squareMass g u R := by
  exact integral_nonneg (fun x ↦ sq_nonneg (u x))

theorem log_one_add_squareMass_nonneg (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (R : ℝ) :
    0 ≤ Real.log (1 + squareMass g u R) := by
  exact Real.log_nonneg (le_add_of_nonneg_right (squareMass_nonneg g u R))

end SerrinEpigraph
