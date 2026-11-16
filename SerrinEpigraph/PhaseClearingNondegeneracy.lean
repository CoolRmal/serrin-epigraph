module

public import SerrinEpigraph.PhaseClearingHalfBall
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Positive levels near every free-boundary point
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Every sufficiently small ball centered in the closure of the positive phase
contains a value larger than a uniform constant times its radius. -/
theorem RigidityHypotheses.exists_phase_nondegeneracy_constants
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ a R₀ : ℝ, 0 < a ∧ 0 < R₀ ∧
      ∀ c ∈ closure (epigraph g), ∀ R : ℝ, 0 < R → R ≤ R₀ →
        ∃ y ∈ ball c R, a * R < zeroExtension g u y := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_phase_clearing_constants h
  refine ⟨a, R₀, ha, hR₀, fun c hc R hR hRR ↦ ?_⟩
  by_contra hn
  push Not at hn
  have hz := hclear c R hR hRR hn
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (R / 2) (by positivity)
  have hpos := (h.zeroExtension_pos_iff y).mpr hy
  have hyball : y ∈ ball c (R / 2) := by
    change dist y c < R / 2
    rwa [dist_comm]
  have hh := hz hyball
  change zeroExtension g u y = 0 at hh
  linarith

/-- One fixed interior level is attained within a fixed distance of every original
free-boundary point. This is the level-location consequence of clearing. -/
theorem RigidityHypotheses.exists_fixed_level_near_freeBoundary
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ α R₀ : ℝ, α ∈ Ioo (0 : ℝ) 1 ∧ 0 < R₀ ∧
      ∀ c ∈ frontier (epigraph g),
        ∃ y ∈ ball c R₀, zeroExtension g u y = α := by
  obtain ⟨a, R₀, ha, hR₀, hnd⟩ := hr.exists_phase_nondegeneracy_constants h
  let α := min (a * R₀ / 2) (1 / 2 : ℝ)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαone : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hαa : α < a * R₀ := (min_le_left _ _).trans_lt (by nlinarith [mul_pos ha hR₀])
  refine ⟨α, R₀, ⟨hα, hαone⟩, hR₀, ?_⟩
  intro c hc
  obtain ⟨y, hy, hUy⟩ := hnd c (frontier_subset_closure hc) R₀ hR₀ le_rfl
  have hc0 : zeroExtension g u c = 0 := by
    rw [h.zeroExtension_eqOn_closure (frontier_subset_closure hc)]
    exact h.solution_zero_frontier hc
  have hconn := (convex_ball c R₀).isPreconnected
  have himage := hconn.intermediate_value (mem_ball_self hR₀) hy
    h.zeroExtension_continuous.continuousOn
  apply himage
  rw [hc0]
  exact ⟨hα.le, hαa.le.trans hUy.le⟩

end SerrinEpigraph
