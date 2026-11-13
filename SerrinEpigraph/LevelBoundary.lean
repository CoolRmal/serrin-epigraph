module

public import SerrinEpigraph.LevelGradient

/-!
# The zero-level boundary of the vertical foliation
-/

public section

noncomputable section

open InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The total inverse height equals the graph height at level zero. -/
theorem RigidityHypotheses.levelHeightReal_zero (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : hr.levelHeightReal h y 0 = g y := by
  simp [levelHeightReal]

/-- The total inverse height never lies below the original boundary. -/
theorem RigidityHypotheses.graph_le_levelHeightReal (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : ℝ) : g y ≤ hr.levelHeightReal h y s := by
  by_cases hs : s ∈ Set.Ioo (0 : ℝ) 1
  · rw [hr.levelHeightReal_eq h y hs]
    exact (hr.levelHeight_spec h y ⟨s, hs⟩).1.le
  · simp [levelHeightReal, hs]

/-- The inverse height extends jointly continuously to level zero. -/
theorem RigidityHypotheses.levelHeightReal_continuousAt_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    ContinuousAt (fun p : Space m × ℝ ↦ hr.levelHeightReal h p.1 p.2) (y, 0) := by
  have hg : ContinuousAt (fun p : Space m × ℝ ↦ g p.1) (y, 0) :=
    (h.graph_contDiff.continuous.comp continuous_fst).continuousAt
  change Tendsto _ (𝓝 (y, 0)) (𝓝 (hr.levelHeightReal h y 0))
  rw [hr.levelHeightReal_zero h y]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hg.eventually (eventually_gt_nhds ha)] with p hp
    exact hp.trans_le (hr.graph_le_levelHeightReal h p.1 p.2)
  · intro b hb
    have hx : point y b ∈ epigraph g := by simpa [epigraph] using hb
    have hu : (0 : ℝ) < u (point y b) := h.positive _ hx
    have hc : ContinuousAt (fun p : Space m × ℝ ↦ u (point p.1 b)) (y, 0) := by
      have hc0 : ContinuousAt (fun z ↦ u (point z b)) y :=
        h.continuousAt_horizontal_section hb
      simpa only [Function.comp_def] using
        hc0.comp (f := Prod.fst) (continuous_fst.continuousAt (x := (y, (0 : ℝ))))
    have he₁ := hg.eventually (eventually_lt_nhds hb)
    have he₂ := continuous_snd.continuousAt.eventually_lt hc hu
    filter_upwards [he₁, he₂] with p hp₁ hp₂
    by_cases hs : p.2 ∈ Set.Ioo (0 : ℝ) 1
    · rw [hr.levelHeightReal_eq h p.1 hs]
      exact (hr.levelHeight_lt_iff h p.1 ⟨p.2, hs⟩ hp₁).mpr hp₂
    · simpa only [levelHeightReal, dite_eq_right hs] using hp₁

/-- Every totalized level point belongs to the closed epigraph. -/
theorem RigidityHypotheses.levelPoint_mem_closure (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (p : Space m × ℝ) :
    hr.levelPoint h p ∈ closure (epigraph g) :=
  point_mem_closure_epigraph (hr.graph_le_levelHeightReal h p.1 p.2)

/-- The zero level point is the corresponding graph point. -/
theorem RigidityHypotheses.levelPoint_zero (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : hr.levelPoint h (y, 0) = point y (g y) := by
  simp only [levelPoint, hr.levelHeightReal_zero h y]

/-- Level points converge jointly to the graph at level zero. -/
theorem RigidityHypotheses.levelPoint_continuousAt_zero (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : ContinuousAt (hr.levelPoint h) (y, 0) :=
  pointContinuousLinearMap.continuous.continuousAt.comp
    (continuous_fst.continuousAt.prodMk (hr.levelHeightReal_continuousAt_zero h y))

/-- The gradient field defined using the derivative within the closed epigraph. -/
@[expose] def RigidityHypotheses.closedLevelGradient (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (p : Space m × ℝ) : Space (m + 1) :=
  gradientWithin u (closure (epigraph g)) (hr.levelPoint h p)

/-- The closed gradient agrees with the interior foliation gradient at positive intermediate levels. -/
theorem RigidityHypotheses.closedLevelGradient_eq (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    hr.closedLevelGradient h p = hr.levelGradient h p := by
  simp only [closedLevelGradient, gradientWithin, levelGradient, gradient,
    fderivWithin_closure_eq_fderiv h.graph_contDiff.continuous (hr.levelPoint_mem h hs)]

/-- The closed gradient field is continuous at the zero level. -/
theorem RigidityHypotheses.closedLevelGradient_continuousAt_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    ContinuousAt (hr.closedLevelGradient h) (y, 0) := by
  have hd := h.solution_contDiffOn_closure.continuousOn_fderivWithin
    (uniqueDiffOn_closure_epigraph h.graph_contDiff.differentiable_one) le_rfl
  have hc : ContinuousOn (gradientWithin u (closure (epigraph g))) (closure (epigraph g)) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn hd
  exact (hc _ (hr.levelPoint_mem_closure h (y, 0))).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hr.levelPoint_continuousAt_zero h y,
      Filter.Eventually.of_forall (hr.levelPoint_mem_closure h)⟩)

/-- The interior foliation gradient has the boundary gradient as its zero-level trace. -/
theorem RigidityHypotheses.levelGradient_tendsto_boundary
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    Tendsto (hr.levelGradient h)
      (𝓝[{p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1}] (y, 0))
      (𝓝 (gradientWithin u (closure (epigraph g)) (point y (g y)))) := by
  have hc := (hr.closedLevelGradient_continuousAt_zero h y).continuousWithinAt
    (s := {p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1})
  have he : hr.levelGradient h =ᶠ[𝓝[{p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1}] (y, 0)]
      hr.closedLevelGradient h := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hr.closedLevelGradient_eq h hp).symm
  have ht := hc.tendsto.congr' he.symm
  simpa only [closedLevelGradient, hr.levelPoint_zero h y] using ht

/-- The zero-level vertical gradient has the value forced by the Neumann condition. -/
theorem RigidityHypotheses.closedLevelGradient_vertical_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    inner ℝ (hr.closedLevelGradient h (y, 0)) (verticalDirection m) =
      κ / Real.sqrt (1 + ‖gradient g y‖ ^ 2) := by
  change inner ℝ (gradientWithin u (closure (epigraph g)) (hr.levelPoint h (y, 0)))
    (verticalDirection m) = _
  rw [hr.levelPoint_zero h y, inner_gradientWithin_left]
  exact boundary_vertical_derivative_eq (h.graph_contDiff.differentiable_one y)
    (h.solution_contDiffOn_closure.differentiableOn_one _
      (point_mem_closure_epigraph (le_refl (g y)))) h.dirichlet (h.neumann y)

end SerrinEpigraph
