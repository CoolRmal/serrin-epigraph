module

public import SerrinEpigraph.LevelHeightContinuity
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Differentiating the inverse level height
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Extend the inverse height outside the open unit interval by the boundary height. -/
@[expose] def RigidityHypotheses.levelHeightReal (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo (0 : ℝ) 1 then hr.levelHeight h y ⟨s, hs⟩ else g y

/-- On the open unit interval the real extension is the inverse height. -/
theorem RigidityHypotheses.levelHeightReal_eq (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    hr.levelHeightReal h y s = hr.levelHeight h y ⟨s, hs⟩ := by
  simp [levelHeightReal, hs]

/-- The extended inverse height is continuous at every intermediate level. -/
theorem RigidityHypotheses.levelHeightReal_continuousAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (hr.levelHeightReal h y) s := by
  have hc : ContinuousOn (hr.levelHeightReal h y) (Set.Ioo (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun r : Set.Ioo (0 : ℝ) 1 ↦ hr.levelHeightReal h y r)
    have he : (fun r : Set.Ioo (0 : ℝ) 1 ↦ hr.levelHeightReal h y r) =
        hr.levelHeight h y := by
      funext r
      exact hr.levelHeightReal_eq h y r.property
    rw [he]
    exact hr.levelHeight_continuous h y
  exact hc.continuousAt (isOpen_Ioo.mem_nhds hs)

/-- The level derivative of inverse height is the reciprocal vertical derivative of the solution. -/
theorem RigidityHypotheses.levelHeightReal_hasDerivAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (hr.levelHeightReal h y)
      (verticalDerivative u (point y (hr.levelHeightReal h y s)))⁻¹ s := by
  have ht : g y < hr.levelHeightReal h y s := by
    rw [hr.levelHeightReal_eq h y hs]
    exact (hr.levelHeight_spec h y ⟨s, hs⟩).1
  have hx : point y (hr.levelHeightReal h y s) ∈ epigraph g := by
    simpa [epigraph] using ht
  have hp := h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg _ hx
  apply (h.vertical_section_hasDerivAt y ht).of_local_left_inverse
    (hr.levelHeightReal_continuousAt h y hs) (ne_of_gt hp)
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr'
  rw [hr.levelHeightReal_eq h y hr']
  exact (hr.levelHeight_spec h y ⟨r, hr'⟩).2

/-- The inverse height has a strictly positive derivative with respect to the level. -/
theorem RigidityHypotheses.levelHeightReal_deriv_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    0 < deriv (hr.levelHeightReal h y) s := by
  rw [(hr.levelHeightReal_hasDerivAt h y hs).deriv]
  apply inv_pos.mpr
  apply h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg
  rw [hr.levelHeightReal_eq h y hs]
  simpa [epigraph] using (hr.levelHeight_spec h y ⟨s, hs⟩).1

end SerrinEpigraph
