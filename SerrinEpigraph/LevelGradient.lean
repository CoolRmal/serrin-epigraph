module

public import SerrinEpigraph.LevelHeightSmooth
public import SerrinEpigraph.NormalizedPotential

/-!
# The gradient field associated with the vertical foliation
-/

public section

noncomputable section

open InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The point on a vertical ray where the specified solution level is attained. -/
@[expose] def RigidityHypotheses.levelPoint (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (p : Space m × ℝ) : Space (m + 1) :=
  point p.1 (hr.levelHeightReal h p.1 p.2)

/-- The foliation gradient, indexed by horizontal position and solution level. -/
@[expose] def RigidityHypotheses.levelGradient (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (p : Space m × ℝ) : Space (m + 1) :=
  gradient u (hr.levelPoint h p)

/-- Intermediate levels give points strictly inside the original domain. -/
theorem RigidityHypotheses.levelPoint_mem (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    hr.levelPoint h p ∈ epigraph g := by
  change point p.1 (hr.levelHeightReal h p.1 p.2) ∈ epigraph g
  rw [hr.levelHeightReal_eq h p.1 hs]
  simpa [epigraph] using (hr.levelHeight_spec h p.1 ⟨p.2, hs⟩).1

/-- The level point realizes its prescribed solution value. -/
theorem RigidityHypotheses.solution_levelPoint (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    u (hr.levelPoint h p) = p.2 := by
  change u (point p.1 (hr.levelHeightReal h p.1 p.2)) = p.2
  rw [hr.levelHeightReal_eq h p.1 hs]
  exact (hr.levelHeight_spec h p.1 ⟨p.2, hs⟩).2

/-- The level point depends twice continuously differentiably on its parameters. -/
theorem RigidityHypotheses.levelPoint_contDiffAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (hr.levelPoint h) p :=
  pointContinuousLinearMap.contDiff.contDiffAt.comp p
    (contDiffAt_fst.prodMk (hr.levelHeightReal_contDiffAt h hs))

/-- The foliation gradient is jointly continuously differentiable. -/
theorem RigidityHypotheses.levelGradient_contDiffAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (hr.levelGradient h) p := by
  have hd := h.solution_contDiffOn.fderiv_of_isOpen
    (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num)
  have hc := hd.contDiffAt ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds
    (hr.levelPoint_mem h hs))
  have hcomp := hc.comp p ((hr.levelPoint_contDiffAt h hs).of_le (by norm_num))
  exact (toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp p hcomp

/-- Evaluating the level point at the original solution recovers the original point. -/
theorem RigidityHypotheses.levelPoint_solution (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    hr.levelPoint h (horizontal x, u x) = x := by
  have hs : u x ∈ Set.Ioo (0 : ℝ) 1 := ⟨h.positive x hx, hr.solution_lt_one x hx⟩
  change point (horizontal x) (hr.levelHeightReal h (horizontal x) (u x)) = x
  rw [hr.levelHeightReal_eq h (horizontal x) hs, hr.levelHeight_solution h hx]
  exact point_horizontal_last x

/-- The foliation gradient agrees with the solution gradient on its graph. -/
theorem RigidityHypotheses.levelGradient_solution (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    hr.levelGradient h (horizontal x, u x) = gradient u x := by
  simp only [levelGradient, hr.levelPoint_solution h hx]

/-- The vertical component of the foliation gradient is strictly positive. -/
theorem RigidityHypotheses.levelGradient_vertical_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    0 < inner ℝ (hr.levelGradient h p) (verticalDirection m) := by
  change 0 < inner ℝ (gradient u (hr.levelPoint h p)) (verticalDirection m)
  rw [inner_gradient_left]
  exact h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg _ (hr.levelPoint_mem h hs)

/-- The affine energy expression determined by a leaf lies below the energy density. -/
theorem RigidityHypotheses.levelGradient_energy_bound (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (p : Space m × ℝ) (v : Space (m + 1)) :
    inner ℝ (hr.levelGradient h p) v - ‖hr.levelGradient h p‖ ^ 2 / 2 +
        normalizedPotential f p.2 ≤ ‖v‖ ^ 2 / 2 + normalizedPotential f p.2 := by
  have hn := sq_nonneg ‖hr.levelGradient h p - v‖
  rw [norm_sub_sq_real] at hn
  linarith

/-- On the solution graph the affine energy bound is attained. -/
theorem RigidityHypotheses.levelGradient_energy_eq (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    inner ℝ (hr.levelGradient h (horizontal x, u x)) (gradient u x) -
        ‖hr.levelGradient h (horizontal x, u x)‖ ^ 2 / 2 + normalizedPotential f (u x) =
      ‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x) := by
  rw [hr.levelGradient_solution h hx, real_inner_self_eq_norm_sq]
  ring

/-- The differential of the level point follows the inverse height differential. -/
theorem RigidityHypotheses.levelPoint_fderiv_apply (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (q : Space m × ℝ) :
    fderiv ℝ (hr.levelPoint h) p q = point q.1
      ((q.2 - fderiv ℝ u (hr.levelPoint h p) (point q.1 0)) /
        verticalDerivative u (hr.levelPoint h p)) := by
  have hd := ((hr.levelHeightReal_contDiffAt h hs).differentiableAt
    (by norm_num)).hasFDerivAt
  have hp := pointContinuousLinearMap.hasFDerivAt.comp p (hasFDerivAt_fst.prodMk hd)
  have he := congrArg (fun L : (Space m × ℝ) →L[ℝ] Space (m + 1) ↦ L q) hp.fderiv
  change fderiv ℝ (hr.levelPoint h) p q = point q.1
    (fderiv ℝ (fun r : Space m × ℝ ↦ hr.levelHeightReal h r.1 r.2) p q) at he
  rw [hr.levelHeightReal_fderiv_apply h hs q] at he
  exact he

/-- The foliation gradient differential is the Hessian applied to the lifted variation. -/
theorem RigidityHypotheses.levelGradient_fderiv_apply (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (q : Space m × ℝ) :
    fderiv ℝ (hr.levelGradient h) p q =
      fderiv ℝ (gradient u) (hr.levelPoint h p) (point q.1
        ((q.2 - fderiv ℝ u (hr.levelPoint h p) (point q.1 0)) /
          verticalDerivative u (hr.levelPoint h p))) := by
  have hd := h.solution_contDiffOn.fderiv_of_isOpen
    (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num)
  have hc := hd.contDiffAt ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds
    (hr.levelPoint_mem h hs))
  have hg : ContDiffAt ℝ 1 (gradient u) (hr.levelPoint h p) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp _ hc
  have hchain := (hg.differentiableAt (by norm_num)).hasFDerivAt.comp p
    (((hr.levelPoint_contDiffAt h hs).differentiableAt (by norm_num)).hasFDerivAt)
  have he := congrArg (fun L : (Space m × ℝ) →L[ℝ] Space (m + 1) ↦ L q) hchain.fderiv
  change fderiv ℝ (hr.levelGradient h) p q =
    fderiv ℝ (gradient u) (hr.levelPoint h p) (fderiv ℝ (hr.levelPoint h) p q) at he
  rw [hr.levelPoint_fderiv_apply h hs q] at he
  exact he

end SerrinEpigraph
