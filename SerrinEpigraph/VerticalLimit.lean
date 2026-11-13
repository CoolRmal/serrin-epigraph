module

public import SerrinEpigraph.Nonnegative
public import SerrinEpigraph.StrongMaximum
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Limits along vertical rays

Strict vertical monotonicity and boundedness give a positive finite limit on each ray.
No assertion that different rays have the same limit is assumed here.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Differentiating a vertical section recovers the vertical directional derivative. -/
theorem Hypotheses.vertical_section_hasDerivAt (h : Hypotheses g u f κ)
    (y : Space m) {t : ℝ} (ht : g y < t) :
    HasDerivAt (fun s ↦ u (point y s)) (verticalDerivative u (point y t)) t := by
  have hp : point y t ∈ epigraph g := by simpa [epigraph] using ht
  have hdw := h.solution_contDiffOn.differentiableOn (by norm_num) (point y t) hp
  have hd := hdw.differentiableAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hp)
  have hline : HasDerivAt (fun s : ℝ ↦ point y 0 + s • verticalDirection m)
      (verticalDirection m) t := by
    simpa using ((hasDerivAt_id t).smul_const (verticalDirection m)).const_add (point y 0)
  have hpoint : HasDerivAt (point y) (verticalDirection m) t := by
    simpa only [point_add_vertical, zero_add] using hline
  exact hd.hasFDerivAt.comp_hasDerivAt t hpoint

/-- Each vertical section is strictly increasing above the graph. -/
theorem Hypotheses.vertical_section_strictMonoOn (h : Hypotheses g u f κ)
    (y : Space m) : StrictMonoOn (fun t ↦ u (point y t)) (Set.Ioi (g y)) := by
  have hpos := h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg
  apply strictMonoOn_of_deriv_pos (convex_Ioi (g y))
  · intro t ht
    exact (h.vertical_section_hasDerivAt y ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : g y < t := by simpa using ht
    rw [(h.vertical_section_hasDerivAt y ht').deriv]
    exact hpos _ (by simpa [epigraph] using ht')

/-- Every vertical ray has a positive limit at most one. -/
theorem RigidityHypotheses.exists_vertical_limit (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) :
    ∃ L : ℝ, 0 < L ∧ L ≤ 1 ∧ Tendsto (fun t ↦ u (point y t)) atTop (𝓝 L) := by
  let v : ℝ → ℝ := fun t ↦ u (point y (max t (g y + 1)))
  have hint (t : ℝ) : g y < max t (g y + 1) :=
    (lt_add_one (g y)).trans_le (le_max_right _ _)
  have hmono : Monotone v := by
    intro s t hst
    exact (h.vertical_section_strictMonoOn y).monotoneOn (hint s) (hint t)
      (max_le_max_right _ hst)
  have hb : BddAbove (Set.range v) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (hr.solution_lt_one _ (by simp [epigraph])).le
  refine ⟨⨆ t, v t, ?_, ?_, ?_⟩
  · exact (h.positive (point y (max 0 (g y + 1)))
      (by simp [epigraph])).trans_le (le_ciSup hb 0)
  · exact ciSup_le (fun t ↦ (hr.solution_lt_one _ (by simp [epigraph])).le)
  · apply (tendsto_atTop_ciSup hmono hb).congr'
    filter_upwards [eventually_ge_atTop (g y + 1)] with t ht
    simp only [v, max_eq_left ht]

/-- Every finite interior value on a vertical ray is strictly below its limiting value. -/
theorem Hypotheses.vertical_section_lt_limit (h : Hypotheses g u f κ)
    (y : Space m) {L : ℝ} (hL : Tendsto (fun t ↦ u (point y t)) atTop (𝓝 L))
    {t : ℝ} (ht : g y < t) : u (point y t) < L := by
  have hmono := h.vertical_section_strictMonoOn y
  have hstep : u (point y t) < u (point y (t + 1)) :=
    hmono ht (ht.trans (lt_add_one t)) (lt_add_one t)
  have hle : u (point y (t + 1)) ≤ L := by
    apply ge_of_tendsto hL
    filter_upwards [eventually_ge_atTop (t + 1)] with s hs
    exact hmono.monotoneOn (ht.trans (lt_add_one t))
      ((ht.trans (lt_add_one t)).trans_le hs) hs
  exact hstep.trans_le hle

end SerrinEpigraph
