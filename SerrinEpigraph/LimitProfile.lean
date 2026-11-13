module

public import SerrinEpigraph.TranslatedDomain
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# The measurable horizontal limit profile

The profile is selected from the proved ray limits. It is approximated by continuous
sections at integer distances above the graph. Constancy is not assumed.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The limit of the solution along the vertical ray above a horizontal point. -/
@[expose] def RigidityHypotheses.verticalLimitProfile (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : ℝ :=
  (hr.exists_vertical_limit h y).choose

/-- The selected profile retains positivity, the upper bound, and the actual ray limit. -/
theorem RigidityHypotheses.verticalLimitProfile_spec (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) :
    0 < hr.verticalLimitProfile h y ∧ hr.verticalLimitProfile h y ≤ 1 ∧
      Tendsto (fun t ↦ u (point y t)) atTop (𝓝 (hr.verticalLimitProfile h y)) :=
  (hr.exists_vertical_limit h y).choose_spec

/-- A section at any fixed positive distance above the graph is continuous. -/
theorem Hypotheses.continuous_graph_section (h : Hypotheses g u f κ)
    {a : ℝ} (ha : 0 < a) : Continuous (fun y ↦ u (point y (g y + a))) := by
  have hp : Continuous (fun y ↦ point y (g y + a)) :=
    pointContinuousLinearMap.continuous.comp
      (continuous_id.prodMk (h.graph_contDiff.continuous.add continuous_const))
  exact h.solution_contDiffOn.continuousOn.comp_continuous hp
    (fun y ↦ by simpa [epigraph] using lt_add_of_pos_right (g y) ha)

/-- Sections at increasing integer distances converge pointwise to the profile. -/
theorem RigidityHypotheses.graph_sections_tendsto (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) :
    Tendsto (fun n : ℕ ↦ u (point y (g y + (n : ℝ) + 1))) atTop
      (𝓝 (hr.verticalLimitProfile h y)) := by
  apply (hr.verticalLimitProfile_spec h y).2.2.comp
  exact tendsto_atTop_add_const_right _ 1
    (tendsto_atTop_add_const_left _ (g y) tendsto_natCast_atTop_atTop)

/-- The horizontal limit profile is measurable as a pointwise limit of continuous sections. -/
theorem RigidityHypotheses.verticalLimitProfile_measurable (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) : Measurable (hr.verticalLimitProfile h) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n : ℕ ↦ fun y ↦ u (point y (g y + (n : ℝ) + 1)))
  · intro n
    have hc := h.continuous_graph_section (a := (n : ℝ) + 1) (by positivity)
    simpa only [add_assoc] using hc.measurable
  · exact tendsto_pi_nhds.mpr (hr.graph_sections_tendsto h)

/-- The original solution lies strictly below the horizontal limit profile. -/
theorem RigidityHypotheses.solution_lt_verticalLimitProfile
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    u x < hr.verticalLimitProfile h (horizontal x) := by
  have hb := h.vertical_section_lt_limit (horizontal x)
    (hr.verticalLimitProfile_spec h (horizontal x)).2.2 hx
  simpa only [point_horizontal_last] using hb

/-- Upward translations at any ambient point converge to the profile at its horizontal coordinate. -/
theorem RigidityHypotheses.vertical_translates_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    Tendsto (fun t : ℝ ↦ u (x + t • verticalDirection m)) atTop
      (𝓝 (hr.verticalLimitProfile h (horizontal x))) := by
  have ht : Tendsto (fun t : ℝ ↦ x (Fin.last m) + t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  simpa only [add_vertical_eq_point, Function.comp_def] using
    (hr.verticalLimitProfile_spec h (horizontal x)).2.2.comp ht

/-- The nonlinear reaction also converges under upward translation. -/
theorem RigidityHypotheses.reaction_vertical_translates_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    Tendsto (fun t : ℝ ↦ f (u (x + t • verticalDirection m))) atTop
      (𝓝 (f (hr.verticalLimitProfile h (horizontal x)))) := by
  have hpos := (hr.verticalLimitProfile_spec h (horizontal x)).1
  have hc : ContinuousAt f (hr.verticalLimitProfile h (horizontal x)) :=
    h.reaction_contDiffOn.continuousOn.continuousAt (Ici_mem_nhds hpos)
  exact hc.tendsto.comp (hr.vertical_translates_tendsto h x)

end SerrinEpigraph
