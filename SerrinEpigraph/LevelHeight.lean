module

public import SerrinEpigraph.LimitOne
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The unique height of each intermediate solution level

Vertical monotonicity, the zero boundary value, and the limit one parameterize
each vertical ray by the solution values in the open unit interval.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Every value strictly between zero and one is attained exactly once on each vertical ray. -/
theorem RigidityHypotheses.existsUnique_level_height (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ∃! t : ℝ, g y < t ∧ u (point y t) = s := by
  have he : ∀ᶠ t : ℝ in atTop, s < u (point y t) :=
    (hr.vertical_section_tendsto_one h y).eventually (eventually_gt_nhds hs.2)
  obtain ⟨b, hb, hsb⟩ := ((eventually_gt_atTop (g y)).and he).exists
  have hc : ContinuousOn (fun t ↦ u (point y t)) (Set.Icc (g y) b) :=
    h.solution_contDiffOn_closure.continuousOn.comp (continuous_point y).continuousOn
      (fun t ht ↦ point_mem_closure_epigraph ht.1)
  have hsrange : s ∈ Set.Icc (u (point y (g y))) (u (point y b)) := by
    rw [h.dirichlet y]
    exact ⟨hs.1.le, hsb.le⟩
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc hb.le hc hsrange
  change u (point y t) = s at hts
  have hgt : g y < t := by
    rcases lt_or_eq_of_le ht.1 with hlt | heq
    · exact hlt
    · rw [← heq, h.dirichlet y] at hts
      linarith [hs.1]
  refine ⟨t, ⟨hgt, hts⟩, ?_⟩
  intro r hr
  exact (h.vertical_section_strictMonoOn y).injOn hr.1 hgt (hr.2.trans hts.symm)

/-- The height of a given intermediate level above a horizontal point. -/
@[expose] def RigidityHypotheses.levelHeight (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : Set.Ioo (0 : ℝ) 1) : ℝ :=
  (hr.existsUnique_level_height h y s.property).exists.choose

/-- The selected height is interior and realizes its specified solution level. -/
theorem RigidityHypotheses.levelHeight_spec (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : Set.Ioo (0 : ℝ) 1) :
    g y < hr.levelHeight h y s ∧ u (point y (hr.levelHeight h y s)) = s :=
  (hr.existsUnique_level_height h y s.property).exists.choose_spec

/-- Heights increase strictly with the prescribed solution value. -/
theorem RigidityHypotheses.levelHeight_strictMono (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : StrictMono (hr.levelHeight h y) := by
  intro s r hsr
  have hs := hr.levelHeight_spec h y s
  have hr' := hr.levelHeight_spec h y r
  by_contra hn
  have hb := (h.vertical_section_strictMonoOn y).monotoneOn hr'.1 hs.1 (le_of_not_gt hn)
  rw [hs.2, hr'.2] at hb
  exact (not_le_of_gt hsr) hb

/-- The height parameterization recovers the height of every original interior point. -/
theorem RigidityHypotheses.levelHeight_solution (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    hr.levelHeight h (horizontal x) ⟨u x, h.positive x hx, hr.solution_lt_one x hx⟩ =
      x (Fin.last m) := by
  apply (h.vertical_section_strictMonoOn (horizontal x)).injOn
    (hr.levelHeight_spec h _ _).1 hx
  simpa only [point_horizontal_last] using (hr.levelHeight_spec h (horizontal x)
    ⟨u x, h.positive x hx, hr.solution_lt_one x hx⟩).2

/-- At a fixed horizontal point, the inverse level parameterization is continuous. -/
theorem RigidityHypotheses.levelHeight_continuous (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : Continuous (hr.levelHeight h y) := by
  let H : Set.Ioo (0 : ℝ) 1 → Set.Ioi (g y) :=
    fun s ↦ ⟨hr.levelHeight h y s, (hr.levelHeight_spec h y s).1⟩
  have hmono : Monotone H := (hr.levelHeight_strictMono h y).monotone
  have hsurj : Function.Surjective H := by
    intro t
    have hx : point y t ∈ epigraph g := by
      simpa only [epigraph, Set.mem_ofPred_eq, Set.mem_Ioi, horizontal_point, last_point] using t.property
    refine ⟨⟨u (point y t), h.positive _ hx, hr.solution_lt_one _ hx⟩, ?_⟩
    apply Subtype.ext
    have heq := hr.levelHeight_solution h hx
    simpa only [horizontal_point, last_point] using heq
  exact continuous_subtype_val.comp (hmono.continuous_of_surjective hsurj)

end SerrinEpigraph
