module

public import SerrinEpigraph.BallLowerBound
public import SerrinEpigraph.LimitProfile

/-!
# Identification of every vertical limit with the stable equilibrium
-/

public section

noncomputable section

open Filter Metric
open scoped Topology

namespace SerrinEpigraph

/-- The inverse-square comparison coefficient is smaller than any positive coefficient
for a sufficiently large radius. -/
theorem exists_radius_coefficient_lt (D c : ℝ) (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ D / R ^ 2 < c := by
  obtain ⟨R, hR⟩ := exists_gt (max 1 (D / c))
  have hRone : 1 < R := (le_max_left _ _).trans_lt hR
  have hRpos : 0 < R := zero_lt_one.trans hRone
  have hDc : D < R * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hR)
  refine ⟨R, hRpos, (div_lt_iff₀ (sq_pos_of_pos hRpos)).mpr ?_⟩
  have hsq : R < R ^ 2 := by nlinarith
  have := mul_lt_mul_of_pos_right hsq hc
  nlinarith

/-- Under the normalized reaction and bounded-solution conditions, every vertical ray limit
is exactly the equilibrium one. -/
theorem RigidityHypotheses.verticalLimitProfile_eq_one {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    hr.verticalLimitProfile h y = 1 := by
  have hspec := hr.verticalLimitProfile_spec h y
  apply le_antisymm hspec.2.1
  by_contra hnot
  have hLlt : hr.verticalLimitProfile h y < 1 := lt_of_not_ge hnot
  let a := (hr.verticalLimitProfile h y + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hspec.1]
  have haone : a < 1 := by dsimp [a]; linarith
  have hLa : hr.verticalLimitProfile h y < a := by dsimp [a]; linarith
  have hc : 0 < f a / a := div_pos (hr.reaction_pos a ⟨ha, haone⟩) ha
  obtain ⟨R, hR, hgap⟩ := exists_radius_coefficient_lt
    (((Module.finrank ℝ (Space (m + 1)) : ℝ) + 2) ^ 2) (f a / a) hc
  let z := point y 0
  obtain ⟨T, hT⟩ := compact_eventually_in_epigraph h.graph_contDiff.continuous
    (isCompact_closedBall z R)
  have hbound (t : ℝ) (ht : T ≤ t) : a ≤ u (z + t • verticalDirection m) := by
    apply h.solution_ge_at_ball_center hR ha _ hgap
    intro x hx
    have hdist : dist (x - t • verticalDirection m) z = dist x (z + t • verticalDirection m) := by
      simp only [dist_eq_norm]
      congr 1
      abel
    have hmem : x - t • verticalDirection m ∈ closedBall z R := by
      simpa only [mem_closedBall, hdist] using hx
    simpa only [sub_add_cancel] using hT t ht (x - t • verticalDirection m) hmem
  have hlim : Tendsto (fun t : ℝ ↦ u (z + t • verticalDirection m)) atTop
      (𝓝 (hr.verticalLimitProfile h y)) := by
    simpa only [z, horizontal_point] using hr.vertical_translates_tendsto h z
  have hle : a ≤ hr.verticalLimitProfile h y := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop T] with t ht
    exact hbound t ht
  exact (not_le_of_gt hLa) hle

/-- The original solution converges to one along every vertical ray. -/
theorem RigidityHypotheses.vertical_section_tendsto_one {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    Tendsto (fun t ↦ u (point y t)) atTop (𝓝 1) := by
  simpa only [hr.verticalLimitProfile_eq_one h y] using (hr.verticalLimitProfile_spec h y).2.2

end SerrinEpigraph
