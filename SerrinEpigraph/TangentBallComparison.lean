module

public import SerrinEpigraph.CompactComparison
public import SerrinEpigraph.TranslatedDomain

/-!
# Comparison on balls touching the epigraph boundary
-/

public section

open Set Filter Metric
open scoped Topology

namespace SerrinEpigraph

/-- A positive upward displacement moves every point of the closed epigraph into its interior. -/
theorem upward_mem_epigraph_of_mem_closure {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {x : Space (m + 1)} (hx : x ∈ closure (epigraph g))
    {t : ℝ} (ht : 0 < t) : x + t • verticalDirection m ∈ epigraph g := by
  rw [closure_epigraph hg] at hx
  rw [add_vertical_eq_point]
  simp only [epigraph, mem_ofPred_eq, horizontal_point, last_point] at hx ⊢
  linarith

/-- The closed ball moves strictly inside the epigraph under every positive upward shift. -/
theorem upward_closedBall_subset_epigraph {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {c : Space (m + 1)} {R : ℝ}
    (hball : closedBall c R ⊆ closure (epigraph g)) {t : ℝ} (ht : 0 < t) :
    closedBall (c + t • verticalDirection m) R ⊆ epigraph g := by
  intro x hx
  have hx' : x - t • verticalDirection m ∈ closedBall c R := by
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    convert hx using 1
    congr 1
    abel
  have he := upward_mem_epigraph_of_mem_closure hg (hball hx') ht
  simpa only [sub_add_cancel] using he

/-- Ball comparison remains valid when the closed ball touches the epigraph boundary. -/
theorem RadialBallProfile.spatial_le_solution_of_closedBall_subset_closure
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R : ℝ}
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) {c : Space (m + 1)}
    (hball : closedBall c R ⊆ closure (epigraph g)) :
    ∀ x ∈ closedBall c R, v.spatial c x ≤ u x := by
  intro x hx
  have hshift : ∀ t : ℝ, 0 < t → v.spatial c x ≤ u (x + t • verticalDirection m) := by
    intro t ht
    have hsub := upward_closedBall_subset_epigraph h.graph_contDiff.continuous hball ht
    have hmem : x + t • verticalDirection m ∈ closedBall (c + t • verticalDirection m) R := by
      simpa only [mem_closedBall, dist_add_right] using hx
    have hcomp := v.spatial_le_solution h hr hsub _ hmem
    simpa only [RadialBallProfile.spatial, add_sub_add_right_eq_sub] using hcomp
  have hpath : Tendsto (fun t : ℝ ↦ x + t • verticalDirection m) (𝓝[>] 0) (𝓝 x) := by
    have hc : ContinuousAt (fun t : ℝ ↦ x + t • verticalDirection m) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hwithin : Tendsto (fun t : ℝ ↦ x + t • verticalDirection m) (𝓝[>] 0)
      (𝓝[closure (epigraph g)] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hpath, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact subset_closure
      (upward_mem_epigraph_of_mem_closure h.graph_contDiff.continuous (hball hx) ht)
  have hlim := (h.solution_contDiffOn_closure.continuousOn x (hball hx)).tendsto.comp hwithin
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hshift t ht

end SerrinEpigraph
