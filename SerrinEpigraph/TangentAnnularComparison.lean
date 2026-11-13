module

public import SerrinEpigraph.AnnularComparison

/-!
# Annular comparison at an exterior tangent ball
-/

public section

open Set Filter Metric
open scoped Topology

namespace SerrinEpigraph

/-- The exterior annular comparison survives the limit of downward shifts, including
the boundary of the comparison domain. -/
theorem IncreasingRadialSegment.solution_le_spatial_of_exterior_ball
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1) {c : Space (m + 1)}
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ) :
    ∀ x ∈ closure (epigraph g ∩ ball c b), u x ≤ v.spatial c x := by
  have hclΩ : closure (epigraph g ∩ ball c b) ⊆ closure (epigraph g) :=
    closure_mono inter_subset_left
  have hclB : closure (epigraph g ∩ ball c b) ⊆ closedBall c b :=
    closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  have hdist : ∀ x ∈ closure (epigraph g), a ≤ dist x c := by
    intro x hx
    exact le_of_not_gt (fun hlt ↦ hball hlt hx)
  have hclA : closure (epigraph g ∩ ball c b) ⊆ closedRadialAnnulus c a b := by
    intro x hx
    exact ⟨by simpa only [dist_eq_norm] using hdist x (hclΩ hx),
      by simpa only [mem_closedBall, dist_eq_norm] using hclB hx⟩
  have hcomp : ∀ x ∈ epigraph g ∩ ball c b, u x ≤ v.spatial c x := by
    intro x hx
    let r : ℝ → ℝ := fun t ↦ ‖x - (c - t • verticalDirection m)‖
    have hc : ContinuousAt r 0 := by dsimp [r]; fun_prop
    have hr0 : r 0 = ‖x - c‖ := by simp [r]
    have hlim : Tendsto r (𝓝[>] 0) (𝓝 ‖x - c‖) := by
      simpa only [hr0] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), r t < b :=
      hlim.eventually (Iio_mem_nhds (by simpa only [mem_ball, dist_eq_norm] using hx.2))
    have hwithin : Tendsto r (𝓝[>] 0) (𝓝[Icc a b] ‖x - c‖) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hlim, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hlt] with t ht htb
      refine ⟨?_, htb.le⟩
      have hd := dist_gt_radius_of_downward_exterior_ball h.graph_contDiff.continuous
        v.inner_pos hball ht (subset_closure hx.1)
      simpa only [dist_eq_norm] using hd.le
    have hmem : ‖x - c‖ ∈ Icc a b :=
      hclA (subset_closure hx)
    have hvalue := (v.value_continuous _ hmem).tendsto.comp hwithin
    apply ge_of_tendsto hvalue
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht htb
    exact v.solution_le_downward_spatial h hr hb hball ht x
      (subset_closure ⟨hx.1, by simpa only [mem_ball, dist_eq_norm] using htb⟩)
  exact fun _ hx ↦ le_on_closure hcomp
    (h.solution_contDiffOn_closure.continuousOn.mono hclΩ)
    ((v.spatial_continuousOn c).mono hclA) hx

end SerrinEpigraph
