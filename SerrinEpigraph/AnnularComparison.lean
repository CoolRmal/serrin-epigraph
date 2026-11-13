module

public import SerrinEpigraph.AnnularRegularity
public import SerrinEpigraph.ComponentComparison
public import SerrinEpigraph.ExteriorBallGeometry

/-!
# Comparison with exterior annular solutions
-/

public section

open Set Metric MeasureTheory

namespace SerrinEpigraph

/-- An annular solution with outer value one bounds the original solution above when
its inner closed ball is strictly separated from the closed epigraph. -/
theorem IncreasingRadialSegment.solution_le_spatial_of_separation
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1) {c : Space (m + 1)}
    (hsep : ∀ x ∈ closure (epigraph g), a < dist x c) :
    ∀ x ∈ closure (epigraph g ∩ ball c b), u x ≤ v.spatial c x := by
  let D := epigraph g ∩ ball c b
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hclΩ : closure D ⊆ closure (epigraph g) := closure_mono inter_subset_left
  have hclB : closure D ⊆ closedBall c b :=
    closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  have hclA : closure D ⊆ closedRadialAnnulus c a b := by
    intro x hx
    exact ⟨by simpa only [dist_eq_norm] using (hsep x (hclΩ hx)).le,
      by simpa only [mem_closedBall, dist_eq_norm] using hclB hx⟩
  have hDA : D ⊆ radialAnnulus c a b := by
    intro x hx
    exact ⟨by simpa only [dist_eq_norm] using hsep x (subset_closure hx.1),
      by simpa only [mem_ball, dist_eq_norm] using hx.2⟩
  have hproper : D ≠ univ := by
    intro he
    have hx : point 0 (g 0) ∈ D := he ▸ mem_univ _
    simpa only [epigraph, mem_ofPred_eq, horizontal_point, last_point, lt_self_iff_false]
      using hx.1
  apply nonlinear_comparison_on_proper_open (μ := volume) (hΩ.inter isOpen_ball) hproper
    ((isCompact_closedBall c b).of_isClosed_subset isClosed_closure hclB)
    ((v.spatial_contDiffOn_two h.reaction_contDiffOn c).mono hDA)
    (h.solution_contDiffOn.mono inter_subset_left)
    ((v.spatial_continuousOn c).mono hclA)
    (h.solution_contDiffOn_closure.continuousOn.mono hclΩ)
    h.reaction_contDiffOn h.reaction_structure
    (fun x hx ↦ v.spatial_equation (hDA hx))
    (fun x hx ↦ h.equation x hx.1) ?_ (fun x hx ↦ (h.positive x hx.1).le) ?_
  · intro x hx
    by_cases he : ‖x - c‖ = b
    · simpa only [IncreasingRadialSegment.spatial, he, hb] using (zero_lt_one : (0 : ℝ) < 1)
    · exact v.spatial_pos ⟨by simpa only [dist_eq_norm] using hsep x (hclΩ hx),
        lt_of_le_of_ne (hclA hx).2 he⟩
  · intro x hx
    by_cases hxΩ : x ∈ epigraph g
    · have hout : b ≤ dist x c := not_lt.mp (fun hlt ↦ hx.2 ⟨hxΩ, hlt⟩)
      have hs : x ∈ sphere c b := le_antisymm (hclB hx.1) hout
      rw [v.spatial_outer_one hb hs]
      exact (hr.solution_lt_one x hxΩ).le
    · have hle : g (horizontal x) ≤ x (Fin.last m) := by
        simpa only [closure_epigraph h.graph_contDiff.continuous, mem_ofPred_eq]
          using hclΩ hx.1
      have he : g (horizontal x) = x (Fin.last m) := le_antisymm hle (not_lt.mp hxΩ)
      have hz : u x = 0 := by
        convert h.dirichlet (horizontal x) using 1
        rw [he, point_horizontal_last]
      rw [hz]
      exact (v.spatial_range (hclA hx.1)).1

/-- Moving an exterior ball downward makes its annular profile an upper comparison solution. -/
theorem IncreasingRadialSegment.solution_le_downward_spatial
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1) {c : Space (m + 1)}
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ) {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ closure (epigraph g ∩ ball (c - t • verticalDirection m) b),
      u x ≤ v.spatial (c - t • verticalDirection m) x :=
  v.solution_le_spatial_of_separation h hr hb (fun _ hx ↦
    dist_gt_radius_of_downward_exterior_ball h.graph_contDiff.continuous
      v.inner_pos hball ht hx)

end SerrinEpigraph
