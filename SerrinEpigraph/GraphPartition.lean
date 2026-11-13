module

public import SerrinEpigraph.FiniteGraphCover
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth weights for finite graph covers
-/

public section

open Set Metric
open scoped Manifold Topology ContDiff

namespace SerrinEpigraph

/-- A finite ball cover of a compact base admits compactly supported smooth weights,
with total weight one on the base and at most one everywhere. -/
theorem exists_smooth_graphPartition {d : ℕ} {B : Set (Space d)} (hB : IsCompact B)
    (s : Finset (Space d)) (r : Space d → ℝ)
    (hcover : B ⊆ ⋃ y ∈ s, ball y (r y / 2)) :
    ∃ η : s → Space d → ℝ,
      (∀ i, ContDiff ℝ ∞ (η i)) ∧
      (∀ i, HasCompactSupport (η i)) ∧
      (∀ i, tsupport (η i) ⊆ ball (i : Space d) (r i / 2)) ∧
      (∀ i x, 0 ≤ η i x) ∧
      (∀ x ∈ B, ∑ i, η i x = 1) ∧
      (∀ x, ∑ i, η i x ≤ 1) := by
  classical
  have hc : B ⊆ ⋃ i : s, ball (i : Space d) (r i / 2) := by
    simpa only [iUnion_subtype] using hcover
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, Space d)) hB.isClosed (fun i : s ↦ ball (i : Space d) (r i / 2))
    (fun _ ↦ isOpen_ball) hc
  refine ⟨fun i ↦ p i, fun i ↦ (p i).contMDiff.contDiff, ?_, hp, p.nonneg, ?_, ?_⟩
  · intro i
    exact (isCompact_closedBall (i : Space d) (r i / 2)).of_isClosed_subset
      (isClosed_tsupport _) ((hp i).trans ball_subset_closedBall)
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hx
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using p.sum_le_one x

end SerrinEpigraph
