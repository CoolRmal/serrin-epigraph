module

public import SerrinEpigraph.GraphAreaDensity

/-!
# Finite graph covers with local area recovery bounds
-/

public section

open Set Metric MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- A compact base admits finitely many buffered graph patches whose recovery coefficients
are within an arbitrary area-density error. -/
theorem RigidityHypotheses.exists_finite_graphRecovery_cover
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {B : Set (Space d)} (hB : IsCompact B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (Space d)) (r L : Space d → ℝ),
      (∀ y ∈ s, y ∈ B ∧ 0 < r y ∧ 0 < L y) ∧
      B ⊆ ⋃ y ∈ s, ball y (r y / 2) ∧
      ∀ y ∈ s, ∀ (δ R : ℝ), 0 < δ → 0 < R →
        ∀ (A : Set (Space d)), IsCompact A → A ⊆ closedBall y (r y / 2) →
        ∀ (K : Set (Space (d + 1))), IsCompact K → (∀ x ∈ K, horizontal x ∈ A) →
        (∫ x in K, rescaledPhaseEnergyDensity f R
          (geometricRecoveryProfile f δ R (fun z ↦ graphHeight b z / L y)) x) ≤
          ((∫ z in A, graphAreaDensity b z) + ε * (volume A).toReal) *
            recoveryActionPrimitive f δ 1 := by
  classical
  choose r L hrpos hL hbound using
    (fun y : Space d ↦ hr.exists_local_graphRecovery_area_bound h hb y hε)
  have hcover : B ⊆ ⋃ y ∈ B, ball y (r y / 2) := by
    intro y hy
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, mem_ball_self (by linarith [hrpos y])⟩⟩
  obtain ⟨s, hsB, hsfin, hscover⟩ := hB.elim_finite_subcover_image
    (fun y (_ : y ∈ B) ↦ isOpen_ball) hcover
  refine ⟨hsfin.toFinset, r, L,
    fun y hy ↦ ⟨hsB (hsfin.mem_toFinset.mp hy), hrpos y, hL y⟩, ?_, ?_⟩
  · simpa only [hsfin.mem_toFinset] using hscover
  intro y hy δ R hδ hR A hA hsub K hK hproj
  apply hbound y δ R hδ hR A hA _ K hK hproj
  exact hsub.trans (closedBall_subset_ball (by linarith [hrpos y]))

end SerrinEpigraph
