module

public import SerrinEpigraph.AnnularTransitionCost
public import SerrinEpigraph.GluingMismatchConvergence

/-!
# Annular gluing with vanishing energy error
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Bounded-energy inputs with a common limit only on the annulus can be glued
with an error tending to zero; their limits inside the inner ball may differ. -/
theorem RigidityHypotheses.exists_annular_gluing_sequence
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v : ℕ → Space d → ℝ} {z : Space d → ℝ}
    (hU : ∀ j, LocallyLipschitz (U j)) (hv : ∀ j, LocallyLipschitz (v j))
    (hUval : ∀ j x, U j x ∈ Icc (0 : ℝ) 1)
    (hvval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {r t B : ℝ} (hradius : 0 < r) (ht : 0 < t)
    (hz : IntegrableOn z (closedBall 0 (r + t) \ ball 0 r))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    (hEB : ∀ j,
      (∫ x in closedBall 0 (r + t) \ ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in closedBall 0 (r + t) \ ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B)
    (hUz : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t) \ ball 0 r,
      ‖U j x - z x‖) atTop (𝓝 0))
    (hvz : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t) \ ball 0 r,
      ‖v j x - z x‖) atTop (𝓝 0)) :
    ∃ (η : ℕ → Space d → ℝ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) ∧
      ∀ j, ContDiff ℝ 1 (η j) ∧ HasCompactSupport (η j) ∧
        tsupport (η j) ⊆ ball 0 (r + t) ∧
        (∀ x ∈ ball 0 r, η j x = 1) ∧
        (∀ x, η j x ∈ Icc (0 : ℝ) 1) ∧
        (∫ x in closedBall 0 (r + t),
          rescaledPhaseEnergyDensity f (R j) (gluedCompetitor (U j) (v j) (η j)) x) ≤
          (∫ x in closedBall 0 (r + t),
            (1 - η j x) * rescaledPhaseEnergyDensity f (R j) (U j) x +
            η j x * rescaledPhaseEnergyDensity f (R j) (v j) x) + ε j := by
  obtain ⟨C, _, hc⟩ := hr.exists_annular_glued_energy_comparison h
  have hRpos : ∀ j, 0 < R j := fun j ↦ lt_of_lt_of_le zero_lt_one (hR j)
  have hN : ∀ j, 0 < ⌈R j⌉₊ := fun j ↦ Nat.one_le_ceil_iff.mpr (hRpos j)
  have hex := fun j ↦ hc d ⌈R j⌉₊ r t (R j) (hN j) hradius ht (hRpos j)
    (U j) (v j) (hU j) (hv j) (hUval j) (hvval j)
  choose η hη using hex
  let ε : ℕ → ℝ := fun j ↦
    (∫ x in closedBall 0 (r + t) \ ball 0 r,
      gluingCost f (R j) (C * (⌈R j⌉₊ : ℝ) / t) (U j) (v j) x) / ⌈R j⌉₊
  have he : Tendsto ε atTop (𝓝 0) :=
    hr.gluingCost_average_tendsto_zero_of_common_limit h hU hv hUval hvval
      ((isCompact_closedBall 0 (r + t)).diff isOpen_ball) hz ht hR hRtop hEB hUz hvz
  refine ⟨η, ε, he, fun j ↦ ?_⟩
  obtain ⟨hd, hcompact, hs, hone, hval, _, henergy⟩ := hη j
  exact ⟨hd, hcompact, hs, hone, hval, henergy⟩

end SerrinEpigraph
