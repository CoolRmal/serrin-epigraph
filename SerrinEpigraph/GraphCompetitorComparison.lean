module

public import SerrinEpigraph.RecoveryMinimality
public import SerrinEpigraph.GraphRecoverySubsequence

/-!
# Comparing the limiting phase with graph competitors
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- A smooth graph competitor agreeing with the limiting phase in an annulus
bounds that phase's interior perimeter by its graph area on a base neighborhood.
The recovery sequence uses the original scales, so the limiting phase is fixed. -/
theorem RigidityHypotheses.limiting_perimeter_le_graph_competitor_area
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {r t a : ℝ} (hradius : 0 < r) (ht : 0 < t) (har : a < r)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {b : Space m → ℝ} (hb : ContDiff ℝ 1 b)
    (hagree : ∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ epigraph b)
    {A D : Set (Space m)} (hA : IsCompact A) (hD : IsCompact D) (hDA : D ⊆ interior A)
    (hproj : ∀ x ∈ closedBall 0 (r + t), horizontal x ∈ D) :
    variationalPerimeter basis E (ball 0 a) ≤
      ENNReal.ofReal (∫ y in A, graphAreaDensity b y) := by
  obtain ⟨n, B, v, _, hnt, _, hRnt, hv, hval, hvlim, hbound, hBt⟩ :=
    hr.exists_graphRecovery_subsequence h R (fun j ↦ zero_lt_one.trans_le (hR j)) hRt
      hb hA hD hDA (isCompact_closedBall 0 (r + t)) hproj
  have he := hr.perimeter_le_recovery_bound_of_annular_agreement h basis hradius ht har
    (fun j ↦ hR (n j)) hRnt hv hval hE (isOpen_epigraph hb.continuous).measurableSet
    hagree (hUlim.comp hnt) hvlim hbound hBt
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  rw [mul_comm (∫ y in A, graphAreaDensity b y), ENNReal.ofReal_mul hc.le] at he
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp he

end SerrinEpigraph
