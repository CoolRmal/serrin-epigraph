module

public import SerrinEpigraph.GraphCompetitorComparison
public import SerrinEpigraph.SolutionPhaseConvergence

/-!
# Existence of a limiting phase with graph comparison bounds
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The PDE hypotheses produce a single phase limit on every compact set and
comparison bounds against every C1 graph agreeing with it in an annulus. -/
theorem RigidityHypotheses.exists_limiting_phase_with_graph_comparison
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R (φ j) • x) -
          E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
      ∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
        (r t a : ℝ), 0 < r → 0 < t → a < r →
        ∀ b : Space m → ℝ, ContDiff ℝ 1 b →
        (∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ epigraph b) →
        ∀ A D : Set (Space m), IsCompact A → IsCompact D → D ⊆ interior A →
        (∀ x ∈ closedBall 0 (r + t), horizontal x ∈ D) →
        variationalPerimeter basis E (ball 0 a) ≤
          ENNReal.ofReal (∫ y in A, graphAreaDensity b y) := by
  obtain ⟨φ, hφ, E, hE, hlim⟩ :=
    hr.solution_and_phaseIndicator_measurable_limit h R hR hRt
  have hlocal (K : Set (Space (m + 1))) (hK : IsCompact K) :
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R (φ j) • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    obtain ⟨s, hs⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
    obtain ⟨k, hk⟩ := exists_nat_gt s
    have hsub : K ⊆ closedBall 0 (k + 1 : ℝ) := hs.trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ)))
        (closedBall 0 (k + 1 : ℝ)) :=
      (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).indicator hE
    apply integral_norm_sub_tendsto_of_subset hsub _ (hlim k).2
    intro j
    have hc := h.zeroExtension_continuous.comp (continuous_id.const_smul (R (φ j)))
    exact ((hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).sub hiE).norm
  refine ⟨φ, hφ, E, hE, hlocal, ?_⟩
  intro basis r t a hradius ht har b hb hagree A D hA hD hDA hproj
  exact hr.limiting_perimeter_le_graph_competitor_area h basis hradius ht har
    (fun j ↦ hR (φ j)) (hRt.comp hφ.tendsto_atTop) hE
    (hlocal _ (isCompact_closedBall _ _)) hb hagree hA hD hDA hproj

end SerrinEpigraph
