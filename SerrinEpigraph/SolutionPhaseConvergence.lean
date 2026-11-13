module

public import SerrinEpigraph.PhaseSetConvergence

/-!
# The rescaled solutions converge to the limiting phase indicator
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Convergence of positive-phase indicators transfers to the rescaled solutions. -/
theorem RigidityHypotheses.solution_limit_of_phaseIndicator_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0) := by
  let F := fun j x ↦ zeroExtension g u (R j • x)
  let P := fun j x ↦ positivePhaseIndicator (zeroExtension g u) (R j • x)
  let V := E.indicator (fun _ ↦ (1 : ℝ))
  have hcont (j : ℕ) : Continuous (F j) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
  have hF (j : ℕ) : IntegrableOn (F j) (closedBall 0 r) :=
    (hcont j).continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hP (j : ℕ) : IntegrableOn (P j) (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator
      (isOpen_lt (continuous_const (y := (0 : ℝ))) (hcont j)).measurableSet
  have hV : IntegrableOn V (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator hE
  have herr : Tendsto (fun j ↦ ∫ x in closedBall 0 r, ‖F j x - P j x‖)
      atTop (𝓝 0) := by
    simpa only [F, P, Real.norm_eq_abs, abs_sub_comm, phaseIndicatorError,
      Function.comp_def] using (hr.phaseIndicatorError_tendsto_zero h hradius).comp hR
  have hsum := herr.add ht
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro j
    exact integral_nonneg (fun x ↦ norm_nonneg _)
  · intro j
    exact integral_norm_sub_triangle (hF j) (hP j) hV

/-- The solutions and their positive-phase indicators share one local integral limit. -/
theorem RigidityHypotheses.solution_and_phaseIndicator_measurable_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      ∀ k : ℕ,
        Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          ‖positivePhaseIndicator (zeroExtension g u) (R (φ j) • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) ∧
        Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          ‖zeroExtension g u (R (φ j) • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, E, hE, ht⟩ := hr.phaseIndicator_measurable_phase_limit h R hR hRtop
  refine ⟨φ, hφ, E, hE, fun k ↦ ⟨ht k, ?_⟩⟩
  exact hr.solution_limit_of_phaseIndicator_limit h (fun j ↦ R (φ j))
    (hRtop.comp hφ.tendsto_atTop) (by positivity) hE (ht k)

end SerrinEpigraph
