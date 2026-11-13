module

public import SerrinEpigraph.GlobalPhaseSet
public import SerrinEpigraph.EpigraphRescaling

/-!
# Local integral convergence of the phase indicators
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Primitive convergence to a weighted phase implies convergence of the phase indicators. -/
theorem RigidityHypotheses.phaseIndicator_limit_of_primitive_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖phasePrimitive f (zeroExtension g u (R j • x)) -
        E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  let c := phasePrimitive f 1
  let F := fun j x ↦ phasePrimitive f (zeroExtension g u (R j • x))
  let P := fun j x ↦ c * positivePhaseIndicator (zeroExtension g u) (R j • x)
  let V := E.indicator (fun _ ↦ c)
  have hF (j : ℕ) : IntegrableOn (F j) (closedBall 0 r) :=
    ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R j))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 r)
  have hP (j : ℕ) : IntegrableOn (P j) (closedBall 0 r) := by
    have hc := h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
    have hi : IntegrableOn
        ({x | 0 < zeroExtension g u (R j • x)}.indicator (fun _ ↦ (1 : ℝ)))
        (closedBall 0 r) :=
      (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator
        (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
    exact hi.const_mul c
  have hV : IntegrableOn V (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator hE
  have herr : Tendsto (fun j ↦ ∫ x in closedBall 0 r, ‖P j x - F j x‖)
      atTop (𝓝 0) := by
    simpa only [P, F, c, Real.norm_eq_abs, primitiveIndicatorError, Function.comp_def] using
      (hr.primitiveIndicatorError_tendsto_zero h hradius).comp hR
  have hsum := herr.add ht
  simp only [zero_add] at hsum
  have hweighted : Tendsto (fun j ↦ ∫ x in closedBall 0 r, ‖P j x - V x‖)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · intro j
      exact integral_nonneg (fun x ↦ norm_nonneg _)
    · intro j
      exact integral_norm_sub_triangle (hP j) (hF j) hV
  have hc : 0 < c := hr.phasePrimitive_one_pos h
  have heq (j : ℕ) :
      (∫ x in closedBall 0 r, ‖P j x - V x‖) = c *
      ∫ x in closedBall 0 r,
        ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
          E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by
      have hv : V x = c * E.indicator (fun _ ↦ (1 : ℝ)) x := by
        by_cases hx : x ∈ E <;> simp [V, hx]
      dsimp only [P]
      rw [hv, ← mul_sub, norm_mul, Real.norm_of_nonneg hc.le])
  have hdiv := hweighted.div_const c
  simp only [zero_div] at hdiv
  simpa only [heq, mul_div_cancel_left₀ _ (ne_of_gt hc)] using hdiv

/-- Diverging dilations have a locally convergent subsequence of positive-phase indicators. -/
theorem RigidityHypotheses.phaseIndicator_measurable_phase_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖positivePhaseIndicator (zeroExtension g u) (R (φ j) • x) -
          E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, E, hE, ht⟩ := hr.phasePrimitive_measurable_phase_limit h R hR hRtop
  refine ⟨φ, hφ, E, hE, fun k ↦ ?_⟩
  exact hr.phaseIndicator_limit_of_primitive_limit h (fun j ↦ R (φ j))
    (hRtop.comp hφ.tendsto_atTop) (by positivity) hE (ht k)

/-- The rescaled epigraphs have a subsequence converging locally in indicator integral norm. -/
theorem RigidityHypotheses.rescaledEpigraph_integral_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖(epigraph (rescaledGraph g (R (φ j)))).indicator (fun _ ↦ (1 : ℝ)) x -
          E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, E, hE, ht⟩ := hr.phaseIndicator_measurable_phase_limit h R hR hRtop
  refine ⟨φ, hφ, E, hE, fun k ↦ ?_⟩
  have he (j : ℕ) (x : Space (m + 1)) :
      positivePhaseIndicator (zeroExtension g u) (R (φ j) • x) =
      (epigraph (rescaledGraph g (R (φ j)))).indicator (fun _ ↦ (1 : ℝ)) x := by
    have hp : 0 < R (φ j) := lt_of_lt_of_le zero_lt_one (hR (φ j))
    classical
    change (if 0 < zeroExtension g u (R (φ j) • x) then (1 : ℝ) else 0) =
      (if x ∈ epigraph (rescaledGraph g (R (φ j))) then 1 else 0)
    simp only [h.zeroExtension_pos_iff, mem_epigraph_rescaledGraph_iff hp]
  simpa only [he] using ht k

end SerrinEpigraph
