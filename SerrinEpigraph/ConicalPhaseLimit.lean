module

public import SerrinEpigraph.PhaseDilationInvariance

/-!
# One common phase limit with dilation invariance and geometric comparison
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- One phase limit simultaneously has local convergence, dilation invariance, finite local
perimeter, vertical order, graph-competitor minimality, and the applicable one-sided cone bound.
Nontriviality and classification as a half-space are not asserted here. -/
theorem RigidityHypotheses.exists_dilation_invariant_phase
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
        (∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) ∧
        (∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ)
          (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))),
          variationalPerimeter basis E (ball 0 (k + 1 : ℝ)) ≤
            ENNReal.ofReal (C * (k + 1 : ℝ) ^ m)) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E) ∧
        (∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
          (s r₀ : ℝ), 0 < s → r₀ < s →
          ∀ b : Space m → ℝ, ContDiff ℝ 1 b →
          (∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀), x ∈ E ↔ x ∈ epigraph b) →
          variationalPerimeter basis E (ball 0 s) ≤
            variationalPerimeter basis (epigraph b) (ball 0 s)) ∧
        (HasOneSidedLinearBound g →
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) := by
  obtain ⟨R, hR, hRt, E, hE, hlocal, hD, hvertical, hminimal⟩ :=
    hr.exists_phase_with_vanishing_radial_defect h
  refine ⟨R, hR, hRt, E, hE, hlocal,
    fun _ ha ↦ hr.phase_limit_dilation_invariant h hR hD hE hlocal ha,
    hr.phase_limit_perimeter_bound h hR hE
      (fun k ↦ hlocal _ (isCompact_closedBall _ _)), hvertical, hminimal, ?_⟩
  intro hg
  apply h.phase_limit_oneSided_cone hg (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hE
  intro k
  exact hr.phaseIndicator_limit_of_solution_limit h R hRt (by positivity) hE
    (hlocal _ (isCompact_closedBall _ _))

end SerrinEpigraph
