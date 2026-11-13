module

public import SerrinEpigraph.FinitePerimeterMinimality

/-!
# A common nontrivial conical phase minimizing perimeter
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- One common phase is nontrivial, dilation invariant, vertically ordered,
and perimeter minimizing against all measurable compact perturbations in balls.
It retains the applicable one-sided cone constraint and local equipartition. -/
theorem RigidityHypotheses.exists_minimizing_conical_phase
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
        (volume E ≠ 0 ∧ volume Eᶜ ≠ 0) ∧
        (∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) ∧
        (∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ)
          (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))),
          variationalPerimeter basis E (ball 0 (k + 1 : ℝ)) ≤
            ENNReal.ofReal (C * (k + 1 : ℝ) ^ m)) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E) ∧
        (∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
          (s r₀ : ℝ), 0 < s → r₀ < s →
          ∀ D : Set (Space (m + 1)), MeasurableSet D →
          (∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀), x ∈ E ↔ x ∈ D) →
          variationalPerimeter basis E (ball 0 s) ≤ variationalPerimeter basis D (ball 0 s)) ∧
        (HasOneSidedLinearBound g →
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K,
            rescaledDiscrepancyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)
              atTop (𝓝 0)) ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦
            (∫ x in K, rescaledPhaseEnergyDensity f (R j)
              (fun y ↦ zeroExtension g u (R j • y)) x) -
            (∫ x in K, ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖))
              atTop (𝓝 0)) := by
  obtain ⟨R, hR, hRt, E, hE, hlocal, hnontriv, hdilation, hperim, hvertical, _, hside,
    hdiscrepancy, hgap⟩ := hr.exists_phase_with_equipartition h
  refine ⟨R, hR, hRt, E, hE, hlocal, hnontriv, hdilation, hperim, hvertical, ?_,
    hside, hdiscrepancy, hgap⟩
  intro basis s r₀ hs hr₀ D hD hagree
  exact hr.limiting_phase_perimeter_minimality_ae h basis hs hr₀ hR hRt hE hD
    (hlocal _ (isCompact_closedBall _ _)) hagree

end SerrinEpigraph
