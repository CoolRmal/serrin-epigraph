module

public import SerrinEpigraph.EnergyPerimeterIdentification

/-!
# Positive homogeneous perimeter mass of the limiting phase
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- A positive finite interface coefficient can be cancelled in an exact
weighted perimeter identity. -/
theorem ennreal_eq_of_positive_weighted_eq {P : ℝ≥0∞} {σ M : ℝ} (hσ : 0 < σ)
    (h : ENNReal.ofReal σ * P = ENNReal.ofReal M) : P = ENNReal.ofReal (M / σ) := by
  apply (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hσ).ne' ENNReal.ofReal_ne_top).mp
  rw [h, ← ENNReal.ofReal_mul hσ.le]
  congr 1
  field_simp

/-- Every local phase limit has a positive finite homogeneous ball-perimeter
coefficient. The coefficient also determines the full diffuse-energy limits. -/
theorem RigidityHypotheses.exists_positive_phase_perimeter_mass
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    ∃ P : ℝ, 0 < P ∧
      (∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (s : ℝ), 0 < s →
        variationalPerimeter basis E (ball 0 s) = ENNReal.ofReal (P * s ^ m)) ∧
      ∀ s : ℝ, 0 < s →
        Tendsto (fun T : ℝ ↦ ∫ x in closedBall 0 s,
          rescaledPhaseEnergyDensity f T (fun y ↦ zeroExtension g u (T • y)) x)
            atTop (𝓝 (phasePrimitive f 1 * P * s ^ m)) := by
  obtain ⟨L, hL, henergy⟩ := hr.exists_positive_asymptotic_energy_mass h
  have hσ := hr.phasePrimitive_one_pos h
  refine ⟨L / phasePrimitive f 1, div_pos hL hσ, ?_, ?_⟩
  · intro basis s hs
    have he := ennreal_eq_of_positive_weighted_eq hσ
      (hr.phase_perimeter_eq_energy_mass h henergy hR hRt hE hlocal basis hs)
    convert he using 1
    congr 1
    ring
  · intro s hs
    convert henergy s hs using 1
    congr 1
    field_simp

end SerrinEpigraph
