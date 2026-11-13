module

public import SerrinEpigraph.HomogeneousPhasePerimeter

/-!
# Identification of primitive gradient mass along equipartition scales
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Local equipartition and the exact energy-perimeter identity identify the
limit of primitive gradient mass with the limiting phase's weighted perimeter. -/
theorem RigidityHypotheses.primitive_mass_tendsto_phase_perimeter
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {s : ℝ} (hs : 0 < s)
    (hgap : Tendsto (fun j ↦
      (∫ x in closedBall 0 s, rescaledPhaseEnergyDensity f (R j)
        (fun y ↦ zeroExtension g u (R j • y)) x) -
      (∫ x in closedBall 0 s,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖))
          atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖)
        atTop (𝓝 (phasePrimitive f 1 * (variationalPerimeter basis E (ball 0 s)).toReal)) := by
  obtain ⟨P, hP, hperim, henergy⟩ := hr.exists_positive_phase_perimeter_mass h hR hRt hE hlocal
  have ht := ((henergy s hs).comp hRt).sub hgap
  rw [hperim basis s hs,
    ENNReal.toReal_ofReal (mul_nonneg hP.le (pow_nonneg hs.le _))]
  simpa only [Function.comp_def, sub_sub_cancel, sub_zero, mul_assoc] using ht

end SerrinEpigraph
