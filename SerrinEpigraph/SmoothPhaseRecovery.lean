module

public import SerrinEpigraph.ThresholdSelection

/-!
# Quantitative recovery from a smooth approximation of a measurable phase
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- A smooth phase approximation yields normalized locally Lipschitz competitors
with simultaneous integral-error and sharp asymptotic gradient-mass energy bounds. -/
theorem RigidityHypotheses.exists_smoothPhaseRecovery
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 2 φ) {E K : Set (Space d)}
    (hE : MeasurableSet E) (hK : IsCompact K) {ε δ τ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hτ : 0 < τ) (hτhalf : τ < 1 / 2) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      recoveryTravelTime f δ 1 * A / R ≤ τ / 2 →
      ∃ v : Space d → ℝ, LocallyLipschitz v ∧ (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
        (∫ x in K, ‖v x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) ≤
          (2 / τ) * ∫ x in K, ‖φ x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ ∧
        (∫ x in K, rescaledPhaseEnergyDensity f R v x) ≤
          (1 + recoveryTravelTime f δ 1 * C / R) ^ 2 *
            ((recoveryActionPrimitive f δ 1 *
              ((∫ x in K, ‖gradient φ x‖) + ε * (volume K).toReal)) / (1 - 2 * τ)) := by
  let a := regularizedGradientWidth φ ε
  have ha : ContDiff ℝ 1 a := regularizedGradientWidth_contDiff hφ hε
  have hpos (x : Space d) : 0 < a x := (regularizedGradientWidth_bounds φ hε x).1
  have hg (x : Space d) : ‖gradient φ x‖ ≤ a x :=
    (regularizedGradientWidth_bounds φ hε x).2.1
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  obtain ⟨A, C, hA, hC, hbound⟩ := exists_regularizedGradientWidth_bounds hφ hε hK
  refine ⟨A, C, hA, hC, fun R hR hwidth ↦ ?_⟩
  obtain ⟨t, ht, he⟩ := hr.exists_thresholdRecovery_energy_le h hδ hR hφ1 ha hpos hK hC
    (fun x _ ↦ hg x) (fun x hx ↦ (hbound x hx).2) hτhalf
  obtain ⟨hv, hval⟩ := hr.thresholdRecovery_regular h hδ (R := R) hφ1 ha hpos t
  refine ⟨thresholdRecovery f δ R φ a t, hv, hval, ?_, ?_⟩
  · apply hr.integral_thresholdRecovery_phase_error_le h hδ hR hφ1 ha hpos hE hK hτ ht
    intro x hx
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound x hx).1 (hr.recoveryTravelTime_one_pos h hδ).le)
      hR.le).trans hwidth
  · have hmass := integral_regularizedGradientWidth_le hφ hε hK
    have hact : 0 ≤ recoveryActionPrimitive f δ 1 :=
      (hr.phasePrimitive_one_pos h).le.trans (hr.recoveryActionPrimitive_bounds h hδ).1
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hmass hact

end SerrinEpigraph
