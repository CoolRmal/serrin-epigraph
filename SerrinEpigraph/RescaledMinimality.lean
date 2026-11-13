module

public import SerrinEpigraph.ClosedLipschitzMinimality
public import SerrinEpigraph.RescaledPhaseEnergy
public import SerrinEpigraph.GluedCompetitor

/-!
# Minimality in rescaled coordinates
-/

public section

open Set MeasureTheory Metric

namespace SerrinEpigraph

/-- Pulling back a perturbation by inverse dilation preserves its ball support. -/
theorem tsupport_inverse_dilation_sub_subset {d : ℕ} {U v : Space d → ℝ}
    {R r : ℝ} (hR : 0 < R)
    (hs : tsupport (fun x ↦ v x - U (R • x)) ⊆ closedBall 0 r) :
    tsupport (fun x ↦ v (R⁻¹ • x) - U x) ⊆ closedBall 0 (R * r) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hy : R⁻¹ • x ∈ tsupport (fun y ↦ v y - U (R • y)) := by
    apply subset_closure
    simpa [Function.mem_support, smul_inv_smul₀ hR.ne'] using hx
  have hb := hs hy
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hR] at hb ⊢
  calc
    ‖x‖ = R * (R⁻¹ * ‖x‖) := by field_simp
    _ ≤ R * r := mul_le_mul_of_nonneg_left hb hR.le

/-- Every closed-range locally Lipschitz perturbation of the dilated solution obeys
minimality for the corresponding rescaled energy. -/
theorem RigidityHypotheses.rescaledPhaseEnergy_minimal
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R r : ℝ} (hR : 0 < R) {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport (fun x ↦ v x - zeroExtension g u (R • x)) ⊆ closedBall 0 r) :
    (∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) ≤
      ∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f R v x := by
  have hmin := hr.phaseEnergy_minimal_lipschitz_closedRange h
    (hv.comp (lipschitzWith_smul R⁻¹).locallyLipschitz)
    (isCompact_closedBall 0 (R * r)) (tsupport_inverse_dilation_sub_subset hR hs)
    (fun x ↦ hval (R⁻¹ • x))
  have he := integral_rescaledPhaseEnergyDensity f (fun y ↦ v (R⁻¹ • y)) hR r
  simp only [inv_smul_smul₀ hR.ne'] at he
  rw [integral_rescaledPhaseEnergyDensity f _ hR r, he]
  exact mul_le_mul_of_nonneg_left hmin (inv_nonneg.mpr (pow_nonneg hR.le m))

/-- Cutoff gluing in a rescaled ball gives an admissible energy comparison. -/
theorem RigidityHypotheses.rescaledPhaseEnergy_le_gluedCompetitor
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R r : ℝ} (hR : 0 < R) {v η : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport η ⊆ closedBall 0 r) :
    (∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) ≤
      ∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f R
        (gluedCompetitor (fun y ↦ zeroExtension g u (R • y)) v η) x := by
  apply hr.rescaledPhaseEnergy_minimal h hR
    (gluedCompetitor_locallyLipschitz
      (h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul R).locallyLipschitz) hv hη)
    (gluedCompetitor_mem_Icc
      (fun x ↦ ⟨h.zeroExtension_nonneg (R • x), (hr.zeroExtension_lt_one (R • x)).le⟩)
      hvval hηval)
  exact (gluedCompetitor_tsupport_sub_subset _ _ _).trans hs

end SerrinEpigraph
