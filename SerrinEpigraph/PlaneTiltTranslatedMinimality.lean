module

public import SerrinEpigraph.PlaneTiltTranslatedClearing
public import SerrinEpigraph.GluingEnergyCancellation

/-!
# Actual variational comparisons in translated dilation coordinates
-/

public section
noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Inverse translation and dilation carry perturbation support into the physical ball. -/
theorem tsupport_inverse_translate_dilation_sub_subset {d : ℕ} {U v : Space d → ℝ}
    (c : Space d) {R r : ℝ} (hR : 0 < R)
    (hs : tsupport (fun x ↦ v x - U (c + R • x)) ⊆ closedBall 0 r) :
    tsupport (fun x ↦ v (R⁻¹ • (x - c)) - U x) ⊆ closedBall c (R * r) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have he : c + R • (R⁻¹ • (x - c)) = x := by simp [smul_smul, hR.ne']
  have hy : R⁻¹ • (x - c) ∈ tsupport (fun y ↦ v y - U (c + R • y)) := by
    apply subset_closure
    simpa only [Function.mem_support, he] using hx
  have hb := hs hy
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hR] at hb
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖x - c‖ = R * (R⁻¹ * ‖x - c‖) := by field_simp
    _ ≤ R * r := mul_le_mul_of_nonneg_left hb hR.le

/-- The translated dilation of the original solution minimizes its actual rescaled energy. -/
theorem RigidityHypotheses.translated_rescaledPhaseEnergy_minimal
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R r : ℝ} (hR : 0 < R) {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport (fun x ↦ v x - zeroExtension g u (c + R • x)) ⊆ closedBall 0 r) :
    (∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • y)) x) ≤
      ∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f R v x := by
  have hvp : LocallyLipschitz (fun x ↦ v (R⁻¹ • (x - c))) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using hv.comp (((lipschitzWith_smul R⁻¹).comp
      (isometry_add_right (-c)).lipschitzWith).locallyLipschitz)
  have hmin := hr.phaseEnergy_minimal_lipschitz_closedRange h hvp
    (isCompact_closedBall c (R * r)) (tsupport_inverse_translate_dilation_sub_subset c hR hs)
    (fun x ↦ hval (R⁻¹ • (x - c)))
  have he := integral_rescaledPhaseEnergyDensity_translate f
    (fun y ↦ v (R⁻¹ • (y - c))) c hR r
  simp only [add_sub_cancel_left, inv_smul_smul₀ hR.ne'] at he
  rw [integral_rescaledPhaseEnergyDensity_translate f _ c hR r, he]
  exact mul_le_mul_of_nonneg_left hmin (inv_nonneg.mpr (pow_nonneg hR.le m))

/-- Compact cutoff gluing remains admissible at every translated center. -/
theorem RigidityHypotheses.translated_rescaledPhaseEnergy_le_gluedCompetitor
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R r : ℝ} (hR : 0 < R) {v η : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport η ⊆ closedBall 0 r) :
    (∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • y)) x) ≤
      ∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f R
        (gluedCompetitor (fun y ↦ zeroExtension g u (c + R • y)) v η) x := by
  apply hr.translated_rescaledPhaseEnergy_minimal h c hR
    (gluedCompetitor_locallyLipschitz
      (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c R) hv hη)
    (gluedCompetitor_mem_Icc
      (fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩) hvval hηval)
  exact (gluedCompetitor_tsupport_sub_subset _ _ _).trans hs

/-- Minimality and a glued comparison imply an inner-ball comparison directly against
the candidate's outer-ball energy. -/
theorem RigidityHypotheses.translated_inner_energy_le_of_glued_comparison
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {R r t ε : ℝ} (hR : 0 < R) (ht : 0 ≤ t)
    {v η : Space (m + 1) → ℝ} (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport η ⊆ closedBall 0 (r + t)) (hone : ∀ x ∈ ball 0 r, η x = 1)
    (hcomp : (∫ x in closedBall 0 (r + t), rescaledPhaseEnergyDensity f R
        (gluedCompetitor (fun y ↦ zeroExtension g u (c + R • y)) v η) x) ≤
      (∫ x in closedBall 0 (r + t),
        (1 - η x) * rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • y)) x +
        η x * rescaledPhaseEnergyDensity f R v x) + ε) :
    (∫ x in ball 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (c + R • y)) x) ≤
      (∫ x in closedBall 0 (r + t), rescaledPhaseEnergyDensity f R v x) + ε := by
  have hU := locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c R
  have hUval : ∀ x, zeroExtension g u (c + R • x) ∈ Icc (0 : ℝ) 1 :=
    fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  apply inner_energy_le_of_weighted_comparison measurableSet_closedBall measurableSet_ball
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    (h.integrableOn_rescaledPhaseEnergy hU hUval R (isCompact_closedBall _ _))
    (h.integrableOn_rescaledPhaseEnergy hv hvval R (isCompact_closedBall _ _))
    (fun x _ ↦ hr.rescaledPhaseEnergyDensity_nonneg h hR.le hUval x)
    (fun x _ ↦ hr.rescaledPhaseEnergyDensity_nonneg h hR.le hvval x)
    hη.continuous hηval hone
  exact (hr.translated_rescaledPhaseEnergy_le_gluedCompetitor h c hR hv hη hvval hηval hs).trans hcomp

end SerrinEpigraph
