module

public import SerrinEpigraph.AnnularTransitionCost
public import SerrinEpigraph.RescaledMinimality

/-!
# Cancelling the reference energy outside the inner region
-/

public section

open Set MeasureTheory Metric

namespace SerrinEpigraph

/-- A cutoff-weighted energy is bounded by the candidate energy and the reference
energy outside the set where the cutoff is one. -/
theorem integral_weighted_energy_le {d : ℕ} {K S : Set (Space d)}
    (hK : MeasurableSet K) (hS : MeasurableSet S) {E F η : Space d → ℝ}
    (hE : IntegrableOn E K) (hF : IntegrableOn F K)
    (hEn : ∀ x ∈ K, 0 ≤ E x) (hFn : ∀ x ∈ K, 0 ≤ F x)
    (hη : Continuous η) (hval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hone : ∀ x ∈ S, η x = 1) :
    (∫ x in K, (1 - η x) * E x + η x * F x) ≤
      (∫ x in K, F x) + ∫ x in K \ S, E x := by
  have hiE := hE.bdd_mul (continuous_const.sub hη).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ show ‖1 - η x‖ ≤ 1 by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr (hval x).2)]
      linarith [(hval x).1]))
  have hiF := hF.bdd_mul hη.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ show ‖η x‖ ≤ 1 by
      simpa only [Real.norm_of_nonneg (hval x).1] using (hval x).2))
  have hA := hK.diff hS
  have hiA := hE.indicator hA
  have he := integral_mono_ae (hiE.add hiF) (hF.add hiA)
    (ae_restrict_of_forall_mem hK (fun x hx ↦ show
      (1 - η x) * E x + η x * F x ≤ F x + (K \ S).indicator E x by
      by_cases hs : x ∈ S
      · simp [hone x hs, hs]
      · rw [indicator_of_mem (show x ∈ K \ S from ⟨hx, hs⟩)]
        nlinarith [mul_nonneg (hval x).1 (hEn x hx),
          mul_nonneg (sub_nonneg.mpr (hval x).2) (hFn x hx)]))
  simp only [Pi.add_apply, Pi.sub_apply] at he
  rw [integral_add hF hiA, setIntegral_indicator hA, inter_eq_right.mpr sdiff_subset] at he
  exact he

/-- A weighted comparison cancels the reference energy outside the inner region. -/
theorem inner_energy_le_of_weighted_comparison {d : ℕ} {K S : Set (Space d)}
    (hK : MeasurableSet K) (hS : MeasurableSet S) (hSK : S ⊆ K)
    {E F η : Space d → ℝ} (hE : IntegrableOn E K) (hF : IntegrableOn F K)
    (hEn : ∀ x ∈ K, 0 ≤ E x) (hFn : ∀ x ∈ K, 0 ≤ F x)
    (hη : Continuous η) (hval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hone : ∀ x ∈ S, η x = 1) {ε : ℝ}
    (hcomp : (∫ x in K, E x) ≤ (∫ x in K, (1 - η x) * E x + η x * F x) + ε) :
    (∫ x in S, E x) ≤ (∫ x in K, F x) + ε := by
  have hw := integral_weighted_energy_le hK hS hE hF hEn hFn hη hval hone
  have hs := integral_inter_add_sdiff hS hE
  rw [inter_eq_right.mpr hSK] at hs
  linarith

/-- Minimality and a glued comparison imply an inner-ball comparison directly against
the candidate's outer-ball energy. -/
theorem RigidityHypotheses.inner_energy_le_of_glued_comparison
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R r t ε : ℝ} (hR : 0 < R) (ht : 0 ≤ t)
    {v η : Space (m + 1) → ℝ} (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport η ⊆ closedBall 0 (r + t)) (hone : ∀ x ∈ ball 0 r, η x = 1)
    (hcomp : (∫ x in closedBall 0 (r + t), rescaledPhaseEnergyDensity f R
        (gluedCompetitor (fun y ↦ zeroExtension g u (R • y)) v η) x) ≤
      (∫ x in closedBall 0 (r + t),
        (1 - η x) * rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x +
        η x * rescaledPhaseEnergyDensity f R v x) + ε) :
    (∫ x in ball 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) ≤
      (∫ x in closedBall 0 (r + t), rescaledPhaseEnergyDensity f R v x) + ε := by
  have hU := h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul R).locallyLipschitz
  have hUval : ∀ x, zeroExtension g u (R • x) ∈ Icc (0 : ℝ) 1 :=
    fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  apply inner_energy_le_of_weighted_comparison measurableSet_closedBall measurableSet_ball
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    (h.integrableOn_rescaledPhaseEnergy hU hUval R (isCompact_closedBall _ _))
    (h.integrableOn_rescaledPhaseEnergy hv hvval R (isCompact_closedBall _ _))
    (fun x _ ↦ hr.rescaledPhaseEnergyDensity_nonneg h hR.le hUval x)
    (fun x _ ↦ hr.rescaledPhaseEnergyDensity_nonneg h hR.le hvval x)
    hη.continuous hηval hone
  exact (hr.rescaledPhaseEnergy_le_gluedCompetitor h hR hv hη hvval hηval hs).trans hcomp

end SerrinEpigraph
