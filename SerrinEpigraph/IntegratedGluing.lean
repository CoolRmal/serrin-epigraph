module

public import SerrinEpigraph.GluingCostIntegral

/-!
# Integrated comparison for glued competitors
-/

public section

open Set MeasureTheory

namespace SerrinEpigraph

/-- Integrating the localized gluing estimate incurs only the transition-region cost. -/
theorem RigidityHypotheses.integral_glued_energy_le
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1) {R G : ℝ} (hR : 0 < R)
    (hgrad : ∀ x, ‖gradient η x‖ ≤ G)
    {K : Set (Space d)} (hK : IsCompact K) (hs : tsupport η ⊆ K) :
    (∫ x in K, rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x) ≤
      (∫ x in K, (1 - η x) * rescaledPhaseEnergyDensity f R U x +
        η x * rescaledPhaseEnergyDensity f R v x) +
      ∫ x in {x | 0 < η x ∧ η x < 1}, gluingCost f R G U v x := by
  have hT : MeasurableSet {x | 0 < η x ∧ η x < 1} :=
    ((isOpen_lt continuous_const hη.continuous).inter
      (isOpen_lt hη.continuous continuous_const)).measurableSet
  have hTK : {x | 0 < η x ∧ η x < 1} ⊆ K := by
    intro x hx
    exact hs (subset_closure (ne_of_gt hx.1))
  have hiU := h.integrableOn_rescaledPhaseEnergy hU hUval R hK
  have hiv := h.integrableOn_rescaledPhaseEnergy hv hvval R hK
  have hiwU := hiU.bdd_mul (continuous_const.sub hη.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ show ‖1 - η x‖ ≤ 1 by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr (hηval x).2)]
      linarith [(hηval x).1]))
  have hiwv := hiv.bdd_mul hη.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ show ‖η x‖ ≤ 1 by
      simpa only [Real.norm_of_nonneg (hηval x).1] using (hηval x).2))
  have hiw := hiwU.add hiwv
  have hic := (h.integrableOn_gluingCost hU hv hUval hvval R G hK).indicator hT
  have hig := h.integrableOn_rescaledPhaseEnergy
    (gluedCompetitor_locallyLipschitz hU hv hη)
    (gluedCompetitor_mem_Icc hUval hvval hηval) R hK
  have he := integral_mono_ae hig (hiw.add hic)
    (ae_restrict_of_ae (hr.gluedCompetitor_localized_cost_bound_ae h hU hv hη
      hUval hvval hηval hR hgrad))
  change IntegrableOn (fun x ↦ (1 - η x) * rescaledPhaseEnergyDensity f R U x +
    η x * rescaledPhaseEnergyDensity f R v x) K at hiw
  simp only [Pi.add_apply, Pi.sub_apply] at he
  rw [integral_add hiw hic, setIntegral_indicator hT, inter_eq_right.mpr hTK] at he
  exact he

/-- Selecting the cutoff gives an integrated gluing comparison with averaged cost. -/
theorem RigidityHypotheses.exists_glued_energy_comparison
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ) (r t R : ℝ),
      0 < N → 0 < r → 0 < t → 0 < R →
      ∀ U v : Space d → ℝ, LocallyLipschitz U → LocallyLipschitz v →
      (∀ x, U x ∈ Icc (0 : ℝ) 1) → (∀ x, v x ∈ Icc (0 : ℝ) 1) →
      ∃ η : Space d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        tsupport η ⊆ Metric.ball 0 (r + t) ∧
        (∀ x ∈ Metric.ball 0 r, η x = 1) ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖gradient η x‖ ≤ C * N / t) ∧
        (∫ x in Metric.closedBall 0 (r + t),
          rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x) ≤
          (∫ x in Metric.closedBall 0 (r + t),
            (1 - η x) * rescaledPhaseEnergyDensity f R U x +
            η x * rescaledPhaseEnergyDensity f R v x) +
          (∫ x in Metric.closedBall 0 (r + t), gluingCost f R (C * N / t) U v x) / N := by
  obtain ⟨C, hC, hc⟩ := hr.exists_cutoff_with_small_gluing_cost h
  refine ⟨C, hC, fun d N r t R hN hradius ht hR U v hU hv hUval hvval ↦ ?_⟩
  obtain ⟨η, hη, hcompact, hs, hone, hval, hgrad, hcost⟩ :=
    hc d N r t R hN hradius ht hR.le U v hU hv hUval hvval
  refine ⟨η, hη, hcompact, hs, hone, hval, hgrad, ?_⟩
  have he := hr.integral_glued_energy_le h hU hv hη.locallyLipschitz hUval hvval hval
    hR hgrad (isCompact_closedBall 0 (r + t)) (hs.trans Metric.ball_subset_closedBall)
  exact he.trans (add_le_add le_rfl hcost)

end SerrinEpigraph
