module

public import SerrinEpigraph.IntegratedGluing

/-!
# Cutoff selection using only annular cost
-/

public section

open Set MeasureTheory Metric

namespace SerrinEpigraph

/-- Cutoff selection only requires cost control on the annulus, where the transition
occurs. The values and cost inside the inner ball are irrelevant to selection. -/
theorem exists_cutoff_with_small_annular_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ) (r t : ℝ), 0 < N → 0 < r → 0 < t →
      ∀ F : Space d → ℝ, IntegrableOn F (closedBall 0 (r + t) \ ball 0 r) →
      (∀ x ∈ closedBall 0 (r + t) \ ball 0 r, 0 ≤ F x) →
      ∃ η : Space d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        tsupport η ⊆ ball 0 (r + t) ∧
        (∀ x ∈ ball 0 r, η x = 1) ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖gradient η x‖ ≤ C * N / t) ∧
        (∫ x in {x | 0 < η x ∧ η x < 1}, F x) ≤
          (∫ x in closedBall 0 (r + t) \ ball 0 r, F x) / N := by
  obtain ⟨C, hC, hc⟩ := exists_cutoff_in_fixed_annulus_with_small_cost
  refine ⟨C, hC, fun d N r t hN hr ht F hF hpos ↦ ?_⟩
  let A : Set (Space d) := closedBall 0 (r + t) \ ball 0 r
  have hA : MeasurableSet A := measurableSet_closedBall.diff measurableSet_ball
  have hi : IntegrableOn (A.indicator F) (closedBall 0 (r + t)) :=
    (hF.integrable_indicator hA).integrableOn
  have hp : ∀ x ∈ closedBall 0 (r + t), 0 ≤ A.indicator F x := by
    intro x _
    by_cases hx : x ∈ A
    · simpa only [indicator_of_mem hx] using hpos x hx
    · simp only [indicator_of_notMem hx, le_refl]
  obtain ⟨η, hη, hcompact, hs, hone, hval, hgrad, hcost⟩ :=
    hc d N r t hN hr ht (A.indicator F) hi hp
  refine ⟨η, hη, hcompact, hs, hone, hval, hgrad, ?_⟩
  have hTA : {x | 0 < η x ∧ η x < 1} ⊆ A := by
    intro x hx
    refine ⟨ball_subset_closedBall (hs (subset_closure (ne_of_gt hx.1))), ?_⟩
    intro hb
    have he := hone x hb
    linarith [hx.2]
  have hAK : A ⊆ closedBall 0 (r + t) := sdiff_subset
  rw [setIntegral_indicator hA, setIntegral_indicator hA,
    inter_eq_left.mpr hTA, inter_eq_right.mpr hAK] at hcost
  exact hcost

/-- The actual gluing majorant admits a cutoff selected using only its annular integral. -/
theorem RigidityHypotheses.exists_cutoff_with_small_annular_gluing_cost
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ) (r t R : ℝ),
      0 < N → 0 < r → 0 < t → 0 ≤ R →
      ∀ U v : Space d → ℝ, LocallyLipschitz U → LocallyLipschitz v →
      (∀ x, U x ∈ Icc (0 : ℝ) 1) → (∀ x, v x ∈ Icc (0 : ℝ) 1) →
      ∃ η : Space d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        tsupport η ⊆ ball 0 (r + t) ∧
        (∀ x ∈ ball 0 r, η x = 1) ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖gradient η x‖ ≤ C * N / t) ∧
        (∫ x in {x | 0 < η x ∧ η x < 1}, gluingCost f R (C * N / t) U v x) ≤
          (∫ x in closedBall 0 (r + t) \ ball 0 r,
            gluingCost f R (C * N / t) U v x) / N := by
  obtain ⟨C, hC, hc⟩ := exists_cutoff_with_small_annular_cost
  refine ⟨C, hC, fun d N r t R hN hradius ht hR U v hU hv hUval hvval ↦ ?_⟩
  apply hc d N r t hN hradius ht (gluingCost f R (C * N / t) U v)
  · exact (h.integrableOn_gluingCost hU hv hUval hvval R _
      (isCompact_closedBall 0 (r + t))).mono_set sdiff_subset
  · exact fun x _ ↦ hr.gluingCost_nonneg h hUval hvval hR _ x

/-- Annular cutoff selection bounds the integrated gluing error using only annular cost. -/
theorem RigidityHypotheses.exists_annular_glued_energy_comparison
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
          (∫ x in Metric.closedBall 0 (r + t) \ Metric.ball 0 r, gluingCost f R (C * N / t) U v x) / N := by
  obtain ⟨C, hC, hc⟩ := hr.exists_cutoff_with_small_annular_gluing_cost h
  refine ⟨C, hC, fun d N r t R hN hradius ht hR U v hU hv hUval hvval ↦ ?_⟩
  obtain ⟨η, hη, hcompact, hs, hone, hval, hgrad, hcost⟩ :=
    hc d N r t R hN hradius ht hR.le U v hU hv hUval hvval
  refine ⟨η, hη, hcompact, hs, hone, hval, hgrad, ?_⟩
  have he := hr.integral_glued_energy_le h hU hv hη.locallyLipschitz hUval hvval hval
    hR hgrad (isCompact_closedBall 0 (r + t)) (hs.trans Metric.ball_subset_closedBall)
  exact he.trans (add_le_add le_rfl hcost)

end SerrinEpigraph
