module

public import SerrinEpigraph.MinimizingConicalPhase

/-!
# Upper energy comparison with recovery of the same limiting phase
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Recovery of the same local phase controls inner diffuse energy up to a
vanishing error; its annular energy bound follows from the convergent recovery cost. -/
theorem RigidityHypotheses.exists_inner_energy_recovery_error
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {r t : ℝ} (hradius : 0 < r) (ht : 0 < t)
    {R B : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hvlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hbound : ∀ j, (∫ x in closedBall 0 (r + t),
      rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B j)
    {L : ℝ} (hBt : Tendsto B atTop (𝓝 L)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ j,
      (∫ x in ball 0 r, rescaledPhaseEnergyDensity f (R j)
        (fun y ↦ zeroExtension g u (R j • y)) x) ≤ B j + ε j := by
  let U := fun j x ↦ zeroExtension g u (R j • x)
  let K : Set (Space (m + 1)) := closedBall 0 (r + t)
  let S : Set (Space (m + 1)) := K \ ball 0 r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hUval (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRpos (j : ℕ) : 0 < R j := zero_lt_one.trans_le (hR j)
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hUz := integral_norm_sub_tendsto_of_subset (show S ⊆ K from sdiff_subset)
    (fun j ↦ (((hU j).continuous.continuousOn.integrableOn_compact hK).sub hiE).norm) hUlim
  have hvz := integral_norm_sub_tendsto_of_subset (show S ⊆ K from sdiff_subset)
    (fun j ↦ (((hv j).continuous.continuousOn.integrableOn_compact hK).sub hiE).norm) hvlim
  obtain ⟨C, _, hC⟩ := hr.rescaledPhaseEnergy_bound h
  obtain ⟨M, hM⟩ := hBt.bddAbove_range
  let q := max 1 (r + t)
  have hq : 1 ≤ q := le_max_left _ _
  have hSq : S ⊆ closedBall 0 q := sdiff_subset.trans
    (closedBall_subset_closedBall (le_max_right _ _))
  have hEB (j : ℕ) :
      (∫ x in S, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in S, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ C * q ^ m + M := by
    have hiU := h.integrableOn_rescaledPhaseEnergy (hU j) (hUval j) (R j)
      (isCompact_closedBall 0 q)
    have hiv := h.integrableOn_rescaledPhaseEnergy (hv j) (hval j) (R j) hK
    have hEU := setIntegral_mono_set hiU
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hUval j)))
      (Eventually.of_forall hSq)
    have hEv := setIntegral_mono_set hiv
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hval j)))
      (Eventually.of_forall (show S ⊆ K from sdiff_subset))
    have hRq : 1 ≤ R j * q := by nlinarith [hR j, hq]
    exact add_le_add (hEU.trans (hC (R j) q (hRpos j) hRq))
      (hEv.trans ((hbound j).trans (hM (mem_range_self j))))
  obtain ⟨ε, hεt, hcomp⟩ := hr.exists_inner_energy_comparison_error h hv hval hradius ht
    (hiE.mono_set sdiff_subset) hR hRt hEB hUz hvz
  exact ⟨ε, hεt, fun j ↦ (hcomp j).trans (add_le_add (hbound j) le_rfl)⟩

end SerrinEpigraph
