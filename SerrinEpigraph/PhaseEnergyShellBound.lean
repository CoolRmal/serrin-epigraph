module

public import SerrinEpigraph.RadialCutoffCompetitor

/-!
# Ball energy controlled by a unit shell
-/

public section
noncomputable section

open Set Metric MeasureTheory Filter

namespace SerrinEpigraph

/-- Minimality and a radial cutoff bound the energy in a ball by a constant times
the volume of its outer unit shell. -/
theorem RigidityHypotheses.phaseEnergy_le_unitShell
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ M : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hM : 0 ≤ M) (hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ M) (R : ℝ) :
    (∫ x in closedBall 0 R, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
      ∫ _x in closedBall (0 : Space (m + 1)) (R + 1) \ closedBall 0 R, (1 / 2 + M) := by
  let U := zeroExtension g u
  let V := radialCutoffCompetitor U R
  let B := closedBall (0 : Space (m + 1)) R
  let A := closedBall (0 : Space (m + 1)) (R + 1)
  let E := phaseEnergyDensity f 0 U
  let F := phaseEnergyDensity f 0 V
  have hAB : B ⊆ A := closedBall_subset_closedBall (by linarith)
  have hval : ∀ x, U x ∈ Icc (0 : ℝ) 1 :=
    fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩
  have hV := radialCutoffCompetitor_locallyLipschitz h.zeroExtension_locallyLipschitz R
  have hiE : IntegrableOn E A := hr.integrableOn_phaseEnergy_zeroExtension h 0
    (isCompact_closedBall _ _)
  have hiF : IntegrableOn F A := h.integrableOn_lipschitz_phaseEnergy hV
    (radialCutoffCompetitor_mem_Icc hval R) 0 (isCompact_closedBall _ _)
  have hiC : IntegrableOn (fun _ : Space (m + 1) ↦ (1 / 2 + M)) (A \ B) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).mono_set sdiff_subset
  have hm : (∫ x in A, E x) ≤ ∫ x in A, F x :=
    hr.phaseEnergy_minimal_lipschitz_closedRange h hV (isCompact_closedBall _ _)
      (radialCutoffCompetitor_tsupport_subset (fun x ↦ (hval x).2) R)
      (radialCutoffCompetitor_mem_Icc hval R)
  have hz : (∫ x in B, F x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hv0 : radialCutoffCompetitor U R x = 0 :=
      radialCutoffCompetitor_zero h.zeroExtension_nonneg hx
    change phaseEnergyDensity f 0 (radialCutoffCompetitor U R) x = 0
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hv0,
      lt_self_iff_false, ite_false]
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  have he := integral_inter_add_sdiff hB hiE
  have hf := integral_inter_add_sdiff hB hiF
  have hinter : A ∩ B = B := inter_eq_right.mpr hAB
  rw [hinter] at he hf
  rw [hz, zero_add] at hf
  have hshell : (∫ x in A \ B, F x) ≤ (∫ x in A \ B, E x) +
      ∫ _x in A \ B, (1 / 2 + M) := by
    rw [← integral_add (hiE.mono_set sdiff_subset) hiC]
    apply integral_mono_ae (hiF.mono_set sdiff_subset)
      ((hiE.mono_set sdiff_subset).add hiC)
    filter_upwards [ae_restrict_of_ae h.zeroExtension_ae_differentiableAt] with x hx
    exact hr.radialCutoff_phaseEnergy_le h hM hW h.zeroExtension_continuous hval hx R
  change (∫ x in B, E x) ≤ ∫ _x in A \ B, (1 / 2 + M)
  linarith

/-- A single positive constant controls all ball energies by outer unit-shell volume. -/
theorem RigidityHypotheses.exists_phaseEnergy_unitShell_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ,
      (∫ x in closedBall 0 R, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        C * volume.real (closedBall (0 : Space (m + 1)) (R + 1) \ closedBall 0 R) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h.normalizedPotential_continuousOn
  refine ⟨1 / 2 + |M|, by positivity, fun R ↦ ?_⟩
  have hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ |M| := by
    intro s hs
    exact (le_abs_self _).trans ((hM s hs).trans (le_abs_self M))
  have he := hr.phaseEnergy_le_unitShell h (abs_nonneg M) hW R
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using he

end SerrinEpigraph
