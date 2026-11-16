module

public import SerrinEpigraph.PlaneTiltEnergyAway
public import SerrinEpigraph.DiffuseTiltTranslatedConvergence

/-!
# Off-plane energy exclusion for arbitrary moving centers
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- CO6 remains valid for arbitrary moving centers. The exact sharp all-center bound
supplies the mass estimate, so no new translated monotonicity hypothesis is needed. -/
theorem RigidityHypotheses.translated_energy_tendsto_zero_away_plane
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) :
    Tendsto (fun j ↦ ∫ x in K,
      rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) x)
        atTop (𝓝 0) := by
  have hU (j : ℕ) : LocallyLipschitz (fun x ↦ zeroExtension g u (c j + R j • x)) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hval (j : ℕ) (x : Space (m + 1)) :
      zeroExtension g u (c j + R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  apply integral_density_tendsto_zero_away_plane_of_mass_bound
    (fun j ↦ locallyLipschitz_comp_translate_dilation
      (hr.phasePrimitive_zeroExtension_locallyLipschitz h) (c j) (R j))
    (B := fun _ ↦ phasePrimitive f 1)
    (fun j x ↦ h.phasePrimitive_mem_Icc (hval j x))
    (fun j _ hK ↦ h.integrableOn_rescaledPhaseEnergy (hU j) (hval j) (R j) hK)
    (fun j x ↦ hr.translated_primitive_gradient_le_energy h (c j) (hR j) x)
    (hr.phasePrimitive_one_pos h).le he
    (fun s hs ↦ hr.primitive_local_limit_of_continuous_phase_limit h
      (fun j ↦ (hU j).continuous) hval hE (isCompact_closedBall 0 s) (hlocal s hs))
    (fun j s hs ↦ hr.translated_rescaled_energy_le_surface_bound h hsharp (c j) (hR j) hs)
    _ hK havoid
  intro s hs
  convert tendsto_const_nhds using 1
  congr 1
  ring

end SerrinEpigraph
