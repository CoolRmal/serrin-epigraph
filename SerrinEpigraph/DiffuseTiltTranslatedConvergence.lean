module

public import SerrinEpigraph.PlaneTiltTranslatedEnergy

/-!
# Vanishing tilt for arbitrary translated planar phase limits
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Primitive convergence follows from phase convergence for any continuous sequence
with values in the full closed solution interval. -/
theorem RigidityHypotheses.primitive_local_limit_of_continuous_phase_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, Continuous (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (ht : Tendsto (fun j ↦ ∫ x in K,
      ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖phasePrimitive f (v j x) - E.indicator (fun _ ↦ phasePrimitive f 1) x‖)
        atTop (𝓝 0) := by
  let C := Real.sqrt (2 * normalizedPotential f 0)
  have hiE : IntegrableOn (E.indicator (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hpE : IntegrableOn (E.indicator (fun _ ↦ phasePrimitive f 1)) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hp (j : ℕ) : Continuous (fun x ↦ phasePrimitive f (v j x)) :=
    (hr.phasePrimitive_lipschitzOn h).continuousOn.comp_continuous (hv j) (hval j)
  have hpoint (j : ℕ) (x : Space (m + 1)) :
      ‖phasePrimitive f (v j x) - E.indicator (fun _ ↦ phasePrimitive f 1) x‖ ≤
        C * ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      convert (hr.phasePrimitive_lipschitzOn h).dist_le_mul (v j x) (hval j x)
        1 (by norm_num) using 1
      simp only [dist_eq_norm]
      rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      convert (hr.phasePrimitive_lipschitzOn h).dist_le_mul (v j x) (hval j x)
        0 (by norm_num) using 1 <;> simp only [dist_eq_norm, phasePrimitive_zero]
      rfl
  have hmajor := ht.const_mul C
  simp only [mul_zero] at hmajor
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ hmajor
  intro j
  rw [← integral_const_mul]
  exact integral_mono (((hp j).continuousOn.integrableOn_compact hK).sub hpE).norm
    ((((hv j).continuousOn.integrableOn_compact hK).sub hiE).norm.const_mul C) (hpoint j)

/-- A sharp all-center bound gives oriented primitive-defect convergence for every
translated planar phase limit, with no constraint on the sequence of centers. -/
theorem RigidityHypotheses.translated_primitive_defect_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (c j + R j • y))) x‖ -
        inner ℝ (gradient (fun y ↦ phasePrimitive f
          (zeroExtension g u (c j + R j • y))) x) e) atTop (𝓝 0) := by
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  apply integral_oriented_gradient_defect_tendsto_zero_of_positive_halfspace_limit_of_mass_bound
    (fun j ↦ locallyLipschitz_comp_translate_dilation
      (hr.phasePrimitive_zeroExtension_locallyLipschitz h) (c j) (R j))
    (B := fun _ ↦ phasePrimitive f 1)
    (fun j x ↦ h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    (hr.phasePrimitive_one_pos h).le he
    (fun s hs ↦ hr.primitive_local_limit_of_continuous_phase_limit h
      (fun j ↦ (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz
        (c j) (R j)).continuous)
      (fun j x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
      hE (isCompact_closedBall 0 s) (hlocal s hs))
    (fun j s hs ↦ hr.translated_primitive_mass_le_surface_bound h hsharp (c j) (hR j) hs)
    _ hradius
  intro s hs
  convert tendsto_const_nhds using 1
  congr 1
  ring

/-- Any centered planar phase limit under the sharp global mass bound has vanishing
actual diffuse tilt. The centers may vary arbitrarily or escape to infinity. -/
theorem RigidityHypotheses.translated_diffuseTilt_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) e x)
        atTop (𝓝 0) := by
  have ht := (hr.translated_primitive_defect_tendsto_zero h hsharp c hR he hlocal
    hradius).const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦
    diffuseTiltDensity_nonneg (hR j) _ he x)) _ ht
  intro j
  exact hr.integral_translated_diffuseTilt_le_primitive_defect h (c j) (hR j) he
    (isCompact_closedBall 0 r)

end SerrinEpigraph
