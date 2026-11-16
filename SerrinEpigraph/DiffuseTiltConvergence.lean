module

public import SerrinEpigraph.DiffuseTiltEstimate
public import SerrinEpigraph.PlaneTiltRotation

/-!
# Diffuse tilt vanishes along a planar phase limit with exact primitive mass
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Local phase convergence transfers to the primitive by its proved Lipschitz bound
on the full closed solution range. -/
theorem RigidityHypotheses.primitive_local_limit_of_phase_local_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (ht : Tendsto (fun j ↦ ∫ x in K,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖phasePrimitive f (zeroExtension g u (R j • x)) -
        E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0) := by
  let C := Real.sqrt (2 * normalizedPotential f 0)
  have hiE : IntegrableOn (E.indicator (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hpE : IntegrableOn (E.indicator (fun _ ↦ phasePrimitive f 1)) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hu (j : ℕ) : Continuous (fun x ↦ zeroExtension g u (R j • x)) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
  have hp (j : ℕ) : Continuous
      (fun x ↦ phasePrimitive f (zeroExtension g u (R j • x))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R j))
  have hpoint (j : ℕ) (x : Space (m + 1)) :
      ‖phasePrimitive f (zeroExtension g u (R j • x)) -
        E.indicator (fun _ ↦ phasePrimitive f 1) x‖ ≤
      C * ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
    have hU := show zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 from
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      convert (hr.phasePrimitive_lipschitzOn h).dist_le_mul (zeroExtension g u (R j • x))
        hU 1 (by norm_num) using 1
      simp only [dist_eq_norm]
      rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      convert (hr.phasePrimitive_lipschitzOn h).dist_le_mul (zeroExtension g u (R j • x))
        hU 0 (by norm_num) using 1 <;> simp only [dist_eq_norm, phasePrimitive_zero]
      rfl
  have hmajor := ht.const_mul C
  simp only [mul_zero] at hmajor
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ hmajor
  intro j
  rw [← integral_const_mul]
  exact integral_mono (((hp j).continuousOn.integrableOn_compact hK).sub hpE).norm
    ((((hu j).continuousOn.integrableOn_compact hK).sub hiE).norm.const_mul C) (hpoint j)

/-- The FE1 conclusion for the actual solution in coordinates in which its limiting
positive halfspace is horizontal. Exact primitive ball mass is the only energy-limit input. -/
theorem RigidityHypotheses.diffuseTilt_tendsto_zero_of_horizontal_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) -
        (epigraph (fun _ : Space m ↦ (0 : ℝ))).indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (hmass : ∀ s : ℝ, 0 < s → Tendsto
      (fun j ↦ ∫ x in closedBall 0 s,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖) atTop
      (𝓝 (phasePrimitive f 1 * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (R j • y))
        (verticalDirection m) x) atTop (𝓝 0) := by
  have hdef := integral_oriented_gradient_defect_tendsto_zero_of_halfspace_limit
    (fun j ↦ (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul (R j)).locallyLipschitz)
    (B := fun _ ↦ phasePrimitive f 1)
    (fun j x ↦ h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    (hr.phasePrimitive_one_pos h).le
    (fun s hs ↦ hr.primitive_local_limit_of_phase_local_limit h R
      (isOpen_epigraph continuous_const).measurableSet (isCompact_closedBall 0 s)
      (hlocal s hs)) hmass hradius
  have hmajor := hdef.const_mul 2
  simp only [mul_zero] at hmajor
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦
    diffuseTiltDensity_nonneg (hR j) _ (norm_verticalDirection m) x)) _ hmajor
  intro j
  exact hr.integral_diffuseTilt_le_primitive_defect h (hR j) (norm_verticalDirection m)
    (isCompact_closedBall 0 r)

/-- FE1 for an arbitrary unit normal: planar phase convergence and exact primitive
mass imply vanishing tangential kinetic energy on every fixed ball. -/
theorem RigidityHypotheses.diffuseTilt_tendsto_zero_of_positive_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ s : ℝ, 0 < s → Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (hmass : ∀ s : ℝ, 0 < s → Tendsto
      (fun j ↦ ∫ x in closedBall 0 s,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖) atTop
      (𝓝 (phasePrimitive f 1 * (s ^ m * volume.real (closedBall (0 : Space m) 1)))))
    {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (R j • y)) e x)
        atTop (𝓝 0) := by
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  have hdef := integral_oriented_gradient_defect_tendsto_zero_of_positive_halfspace_limit
    (fun j ↦ (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul (R j)).locallyLipschitz)
    (B := fun _ ↦ phasePrimitive f 1)
    (fun j x ↦ h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    (hr.phasePrimitive_one_pos h).le he
    (fun s hs ↦ hr.primitive_local_limit_of_phase_local_limit h R hE
      (isCompact_closedBall 0 s) (hlocal s hs)) hmass hradius
  have hmajor := hdef.const_mul 2
  simp only [mul_zero] at hmajor
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦
    diffuseTiltDensity_nonneg (hR j) _ he x)) _ hmajor
  intro j
  exact hr.integral_diffuseTilt_le_primitive_defect h (hR j) he (isCompact_closedBall 0 r)

end SerrinEpigraph
