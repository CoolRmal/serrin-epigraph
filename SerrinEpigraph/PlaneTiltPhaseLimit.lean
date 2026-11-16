module

public import SerrinEpigraph.PlaneTiltPerimeter
public import SerrinEpigraph.PlaneTiltSharpMass

/-!
# Planar phase limits determine the sharp energy mass and diffuse tilt
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A planar phase limit identifies the full asymptotic energy coefficient with the
one-dimensional interface cost times the Euclidean unit-ball constant. -/
theorem RigidityHypotheses.rescaled_energy_tendsto_of_positive_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun T : ℝ ↦ ∫ x in closedBall 0 s,
      rescaledPhaseEnergyDensity f T (fun y ↦ zeroExtension g u (T • y)) x) atTop
        (𝓝 (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * s ^ m)) := by
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  obtain ⟨P, hP, hperim, henergy⟩ :=
    hr.exists_positive_phase_perimeter_mass h hR hRt hE hlocal
  have hp := congrArg ENNReal.toReal
    (hperim (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 1 zero_lt_one)
  rw [positive_halfspace_perimeter_toReal _ he zero_lt_one, one_pow, one_mul,
    mul_one, ENNReal.toReal_ofReal hP.le] at hp
  simpa only [← hp] using henergy s hs

/-- The normalized original energy has the planar coefficient as its full limit. -/
theorem RigidityHypotheses.surface_energy_tendsto_of_positive_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) :
    Tendsto (fun T : ℝ ↦ T ^ (-(m : ℤ)) * ∫ x in closedBall 0 T,
      phaseEnergyDensity f 0 (zeroExtension g u) x) atTop
        (𝓝 (phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1))) := by
  have ht := hr.rescaled_energy_tendsto_of_positive_halfspace_limit h hR hRt he hlocal
    (s := 1) zero_lt_one
  simp only [one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [integral_rescaledPhaseEnergyDensity f _ hT, mul_one, zpow_neg, zpow_natCast]

/-- One planar blowdown gives the exact surface-energy bound at every center and scale. -/
theorem RigidityHypotheses.phaseEnergy_le_planar_mass_of_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) (c : Space (m + 1)) {r : ℝ} (hradius : 0 < r) :
    (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
      phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m :=
  hr.phaseEnergy_le_asymptotic_mass h
    (hr.surface_energy_tendsto_of_positive_halfspace_limit h hR hRt he hlocal) c hradius

/-- Equipartition along a planar phase sequence identifies the actual primitive mass. -/
theorem RigidityHypotheses.primitive_mass_tendsto_of_positive_halfspace_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (hB : ∀ k : ℕ, Tendsto (fun j ↦
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖) atTop
        (𝓝 (phasePrimitive f 1 * (s ^ m * volume.real (closedBall (0 : Space m) 1)))) := by
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  have hgap := hr.rescaled_energy_primitive_gap_tendsto_zero h
    (fun j ↦ zero_lt_one.trans_le (hR j)) hB (isCompact_closedBall 0 s)
  have ht := hr.primitive_mass_tendsto_phase_perimeter h hR hRt hE hlocal
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) hs hgap
  simpa only [positive_halfspace_perimeter_toReal _ he hs] using ht

/-- The selected equipartition sequence needs no separate primitive-mass premise:
its planar phase limit alone supplies the exact mass used by FE1. -/
theorem RigidityHypotheses.diffuseTilt_tendsto_zero_of_planar_phase_equipartition
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (hB : ∀ k : ℕ, Tendsto (fun j ↦
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (R j • y)) e x)
        atTop (𝓝 0) :=
  hr.diffuseTilt_tendsto_zero_of_positive_halfspace_limit h
    (fun j ↦ zero_lt_one.trans_le (hR j)) he
    (fun s _ ↦ hlocal _ (isCompact_closedBall 0 s))
    (fun _ hs ↦ hr.primitive_mass_tendsto_of_positive_halfspace_limit h hR hRt he hlocal hB hs)
    hradius

/-- A planar phase limit alone forces the actual primitive's oriented defect to vanish.
The required upper mass bound is the already identified diffuse energy. -/
theorem RigidityHypotheses.primitive_defect_tendsto_zero_of_planar_phase_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖ -
        inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x) e)
          atTop (𝓝 0) := by
  have hE : MeasurableSet {y : Space (m + 1) | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  apply integral_oriented_gradient_defect_tendsto_zero_of_positive_halfspace_limit_of_mass_bound
    (fun j ↦ (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul (R j)).locallyLipschitz)
    (B := fun _ ↦ phasePrimitive f 1)
    (fun j x ↦ h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    (hr.phasePrimitive_one_pos h).le he
    (fun s _ ↦ hr.primitive_local_limit_of_phase_local_limit h R hE
      (isCompact_closedBall 0 s) (hlocal _ (isCompact_closedBall 0 s)))
    (fun j s _ ↦ hr.rescaledPrimitive_gradient_integral_le_energy h
      (zero_lt_one.trans_le (hR j)) s) _ hradius
  intro s hs
  simpa only [Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using
    (hr.rescaled_energy_tendsto_of_positive_halfspace_limit h hR hRt he hlocal hs).comp hRt

/-- FE1 directly from a planar phase limit: no independent equipartition or mass
convergence premise is needed for the actual solution. -/
theorem RigidityHypotheses.diffuseTilt_tendsto_zero_of_planar_phase_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0)) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      diffuseTiltDensity (R j) (fun y ↦ zeroExtension g u (R j • y)) e x)
        atTop (𝓝 0) := by
  have ht := (hr.primitive_defect_tendsto_zero_of_planar_phase_limit h hR hRt he hlocal
    hradius).const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦
    diffuseTiltDensity_nonneg (zero_lt_one.trans_le (hR j)) _ he x)) _ ht
  intro j
  exact hr.integral_diffuseTilt_le_primitive_defect h (zero_lt_one.trans_le (hR j)) he
    (isCompact_closedBall 0 r)

end SerrinEpigraph
