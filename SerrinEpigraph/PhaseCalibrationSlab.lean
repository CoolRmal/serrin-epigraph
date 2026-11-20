module

public import SerrinEpigraph.PhaseCalibrationDefect

/-!
# Exact vertical calibration on slabs

On every vertical segment the calibration density `√(2W(v)) ∂ₜ v` integrates exactly to the
jump of `Φ(v)`; by Fubini the same holds on slabs `B × (-τ, τ)`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **Exact vertical FTC for the calibration density.** On every vertical segment the
calibration density `√(2W(v)) ∂ₜ v` of `v = zeroExtension g u (c + R • Q ·)` integrates to the
jump of `Φ(v)`: `t ↦ Φ(v(y, t))` is locally Lipschitz, and its derivative is the density at
every height (chain rule on the positive phase, local minima on the zero phase). -/
theorem RigidityHypotheses.integral_Ioo_vertical_phaseCalibration_eq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) (R : ℝ)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (y : Space m) {τ : ℝ} (hτ : 0 < τ) :
    (∫ t in Ioo (-τ) τ, Real.sqrt (2 * normalizedPotential f
        (zeroExtension g u (c + R • Q (point y t)))) *
        verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) (point y t)) =
      phasePrimitive f (zeroExtension g u (c + R • Q (point y τ))) -
        phasePrimitive f (zeroExtension g u (c + R • Q (point y (-τ)))) := by
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (c + R • Q z)
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz c R Q
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hG : LocallyLipschitz (fun s ↦ phasePrimitive f (v (point y s))) :=
    (hr.phasePrimitive_comp_locallyLipschitz h hvL hval).comp
      (contDiff_point_vertical y).locallyLipschitz
  obtain ⟨K, hK⟩ := (hG.locallyLipschitzOn (s := uIcc (-τ) τ)).exists_lipschitzOnWith_of_compact
    isCompact_uIcc
  have hFTC := (LipschitzOnWith.absolutelyContinuousOnInterval hK).integral_deriv_eq_sub
  -- the derivative of `t ↦ Φ(v(y, t))` is the calibration density at every height
  have hderiv : ∀ t, deriv (fun s ↦ phasePrimitive f (v (point y s))) t =
      Real.sqrt (2 * normalizedPotential f (v (point y t))) *
        verticalDerivative v (point y t) := by
    intro t
    rcases (hval (point y t)).1.eq_or_lt with hzero | hpos
    · -- zero phase: both sides vanish as derivatives at local minima
      have hmin : IsLocalMin (fun s ↦ phasePrimitive f (v (point y s))) t :=
        Eventually.of_forall fun s ↦ by
          simp only [← hzero, phasePrimitive_zero]
          exact phasePrimitive_nonneg f (hval _).1
      have hvmin : IsLocalMin v (point y t) :=
        Eventually.of_forall fun z ↦ by
          simp only [← hzero]
          exact (hval z).1
      rw [hmin.deriv_eq_zero, verticalDerivative, hvmin.fderiv_eq_zero,
        zero_apply, mul_zero]
    · -- positive phase: the chain rule
      have hd := h.differentiableAt_rescaled_of_pos c R Q hpos
      exact ((h.phasePrimitive_hasDerivAt ⟨hpos, hr.zeroExtension_lt_one _⟩).comp t
        (hasDerivAt_vertical_section hd)).deriv
  rw [← hFTC, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun t _ ↦ (hderiv t).symm

/-- **Exact slab calibration.** For a measurable bounded set `B` of horizontal points, the
calibration density integrates over the slab `B × (-τ, τ)` to the integrated jump of `Φ(v)`
across it (Fubini and the exact vertical FTC). -/
theorem RigidityHypotheses.setIntegral_slab_phaseCalibration_eq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 ≤ R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {B : Set (Space m)}
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) {τ : ℝ} (hτ : 0 < τ) :
    (∫ z in horizontal ⁻¹' B ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-τ) τ,
        Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z))) *
          verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) =
      ∫ y in B, (phasePrimitive f (zeroExtension g u (c + R • Q (point y τ))) -
        phasePrimitive f (zeroExtension g u (c + R • Q (point y (-τ))))) := by
  set S : Set (Space (m + 1)) :=
    horizontal ⁻¹' B ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-τ) τ
  set J : Space (m + 1) → ℝ := fun z ↦
    Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z))) *
      verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z with hJdef
  have hcl : Continuous (fun z : Space (m + 1) ↦ (z (Fin.last m) : ℝ)) := continuous_last
  have hSm : MeasurableSet S :=
    (hBm.preimage continuous_horizontal.measurable).inter
      (measurableSet_Ioo.preimage hcl.measurable)
  obtain ⟨ρ, hρ⟩ := hBb.subset_closedBall (0 : Space m)
  have hSball : S ⊆ closedBall (0 : Space (m + 1)) (ρ + τ) := by
    intro z hz
    obtain ⟨hzB, hzt⟩ := hz
    have h1 : ‖horizontal z‖ ≤ ρ := by
      have := hρ hzB
      rwa [mem_closedBall, dist_zero_right] at this
    have h2 : |z (Fin.last m)| ≤ τ := abs_le.mpr ⟨hzt.1.le, hzt.2.le⟩
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_horizontal_add_abs_last z]
  have hJS : IntegrableOn J S :=
    hr.integrableOn_phaseCalibrationDensity h c hR Q hSm (isBounded_closedBall.subset hSball)
  set G : Space (m + 1) → ℝ := S.indicator J with hGdef
  have hGi : Integrable G := hJS.integrable_indicator hSm
  have hmp := measurePreserving_point m
  have hmap := integral_map hmp.measurable.aemeasurable
    (show AEStronglyMeasurable G
      (Measure.map (fun p : Space m × ℝ ↦ point p.1 p.2)
        ((volume : Measure (Space m)).prod volume))
      from by rw [hmp.map_eq]; exact hGi.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  have hG'i : Integrable (fun p : Space m × ℝ ↦ G (point p.1 p.2))
      ((volume : Measure (Space m)).prod volume) := hmp.integrable_comp_of_integrable hGi
  -- on every vertical line the slice integral is the jump of the phase primitive
  have hslice : ∀ y : Space m, (∫ t, G (point y t)) =
      B.indicator (fun y ↦ phasePrimitive f (zeroExtension g u (c + R • Q (point y τ))) -
        phasePrimitive f (zeroExtension g u (c + R • Q (point y (-τ))))) y := by
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, ← hr.integral_Ioo_vertical_phaseCalibration_eq h c R Q y hτ,
        ← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
      by_cases ht : t ∈ Ioo (-τ) τ
      · have hmem : point y t ∈ S := ⟨by simpa [horizontal_point] using hy,
          by simpa [last_point] using ht⟩
        simp only [hGdef, indicator_of_mem hmem, indicator_of_mem ht, hJdef]
      · have hmem : point y t ∉ S := fun hS ↦ ht (by simpa [last_point] using hS.2)
        simp only [hGdef, indicator_of_notMem hmem, indicator_of_notMem ht]
    · rw [indicator_of_notMem hy]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
      have hmem : point y t ∉ S := fun hS ↦ hy (by simpa [horizontal_point] using hS.1)
      simp only [hGdef, indicator_of_notMem hmem, Pi.zero_apply]
  rw [← integral_indicator hSm, ← hGdef, hmap, integral_prod _ hG'i, ← integral_indicator hBm]
  exact integral_congr_ae (Eventually.of_forall hslice)

end SerrinEpigraph
