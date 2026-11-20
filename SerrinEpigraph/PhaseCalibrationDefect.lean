module

public import SerrinEpigraph.AlignedFluxVertical

/-!
# The phase calibration defect

For `v = zeroExtension g u (c + R • Q ·)`: the chain rule for `Φ(v)`, the sum-of-squares form
of the defect `e_R(v) - √(2W(v)) ∂ₜ v`, the pointwise AM-GM bound for the calibrated flux and
integrability on bounded sets.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The phase calibration defect `e_R(v) - √(2W(v)) ∂ₜ v`. -/
def phaseCalibrationDefect (f : ℝ → ℝ) (R : ℝ) (v : Space (m + 1) → ℝ)
    (z : Space (m + 1)) : ℝ :=
  rescaledPhaseEnergyDensity f R v z -
    Real.sqrt (2 * normalizedPotential f (v z)) * verticalDerivative v z

/-- The horizontal projection commutes with scalar multiplication. -/
private theorem phaseCalibrationDefect_horizontal_smul (a : ℝ) (p : Space (m + 1)) :
    horizontal (a • p) = a • horizontal p :=
  map_smul (horizontalContinuousLinearMap (m := m)) a p

/-- The scalar AM-GM inequality behind the calibrated flux bound. -/
private theorem phaseCalibrationDefect_amgm {R δ lam w X N : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hlam : 0 < lam) :
    δ⁻¹ * R⁻¹ * |w| * (X * N) ≤
      lam * X ^ 2 * ((2 * R)⁻¹ * w ^ 2 + (2 * R)⁻¹ * N ^ 2) +
        (2 * lam)⁻¹ * δ⁻¹ ^ 2 * (R⁻¹ * N ^ 2) := by
  have hR' := hR.ne'
  have hδ' := hδ.ne'
  have hlam' := hlam.ne'
  rw [← sq_abs w, ← sub_nonneg]
  have e : lam * X ^ 2 * ((2 * R)⁻¹ * |w| ^ 2 + (2 * R)⁻¹ * N ^ 2) +
        (2 * lam)⁻¹ * δ⁻¹ ^ 2 * (R⁻¹ * N ^ 2) - δ⁻¹ * R⁻¹ * |w| * (X * N) =
      (2 * lam * R)⁻¹ * ((lam * X * |w| - δ⁻¹ * N) ^ 2 + lam ^ 2 * X ^ 2 * N ^ 2) := by
    field_simp
    ring
  rw [e]
  positivity

theorem RigidityHypotheses.gradient_phasePrimitive_rescaled
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) (R : ℝ)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (z : Space (m + 1)) :
    gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z =
      Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z))) •
        gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z := by
  rw [gradient_comp_translate_dilation_isometry
      (fun y ↦ phasePrimitive f (zeroExtension g u y)) c R Q z,
    gradient_comp_translate_dilation_isometry (zeroExtension g u) c R Q z,
    hr.gradient_phasePrimitive_zeroExtension h (c + R • Q z), map_smul, smul_comm]

theorem RigidityHypotheses.exists_lipschitzWith_phasePrimitive_rescaled
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 ≤ R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) := by
  exact ⟨_, lipschitzOnWith_univ.mp ((hr.phasePrimitive_lipschitzOn h).comp
    (lipschitzOnWith_univ.mpr (hr.lipschitzWith_rescaled h c hR Q))
    fun z _ ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)⟩

theorem Hypotheses.phaseCalibrationDefect_rescaled_of_eq_zero (h : Hypotheses g u f κ)
    (c : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {z : Space (m + 1)}
    (hz : zeroExtension g u (c + R • Q z) = 0) :
    phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z = 0 ∧
      gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z = 0 := by
  have hg : gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z = 0 :=
    gradient_eq_zero_of_nonneg_zero (v := fun z ↦ zeroExtension g u (c + R • Q z))
      (fun y ↦ h.zeroExtension_nonneg _) hz
  refine ⟨?_, hg⟩
  have hd : verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z = 0 := by
    rw [← inner_gradient_verticalDirection, hg, inner_zero_left]
  have hn : z ∉ {y | 0 < zeroExtension g u (c + R • Q y)} := by
    simp [hz]
  rw [phaseCalibrationDefect, hd, mul_zero, sub_zero, rescaledPhaseEnergyDensity,
    indicator_of_notMem hn]

theorem RigidityHypotheses.phaseCalibrationDefect_rescaled_eq_of_pos
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {z : Space (m + 1)}
    (hz : 0 < zeroExtension g u (c + R • Q z)) :
    phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z =
      (2 * R)⁻¹ * (verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z -
          R * Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z)))) ^ 2 +
        (2 * R)⁻¹ *
          ‖horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z)‖ ^ 2 := by
  have hW := hr.normalizedPotential_nonneg h ⟨hz.le, (hr.zeroExtension_lt_one (c + R • Q z)).le⟩
  have hs := Real.sq_sqrt
    (show 0 ≤ 2 * normalizedPotential f (zeroExtension g u (c + R • Q z)) by positivity)
  have hR' := hR.ne'
  rw [phaseCalibrationDefect, rescaledPhaseEnergyDensity_eq_kinetic_add_potential f R
      (fun y ↦ h.zeroExtension_nonneg (c + R • Q y)), phasePotentialDensity,
    indicator_of_mem (s := {y | 0 < zeroExtension g u (c + R • Q y)}) hz,
    norm_gradient_sq_eq_horizontal_add_vertical_sq]
  field_simp
  linear_combination (-R ^ 2) * hs

theorem RigidityHypotheses.phaseCalibrationDefect_rescaled_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (z : Space (m + 1)) :
    0 ≤ phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z := by
  rcases (h.zeroExtension_nonneg (c + R • Q z)).eq_or_lt with h0 | hpos
  · rw [(h.phaseCalibrationDefect_rescaled_of_eq_zero c R Q h0.symm).1]
  · rw [hr.phaseCalibrationDefect_rescaled_eq_of_pos h c hR Q hpos]
    positivity

theorem RigidityHypotheses.abs_inner_flux_sub_primitiveFlux_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ} (hlam : 0 < lam) (ξ : Space m) (z : Space (m + 1)) :
    |inner ℝ ξ (((δ⁻¹ * R⁻¹ *
            verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) •
          horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z)) -
        δ⁻¹ • horizontal
          (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))| ≤
      lam * ‖ξ‖ ^ 2 *
          phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z +
        (2 * lam)⁻¹ * δ⁻¹ ^ 2 *
          diffuseTiltDensity R (fun z ↦ zeroExtension g u (c + R • Q z))
            (verticalDirection m) z := by
  have h0' : horizontal (0 : Space (m + 1)) = 0 := map_zero (horizontalContinuousLinearMap (m := m))
  rw [hr.gradient_phasePrimitive_rescaled h c R Q z, diffuseTiltDensity_vertical_eq]
  rcases (h.zeroExtension_nonneg (c + R • Q z)).eq_or_lt with h0 | hpos
  · obtain ⟨hdef, hg⟩ := h.phaseCalibrationDefect_rescaled_of_eq_zero c R Q h0.symm
    rw [hdef, hg]
    simp [h0']
  · rw [hr.phaseCalibrationDefect_rescaled_eq_of_pos h c hR Q hpos,
      phaseCalibrationDefect_horizontal_smul, smul_smul, ← sub_smul, real_inner_smul_right,
      abs_mul]
    have hR' := hR.ne'
    have hcoef : δ⁻¹ * R⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z -
          δ⁻¹ * Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z))) =
        δ⁻¹ * R⁻¹ * (verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z -
          R * Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z)))) := by
      field_simp
    rw [hcoef, abs_mul, abs_of_pos (by positivity : 0 < δ⁻¹ * R⁻¹)]
    calc _ ≤ δ⁻¹ * R⁻¹ * |verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z -
            R * Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z)))| *
          (‖ξ‖ * ‖horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z)‖) := by
          gcongr
          exact abs_real_inner_le_norm _ _
      _ ≤ _ := phaseCalibrationDefect_amgm hR hδ hlam

theorem RigidityHypotheses.integrableOn_phaseCalibrationDensity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 ≤ R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {S : Set (Space (m + 1))}
    (hSm : MeasurableSet S) (hSb : Bornology.IsBounded S) :
    IntegrableOn (fun z ↦ Real.sqrt (2 * normalizedPotential f
        (zeroExtension g u (c + R • Q z))) *
      verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) S := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, LipschitzWith K (fun z ↦ zeroExtension g u (c + R • Q z)) :=
    ⟨_, hr.lipschitzWith_rescaled h c hR Q⟩
  have hval : ∀ z, zeroExtension g u (c + R • Q z) ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hWc : Continuous (fun z ↦ normalizedPotential f (zeroExtension g u (c + R • Q z))) :=
    h.normalizedPotential_continuousOn.comp_continuous hK.continuous hval
  have hmeas : Measurable (fun z ↦ Real.sqrt (2 * normalizedPotential f
        (zeroExtension g u (c + R • Q z))) *
      verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) :=
    (continuous_const.mul hWc).sqrt.measurable.mul (measurable_verticalDerivative _)
  refine Measure.integrableOn_of_bounded (M := Real.sqrt (2 * normalizedPotential f 0) * K)
    hSb.measure_lt_top.ne hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hSm] with z _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : Real.sqrt (2 * normalizedPotential f (zeroExtension g u (c + R • Q z))) ≤
      Real.sqrt (2 * normalizedPotential f 0) := by
    have := hr.normalizedPotential_antitoneOn h ⟨le_rfl, zero_le_one⟩ (hval z) (hval z).1
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : |verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z| ≤ K := by
    have hh := (fderiv ℝ (fun z ↦ zeroExtension g u (c + R • Q z)) z).le_opNorm
      (verticalDirection m)
    rw [norm_verticalDirection, mul_one] at hh
    exact hh.trans (norm_fderiv_le_of_lipschitz ℝ hK)
  exact mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)

theorem RigidityHypotheses.integrableOn_phaseCalibrationDefect
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ}
    (hR : 0 ≤ R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {S : Set (Space (m + 1))}
    (hSm : MeasurableSet S) (hSb : Bornology.IsBounded S) :
    IntegrableOn
      (phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z))) S := by
  obtain ⟨r, hr'⟩ := hSb.subset_closedBall (0 : Space (m + 1))
  have hvL : LocallyLipschitz (fun z ↦ zeroExtension g u (c + R • Q z)) :=
    (hr.lipschitzWith_rescaled h c hR Q).locallyLipschitz
  have hval : ∀ z, zeroExtension g u (c + R • Q z) ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hE := (h.integrableOn_rescaledPhaseEnergy hvL hval R (isCompact_closedBall _ r)).mono_set
    hr'
  exact hE.sub (hr.integrableOn_phaseCalibrationDensity h c hR Q hSm hSb)

end SerrinEpigraph
