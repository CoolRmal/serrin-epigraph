module

public import SerrinEpigraph.PhaseCalibrationLimit
public import SerrinEpigraph.PhaseCalibrationFlux
public import SerrinEpigraph.HorizontalIntegrationByParts
public import SerrinEpigraph.AlignedColumnStructure
public import SerrinEpigraph.CutoffPrimitiveComparison
public import SerrinEpigraph.AlignedFluxCalibrationAux

/-!
# The vertical flux identification for `C¹` test fields (calibration route)

Along a subsequence of height-limit data, with `v_j` the rotated rescalings, `F_j` the normalized
flux and `f_j = (h_j - a_j)/δ_j` the normalized extended heights at the levels `σ_j`, we prove
`∫_{Q₁} ⟪ζ(y), F_j⟫ + σ ∫ ⟪ζ, ∇f_j⟫ → 0` for `C¹` fields `ζ` supported in `B_{3/4}`
(`RigidityHypotheses.tendsto_verticalFlux_add_of_contDiff`).

With the cutoff `ψ₀(t)` (equal to `1` for `|t| ≤ 1/4`, vanishing for `|t| ≥ 1/2`) and
`Ξ = ψ₀(t) ζ(y)`, there is an exact identity at every index (`afc_abs_flux_add_height_le`),
`X_j = I_j + II_j - δ_j⁻¹ E_j`:
* `I_j = ∫_{Q₁} (1 - ψ₀) ⟪ζ, F_j⟫` is bounded by the flux mass off the slab `|t| < 1/4`, which
  vanishes in the limit (`tendsto_flux_mass_offPlane_of_aligned`);
* `II_j = ∫ ⟪Ξ, F_j - δ_j⁻¹ ∇_y Φ(v_j)⟫` is at most `λ ‖ζ‖² ∫ (e_j - J_j) + 2ᵐ/(2λ)` for every
  `λ > 0` (`abs_integral_flux_sub_primitiveFlux_le` with the tilt normalization), and the
  calibration defect integral tends to `0`
  (`tendsto_setIntegral_phaseCalibrationDefect_of_aligned`);
* after the horizontal integrations by parts (`integral_mul_inner_horizontal_gradient_eq_neg`,
  `integral_inner_gradient_eq_neg_integral_fieldDivergence_mul`), `E_j` is the column error of
  `exists_abs_integral_cutoff_phasePrimitive_add_height_le`, valid on the good columns of
  `eventually_columnStructure_of_alignedHeightLimit`; with the eventual energy and bad-volume
  bounds it gives `δ_j⁻¹ |E_j| ≲ 1/(R_j δ_j) + δ_j → 0`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ## Per-index estimates -/

/-- The slab `B_{3/4} × (-1, 1)` lies in the vertical cylinder `Q₁`. -/
private theorem afc_slab_subset_tiltCylinder_one :
    horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
        (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1 ⊆
      tiltCylinder (verticalDirection m) 1 := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  rw [mem_preimage, mem_ball, dist_zero_right] at h1
  rw [mem_preimage, mem_Ioo] at h2
  rw [mem_tiltCylinder_vertical_iff]
  exact ⟨by linarith, abs_lt.mpr h2⟩

/-- The column error, divided by `δ`, against the rate `C EB / (R δ) + σ (2 + τ) M δ`. -/
private theorem afc_inv_mul_error_le {δ R G C σ τ Ie EB Vb M : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hIe : Ie ≤ EB)
    (hVb : Vb ≤ M * δ ^ 2) :
    δ⁻¹ * (G * (C * R⁻¹ * Ie + σ * (2 + τ) * Vb)) ≤
      G * (C * EB * (R * δ)⁻¹ + σ * (2 + τ) * (M * δ)) := by
  have h1 : δ⁻¹ * (C * R⁻¹ * Ie) ≤ C * EB * (R * δ)⁻¹ := by
    have h1' : C * R⁻¹ * Ie ≤ C * R⁻¹ * EB := mul_le_mul_of_nonneg_left hIe (by positivity)
    calc δ⁻¹ * (C * R⁻¹ * Ie) ≤ δ⁻¹ * (C * R⁻¹ * EB) :=
          mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = C * EB * (R * δ)⁻¹ := by rw [mul_inv]; ring
  have h2 : δ⁻¹ * (σ * (2 + τ) * Vb) ≤ σ * (2 + τ) * (M * δ) := by
    have h2' : δ⁻¹ * Vb ≤ M * δ := by
      rw [inv_mul_le_iff₀ hδ]
      nlinarith
    calc δ⁻¹ * (σ * (2 + τ) * Vb) = σ * (2 + τ) * (δ⁻¹ * Vb) := by ring
      _ ≤ σ * (2 + τ) * (M * δ) := mul_le_mul_of_nonneg_left h2' (by positivity)
  calc δ⁻¹ * (G * (C * R⁻¹ * Ie + σ * (2 + τ) * Vb))
      = G * (δ⁻¹ * (C * R⁻¹ * Ie) + δ⁻¹ * (σ * (2 + τ) * Vb)) := by ring
    _ ≤ G * (C * EB * (R * δ)⁻¹ + σ * (2 + τ) * (M * δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hG

/-- The cutoff remainder `∫_{Q₁} (1 - ψ(t)) ⟪ζ(y), F⟫` is bounded by the flux mass of `Q₁` off
the slab `|t| < 1/4`. -/
private theorem afc_abs_setIntegral_one_sub_cutoff_flux_le {v : Space (m + 1) → ℝ}
    (hvL : LocallyLipschitz v) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {ζ : Space m → Space m}
    {Zb : ℝ} (hZb : ∀ y, ‖ζ y‖ ≤ Zb) {ψ : ℝ → ℝ} (hψ01 : ∀ t, ψ t ∈ Icc (0 : ℝ) 1)
    (hψ1 : ∀ t, |t| ≤ 1 / 4 → ψ t = 1) :
    |∫ z in tiltCylinder (verticalDirection m) 1, (1 - ψ (z (Fin.last m))) *
        inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))| ≤
      Zb * ∫ z in tiltCylinder (verticalDirection m) 1 ∩ {z | 1 / 4 ≤ |z (Fin.last m)|},
        δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖ := by
  have hAm : MeasurableSet {z : Space (m + 1) | 1 / 4 ≤ |z (Fin.last m)|} :=
    (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet
  have hmmI := integrableOn_flux_mass hvL hδ hR
    (isOpen_tiltCylinder (verticalDirection m) 1).measurableSet
    (isBounded_tiltCylinder (norm_verticalDirection m) 1)
  rw [← integral_const_mul, ← setIntegral_indicator hAm, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hmmI.const_mul Zb).indicator hAm)
    (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : z ∈ {z : Space (m + 1) | 1 / 4 ≤ |z (Fin.last m)|}
  · rw [indicator_of_mem hz]
    have h1 : |1 - ψ (z (Fin.last m))| ≤ 1 := by
      obtain ⟨h0, h1⟩ := hψ01 (z (Fin.last m))
      rw [abs_le]
      constructor <;> linarith
    have h2 : |inner ℝ (ζ (horizontal z))
        ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))| ≤
        Zb * (δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) :=
      (abs_inner_flux_le_mass hδ hR (ζ (horizontal z)) z).trans
        (mul_le_mul_of_nonneg_right (hZb _) (by positivity))
    calc |1 - ψ (z (Fin.last m))| * |inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))|
        ≤ 1 * (Zb * (δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖)) :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = Zb * (δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) :=
          one_mul _
  · have hz' : |z (Fin.last m)| < 1 / 4 := not_le.mp hz
    rw [indicator_of_notMem hz, hψ1 _ hz'.le, sub_self, abs_zero, zero_mul]

/-- **The decomposition at one index.** With `Ξ = ψ(t) ζ(y)`, the vertically integrated flux
pairing plus `σ ∫ ⟪ζ, ∇f⟫` (for `f = (h - a)/δ`) equals `I + II - δ⁻¹ E`, where `I` is the cutoff
remainder on `Q₁`, `II` the pairing of `Ξ` with the calibrated flux defect, and `E` the column
error of the cutoff integral of `Φ(v)`; each of the three is then estimated. -/
private theorem afc_abs_flux_add_height_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : Space (m + 1)) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {ζ : Space m → Space m} (hζ : ContDiff ℝ 1 ζ)
    (hζs : tsupport ζ ⊆ ball (0 : Space m) (3 / 4)) {Zb : ℝ} (hZb : ∀ y, ‖ζ y‖ ≤ Zb)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψ01 : ∀ t, ψ t ∈ Icc (0 : ℝ) 1) (hψ1 : ∀ t, |t| ≤ 1 / 4 → ψ t = 1)
    (hψ0 : ∀ t, 1 / 2 ≤ |t| → ψ t = 0) {hh : Space m → ℝ} {L : ℝ≥0}
    (hhL : LipschitzWith L hh) (a : ℝ) {EE : ℝ}
    (hE : |(∫ z, ψ (z (Fin.last m)) *
          fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ (horizontal z) *
          phasePrimitive f (zeroExtension g u (c + R • Q z))) +
        phasePrimitive f 1 *
          ∫ y, fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y * hh y| ≤ EE)
    {lam : ℝ} (hlam : 0 < lam) :
    |(∫ z in tiltCylinder (verticalDirection m) 1, inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z) •
            horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z))) +
        phasePrimitive f 1 * ∫ y, inner ℝ (ζ y) (gradient (normalizedHeight hh a δ) y)| ≤
      Zb * (∫ z in tiltCylinder (verticalDirection m) 1 ∩ {z | 1 / 4 ≤ |z (Fin.last m)|},
          δ⁻¹ * R⁻¹ * |verticalDerivative (fun z ↦ zeroExtension g u (c + R • Q z)) z| *
            ‖horizontal (gradient (fun z ↦ zeroExtension g u (c + R • Q z)) z)‖) +
        (lam * Zb ^ 2 * (∫ z in horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
            (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1,
            phaseCalibrationDefect f R (fun z ↦ zeroExtension g u (c + R • Q z)) z) +
          (2 * lam)⁻¹ * δ⁻¹ ^ 2 * ∫ z in tiltCylinder (verticalDirection m) 2,
            diffuseTiltDensity R (fun z ↦ zeroExtension g u (c + R • Q z))
              (verticalDirection m) z) +
        δ⁻¹ * EE := by
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (c + R • Q z) with hv
  set Z : Set (Space (m + 1)) := horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
    (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1
  set Ξ : Space (m + 1) → Space m := fun z ↦ ψ (z (Fin.last m)) • ζ (horizontal z)
  have hvL : LipschitzWith (⟨κ, h.kappa_pos.le⟩ * Real.toNNReal R) v :=
    hr.lipschitzWith_rescaled h c hR.le Q
  obtain ⟨KW, hWL⟩ := hr.exists_lipschitzWith_phasePrimitive_rescaled h c hR.le Q
  have hcζ : HasCompactSupport ζ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζs)
  have hQ1m : MeasurableSet (tiltCylinder (verticalDirection m) 1) :=
    (isOpen_tiltCylinder _ _).measurableSet
  have hQ1b : Bornology.IsBounded (tiltCylinder (verticalDirection m) 1) :=
    isBounded_tiltCylinder (norm_verticalDirection m) 1
  have hZm : MeasurableSet Z :=
    ((isOpen_ball.preimage continuous_horizontal).inter
      (isOpen_Ioo.preimage continuous_last)).measurableSet
  have hZQ1 : Z ⊆ tiltCylinder (verticalDirection m) 1 := afc_slab_subset_tiltCylinder_one
  have hZQ2 : Z ⊆ tiltCylinder (verticalDirection m) 2 :=
    hZQ1.trans (tiltCylinder_mono _ (by norm_num))
  have hZb' : Bornology.IsBounded Z := hQ1b.subset hZQ1
  have hζm : Measurable fun z : Space (m + 1) ↦ ζ (horizontal z) :=
    hζ.continuous.measurable.comp continuous_horizontal.measurable
  have hΞm : Measurable Ξ :=
    ((hψ.continuous.comp continuous_last).smul
      (hζ.continuous.comp continuous_horizontal)).measurable
  have hΞM : ∀ z, ‖Ξ z‖ ≤ Zb := by
    intro z
    obtain ⟨h0, h1⟩ := hψ01 (z (Fin.last m))
    show ‖ψ (z (Fin.last m)) • ζ (horizontal z)‖ ≤ Zb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hZb _)
  have hΞZ : ∀ z ∉ Z, Ξ z = 0 := by
    intro z hz
    show ψ (z (Fin.last m)) • ζ (horizontal z) = 0
    by_cases h1 : horizontal z ∈ ball (0 : Space m) (3 / 4)
    · have h2 : z (Fin.last m) ∉ Ioo (-1 : ℝ) 1 := fun h2 ↦ hz ⟨h1, h2⟩
      have h3 : 1 / 2 ≤ |z (Fin.last m)| := by
        by_contra hlt
        have hlt' : |z (Fin.last m)| < 1 / 2 := not_le.mp hlt
        exact h2 ⟨by linarith [neg_abs_le (z (Fin.last m))],
          by linarith [le_abs_self (z (Fin.last m))]⟩
      rw [hψ0 _ h3, zero_smul]
    · have h2 : horizontal z ∉ tsupport ζ := fun h' ↦ h1 (hζs h')
      rw [image_eq_zero_of_notMem_tsupport h2, smul_zero]
  -- integrability
  have hiΞV : Integrable (fun z ↦ inner ℝ (Ξ z)
      ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) :=
    hr.integrable_inner_flux_of_bounded h c hR Q δ hΞm hΞM hZb' hΞZ
  have hiΞW : Integrable (fun z ↦ inner ℝ (Ξ z) (horizontal
      (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))) :=
    hr.integrable_inner_primitiveFlux_of_bounded h c hR Q hΞm hΞM hZb' hΞZ
  have hmmI : IntegrableOn (fun z ↦ δ⁻¹ * R⁻¹ * |verticalDerivative v z| *
      ‖horizontal (gradient v z)‖) (tiltCylinder (verticalDirection m) 1) :=
    integrableOn_flux_mass hvL.locallyLipschitz hδ hR hQ1m hQ1b
  have hiQ1 : IntegrableOn (fun z ↦ inner ℝ (ζ (horizontal z))
      ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)))
      (tiltCylinder (verticalDirection m) 1) :=
    (hmmI.const_mul Zb).mono' (hζm.inner (ha6_measurable_flux_vector R δ v)).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs]
        exact (abs_inner_flux_le_mass hδ hR (ζ (horizontal z)) z).trans
          (mul_le_mul_of_nonneg_right (hZb _) (by positivity)))
  -- step (i): the cutoff remainder
  have h1 : (∫ z in tiltCylinder (verticalDirection m) 1, (1 - ψ (z (Fin.last m))) *
        inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) =
      (∫ z in tiltCylinder (verticalDirection m) 1, inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) -
        ∫ z, inner ℝ (Ξ z)
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) := by
    have hwhole : (∫ z, inner ℝ (Ξ z)
        ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) =
        ∫ z in tiltCylinder (verticalDirection m) 1, inner ℝ (Ξ z)
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_).symm
      rw [hΞZ z fun hz' ↦ hz (hZQ1 hz'), inner_zero_left]
    rw [hwhole, ← integral_sub hiQ1 hiΞV.integrableOn]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    show (1 - ψ (z (Fin.last m))) * inner ℝ (ζ (horizontal z))
        ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) =
      inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) -
        inner ℝ (ψ (z (Fin.last m)) • ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))
    rw [real_inner_smul_left]
    ring
  -- step (ii): the calibrated flux defect
  have h2 : (∫ z, inner ℝ (Ξ z)
        ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) =
      (∫ z, inner ℝ (Ξ z)
        (((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) -
          δ⁻¹ • horizontal
            (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))) +
        δ⁻¹ * ∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (horizontal
          (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z)) := by
    have hsplit : ∀ z, inner ℝ (Ξ z)
        (((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) -
          δ⁻¹ • horizontal
            (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z)) =
        inner ℝ (Ξ z) ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) -
          δ⁻¹ * inner ℝ (Ξ z) (horizontal
            (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z)) := by
      intro z
      rw [inner_sub_right, real_inner_smul_right (Ξ z) _ δ⁻¹]
    have hsplit' : ∀ z, inner ℝ (Ξ z) (horizontal
          (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z)) =
        ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (horizontal
          (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z)) :=
      fun z ↦ real_inner_smul_left _ _ _
    simp_rw [hsplit]
    rw [integral_sub hiΞV (hiΞW.const_mul δ⁻¹), integral_const_mul]
    simp_rw [hsplit']
    ring
  -- step (iii): integration by parts for `Φ(v)`
  have h3 : (∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (horizontal
        (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))) =
      -∫ z, ψ (z (Fin.last m)) *
        fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ (horizontal z) *
          phasePrimitive f (zeroExtension g u (c + R • Q z)) :=
    integral_mul_inner_horizontal_gradient_eq_neg hWL hζ hcζ hψ hψc
  -- step (iv): integration by parts for the height
  have h4 : (∫ y, inner ℝ (ζ y) (gradient (normalizedHeight hh a δ) y)) =
      -(δ⁻¹ * ∫ y, fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y * hh y) := by
    simp_rw [gradient_normalizedHeight, real_inner_smul_right]
    rw [integral_const_mul, integral_inner_gradient_eq_neg_integral_fieldDivergence_mul hhL hζ hcζ,
      mul_neg]
  -- the three estimates
  have h5 := hr.abs_integral_flux_sub_primitiveFlux_le h c hR Q hδ hΞm hΞM hZm hZQ2 hΞZ hlam
  rw [← hv] at h5
  have h6 := afc_abs_setIntegral_one_sub_cutoff_flux_le hvL.locallyLipschitz hR hδ hZb hψ01 hψ1
  have hEE : |δ⁻¹ * ((∫ z, ψ (z (Fin.last m)) *
          fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ (horizontal z) *
          phasePrimitive f (zeroExtension g u (c + R • Q z))) +
        phasePrimitive f 1 *
          ∫ y, fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y * hh y)| ≤ δ⁻¹ * EE := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hδ)]
    exact mul_le_mul_of_nonneg_left hE (inv_pos.mpr hδ).le
  have key : (∫ z in tiltCylinder (verticalDirection m) 1, inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) +
        phasePrimitive f 1 * ∫ y, inner ℝ (ζ y) (gradient (normalizedHeight hh a δ) y) =
      (∫ z in tiltCylinder (verticalDirection m) 1, (1 - ψ (z (Fin.last m))) *
        inner ℝ (ζ (horizontal z))
          ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))) +
      (∫ z, inner ℝ (Ξ z)
        (((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z)) -
          δ⁻¹ • horizontal
            (gradient (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) z))) -
      δ⁻¹ * ((∫ z, ψ (z (Fin.last m)) *
          fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ (horizontal z) *
          phasePrimitive f (zeroExtension g u (c + R • Q z))) +
        phasePrimitive f 1 *
          ∫ y, fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y * hh y) := by
    linear_combination -h1 + h2 + δ⁻¹ * h3 + phasePrimitive f 1 * h4
  rw [key]
  obtain ⟨h5a, h5b⟩ := abs_le.mp h5
  obtain ⟨h6a, h6b⟩ := abs_le.mp h6
  obtain ⟨hEa, hEb⟩ := abs_le.mp hEE
  rw [abs_le]
  constructor <;> linarith

/-! ## The flux identification -/

/-- **(C⋆) for `C¹` test fields.** Along height-limit data of an aligned sequence,
`∫_{Q₁} ⟪ζ(y), F_j⟫ + σ ∫ ⟪ζ, ∇f_j⟫ → 0` for every `C¹` field `ζ` supported in `B_{3/4}`. -/
theorem RigidityHypotheses.tendsto_verticalFlux_add_of_contDiff
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0} (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hρ : 3 / 4 < ρ) (hρr₀ : ρ + |r₀| < 2) (hτ : 0 < τ) (hs₁ : 0 < s₁) (hs₂ : s₂ < 1)
    {x : ℕ → Space (m + 1)} {R : ℕ → ℝ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {δ : ℕ → ℝ} {e : Space (m + 1)} (hal : IsAlignedSequence g u x R Q δ e)
    {φ : ℕ → ℕ} {σl a : ℕ → ℝ} {H : Space m → ℝ}
    (hlim : IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H)
    {ζ : Space m → Space m} (hζ : ContDiff ℝ 1 ζ)
    (hζs : tsupport ζ ⊆ ball (0 : Space m) (3 / 4)) :
    Tendsto (fun j ↦ (∫ z in tiltCylinder (verticalDirection m) 1,
        inner ℝ (ζ (horizontal z))
          (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z) •
            horizontal (gradient (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z))) +
      phasePrimitive f 1 * ∫ y, inner ℝ (ζ y)
        (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y))
      atTop (𝓝 0) := by
  obtain ⟨-, hR, hRt, hδ, hδ0, hRδ, htilt, he, hloc, hQ⟩ := id hal
  have hφ : StrictMono φ := hlim.1
  have hσl : ∀ j, σl j ∈ Icc s₁ s₂ := hlim.2.1
  have hσ0 : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  -- the vertical cutoff `ψ₀`, equal to `1` on `[-1/4, 1/4]` and supported in `[-1/2, 1/2]`
  let ψ₀ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hψ01 : ∀ t, ψ₀ t ∈ Icc (0 : ℝ) 1 := fun t ↦ ⟨ψ₀.nonneg, ψ₀.le_one⟩
  have hψ1 : ∀ t : ℝ, |t| ≤ 1 / 4 → ψ₀ t = 1 := fun t ht ↦
    ψ₀.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact ht)
  have hψ0 : ∀ t : ℝ, 1 / 2 ≤ |t| → ψ₀ t = 0 := fun t ht ↦
    ψ₀.zero_of_le_dist (by rw [dist_zero_right, Real.norm_eq_abs]; exact ht)
  -- the divergence of the test field
  have hcζ : HasCompactSupport ζ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζs)
  have hdvc : Continuous (fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ) :=
    fieldDivergence_continuous _ hζ
  have hdv0 : ∀ y ∉ ball (0 : Space m) (3 / 4),
      fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y = 0 := fun y hy ↦
    fieldDivergence_zero_of_notMem_tsupport _ ζ fun h' ↦ hy (hζs h')
  have hdvi : (∫ y, fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y) = 0 :=
    integral_fieldDivergence_eq_zero _ hζ hcζ
  have hcdv : HasCompactSupport (fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ) :=
    hcζ.mono' fun y hy ↦ by
      by_contra hn
      exact hy (fieldDivergence_zero_of_notMem_tsupport _ ζ hn)
  -- constants fixed before any index
  obtain ⟨Z0, hZ0⟩ := hζ.continuous.bounded_above_of_compact_support hcζ
  obtain ⟨G0, hG0⟩ := hdvc.bounded_above_of_compact_support hcdv
  have hZb : ∀ y, ‖ζ y‖ ≤ max Z0 0 := fun y ↦ (hZ0 y).trans (le_max_left _ _)
  have hG : ∀ y, |fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ y| ≤ max G0 0 :=
    fun y ↦ by
      have := hG0 y
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
  have hG0' : 0 ≤ max G0 0 := le_max_right _ _
  obtain ⟨C, hC0, hC⟩ := hr.exists_abs_integral_cutoff_phasePrimitive_add_height_le h hs₂
  -- the eventual inputs
  have hT3 := (hr.tendsto_setIntegral_phaseCalibrationDefect_of_aligned h hsharp x hR hRt he hloc
    hQ (r := 3 / 4) (by norm_num)).comp hφ.tendsto_atTop
  have hoff := (hr.tendsto_flux_mass_offPlane_of_aligned h hsharp x hR hRt hδ hδ0 hRδ htilt he
    hloc hQ (r := 1) (c := 1 / 4) one_pos (by norm_num) (by norm_num)).comp hφ.tendsto_atTop
  have hcol := hr.eventually_columnStructure_of_alignedHeightLimit h hsharp hτ hs₁ hs₂ hal hlim
    (η := 1 / 4) (by norm_num)
  have hbad := hφ.tendsto_atTop.eventually
    (hr.eventually_volume_real_ball_sdiff_verticalGoodSet_le h hsharp hℓ hb0 hb1 (by linarith)
      hρr₀ hal)
  have hen := hφ.tendsto_atTop.eventually
    (hr.eventually_setIntegral_closedBall_two_energy_le h hsharp hal)
  -- the column error rate
  have hBt : Tendsto (fun j ↦ max G0 0 *
      (C * (phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1) *
          (R (φ j) * δ (φ j))⁻¹ +
        phasePrimitive f 1 * (2 + τ) *
          ((5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) / ℓ * 2 ^ m * δ (φ j))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j ↦ (R (φ j) * δ (φ j))⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp hRδ).comp hφ.tendsto_atTop
    have h2 : Tendsto (fun j ↦ δ (φ j)) atTop (𝓝 0) := hδ0.comp hφ.tendsto_atTop
    have h3 := ((h1.const_mul
      (C * (phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1))).add
      ((h2.const_mul ((5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) / ℓ * 2 ^ m)).const_mul
        (phasePrimitive f 1 * (2 + τ)))).const_mul (max G0 0)
    simpa using h3
  -- the estimate at each index
  have hmain : ∀ᶠ j in atTop, ∀ lam : ℝ, 0 < lam →
      |(∫ z in tiltCylinder (verticalDirection m) 1,
        inner ℝ (ζ (horizontal z))
          (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z) •
            horizontal (gradient (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z))) +
        phasePrimitive f 1 * ∫ y, inner ℝ (ζ y)
          (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y)| ≤
      max Z0 0 * (∫ z in tiltCylinder (verticalDirection m) 1 ∩ {z | 1 / 4 ≤ |z (Fin.last m)|},
          (δ (φ j))⁻¹ * (R (φ j))⁻¹ *
            |verticalDerivative (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z| *
            ‖horizontal (gradient (fun z ↦ zeroExtension g u
              (x (φ j) + R (φ j) • Q (φ j) z)) z)‖) +
        (lam * max Z0 0 ^ 2 * (∫ z in horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
            (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1,
            phaseCalibrationDefect f (R (φ j))
              (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z) +
          (2 * lam)⁻¹ * 2 ^ m) +
        max G0 0 *
          (C * (phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1) *
              (R (φ j) * δ (φ j))⁻¹ +
            phasePrimitive f 1 * (2 + τ) *
              ((5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) / ℓ * 2 ^ m * δ (φ j))) := by
    filter_upwards [hcol, hbad, hen] with j hcolj hbadj henj
    intro lam hlam
    have hRj := hR (φ j)
    have hδj := hδ (φ j)
    have hvL := hr.lipschitzWith_rescaled h (x (φ j)) hRj.le (Q (φ j))
    have hval : ∀ z, zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z) ∈ Icc (0 : ℝ) 1 :=
      fun z ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
    set D : Set (Space m) := verticalGoodSet (R (φ j))
      (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) ℓ r₀ b ρ
    set ht : Space m → ℝ := extendedHeight D L τ s₁ s₂
      (fun s y ↦ slabLevelHeight (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
        τ s y) (σl j)
    have hDm : MeasurableSet D := (isOpen_verticalGoodSet hRj hvL ℓ r₀ b ρ).measurableSet
    have htL : LipschitzWith L ht := extendedHeight_lipschitzWith_of_any _ _ _ _ _ _ _
    have htτ : ∀ y, |ht y| ≤ τ := fun y ↦
      abs_le.mpr (LevelGraphFamily.extendedHeight_mem_Icc hτ.le _ _ _ _ _ _ y)
    -- (III) the column comparison (T8) on the good columns of (T6)
    have hE := hC (x (φ j)) (R (φ j)) hRj (Q (φ j)) (σl j) (hs₁.le.trans (hσl j).1) (hσl j).2
      ψ₀ ψ₀.continuous.measurable hψ01 hψ1 hψ0 D hDm ht htL.continuous τ hτ.le htτ
      (fun y hy ↦ ⟨(hcolj y hy.1).1.le, (hcolj y hy.1).2⟩)
      (fieldDivergence (EuclideanSpace.basisFun (Fin m) ℝ) ζ) hdvc.measurable (max G0 0) hG
      hdv0 hdvi
    have hidx := afc_abs_flux_add_height_le hr h (x (φ j)) hRj hδj (Q (φ j)) hζ hζs hZb
      ψ₀.contDiff ψ₀.hasCompactSupport hψ01 hψ1 hψ0 htL (a j) hE hlam
    -- the tilt normalization
    have hTq : (∫ z in tiltCylinder (verticalDirection m) 2,
        diffuseTiltDensity (R (φ j))
          (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) (verticalDirection m) z) =
        2 ^ m * δ (φ j) ^ 2 := by
      have h1 := htilt (φ j)
      unfold cylinderTilt at h1
      rw [← h1, ← mul_assoc, zpow_neg, zpow_natCast,
        mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
    -- the energy on the slab
    have hIe : (∫ z in horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
          (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1,
          rescaledPhaseEnergyDensity f (R (φ j))
            (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z) ≤
        phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1 := by
      have hZcB : horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
          (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1 ⊆
            closedBall (0 : Space (m + 1)) 2 := by
        have h1 := ha6_tiltCylinder_subset_closedBall (m := m) 1
        rw [mul_one] at h1
        exact afc_slab_subset_tiltCylinder_one.trans h1
      refine (setIntegral_mono_set ?_ (Eventually.of_forall ?_)
        (Eventually.of_forall hZcB)).trans henj
      · exact h.integrableOn_rescaledPhaseEnergy hvL.locallyLipschitz hval (R (φ j))
          (isCompact_closedBall _ 2)
      · exact hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
    -- the bad columns
    have hVb : volume.real (ball (0 : Space m) (3 / 4) \ D) ≤
        (5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) / ℓ * 2 ^ m * δ (φ j) ^ 2 := by
      have hfin : volume (ball (0 : Space m) ρ \ D) ≠ ⊤ :=
        ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
      refine (measureReal_mono (sdiff_subset_sdiff_left (ball_subset_ball hρ.le)) hfin).trans ?_
      refine hbadj.trans (le_of_eq ?_)
      ring
    have herr := afc_inv_mul_error_le hδj hRj hG0' hC0 hσ0.le hτ.le hIe hVb
    have hδ2 : (2 * lam)⁻¹ * (δ (φ j))⁻¹ ^ 2 * (2 ^ m * δ (φ j) ^ 2) = (2 * lam)⁻¹ * 2 ^ m := by
      field_simp
    refine hidx.trans ?_
    rw [hTq, hδ2]
    linarith
  -- conclusion
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlam : 0 < 2 ^ (m + 1) / ε := by positivity
  have hlam2 : (2 * (2 ^ (m + 1) / ε))⁻¹ * 2 ^ m = ε / 4 := by
    rw [pow_succ]
    field_simp
    ring
  have hS := ((hoff.const_mul (max Z0 0)).add
    (hT3.const_mul (2 ^ (m + 1) / ε * max Z0 0 ^ 2))).add hBt
  rw [mul_zero, mul_zero, add_zero, add_zero] at hS
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hS.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hmain
  refine ⟨max N₁ N₂, fun j hj ↦ ?_⟩
  have h1 := hN₁ j (le_of_max_le_left hj)
  have h2 := hN₂ j (le_of_max_le_right hj) (2 ^ (m + 1) / ε) hlam
  simp only [Function.comp_apply] at h1
  rw [Real.dist_eq, sub_zero]
  linarith

end SerrinEpigraph
