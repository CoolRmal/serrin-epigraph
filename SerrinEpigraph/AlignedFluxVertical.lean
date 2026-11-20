module

public import SerrinEpigraph.AlignedFluxOffPlane
public import SerrinEpigraph.AlignedHeightDecomposition

/-!
# Reduction of the flux identification (C) to its vertically integrated form

The input (C) `HasAlignedFluxIdentification` tests the normalized flux
`F_j = ε ∂ₜ v_j ∇_y v_j / δ_j` against products `ψ(t) ζ(y)`. Because `F_j` has bounded mass on
`Q₁` (`|F| ≤ e_ε/2 + ε |∇_y v|²/(2δ²)`, sharp ball energy and the tilt normalization) and
vanishing mass off the plane (`tendsto_flux_mass_offPlane_of_aligned`), `ψ(t)` may be replaced by
`ψ(0)`: (C) follows from the *vertically integrated* identification
`HasAlignedVerticalFluxIdentification`,
`∫_{Q₁} ⟪ζ(y), F_j⟫ + σ ∫ ⟪ζ, ∇f_j⟫ → 0` for continuous `ζ` supported in `B_{3/4}`
(`RigidityHypotheses.hasAlignedFluxIdentification_of_vertical`). No parameter conditions are
added by this reduction.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **(C⋆) The vertically integrated flux identification.** For height-limit data along an
aligned sequence, `∫_{Q₁} ⟪ζ(y), F_j⟫ + σ ∫ ⟪ζ, ∇f_j⟫ → 0` for continuous `ζ` supported in
`B_{3/4}`. -/
def HasAlignedVerticalFluxIdentification (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ : ℝ)
    (ℓ r₀ b ρ τ s₁ s₂ : ℝ) (L : ℝ≥0) (c K : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
    ∀ (φ : ℕ → ℕ) (σl a : ℕ → ℝ) (H : Space m → ℝ),
      IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H →
      ∀ ζ : Space m → Space m, Continuous ζ → tsupport ζ ⊆ ball (0 : Space m) (3 / 4) →
      Tendsto (fun j ↦ (∫ z in tiltCylinder (verticalDirection m) 1,
          inner ℝ (ζ (horizontal z))
            (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
                (x (φ j) + R (φ j) • Q (φ j) z)) z) •
              horizontal (gradient (fun z ↦ zeroExtension g u
                (x (φ j) + R (φ j) • Q (φ j) z)) z))) +
        σ * ∫ y, inner ℝ (ζ y)
          (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y))
        atTop (𝓝 0)

/-! ## Per-index estimates -/

section PerIndex

variable {v : Space (m + 1) → ℝ} {δ R : ℝ}

theorem abs_vd_mul_norm_horizontal_le (v : Space (m + 1) → ℝ) (z : Space (m + 1)) :
    |verticalDerivative v z| * ‖horizontal (gradient v z)‖ ≤ ‖gradient v z‖ ^ 2 := by
  have h1 := verticalDerivative_sq_le_gradient v z
  have h2 := horizontal_norm_sq_le_gradient v z
  nlinarith [abs_nonneg (verticalDerivative v z), norm_nonneg (horizontal (gradient v z)),
    sq_abs (verticalDerivative v z)]

theorem integrableOn_flux_mass (hvL : LocallyLipschitz v) (hδ : 0 < δ) (hR : 0 < R)
    {S : Set (Space (m + 1))} (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) :
    IntegrableOn (fun z ↦ δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) S :=
  integrableOn_of_abs_le_mul_gradient_sq
    (F := fun z ↦ δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) hvL
    ((measurable_const.mul (continuous_abs.measurable.comp (measurable_verticalDerivative v))).mul
      (continuous_horizontal.measurable.comp (measurable_gradient v)).norm) hS hSb
    (C := δ⁻¹ * R⁻¹) fun z _ ↦ by
      show |δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖| ≤
        δ⁻¹ * R⁻¹ * ‖gradient v z‖ ^ 2
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le)
        (inv_nonneg.mpr hR.le)) (abs_nonneg _)) (norm_nonneg _))]
      calc δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖
          = δ⁻¹ * R⁻¹ * (|verticalDerivative v z| * ‖horizontal (gradient v z)‖) := by ring
        _ ≤ δ⁻¹ * R⁻¹ * ‖gradient v z‖ ^ 2 := by
            gcongr
            exact abs_vd_mul_norm_horizontal_le v z

theorem abs_inner_flux_le_mass (hδ : 0 < δ) (hR : 0 < R) (ζ : Space m) (z : Space (m + 1)) :
    |inner ℝ ζ ((δ⁻¹ * R⁻¹ * verticalDerivative v z) • horizontal (gradient v z))| ≤
      ‖ζ‖ * (δ⁻¹ * R⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖) := by
  refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hδ),
    abs_of_pos (inv_pos.mpr hR)]

end PerIndex

/-! ## The reduction -/

/-- **(C) from (C⋆).** -/
theorem RigidityHypotheses.hasAlignedFluxIdentification_of_vertical
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {σ ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0}
    (hCs : HasAlignedVerticalFluxIdentification g u σ ℓ r₀ b ρ τ s₁ s₂ L c K) :
    HasAlignedFluxIdentification g u σ ℓ r₀ b ρ τ s₁ s₂ L c K := by
  intro x R Q δ e hal φ σl a H hlim ζ hζ hζs ψ hψ hψs
  have hCs' := hCs x R Q δ e hal φ σl a H hlim ζ hζ hζs
  obtain ⟨hx, hR, hRt, hδ, hδ0, hRδ, htilt, he, hloc, hQ⟩ := hal
  have hφ : StrictMono φ := hlim.1
  set Q1 : Set (Space (m + 1)) := tiltCylinder (verticalDirection m) 1 with hQ1
  have hQ1m : MeasurableSet Q1 := (isOpen_tiltCylinder _ _).measurableSet
  have hQ1b : Bornology.IsBounded Q1 := isBounded_tiltCylinder (norm_verticalDirection m) 1
  have hQ12 : Q1 ⊆ closedBall (0 : Space (m + 1)) 2 := by
    have h1 := ha6_tiltCylinder_subset_closedBall (m := m) 1
    rwa [mul_one] at h1
  have hQ1Q2 : Q1 ⊆ tiltCylinder (verticalDirection m) 2 := tiltCylinder_mono _ (by norm_num)
  have hcζ : HasCompactSupport ζ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζs)
  have hcψ : HasCompactSupport ψ := isCompact_of_isClosed_isBounded (isClosed_tsupport _)
    ((Metric.isBounded_Ioo _ _).subset hψs)
  obtain ⟨Z0, hZ0⟩ := hζ.bounded_above_of_compact_support hcζ
  obtain ⟨Ψ0, hΨ0⟩ := hψ.bounded_above_of_compact_support hcψ
  set Z : ℝ := max Z0 0 with hZ
  set Ψ : ℝ := max Ψ0 0 with hΨ
  have hZ0' : 0 ≤ Z := le_max_right _ _
  have hΨ0' : 0 ≤ Ψ := le_max_right _ _
  have hZb : ∀ y, ‖ζ y‖ ≤ Z := fun y ↦ (hZ0 y).trans (le_max_left _ _)
  have hΨb : ∀ t, |ψ t| ≤ Ψ := fun t ↦ by
    have := hΨ0 t
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨-, hE2, -⟩ := hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp x hR
    he hloc (r := 2) two_pos
  set EB : ℝ := phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1
    with hEB
  have hEev : ∀ᶠ j in atTop, (∫ z in closedBall (0 : Space (m + 1)) 2,
      rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) ≤
        EB := by
    have hlt : phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) < EB := by
      rw [hEB]
      linarith
    filter_upwards [hE2.eventually_lt_const hlt] with j hj
    rw [setIntegral_closedBall_rescaled_isometry f (zeroExtension g u) (x j) (hR j) (Q j) 2]
    exact hj.le
  set MB : ℝ := EB / 2 + 2 ^ m / 2 with hMB
  have hMB0 : 0 ≤ MB := by
    rw [hMB, hEB]
    have := hr.phasePrimitive_one_pos h
    have : 0 ≤ volume.real (closedBall (0 : Space m) 1) := measureReal_nonneg
    positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (4 * (Z * MB + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨c₀, hc₀, hψc⟩ := Metric.continuousAt_iff.mp hψ.continuousAt ε' hε'0
  have hoff := (hr.tendsto_flux_mass_offPlane_of_aligned h hsharp x hR hRt hδ hδ0 hRδ htilt he
    hloc hQ (r := 1) one_pos (by norm_num) hc₀).comp hφ.tendsto_atTop
  have hoff' := (hoff.const_mul (2 * Ψ * Z)).eventually_lt_const
    (show 2 * Ψ * Z * 0 < ε / 4 by rw [mul_zero]; positivity)
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hCs') (ε / (4 * (|ψ 0| + 1))) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((hφ.tendsto_atTop.eventually hEev).and hoff')
  refine ⟨max N₁ N₂, fun j hj ↦ ?_⟩
  have hj1 := hN₁ j (le_of_max_le_left hj)
  obtain ⟨hjE, hjoff⟩ := hN₂ j (le_of_max_le_right hj)
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)
    with hvdef
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRj := hR (φ j)
  have hδj := hδ (φ j)
  set mm : Space (m + 1) → ℝ := fun z ↦
    (δ (φ j))⁻¹ * (R (φ j))⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖ with hmm
  have hmm0 : ∀ z, 0 ≤ mm z := fun z ↦ by positivity
  have hmmI : IntegrableOn mm Q1 := integrableOn_flux_mass hvL hδj hRj hQ1m hQ1b
  have hmass : (∫ z in Q1, mm z) ≤ MB := by
    have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f (R (φ j)) v z :=
      hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
    have hiE : IntegrableOn (rescaledPhaseEnergyDensity f (R (φ j)) v)
        (closedBall (0 : Space (m + 1)) 2) :=
      h.integrableOn_rescaledPhaseEnergy hvL hval (R (φ j)) (isCompact_closedBall _ 2)
    have hiT : IntegrableOn (diffuseTiltDensity (R (φ j)) v (verticalDirection m))
        (tiltCylinder (verticalDirection m) 2) := by
      refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_
        (isOpen_tiltCylinder _ _).measurableSet
        (isBounded_tiltCylinder (norm_verticalDirection m) 2) (C := (R (φ j))⁻¹) fun z _ ↦ ?_
      · unfold diffuseTiltDensity
        exact (((measurable_gradient v).norm.pow_const 2).sub
          (((measurable_gradient v).inner measurable_const).pow_const 2)).div_const _
      · rw [diffuseTiltDensity_vertical_eq, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (horizontal_norm_sq_le_gradient v z)
          (inv_nonneg.mpr hRj.le)
    have hTq : (∫ z in tiltCylinder (verticalDirection m) 2,
        diffuseTiltDensity (R (φ j)) v (verticalDirection m) z) = 2 ^ m * δ (φ j) ^ 2 := by
      have h1 := htilt (φ j)
      unfold cylinderTilt at h1
      rw [← h1, ← mul_assoc, zpow_neg, zpow_natCast,
        mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
    have hpt : ∀ z, mm z ≤ (1 / 2) * rescaledPhaseEnergyDensity f (R (φ j)) v z +
        (1 / 2) * ((δ (φ j))⁻¹ ^ 2 * diffuseTiltDensity (R (φ j)) v (verticalDirection m) z) := by
      intro z
      have hN := hr.rescaled_isometry_energy_sub_vertical_sq_nonneg h (x (φ j)) hRj (Q (φ j)) z
      rw [diffuseTiltDensity_vertical_eq]
      have hR0 : 0 ≤ (R (φ j))⁻¹ := inv_nonneg.mpr hRj.le
      have key : 0 ≤ (R (φ j))⁻¹ * (|verticalDerivative v z| -
          (δ (φ j))⁻¹ * ‖horizontal (gradient v z)‖) ^ 2 := mul_nonneg hR0 (sq_nonneg _)
      have hp2 : verticalDerivative v z ^ 2 = |verticalDerivative v z| ^ 2 := (sq_abs _).symm
      change 0 ≤ rescaledPhaseEnergyDensity f (R (φ j)) v z -
        (R (φ j))⁻¹ * verticalDerivative v z ^ 2 at hN
      rw [hp2] at hN
      simp only [hmm]
      nlinarith [key, hN]
    have hI1 : IntegrableOn (fun z ↦ (1 / 2) * rescaledPhaseEnergyDensity f (R (φ j)) v z) Q1 :=
      (hiE.mono_set hQ12).const_mul (1 / 2)
    have hI2 : IntegrableOn (fun z ↦ (1 / 2) * ((δ (φ j))⁻¹ ^ 2 *
        diffuseTiltDensity (R (φ j)) v (verticalDirection m) z)) Q1 :=
      ((hiT.mono_set hQ1Q2).const_mul ((δ (φ j))⁻¹ ^ 2)).const_mul (1 / 2)
    have hI12 : IntegrableOn (fun z ↦ (1 / 2) * rescaledPhaseEnergyDensity f (R (φ j)) v z +
        (1 / 2) * ((δ (φ j))⁻¹ ^ 2 *
          diffuseTiltDensity (R (φ j)) v (verticalDirection m) z)) Q1 := hI1.add hI2
    calc (∫ z in Q1, mm z)
        ≤ ∫ z in Q1, ((1 / 2) * rescaledPhaseEnergyDensity f (R (φ j)) v z +
          (1 / 2) * ((δ (φ j))⁻¹ ^ 2 *
            diffuseTiltDensity (R (φ j)) v (verticalDirection m) z)) :=
          setIntegral_mono_on hmmI hI12 hQ1m fun z _ ↦ hpt z
      _ = (1 / 2) * (∫ z in Q1, rescaledPhaseEnergyDensity f (R (φ j)) v z) +
          (1 / 2) * ((δ (φ j))⁻¹ ^ 2 *
            ∫ z in Q1, diffuseTiltDensity (R (φ j)) v (verticalDirection m) z) := by
          rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_const_mul]
      _ ≤ (1 / 2) * EB + (1 / 2) * ((δ (φ j))⁻¹ ^ 2 * (2 ^ m * δ (φ j) ^ 2)) := by
          have h1 : (∫ z in Q1, rescaledPhaseEnergyDensity f (R (φ j)) v z) ≤ EB :=
            (setIntegral_mono_set hiE (Eventually.of_forall hE0)
              (Eventually.of_forall hQ12)).trans hjE
          have h2 : (∫ z in Q1, diffuseTiltDensity (R (φ j)) v (verticalDirection m) z) ≤
              2 ^ m * δ (φ j) ^ 2 := by
            rw [← hTq]
            exact setIntegral_mono_set hiT (Eventually.of_forall fun z ↦ by
              rw [diffuseTiltDensity_vertical_eq]; positivity) (Eventually.of_forall hQ1Q2)
          gcongr
      _ = MB := by
          rw [hMB]
          field_simp
  -- the flux pairing on `Q₁`
  set V : Space (m + 1) → Space m := fun z ↦
    ((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative v z) • horizontal (gradient v z) with hV
  have hVm : Measurable V := ha6_measurable_flux_vector (R (φ j)) (δ (φ j)) v
  have hζm : Measurable (fun z : Space (m + 1) ↦ ζ (horizontal z)) :=
    hζ.measurable.comp continuous_horizontal.measurable
  have hpair : ∀ z, |inner ℝ (ζ (horizontal z)) (V z)| ≤ Z * mm z := fun z ↦
    (abs_inner_flux_le_mass hδj hRj (ζ (horizontal z)) z).trans
      (mul_le_mul_of_nonneg_right (hZb _) (hmm0 z))
  have hVi : IntegrableOn (fun z ↦ inner ℝ (ζ (horizontal z)) (V z)) Q1 :=
    (hmmI.const_mul Z).mono' (hζm.inner hVm).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by rw [Real.norm_eq_abs]; exact hpair z)
  have hψm : Measurable (fun z : Space (m + 1) ↦ ψ (z (Fin.last m))) :=
    hψ.measurable.comp continuous_last.measurable
  have hψVi : IntegrableOn (fun z ↦ ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) Q1 :=
    (hmmI.const_mul (Ψ * Z)).mono' (hψm.mul (hζm.inner hVm)).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_mul, mul_assoc]
        exact mul_le_mul (hΨb _) (hpair z) (abs_nonneg _) hΨ0')
  have hwhole : (∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) =
      ∫ z in Q1, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_).symm
    rw [hQ1, mem_tiltCylinder_vertical_iff, not_and_or, not_lt, not_lt] at hz
    rcases hz with hz | hz
    · have : horizontal z ∉ tsupport ζ := fun h' ↦ by
        have := hζs h'
        rw [mem_ball, dist_zero_right] at this
        linarith
      rw [image_eq_zero_of_notMem_tsupport this, inner_zero_left, mul_zero]
    · have : z (Fin.last m) ∉ tsupport ψ := fun h' ↦ by
        have h2 : |z (Fin.last m)| < 1 / 2 := abs_lt.mpr (hψs h')
        linarith
      rw [image_eq_zero_of_notMem_tsupport this, zero_mul]
  -- the estimate for `ψ(t) - ψ(0)`
  set A : Set (Space (m + 1)) := Q1 ∩ {z | c₀ ≤ |z (Fin.last m)|} with hA
  have hAm : MeasurableSet {z : Space (m + 1) | c₀ ≤ |z (Fin.last m)|} :=
    (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet
  have hdiff : |(∫ z in Q1, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) -
      ψ 0 * ∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z)| ≤
      ε' * Z * (∫ z in Q1, mm z) + 2 * Ψ * Z * ∫ z in A, mm z := by
    rw [← integral_const_mul, ← integral_sub hψVi (hVi.const_mul _)]
    have hbound : IntegrableOn (fun z ↦ ε' * Z * mm z +
        2 * Ψ * Z * {z : Space (m + 1) | c₀ ≤ |z (Fin.last m)|}.indicator mm z) Q1 :=
      (hmmI.const_mul _).add ((hmmI.indicator hAm).const_mul _)
    calc |∫ z in Q1, (ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z) -
          ψ 0 * inner ℝ (ζ (horizontal z)) (V z))|
        ≤ ∫ z in Q1, |ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z) -
          ψ 0 * inner ℝ (ζ (horizontal z)) (V z)| := abs_integral_le_integral_abs
      _ ≤ ∫ z in Q1, (ε' * Z * mm z +
          2 * Ψ * Z * {z : Space (m + 1) | c₀ ≤ |z (Fin.last m)|}.indicator mm z) := by
          refine setIntegral_mono_on (hψVi.sub (hVi.const_mul _)).abs hbound hQ1m fun z _ ↦ ?_
          rw [← sub_mul, abs_mul]
          by_cases hz : z ∈ {z : Space (m + 1) | c₀ ≤ |z (Fin.last m)|}
          · rw [indicator_of_mem hz]
            have h1 : |ψ (z (Fin.last m)) - ψ 0| ≤ 2 * Ψ := by
              have := abs_sub (ψ (z (Fin.last m))) (ψ 0)
              linarith [hΨb (z (Fin.last m)), hΨb 0]
            have h2 := mul_le_mul h1 (hpair z) (abs_nonneg _) (by linarith)
            have h3 : 0 ≤ ε' * Z * mm z := mul_nonneg (mul_nonneg hε'0.le hZ0') (hmm0 z)
            have h4 : 2 * Ψ * (Z * mm z) = 2 * Ψ * Z * mm z := by ring
            linarith
          · rw [indicator_of_notMem hz, mul_zero, add_zero]
            have hlt : |z (Fin.last m)| < c₀ := not_le.mp hz
            have h1 : |ψ (z (Fin.last m)) - ψ 0| ≤ ε' := by
              have := hψc (x := z (Fin.last m)) (by rw [Real.dist_eq, sub_zero]; exact hlt)
              rw [Real.dist_eq] at this
              exact this.le
            calc |ψ (z (Fin.last m)) - ψ 0| * |inner ℝ (ζ (horizontal z)) (V z)|
                ≤ ε' * (Z * mm z) := mul_le_mul h1 (hpair z) (abs_nonneg _) hε'0.le
              _ = ε' * Z * mm z := by ring
      _ = ε' * Z * (∫ z in Q1, mm z) + 2 * Ψ * Z * ∫ z in A, mm z := by
          rw [integral_add (hmmI.const_mul _) ((hmmI.indicator hAm).const_mul _),
            integral_const_mul, integral_const_mul, setIntegral_indicator hAm]
  -- conclusion
  have hJ := hj1
  rw [Real.dist_eq, sub_zero] at hJ
  have hoffj : 2 * Ψ * Z * (∫ z in A, mm z) < ε / 4 := hjoff
  have hmain : (∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) +
      σ * ψ 0 * ∫ y, inner ℝ (ζ y)
        (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y) =
      ψ 0 * ((∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z)) + σ * ∫ y, inner ℝ (ζ y)
        (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y)) +
      ((∫ z in Q1, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) -
        ψ 0 * ∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z)) := by
    rw [hwhole]
    ring
  rw [Real.dist_eq, sub_zero]
  change |(∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) +
      σ * ψ 0 * ∫ y, inner ℝ (ζ y)
        (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y)| < ε
  rw [hmain]
  have hεZ : ε' * Z * (∫ z in Q1, mm z) ≤ ε / 4 := by
    have h1 : ε' * Z * (∫ z in Q1, mm z) ≤ ε' * (Z * MB) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hZ0') hε'0.le
    have h2 : ε' * (Z * MB) ≤ ε / 4 := by
      rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hZ0' hMB0]
    linarith
  have hψJ : |ψ 0| * |(∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z)) + σ * ∫ y, inner ℝ (ζ y)
      (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y)| ≤
      ε / 4 := by
    have h1 : |ψ 0| * (ε / (4 * (|ψ 0| + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg (ψ 0)]
    exact (mul_le_mul_of_nonneg_left hJ.le (abs_nonneg _)).trans h1
  calc |ψ 0 * ((∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z)) + σ * ∫ y, inner ℝ (ζ y)
        (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y)) +
      ((∫ z in Q1, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z)) (V z)) -
        ψ 0 * ∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z))|
      ≤ |ψ 0| * |(∫ z in Q1, inner ℝ (ζ (horizontal z)) (V z)) + σ * ∫ y, inner ℝ (ζ y)
        (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y)| +
        (ε' * Z * (∫ z in Q1, mm z) + 2 * Ψ * Z * ∫ z in A, mm z) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        exact add_le_add le_rfl hdiff
    _ < ε := by linarith

end SerrinEpigraph
