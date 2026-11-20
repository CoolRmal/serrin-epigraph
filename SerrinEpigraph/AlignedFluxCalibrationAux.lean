module

public import SerrinEpigraph.AlignedFluxVertical
public import SerrinEpigraph.AlignedHeightCompactness

/-!
# Eventual bounds along aligned sequences: bad volume, ball energy and flux mass
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

theorem RigidityHypotheses.eventually_volume_real_ball_sdiff_verticalGoodSet_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ : ℝ} (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hρ : 0 < ρ)
    (hρr₀ : ρ + |r₀| < 2) {x : ℕ → Space (m + 1)} {R : ℕ → ℝ}
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)} {δ : ℕ → ℝ} {e : Space (m + 1)}
    (hal : IsAlignedSequence g u x R Q δ e) :
    ∀ᶠ k in atTop, volume.real (ball (0 : Space m) ρ \ verticalGoodSet (R k)
        (fun z ↦ zeroExtension g u (x k + R k • Q k z)) ℓ r₀ b ρ) ≤
      (5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) / ℓ * (2 ^ m * δ k ^ 2) := by
  obtain ⟨-, hR, hRt, -, -, -, htilt, he, hloc, hQ⟩ := hal
  have hV : VerticalPlanarLayers (fun k z ↦ zeroExtension g u (x k + R k • Q k z)) :=
    hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hloc hQ
  have hvL : ∀ k, LipschitzWith (⟨κ, h.kappa_pos.le⟩ * Real.toNNReal (R k))
      (fun z ↦ zeroExtension g u (x k + R k • Q k z)) := fun k ↦
    hr.lipschitzWith_rescaled h (x k) (hR k).le (Q k)
  set η : ℝ := (2 - ρ - |r₀|) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hη1 : η ≤ 1 := by
    rw [hηdef]
    linarith [abs_nonneg r₀]
  set C : ENNReal := ENNReal.ofReal ((5 : ℝ) ^ m) * volume (ball (0 : Space m) 1) /
    ENNReal.ofReal ℓ with hCdef
  have hC : C ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
      (ENNReal.ofReal_pos.mpr hℓ).ne'
  filter_upwards [hV.eventually_volume_sdiff_verticalGoodSet_le hR
    (fun k ↦ (hvL k).locallyLipschitz) hℓ r₀ hb0 hb1 ρ hη hη1] with k hk
  have hint : ∫ z in closedBall (0 : Space (m + 1)) (|ρ| + η + |r₀|),
      diffuseTiltDensity (R k) (fun z ↦ zeroExtension g u (x k + R k • Q k z))
        (verticalDirection m) z ≤ 2 ^ m * δ k ^ 2 := by
    rw [← htilt k]
    exact setIntegral_closedBall_diffuseTiltDensity_le_cylinderTilt (hR k)
      (hvL k).locallyLipschitz (by rw [abs_of_pos hρ, hηdef]; linarith)
  have hk' : volume (ball (0 : Space m) ρ \ verticalGoodSet (R k)
      (fun z ↦ zeroExtension g u (x k + R k • Q k z)) ℓ r₀ b ρ) ≤
      C * ENNReal.ofReal (2 ^ m * δ k ^ 2) :=
    hk.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hint) C)
  have hfin : C * ENNReal.ofReal (2 ^ m * δ k ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  refine (ENNReal.toReal_mono hfin hk').trans (le_of_eq ?_)
  rw [hCdef, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hℓ.le,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

theorem RigidityHypotheses.eventually_setIntegral_closedBall_two_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {x : ℕ → Space (m + 1)} {R : ℕ → ℝ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {δ : ℕ → ℝ} {e : Space (m + 1)} (hal : IsAlignedSequence g u x R Q δ e) :
    ∀ᶠ k in atTop, (∫ z in closedBall (0 : Space (m + 1)) 2,
        rescaledPhaseEnergyDensity f (R k) (fun z ↦ zeroExtension g u (x k + R k • Q k z)) z) ≤
      phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1 := by
  obtain ⟨-, hR, -, -, -, -, -, he, hloc, -⟩ := hal
  obtain ⟨-, hE2, -⟩ := hr.translated_energy_and_tilt_tendsto_of_halfspace_limit h hsharp x hR
    he hloc (r := 2) two_pos
  have hlt : phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) <
      phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1 :=
    lt_add_one _
  filter_upwards [hE2.eventually_lt_const hlt] with k hk
  rw [setIntegral_closedBall_rescaled_isometry f (zeroExtension g u) (x k) (hR k) (Q k) 2]
  exact hk.le

theorem RigidityHypotheses.eventually_setIntegral_flux_mass_le_of_aligned
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {x : ℕ → Space (m + 1)} {R : ℕ → ℝ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {δ : ℕ → ℝ} {e : Space (m + 1)} (hal : IsAlignedSequence g u x R Q δ e) :
    ∀ᶠ k in atTop, (∫ z in tiltCylinder (verticalDirection m) 1,
        (δ k)⁻¹ * (R k)⁻¹ *
          |verticalDerivative (fun z ↦ zeroExtension g u (x k + R k • Q k z)) z| *
          ‖horizontal (gradient (fun z ↦ zeroExtension g u (x k + R k • Q k z)) z)‖) ≤
      (phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1) / 2 +
        2 ^ m / 2 := by
  have hEev := hr.eventually_setIntegral_closedBall_two_energy_le h hsharp hal
  obtain ⟨-, hR, -, hδ, -, -, htilt, -, -, -⟩ := hal
  filter_upwards [hEev] with k hjE
  set EB : ℝ := phasePrimitive f 1 * (2 ^ m * volume.real (closedBall (0 : Space m) 1)) + 1
    with hEB
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x k + R k • Q k z) with hvdef
  set Q1 : Set (Space (m + 1)) := tiltCylinder (verticalDirection m) 1 with hQ1
  have hQ1m : MeasurableSet Q1 := (isOpen_tiltCylinder _ _).measurableSet
  have hQ1b : Bornology.IsBounded Q1 := isBounded_tiltCylinder (norm_verticalDirection m) 1
  have hQ12 : Q1 ⊆ closedBall (0 : Space (m + 1)) 2 := by
    have h1 := ha6_tiltCylinder_subset_closedBall (m := m) 1
    rwa [mul_one] at h1
  have hQ1Q2 : Q1 ⊆ tiltCylinder (verticalDirection m) 2 := tiltCylinder_mono _ (by norm_num)
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRj := hR k
  have hδj := hδ k
  set mm : Space (m + 1) → ℝ := fun z ↦
    (δ k)⁻¹ * (R k)⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖ with hmm
  have hmmI : IntegrableOn mm Q1 := integrableOn_flux_mass hvL hδj hRj hQ1m hQ1b
  have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f (R k) v z :=
    hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
  have hiE : IntegrableOn (rescaledPhaseEnergyDensity f (R k) v)
      (closedBall (0 : Space (m + 1)) 2) :=
    h.integrableOn_rescaledPhaseEnergy hvL hval (R k) (isCompact_closedBall _ 2)
  have hiT : IntegrableOn (diffuseTiltDensity (R k) v (verticalDirection m))
      (tiltCylinder (verticalDirection m) 2) := by
    refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_
      (isOpen_tiltCylinder _ _).measurableSet
      (isBounded_tiltCylinder (norm_verticalDirection m) 2) (C := (R k)⁻¹) fun z _ ↦ ?_
    · unfold diffuseTiltDensity
      exact (((measurable_gradient v).norm.pow_const 2).sub
        (((measurable_gradient v).inner measurable_const).pow_const 2)).div_const _
    · rw [diffuseTiltDensity_vertical_eq, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (horizontal_norm_sq_le_gradient v z)
        (inv_nonneg.mpr hRj.le)
  have hTq : (∫ z in tiltCylinder (verticalDirection m) 2,
      diffuseTiltDensity (R k) v (verticalDirection m) z) = 2 ^ m * δ k ^ 2 := by
    have h1 := htilt k
    unfold cylinderTilt at h1
    rw [← h1, ← mul_assoc, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  have hpt : ∀ z, mm z ≤ (1 / 2) * rescaledPhaseEnergyDensity f (R k) v z +
      (1 / 2) * ((δ k)⁻¹ ^ 2 * diffuseTiltDensity (R k) v (verticalDirection m) z) := by
    intro z
    have hN := hr.rescaled_isometry_energy_sub_vertical_sq_nonneg h (x k) hRj (Q k) z
    rw [diffuseTiltDensity_vertical_eq]
    have hR0 : 0 ≤ (R k)⁻¹ := inv_nonneg.mpr hRj.le
    have key : 0 ≤ (R k)⁻¹ * (|verticalDerivative v z| -
        (δ k)⁻¹ * ‖horizontal (gradient v z)‖) ^ 2 := mul_nonneg hR0 (sq_nonneg _)
    have hp2 : verticalDerivative v z ^ 2 = |verticalDerivative v z| ^ 2 := (sq_abs _).symm
    change 0 ≤ rescaledPhaseEnergyDensity f (R k) v z -
      (R k)⁻¹ * verticalDerivative v z ^ 2 at hN
    rw [hp2] at hN
    simp only [hmm]
    nlinarith [key, hN]
  have hI1 : IntegrableOn (fun z ↦ (1 / 2) * rescaledPhaseEnergyDensity f (R k) v z) Q1 :=
    (hiE.mono_set hQ12).const_mul (1 / 2)
  have hI2 : IntegrableOn (fun z ↦ (1 / 2) * ((δ k)⁻¹ ^ 2 *
      diffuseTiltDensity (R k) v (verticalDirection m) z)) Q1 :=
    ((hiT.mono_set hQ1Q2).const_mul ((δ k)⁻¹ ^ 2)).const_mul (1 / 2)
  have hI12 : IntegrableOn (fun z ↦ (1 / 2) * rescaledPhaseEnergyDensity f (R k) v z +
      (1 / 2) * ((δ k)⁻¹ ^ 2 *
        diffuseTiltDensity (R k) v (verticalDirection m) z)) Q1 := hI1.add hI2
  calc (∫ z in Q1, mm z)
      ≤ ∫ z in Q1, ((1 / 2) * rescaledPhaseEnergyDensity f (R k) v z +
        (1 / 2) * ((δ k)⁻¹ ^ 2 *
          diffuseTiltDensity (R k) v (verticalDirection m) z)) :=
        setIntegral_mono_on hmmI hI12 hQ1m fun z _ ↦ hpt z
    _ = (1 / 2) * (∫ z in Q1, rescaledPhaseEnergyDensity f (R k) v z) +
        (1 / 2) * ((δ k)⁻¹ ^ 2 *
          ∫ z in Q1, diffuseTiltDensity (R k) v (verticalDirection m) z) := by
        rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ (1 / 2) * EB + (1 / 2) * ((δ k)⁻¹ ^ 2 * (2 ^ m * δ k ^ 2)) := by
        have h1 : (∫ z in Q1, rescaledPhaseEnergyDensity f (R k) v z) ≤ EB :=
          (setIntegral_mono_set hiE (Eventually.of_forall hE0)
            (Eventually.of_forall hQ12)).trans hjE
        have h2 : (∫ z in Q1, diffuseTiltDensity (R k) v (verticalDirection m) z) ≤
            2 ^ m * δ k ^ 2 := by
          rw [← hTq]
          exact setIntegral_mono_set hiT (Eventually.of_forall fun z ↦ by
            rw [diffuseTiltDensity_vertical_eq]; positivity) (Eventually.of_forall hQ1Q2)
        gcongr
    _ = EB / 2 + 2 ^ m / 2 := by
        field_simp

end SerrinEpigraph
