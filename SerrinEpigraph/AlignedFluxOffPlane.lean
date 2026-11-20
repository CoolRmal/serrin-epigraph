module

public import SerrinEpigraph.DiffusePlanarAlignment

/-!
# The normalized flux vanishes away from the plane (a step of HA4.1)

Along an aligned HA11 sequence the normalized flux `F_j = ε ∂ₜ v_j ∇_y v_j / δ_j` has total mass
`o(1)` in every cylinder region `Q_r ∩ {|t| ≥ c}` (`0 < r ≤ 2`, `c > 0`): by
`|ab| ≤ a²/(2δ) + δ b²/2`, the mass is at most `δ⁻² ∫ e_ε / 2` (which tends to zero by the FE3
tails `tendsto_energy_tail_of_aligned`) plus `∫_{Q₂} ε |∇_y v|² / 2 = 2ᵐ δ² / 2`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **The flux off the plane.** -/
theorem RigidityHypotheses.tendsto_flux_mass_offPlane_of_aligned
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (x : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hRδ : Tendsto (fun j ↦ R j * δ j) atTop atTop)
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (htilt : ∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
      (verticalDirection m) = δ j ^ 2)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0))
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e)) {r c : ℝ} (hr0 : 0 < r)
    (hr2 : r ≤ 2) (hc : 0 < c) :
    Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|},
      (δ j)⁻¹ * (R j)⁻¹ * |verticalDerivative (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z| *
        ‖horizontal (gradient (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z)‖) atTop
      (𝓝 0) := by
  set A : Set (Space (m + 1)) :=
    tiltCylinder (verticalDirection m) r ∩ {z | c ≤ |z (Fin.last m)|} with hA
  have hAm : MeasurableSet A := (isOpen_tiltCylinder _ _).measurableSet.inter
    (isClosed_le continuous_const (continuous_abs.comp continuous_last)).measurableSet
  have hT := hr.tendsto_energy_tail_of_aligned h hsharp x hR hRt hδ hRδ he hlocal hQ hr0 hc
  have hlim : Tendsto (fun j ↦ (1 / 2) * ((δ j)⁻¹ ^ 2 * ∫ z in A,
      rescaledPhaseEnergyDensity f (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) z) +
      (1 / 2) * (2 ^ m * δ j ^ 2)) atTop (𝓝 0) := by
    have h1 := (hT.const_mul (1 / 2)).add (((hδ0.pow 2).const_mul (2 ^ m)).const_mul (1 / 2))
    simpa using h1
  refine squeeze_zero (fun j ↦ setIntegral_nonneg hAm fun z _ ↦ ?_) (fun j ↦ ?_) hlim
  · have := hδ j
    have := hR j
    positivity
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x j + R j • Q j z) with hvdef
  have hvL : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, v z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRj := hR j
  have hδj := hδ j
  have hAQ2 : A ⊆ tiltCylinder (verticalDirection m) 2 := inter_subset_left.trans
    (tiltCylinder_mono _ hr2)
  have hAb : A ⊆ closedBall (0 : Space (m + 1)) 4 := hAQ2.trans (by
    have := ha6_tiltCylinder_subset_closedBall (m := m) 2
    norm_num at this
    exact this)
  have hiE : IntegrableOn (rescaledPhaseEnergyDensity f (R j) v) A :=
    (h.integrableOn_rescaledPhaseEnergy hvL hval (R j) (isCompact_closedBall _ 4)).mono_set hAb
  have hE0 : ∀ z, 0 ≤ rescaledPhaseEnergyDensity f (R j) v z :=
    hr.rescaledPhaseEnergyDensity_nonneg h hRj.le hval
  have hiT : IntegrableOn (diffuseTiltDensity (R j) v (verticalDirection m))
      (tiltCylinder (verticalDirection m) 2) := by
    refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_ (isOpen_tiltCylinder _ _).measurableSet
      (isBounded_tiltCylinder (norm_verticalDirection m) 2) (C := (R j)⁻¹) fun z _ ↦ ?_
    · unfold diffuseTiltDensity
      exact (((measurable_gradient v).norm.pow_const 2).sub
        (((measurable_gradient v).inner measurable_const).pow_const 2)).div_const _
    · rw [diffuseTiltDensity_vertical_eq, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (horizontal_norm_sq_le_gradient v z)
        (inv_nonneg.mpr hRj.le)
  have hTq : (∫ z in tiltCylinder (verticalDirection m) 2,
      diffuseTiltDensity (R j) v (verticalDirection m) z) = 2 ^ m * δ j ^ 2 := by
    have h1 := htilt j
    unfold cylinderTilt at h1
    rw [← h1, ← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero),
      one_mul]
  -- pointwise AM-GM with parameter `δ`
  have hpt : ∀ z, (δ j)⁻¹ * (R j)⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖ ≤
      (1 / 2) * ((δ j)⁻¹ ^ 2 * rescaledPhaseEnergyDensity f (R j) v z) +
        (1 / 2) * diffuseTiltDensity (R j) v (verticalDirection m) z := by
    intro z
    have hN := hr.rescaled_isometry_energy_sub_vertical_sq_nonneg h (x j) hRj (Q j) z
    rw [diffuseTiltDensity_vertical_eq]
    set p := |verticalDerivative v z|
    set q := ‖horizontal (gradient v z)‖
    have hp2 : verticalDerivative v z ^ 2 = p ^ 2 := (sq_abs _).symm
    have h1 : (R j)⁻¹ * p ^ 2 ≤ rescaledPhaseEnergyDensity f (R j) v z := by
      rw [← hp2]
      change 0 ≤ rescaledPhaseEnergyDensity f (R j) v z - (R j)⁻¹ * verticalDerivative v z ^ 2 at hN
      linarith
    have h2 : (δ j)⁻¹ * (R j)⁻¹ * p * q ≤
        (1 / 2) * ((δ j)⁻¹ ^ 2 * ((R j)⁻¹ * p ^ 2)) + (1 / 2) * ((R j)⁻¹ * q ^ 2) := by
      have hR0 : 0 ≤ (R j)⁻¹ := inv_nonneg.mpr hRj.le
      have key : 0 ≤ (R j)⁻¹ * ((δ j)⁻¹ * p - q) ^ 2 := mul_nonneg hR0 (sq_nonneg _)
      nlinarith [key]
    have h3 : (1 / 2) * ((δ j)⁻¹ ^ 2 * ((R j)⁻¹ * p ^ 2)) ≤
        (1 / 2) * ((δ j)⁻¹ ^ 2 * rescaledPhaseEnergyDensity f (R j) v z) := by
      gcongr
    linarith
  calc (∫ z in A, (δ j)⁻¹ * (R j)⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖)
      ≤ ∫ z in A, ((1 / 2) * ((δ j)⁻¹ ^ 2 * rescaledPhaseEnergyDensity f (R j) v z) +
          (1 / 2) * diffuseTiltDensity (R j) v (verticalDirection m) z) := by
        refine setIntegral_mono_on ?_ (((hiE.const_mul _).const_mul _).add
          ((hiT.mono_set hAQ2).const_mul _)) hAm fun z _ ↦ hpt z
        refine integrableOn_of_abs_le_mul_gradient_sq hvL ?_ hAm
          ((isBounded_closedBall).subset hAb) (C := (δ j)⁻¹ * (R j)⁻¹) fun z _ ↦ ?_
        · exact ((measurable_const.mul
            (continuous_abs.measurable.comp (measurable_verticalDerivative v))).mul
            (continuous_horizontal.measurable.comp (measurable_gradient v)).norm)
        · rw [abs_of_nonneg (by positivity)]
          have h1 := ha6_abs_verticalDerivative_mul_le v z
          have h2 : |verticalDerivative v z| * ‖horizontal (gradient v z)‖ ≤ ‖gradient v z‖ ^ 2 := by
            have := verticalDerivative_sq_le_gradient v z
            have := horizontal_norm_sq_le_gradient v z
            nlinarith [abs_nonneg (verticalDerivative v z), norm_nonneg (horizontal (gradient v z)),
              sq_abs (verticalDerivative v z)]
          calc (δ j)⁻¹ * (R j)⁻¹ * |verticalDerivative v z| * ‖horizontal (gradient v z)‖
              = (δ j)⁻¹ * (R j)⁻¹ * (|verticalDerivative v z| * ‖horizontal (gradient v z)‖) := by
                ring
            _ ≤ (δ j)⁻¹ * (R j)⁻¹ * ‖gradient v z‖ ^ 2 := by gcongr
    _ = (1 / 2) * ((δ j)⁻¹ ^ 2 * ∫ z in A, rescaledPhaseEnergyDensity f (R j) v z) +
          (1 / 2) * ∫ z in A, diffuseTiltDensity (R j) v (verticalDirection m) z := by
        rw [integral_add ((hiE.const_mul _).const_mul _) ((hiT.mono_set hAQ2).const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ (1 / 2) * ((δ j)⁻¹ ^ 2 * ∫ z in A, rescaledPhaseEnergyDensity f (R j) v z) +
          (1 / 2) * (2 ^ m * δ j ^ 2) := by
        rw [← hTq]
        have hmono := setIntegral_mono_set hiT (Eventually.of_forall fun z ↦ by
          rw [diffuseTiltDensity_vertical_eq]; positivity) (Eventually.of_forall hAQ2)
        linarith

end SerrinEpigraph
