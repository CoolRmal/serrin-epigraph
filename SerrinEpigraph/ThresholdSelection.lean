module

public import SerrinEpigraph.ThresholdLayerAverage

/-!
# Selecting threshold competitors with controlled energy
-/

public section

open Set MeasureTheory Filter

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- Averaging over thresholds away from the endpoints selects a normalized
competitor with energy controlled by width mass and transition action. -/
theorem RigidityHypotheses.exists_thresholdRecovery_energy_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {φ a : Space d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (hpos : ∀ x, 0 < a x)
    {K : Set (Space d)} (hK : IsCompact K) {C : ℝ} (hC : 0 ≤ C)
    (hgrad : ∀ x ∈ K, ‖gradient φ x‖ ≤ a x)
    (hrel : ∀ x ∈ K, ‖gradient a x‖ / a x ≤ C)
    {τ : ℝ} (hτhalf : τ < 1 / 2) :
    ∃ t ∈ Icc τ (1 - τ),
      (∫ x in K, rescaledPhaseEnergyDensity f R (thresholdRecovery f δ R φ a t) x) ≤
        (1 + recoveryTravelTime f δ 1 * C / R) ^ 2 *
          ((recoveryActionPrimitive f δ 1 * ∫ x in K, a x) / (1 - 2 * τ)) := by
  let M := fun t ↦ ∫ x in K, recoveryLayerDensity f δ R (thresholdCoordinate φ a t x)
  obtain ⟨hiM, htotal⟩ := hr.threshold_layer_average h hδ hR hφ.continuous ha.continuous hpos hK
  have hMpos (t : ℝ) : 0 ≤ M t := integral_nonneg (fun x ↦
    hr.recoveryLayerDensity_nonneg h hδ hR.le _)
  have hlen : 0 < 1 - 2 * τ := by linarith
  have hvol : (volume (Icc τ (1 - τ))).toReal = 1 - 2 * τ := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - τ - τ)]
    ring
  have hvolpos : volume (Icc τ (1 - τ)) ≠ 0 := by
    rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  obtain ⟨t, ht, htm⟩ := exists_le_setAverage hvolpos (isCompact_Icc.measure_ne_top)
    (hiM.integrableOn (s := Icc τ (1 - τ)))
  have hsmall : M t ≤
      (recoveryActionPrimitive f δ 1 * ∫ x in K, a x) / (1 - 2 * τ) := by
    rw [setAverage_eq, measureReal_def, hvol, smul_eq_mul] at htm
    calc
      M t ≤ (1 - 2 * τ)⁻¹ * ∫ s in Icc τ (1 - τ), M s := htm
      _ ≤ (1 - 2 * τ)⁻¹ * ∫ s, M s := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hiM (Eventually.of_forall hMpos)) (inv_nonneg.mpr hlen.le)
      _ = _ := by rw [htotal]; ring
  refine ⟨t, ht, ?_⟩
  obtain ⟨hv, hval⟩ := hr.thresholdRecovery_regular h hδ (R := R) hφ ha hpos t
  have hiE := h.integrableOn_rescaledPhaseEnergy hv hval R hK
  have hiQ := hr.integrableOn_recoveryLayerDensity_comp h hδ (R := R)
    (thresholdCoordinate_contDiff hφ ha hpos t).continuous hK
  have he := setIntegral_mono_on hiE
    (hiQ.const_mul ((1 + recoveryTravelTime f δ 1 * C / R) ^ 2)) hK.measurableSet
    (fun x hx ↦ hr.thresholdRecovery_energy_le h hδ hR
      (hφ.differentiable_one x) (ha.differentiable_one x) (hpos x) (hgrad x hx)
      hC (hrel x hx) t)
  rw [integral_const_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left hsmall (sq_nonneg _))

end SerrinEpigraph
