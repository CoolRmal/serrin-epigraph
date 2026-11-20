module

public import SerrinEpigraph.AlignedFluxVertical

/-!
# The phase primitive is close to a step function where the potential is small
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- On `(0, 1]` the phase primitive differs from the step `Φ(1) · 1(s > s₀)` by at most a
constant times the potential, uniformly for thresholds `s₀ ≤ s₂ < 1`. -/
theorem RigidityHypotheses.exists_abs_phasePrimitive_sub_ite_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {s₂ : ℝ} (hs₂ : s₂ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0 : ℝ) 1, ∀ s₀ : ℝ, s₀ ≤ s₂ →
      |phasePrimitive f s - (if s₀ < s then phasePrimitive f 1 else 0)| ≤
        C * normalizedPotential f s := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hW⟩ := hr.potential_quadratic_comparison h
  have hσ : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  have hd : 0 < 1 - s₂ := sub_pos.mpr hs₂
  refine ⟨max (Real.sqrt (2 * C₀) / (2 * c₀)) (phasePrimitive f 1 / (c₀ * (1 - s₂) ^ 2)),
    le_max_of_le_left (by positivity), ?_⟩
  intro s hs s₀ hs₀
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  have hΦ := h.phasePrimitive_mem_Icc hsI
  have hWs := hW s hsI
  have hWnn := hr.normalizedPotential_nonneg h hsI
  split_ifs with hlt
  · have hc : ContinuousOn (fun t ↦ Real.sqrt (2 * normalizedPotential f t)) (Icc 0 1) :=
      (continuousOn_const.mul h.normalizedPotential_continuousOn).sqrt
    have hi (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
        IntervalIntegrable (fun t ↦ Real.sqrt (2 * normalizedPotential f t)) volume 0 z :=
      (hc.mono (Icc_subset_Icc_right hz.2)).intervalIntegrable_of_Icc hz.1
    have heq : phasePrimitive f 1 - phasePrimitive f s =
        ∫ t in s..1, Real.sqrt (2 * normalizedPotential f t) := by
      rw [phasePrimitive, phasePrimitive,
        intervalIntegral.integral_interval_sub_left (hi 1 ⟨zero_le_one, le_rfl⟩) (hi s hsI)]
    have hle : (∫ t in s..1, Real.sqrt (2 * normalizedPotential f t)) ≤
        ∫ t in s..1, Real.sqrt (2 * C₀) * (1 - t) := by
      apply intervalIntegral.integral_mono_on hs.2
      · exact (hc.mono (Icc_subset_Icc_left hs.1.le)).intervalIntegrable_of_Icc hs.2
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · intro t ht
        have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le.trans ht.1, ht.2⟩
        have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
        calc Real.sqrt (2 * normalizedPotential f t) ≤ Real.sqrt (2 * C₀ * (1 - t) ^ 2) := by
              apply Real.sqrt_le_sqrt
              have := (hW t htI).2
              nlinarith
          _ = Real.sqrt (2 * C₀) * (1 - t) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h1t]
    rw [integral_linear_equilibrium] at hle
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hΦ.2), heq]
    calc _ ≤ Real.sqrt (2 * C₀) / 2 * (1 - s) ^ 2 := hle
      _ = Real.sqrt (2 * C₀) / (2 * c₀) * (c₀ * (1 - s) ^ 2) := by
          field_simp
      _ ≤ Real.sqrt (2 * C₀) / (2 * c₀) * normalizedPotential f s :=
          mul_le_mul_of_nonneg_left hWs.1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hWnn
  · have hss : s ≤ s₂ := (le_of_not_gt hlt).trans hs₀
    rw [sub_zero, abs_of_nonneg hΦ.1]
    have hsq : (1 - s₂) ^ 2 ≤ (1 - s) ^ 2 := pow_le_pow_left₀ hd.le (by linarith) 2
    calc phasePrimitive f s ≤ phasePrimitive f 1 := hΦ.2
      _ = phasePrimitive f 1 / (c₀ * (1 - s₂) ^ 2) * (c₀ * (1 - s₂) ^ 2) := by
          field_simp
      _ ≤ phasePrimitive f 1 / (c₀ * (1 - s₂) ^ 2) * normalizedPotential f s := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (mul_le_mul_of_nonneg_left hsq hc₀.le).trans hWs.1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hWnn

/-- Pointwise step comparison for an arbitrary function with values in `[0, 1]`. -/
private theorem abs_phasePrimitive_sub_ite_le_rescaled_pps {d : ℕ} {C s₀ s₂ R : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (hs₀ : 0 ≤ s₀) (hs₀₂ : s₀ ≤ s₂)
    (hb : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ s₀ : ℝ, s₀ ≤ s₂ →
      |phasePrimitive f s - (if s₀ < s then phasePrimitive f 1 else 0)| ≤
        C * normalizedPotential f s)
    {v : Space d → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1) (z : Space d) :
    |phasePrimitive f (v z) - (if s₀ < v z then phasePrimitive f 1 else 0)| ≤
      C * R⁻¹ * rescaledPhaseEnergyDensity f R v z := by
  rcases (hv0 z).eq_or_lt with h0 | hpos
  · have he : rescaledPhaseEnergyDensity f R v z = 0 := by
      simp [rescaledPhaseEnergyDensity, ← h0]
    rw [he, ← h0, ite_eq_right (not_lt.mpr hs₀), phasePrimitive_zero]
    simp
  · have hE : rescaledPhaseEnergyDensity f R v z =
        ‖gradient v z‖ ^ 2 / (2 * R) + R * normalizedPotential f (v z) := by
      simp [rescaledPhaseEnergyDensity, hpos]
    have hW : normalizedPotential f (v z) ≤ R⁻¹ * rescaledPhaseEnergyDensity f R v z := by
      rw [hE, mul_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
      have : 0 ≤ R⁻¹ * (‖gradient v z‖ ^ 2 / (2 * R)) := by positivity
      linarith
    calc _ ≤ C * normalizedPotential f (v z) := hb (v z) ⟨hpos, hv1 z⟩ s₀ hs₀₂
      _ ≤ C * (R⁻¹ * rescaledPhaseEnergyDensity f R v z) := mul_le_mul_of_nonneg_left hW hC
      _ = _ := by ring

/-- The step comparison for a rescaled and rotated zero extension, with the potential
bounded by the inverse scale times the rescaled phase energy density. -/
theorem RigidityHypotheses.exists_abs_phasePrimitive_rescaled_sub_ite_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {s₂ : ℝ} (hs₂ : s₂ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Space (m + 1)) (R : ℝ), 0 < R →
      ∀ (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (s₀ : ℝ), 0 ≤ s₀ → s₀ ≤ s₂ →
      ∀ z : Space (m + 1),
        |phasePrimitive f (zeroExtension g u (c + R • Q z)) -
            (if s₀ < zeroExtension g u (c + R • Q z) then phasePrimitive f 1 else 0)| ≤
          C * R⁻¹ * rescaledPhaseEnergyDensity f R
            (fun z ↦ zeroExtension g u (c + R • Q z)) z := by
  obtain ⟨C, hC, hb⟩ := hr.exists_abs_phasePrimitive_sub_ite_le h hs₂
  refine ⟨C, hC, fun c R hR Q s₀ hs₀ hs₀₂ z ↦ ?_⟩
  exact abs_phasePrimitive_sub_ite_le_rescaled_pps hC hR hs₀ hs₀₂ hb
    (v := fun z ↦ zeroExtension g u (c + R • Q z))
    (fun _ ↦ h.zeroExtension_nonneg _) (fun _ ↦ (hr.zeroExtension_lt_one _).le) z

end SerrinEpigraph
