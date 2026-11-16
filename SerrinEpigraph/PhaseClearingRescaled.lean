module

public import SerrinEpigraph.PhaseClearingEnergyDensity
public import SerrinEpigraph.RescaledPhaseEnergy

/-!
# Clearing and energy density at the diffuse-interface scale
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- The ball-energy change of variables is valid about every center. -/
theorem integral_rescaledPhaseEnergyDensity_center {m : ℕ} (f : ℝ → ℝ)
    (U : Space (m + 1) → ℝ) {T : ℝ} (hT : 0 < T) (c : Space (m + 1)) (r : ℝ) :
    (∫ x in closedBall c r, rescaledPhaseEnergyDensity f T (fun y ↦ U (T • y)) x) =
      (T ^ m)⁻¹ * ∫ x in closedBall (T • c) (T * r), phaseEnergyDensity f 0 U x := by
  simp_rw [rescaledPhaseEnergyDensity_dilation f U hT]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume _ _ hT]
  simp only [smul_closedBall' hT.ne', Real.norm_eq_abs, abs_of_pos hT,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, pow_succ]
  field_simp

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The physical clearing constants give the exact scaled half-ball statement. -/
theorem RigidityHypotheses.exists_rescaled_phase_clearing_constants
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ a R₀ : ℝ, 0 < a ∧ 0 < R₀ ∧
      ∀ (T : ℝ), 0 < T → ∀ (c : Space (m + 1)) (r : ℝ), 0 < r → T * r ≤ R₀ →
        (∀ x ∈ ball c r, zeroExtension g u (T • x) ≤ a * (T * r)) →
          EqOn (fun x ↦ zeroExtension g u (T • x)) 0 (ball c (r / 2)) := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_phase_clearing_constants h
  refine ⟨a, R₀, ha, hR₀, ?_⟩
  intro T hT c r hrad hTr hsmall
  have hmap (s : ℝ) : T • ball c s = ball (T • c) (T * s) := by
    rw [_root_.smul_ball hT.ne', Real.norm_eq_abs, abs_of_pos hT]
  have hphysical : ∀ y ∈ ball (T • c) (T * r), zeroExtension g u y ≤ a * (T * r) := by
    intro y hy
    rw [← hmap r] at hy
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
    exact hsmall x hx
  have hz := hclear (T • c) (T * r) (mul_pos hT hrad) hTr hphysical
  intro x hx
  apply hz
  have hy : T • x ∈ T • ball c (r / 2) := Set.smul_mem_smul_set hx
  rw [hmap (r / 2)] at hy
  simpa only [mul_div_assoc] using hy

/-- Scaled interior levels have a scale-independent surface-energy lower bound
once the tested radius exceeds a fixed multiple of the interface thickness. -/
theorem RigidityHypotheses.exists_rescaled_level_energy_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ T : ℝ, 0 < T → ∀ x : Space (m + 1),
        zeroExtension g u (T • x) ∈ Icc a b →
        ∀ r : ℝ, ρ ≤ T * r →
          c₀ * r ^ m ≤ ∫ y in closedBall x r,
            rescaledPhaseEnergyDensity f T (fun z ↦ zeroExtension g u (T • z)) y := by
  obtain ⟨ρ, c₀, hρ, hc₀, hbound⟩ := hr.exists_level_surface_energy_lower_bound h ha hb
  refine ⟨ρ, c₀, hρ, hc₀, ?_⟩
  intro T hT x hx r hradius
  have he := hbound (T • x) hx (T * r) hradius
  rw [integral_rescaledPhaseEnergyDensity_center f _ hT]
  have hi := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (pow_nonneg hT.le m))
  calc
    c₀ * r ^ m = (T ^ m)⁻¹ * (c₀ * (T * r) ^ m) := by rw [mul_pow]; field_simp
    _ ≤ _ := hi

/-- The same scaled density bound holds about every rescaled free-boundary point. -/
theorem RigidityHypotheses.exists_rescaled_freeBoundary_energy_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ T : ℝ, 0 < T → ∀ x : Space (m + 1), T • x ∈ frontier (epigraph g) →
        ∀ r : ℝ, ρ ≤ T * r →
          c₀ * r ^ m ≤ ∫ y in closedBall x r,
            rescaledPhaseEnergyDensity f T (fun z ↦ zeroExtension g u (T • z)) y := by
  obtain ⟨ρ, c₀, hρ, hc₀, hbound⟩ := hr.exists_freeBoundary_surface_energy_lower_bound h
  refine ⟨ρ, c₀, hρ, hc₀, ?_⟩
  intro T hT x hx r hradius
  have he := hbound (T • x) hx (T * r) hradius
  rw [integral_rescaledPhaseEnergyDensity_center f _ hT]
  have hi := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (pow_nonneg hT.le m))
  calc
    c₀ * r ^ m = (T ^ m)⁻¹ * (c₀ * (T * r) ^ m) := by rw [mul_pow]; field_simp
    _ ≤ _ := hi

end SerrinEpigraph
