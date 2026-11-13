module

public import SerrinEpigraph.RescaledPhaseEnergy
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing potential energy under dilation
-/

public section

open MeasureTheory Metric Filter
open scoped Pointwise Topology

namespace SerrinEpigraph

noncomputable section

/-- Potential energy restricted to the positive phase. -/
@[expose] def phasePotentialDensity {d : ℕ} (f : ℝ → ℝ) (v : Space d → ℝ) :
    Space d → ℝ :=
  {x | 0 < v x}.indicator (fun x ↦ normalizedPotential f (v x))

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The phase potential is locally integrable for the zero extension. -/
theorem RigidityHypotheses.integrableOn_phasePotential
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (phasePotentialDensity f (zeroExtension g u)) K := by
  have hc : Continuous (fun x ↦ normalizedPotential f (zeroExtension g u x)) :=
    h.normalizedPotential_continuousOn.comp_continuous h.zeroExtension_continuous
      (fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩)
  exact (hc.continuousOn.integrableOn_compact hK).indicator
    (isOpen_lt continuous_const h.zeroExtension_continuous).measurableSet

/-- The phase potential is nonnegative and bounded by the full energy. -/
theorem RigidityHypotheses.phasePotential_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    0 ≤ phasePotentialDensity f (zeroExtension g u) x ∧
      phasePotentialDensity f (zeroExtension g u) x ≤
        phaseEnergyDensity f 0 (zeroExtension g u) x := by
  by_cases hx : 0 < zeroExtension g u x
  · simp only [phasePotentialDensity, phaseEnergyDensity, Set.indicator_apply,
      Set.mem_ofPred_eq, hx, ite_true, add_zero]
    exact ⟨hr.normalizedPotential_nonneg h
      ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩,
      le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (by norm_num))⟩
  · simp [phasePotentialDensity, phaseEnergyDensity, hx]

/-- The integrated potential on a rescaled ball decays inversely with the scale. -/
theorem RigidityHypotheses.rescaledPotential_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 1 ≤ R * r →
      (∫ x in closedBall 0 r, phasePotentialDensity f (zeroExtension g u) (R • x)) ≤
        C * r ^ m / R := by
  obtain ⟨C, hC, hb⟩ := hr.phaseEnergy_surface_growth h
  refine ⟨C, hC, fun R r hR hRr ↦ ?_⟩
  rw [Measure.setIntegral_comp_smul_of_pos volume _ _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hi := integral_mono (hr.integrableOn_phasePotential h (isCompact_closedBall 0 (R * r)))
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall 0 (R * r)))
    (fun x ↦ (hr.phasePotential_bounds h x).2)
  calc
    _ ≤ (R ^ (m + 1))⁻¹ * (C * (R * r) ^ m) :=
      mul_le_mul_of_nonneg_left (hi.trans (hb (R * r) hRr)) (by positivity)
    _ = C * r ^ m / R := by rw [mul_pow, pow_succ]; field_simp

/-- On every fixed positive-radius ball the rescaled phase potential tends to zero. -/
theorem RigidityHypotheses.rescaledPotential_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫ x in closedBall 0 r,
      phasePotentialDensity f (zeroExtension g u) (R • x)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := hr.rescaledPotential_bound h
  have ht : Tendsto (fun R : ℝ ↦ C * r ^ m / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun R ↦ integral_nonneg
      (fun x ↦ (hr.phasePotential_bounds h (R • x)).1))
  · filter_upwards [eventually_ge_atTop (max 1 (1 / r))] with R hR
    have hpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
    have hmul : 1 ≤ R * r := (div_le_iff₀ hradius).mp ((le_max_right _ _).trans hR)
    exact hb R r hpos hmul

end

end SerrinEpigraph
