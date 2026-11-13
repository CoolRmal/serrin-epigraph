module

public import SerrinEpigraph.EquipartitionPhaseLimit

/-!
# A positive homogeneous limit for energy and primitive variation on balls
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- A surface-normalized energy limit determines every fixed rescaled ball-energy limit. -/
theorem rescaledEnergy_tendsto_of_surface_limit {m : ℕ} (f : ℝ → ℝ)
    (U : Space (m + 1) → ℝ) {L : ℝ}
    (hL : Tendsto (fun R ↦ R ^ (-(m : ℤ)) * ∫ x in closedBall 0 R,
      phaseEnergyDensity f 0 U x) atTop (𝓝 L)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫ x in closedBall 0 r,
      rescaledPhaseEnergyDensity f R (fun y ↦ U (R • y)) x) atTop (𝓝 (r ^ m * L)) := by
  have ht := (hL.comp (Tendsto.atTop_mul_const hr tendsto_id)).const_mul (r ^ m)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [integral_rescaledPhaseEnergyDensity f U hR r]
  simp only [Function.comp_def, id_eq, zpow_neg, zpow_natCast, mul_pow]
  field_simp

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The limiting mass coefficient is positive, and energy on a ball of radius r tends to
that coefficient times r to the surface dimension. -/
theorem RigidityHypotheses.exists_positive_asymptotic_energy_mass
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ L : ℝ, 0 < L ∧ ∀ r : ℝ, 0 < r →
      Tendsto (fun R : ℝ ↦ ∫ x in closedBall 0 r,
        rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x)
          atTop (𝓝 (r ^ m * L)) := by
  obtain ⟨L, _, hL⟩ := hr.surface_scaled_energy_tendsto h
  have ht (r : ℝ) (hr0 : 0 < r) := rescaledEnergy_tendsto_of_surface_limit f _ hL hr0
  obtain ⟨c, hc, hbound⟩ := hr.rescaledEnergy_eventually_pos h
  have hunit : Tendsto (fun R : ℝ ↦ ∫ x in closedBall 0 1,
      rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) atTop (𝓝 L) := by
    simpa only [one_pow, one_mul] using ht 1 zero_lt_one
  exact ⟨L, hc.trans_le (ge_of_tendsto hunit hbound), ht⟩

/-- Along simultaneous defect scales, primitive gradient mass has the same positive homogeneous
ball limits as the diffuse energy. This does not yet identify that mass with phase perimeter. -/
theorem RigidityHypotheses.exists_positive_asymptotic_primitive_mass
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    (hB : ∀ k : ℕ, Tendsto (fun j ↦
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0)) :
    ∃ L : ℝ, 0 < L ∧ ∀ r : ℝ, 0 < r →
      Tendsto (fun j ↦ ∫ x in closedBall 0 r,
        ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖)
          atTop (𝓝 (r ^ m * L)) := by
  obtain ⟨L, hL, henergy⟩ := hr.exists_positive_asymptotic_energy_mass h
  refine ⟨L, hL, fun r hr0 ↦ ?_⟩
  have hgap := hr.rescaled_energy_primitive_gap_tendsto_zero h hR hB (isCompact_closedBall 0 r)
  have ht := ((henergy r hr0).comp hRt).sub hgap
  simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using ht

end SerrinEpigraph
