module

public import SerrinEpigraph.RecoveryProfileRegularity
public import SerrinEpigraph.RadialSlopeBound
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz extension of the recovery profile by constant phases
-/

public section

open Set

namespace SerrinEpigraph

/-- The profile extended by zero before the transition and by one afterwards. -/
@[expose] noncomputable def recoveryProfile (f : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  recoveryProfileCore f δ (min (max t 0) (recoveryTravelTime f δ 1))

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- The interior speed bound extends to a Lipschitz bound at the transition endpoints. -/
theorem RigidityHypotheses.recoveryProfileCore_lipschitzOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    LipschitzOnWith ⟨Real.sqrt (2 * (normalizedPotential f 0 + δ)), Real.sqrt_nonneg _⟩
      (recoveryProfileCore f δ) (Icc 0 (recoveryTravelTime f δ 1)) := by
  have hT := hr.recoveryTravelTime_one_pos h hδ
  have hi : LipschitzOnWith
      ⟨Real.sqrt (2 * (normalizedPotential f 0 + δ)), Real.sqrt_nonneg _⟩
      (recoveryProfileCore f δ) (Ioo 0 (recoveryTravelTime f δ 1)) := by
    apply (convex_Ioo _ _).lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht ↦ (hr.recoveryProfileCore_hasDerivAt h hδ ht).differentiableAt)
    intro t ht
    change ‖deriv (recoveryProfileCore f δ) t‖ ≤ _
    rw [(hr.recoveryProfileCore_hasDerivAt h hδ ht).deriv,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hq := hr.recoveryProfileCore_mem_Ioo h hδ ht
    have hw := hr.normalizedPotential_antitoneOn h (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      ⟨hq.1.le, hq.2.le⟩ hq.1.le
    apply Real.sqrt_le_sqrt
    linarith
  have hc : ContinuousOn (recoveryProfileCore f δ)
      (closure (Ioo 0 (recoveryTravelTime f δ 1))) := by
    rw [closure_Ioo hT.ne]
    exact hr.recoveryProfileCore_continuousOn h hδ
  simpa only [closure_Ioo hT.ne] using LipschitzOnWith.closure hc hi

/-- The clamped time always lies in the finite transition interval. -/
theorem RigidityHypotheses.recoveryProfile_clamped_mem
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (t : ℝ) :
    min (max t 0) (recoveryTravelTime f δ 1) ∈ Icc 0 (recoveryTravelTime f δ 1) :=
  ⟨le_min (le_max_right _ _) (hr.recoveryTravelTime_one_pos h hδ).le, min_le_right _ _⟩

/-- The constant-phase extension preserves the Lipschitz speed bound globally. -/
theorem RigidityHypotheses.recoveryProfile_lipschitz
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    LipschitzWith ⟨Real.sqrt (2 * (normalizedPotential f 0 + δ)), Real.sqrt_nonneg _⟩
      (recoveryProfile f δ) := by
  have hc : LipschitzWith 1 (fun t : ℝ ↦ min (max t 0) (recoveryTravelTime f δ 1)) := by
    simpa only [id_eq, min_comm, max_comm] using
      (LipschitzWith.id.const_max (0 : ℝ)).const_min (recoveryTravelTime f δ 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he := (hr.recoveryProfileCore_lipschitzOn h hδ).dist_le_mul
    _ (hr.recoveryProfile_clamped_mem h hδ x) _ (hr.recoveryProfile_clamped_mem h hδ y)
  exact he.trans (mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul] using hc.dist_le_mul x y)
    (Real.sqrt_nonneg _))

/-- The global extension remains normalized. -/
theorem RigidityHypotheses.recoveryProfile_mem_Icc
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) (t : ℝ) :
    recoveryProfile f δ t ∈ Icc (0 : ℝ) 1 :=
  (hr.recoveryProfileCore_spec h hδ (hr.recoveryProfile_clamped_mem h hδ t)).1

/-- Before the transition the extended profile is zero. -/
theorem RigidityHypotheses.recoveryProfile_eq_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : t ≤ 0) : recoveryProfile f δ t = 0 := by
  simp only [recoveryProfile, max_eq_right ht,
    min_eq_left (hr.recoveryTravelTime_one_pos h hδ).le,
    hr.recoveryProfileCore_zero h hδ]

/-- After the transition the extended profile is one. -/
theorem RigidityHypotheses.recoveryProfile_eq_one
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : recoveryTravelTime f δ 1 ≤ t) : recoveryProfile f δ t = 1 := by
  have hp : 0 ≤ t := (hr.recoveryTravelTime_one_pos h hδ).le.trans ht
  simp only [recoveryProfile, max_eq_left hp, min_eq_right ht,
    hr.recoveryProfileCore_end h hδ]

end SerrinEpigraph
