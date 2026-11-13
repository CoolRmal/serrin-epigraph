module

public import SerrinEpigraph.EquilibriumEstimates
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quadratic lower bounds for the normalized potential
-/

public section

noncomputable section

namespace SerrinEpigraph

/-- The integral of the linear distance to the normalized equilibrium. -/
theorem integral_linear_equilibrium (c s : ℝ) :
    (∫ t in s..1, c * (1 - t)) = (c / 2) * (1 - s) ^ 2 := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume s 1 :=
    continuous_id.intervalIntegrable _ _
  have ho : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume s 1 :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ho hi,
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The potential controls the squared distance to equilibrium from below near one. -/
theorem RigidityHypotheses.exists_potential_quadratic_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ s : ℝ, 0 ≤ s → 1 - δ < s → s ≤ 1 →
      c * (1 - s) ^ 2 ≤ normalizedPotential f s := by
  obtain ⟨c, δ, hc, hδ, hb⟩ := hr.exists_reaction_equilibrium_lower_bound h
  refine ⟨c / 2, δ, by positivity, hδ, ?_⟩
  intro s hs hsδ hsone
  rw [← integral_linear_equilibrium, normalizedPotential]
  have hcont : Continuous (fun t : ℝ ↦ c * (1 - t)) := by fun_prop
  apply intervalIntegral.integral_mono_on hsone
    (hcont.intervalIntegrable _ _)
    (h.reaction_intervalIntegrable hs)
  intro t ht
  exact hb t (lt_of_lt_of_le hsδ ht.1) ht.2

/-- Continuity of the normalized potential includes the endpoint zero. -/
theorem Hypotheses.normalizedPotential_continuousOn (h : Hypotheses g u f κ) :
    ContinuousOn (normalizedPotential f) (Set.Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn f (Set.uIcc (0 : ℝ) 1) :=
    h.reaction_contDiffOn.continuousOn.mono (by
      intro t ht
      simpa only [min_eq_left zero_le_one, Set.mem_Ici] using ht.1)
  have hi : MeasureTheory.IntegrableOn f (Set.uIcc (0 : ℝ) 1) MeasureTheory.volume :=
    hc.integrableOn_Icc
  change ContinuousOn (fun s ↦ ∫ t in s..1, f t) (Set.Icc (0 : ℝ) 1)
  simpa only [Set.uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval_left hi

/-- On the entire normalized solution range the potential controls squared distance to one. -/
theorem RigidityHypotheses.potential_quadratic_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c * (1 - s) ^ 2 ≤ normalizedPotential f s := by
  obtain ⟨c, δ, hc, hδ, hb⟩ := hr.exists_potential_quadratic_lower_bound h
  let a : ℝ := 1 - min δ 1 / 2
  have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [min_le_right δ (1 : ℝ)]
  have ha1 : a < 1 := by dsimp [a]; linarith
  have haδ : 1 - δ < a := by dsimp [a]; linarith [min_le_left δ (1 : ℝ)]
  obtain ⟨d, hd, hdall⟩ := isCompact_Icc.exists_forall_le'
    (h.normalizedPotential_continuousOn.mono (Set.Icc_subset_Icc_right ha1.le))
    (fun s hs ↦ hr.normalizedPotential_pos h hs.1 (hs.2.trans_lt ha1))
  refine ⟨min c d, lt_min hc hd, ?_⟩
  intro s hs
  by_cases hsa : s ≤ a
  · have hsq : (1 - s) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    calc
      min c d * (1 - s) ^ 2 ≤ d * (1 - s) ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ ≤ d := by nlinarith
      _ ≤ normalizedPotential f s := hdall s ⟨hs.1, hsa⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
      (hb s hs.1 (haδ.trans (lt_of_not_ge hsa)) hs.2)

end SerrinEpigraph
