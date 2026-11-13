module

public import SerrinEpigraph.PartitionGradientEnergy

/-!
# Potential error for finite partition recovery
-/

public section

open Set
open scoped NNReal

namespace SerrinEpigraph

/-- The reaction assumptions give a finite Lipschitz constant for the normalized potential. -/
theorem Hypotheses.exists_normalizedPotential_lipschitzOn
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) :
    ∃ C : ℝ≥0, LipschitzOnWith C (normalizedPotential f) (Icc 0 1) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from
      fun _ hx ↦ hx.1))
  let C : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hi : LipschitzOnWith C (normalizedPotential f) (Ioo 0 1) := by
    apply (convex_Ioo _ _).lipschitzOnWith_of_nnnorm_deriv_le
      (fun s hs ↦ (h.normalizedPotential_hasDerivAt hs.1).differentiableAt)
    intro s hs
    change ‖deriv (normalizedPotential f) s‖ ≤ max M 0
    rw [h.normalizedPotential_deriv hs.1, norm_neg]
    exact (hM s ⟨hs.1.le, hs.2.le⟩).trans (le_max_left _ _)
  refine ⟨C, ?_⟩
  have hc : ContinuousOn (normalizedPotential f) (closure (Ioo 0 1)) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact h.normalizedPotential_continuousOn
  simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using
    LipschitzOnWith.closure hc hi

/-- Lipschitz continuity controls the potential defect of a convex mixture by
the weighted differences from its components, without a convexity assumption. -/
theorem partitionRecovery_potential_le {ι : Type*} [Fintype ι] {d : ℕ}
    {W : ℝ → ℝ} {C : ℝ≥0} (hW : LipschitzOnWith C W (Icc 0 1))
    {η v : ι → Space d → ℝ} {x : Space d}
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1)
    (hval : ∀ i, v i x ∈ Icc (0 : ℝ) 1) :
    W (partitionRecovery η v x) ≤ (∑ i, η i x * W (v i x)) +
      C * ∑ i, η i x * ‖partitionRecovery η v x - v i x‖ := by
  classical
  have hm : partitionRecovery η v x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hpos i) (hval i).1)
    · exact (Finset.sum_le_sum (fun i _ ↦
        mul_le_of_le_one_right (hpos i) (hval i).2)).trans hsum.le
  have hi (i : ι) : W (partitionRecovery η v x) ≤
      W (v i x) + C * ‖partitionRecovery η v x - v i x‖ := by
    have hh := hW.dist_le_mul (x := partitionRecovery η v x) hm (y := v i x) (hval i)
    rw [dist_eq_norm, dist_eq_norm] at hh
    have he := (le_abs_self (W (partitionRecovery η v x) - W (v i x))).trans hh
    linarith
  have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (hi i) (hpos i))
  simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul,
    mul_left_comm (η _ x) (C : ℝ), ← Finset.mul_sum] using he

end SerrinEpigraph
