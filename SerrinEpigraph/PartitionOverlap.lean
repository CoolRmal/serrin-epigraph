module

public import SerrinEpigraph.RecoveryScaleMismatch

/-!
# Overlap bounds without dependence on the number of graph patches
-/

public section

open Set
open scoped NNReal

namespace SerrinEpigraph

/-- The distance from a convex mixture to one component is bounded by weighted pair distances. -/
theorem norm_partitionRecovery_sub_le {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} {x : Space d}
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1) (i : ι) :
    ‖partitionRecovery η v x - v i x‖ ≤ ∑ j, η j x * ‖v j x - v i x‖ := by
  classical
  have he : partitionRecovery η v x - v i x = ∑ j, η j x * (v j x - v i x) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul,
      partitionRecovery]
  rw [he]
  simpa only [norm_mul, Real.norm_of_nonneg (hpos _)] using
    norm_sum_le Finset.univ (fun j ↦ η j x * (v j x - v i x))

/-- The potential defect can be estimated using only pairwise differences on overlaps. -/
theorem partitionRecovery_potential_le_pairwise {ι : Type*} [Fintype ι] {d : ℕ}
    {W : ℝ → ℝ} {C : ℝ≥0} (hW : LipschitzOnWith C W (Icc 0 1))
    {η v : ι → Space d → ℝ} {x : Space d}
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1)
    (hval : ∀ i, v i x ∈ Icc (0 : ℝ) 1) :
    W (partitionRecovery η v x) ≤ (∑ i, η i x * W (v i x)) +
      C * ∑ i, ∑ j, η i x * η j x * ‖v j x - v i x‖ := by
  apply (partitionRecovery_potential_le hW hpos hsum hval).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Finset.sum_le_sum
  intro i _
  have he := mul_le_mul_of_nonneg_left (norm_partitionRecovery_sub_le (v := v) hpos hsum i) (hpos i)
  simpa only [Finset.mul_sum, mul_assoc] using he

/-- An active-pair bound controls the whole weighted mismatch independently of the patch count. -/
theorem partition_pairwise_mismatch_le {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} {x : Space d} {D : ℝ}
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1)
    (hpair : ∀ i j, 0 < η i x → 0 < η j x → ‖v j x - v i x‖ ≤ D) :
    (∑ i, ∑ j, η i x * η j x * ‖v j x - v i x‖) ≤ D := by
  classical
  have hp (i j : ι) : η i x * η j x * ‖v j x - v i x‖ ≤ η i x * η j x * D := by
    rcases (hpos i).eq_or_lt with hi | hi
    · simp [← hi]
    rcases (hpos j).eq_or_lt with hj | hj
    · simp [← hj]
    exact mul_le_mul_of_nonneg_left (hpair i j hi hj) (mul_nonneg (hpos i) (hpos j))
  have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hp i j))
  simpa only [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, one_mul] using he

/-- A uniform bound on active pair differences gives a cardinality-free potential error. -/
theorem partitionRecovery_potential_le_of_overlap {ι : Type*} [Fintype ι] {d : ℕ}
    {W : ℝ → ℝ} {C : ℝ≥0} (hW : LipschitzOnWith C W (Icc 0 1))
    {η v : ι → Space d → ℝ} {x : Space d} {D : ℝ}
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1)
    (hval : ∀ i, v i x ∈ Icc (0 : ℝ) 1)
    (hpair : ∀ i j, 0 < η i x → 0 < η j x → ‖v j x - v i x‖ ≤ D) :
    W (partitionRecovery η v x) ≤ (∑ i, η i x * W (v i x)) + C * D :=
  (partitionRecovery_potential_le_pairwise hW hpos hsum hval).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (partition_pairwise_mismatch_le hpos hsum hpair) C.coe_nonneg))

/-- Bounded graph scales and close inverse scales give a common thin-layer mismatch bound. -/
theorem RigidityHypotheses.recoveryProfile_scale_difference_le
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ δ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {L M H ε : ℝ} (hL : 0 < L) (hM : 0 < M) (hLH : L ≤ H) (hMH : M ≤ H)
    (hclose : |L⁻¹ - M⁻¹| ≤ ε) (t : ℝ) :
    ‖recoveryProfile f δ (t / L) - recoveryProfile f δ (t / M)‖ ≤
      (Ioo 0 (recoveryTravelTime f δ 1 * H)).indicator
        (fun _ ↦ Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
          (recoveryTravelTime f δ 1 * H) * ε) t := by
  have hT := (hr.recoveryTravelTime_one_pos h hδ).le
  have hε : 0 ≤ ε := (abs_nonneg _).trans hclose
  have hH : 0 ≤ H := hL.le.trans hLH
  have hs : recoveryTravelTime f δ 1 * max L M ≤ recoveryTravelTime f δ 1 * H :=
    mul_le_mul_of_nonneg_left (max_le hLH hMH) hT
  have hb := hr.recoveryScaleMismatch_le h hδ (by norm_num : (0 : ℝ) < 1) hL hM t
  simp only [recoveryScaleMismatch, one_mul, div_one] at hb
  apply hb.trans
  by_cases ht : t ∈ Ioo 0 (recoveryTravelTime f δ 1 * max L M)
  · rw [indicator_of_mem ht, indicator_of_mem (show t ∈ Ioo 0 (recoveryTravelTime f δ 1 * H) from
      ⟨ht.1, ht.2.trans_le hs⟩)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)) hclose
      (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hT hH))
  · rw [indicator_of_notMem ht]
    exact indicator_nonneg (fun _ _ ↦
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hT hH)) hε) t

/-- The potential error of a finite graph-profile mixture is confined to one common layer,
with no factor depending on the number of patches. -/
theorem RigidityHypotheses.partitionRecovery_potential_overlap_le
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ δ : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) {C : ℝ≥0} (hW : LipschitzOnWith C (normalizedPotential f) (Icc 0 1))
    {η : ι → Space d → ℝ} {L : ι → ℝ} {ρ : Space d → ℝ} {x : Space d} {H ε : ℝ}
    (hpos : ∀ i, 0 ≤ η i x) (hsum : ∑ i, η i x = 1)
    (hL : ∀ i, 0 < L i) (hH : ∀ i, L i ≤ H)
    (hclose : ∀ i j, 0 < η i x → 0 < η j x → |(L j)⁻¹ - (L i)⁻¹| ≤ ε) :
    normalizedPotential f
        (partitionRecovery η (fun i y ↦ recoveryProfile f δ (ρ y / L i)) x) ≤
      (∑ i, η i x * normalizedPotential f (recoveryProfile f δ (ρ x / L i))) +
        C * (Ioo 0 (recoveryTravelTime f δ 1 * H)).indicator
          (fun _ ↦ Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
            (recoveryTravelTime f δ 1 * H) * ε) (ρ x) := by
  apply partitionRecovery_potential_le_of_overlap hW hpos hsum
    (fun i ↦ hr.recoveryProfile_mem_Icc h hδ _)
  intro i j hi hj
  exact hr.recoveryProfile_scale_difference_le h hδ (hL j) (hL i) (hH j) (hH i)
    (hclose i j hi hj) (ρ x)

end SerrinEpigraph
