module

public import SerrinEpigraph.GraphRecoveryComparison

/-!+# Diagonal scales for varying recovery partitions
-/

public section

open Filter
open scoped Topology

namespace SerrinEpigraph

/-- After choosing each partition and regularization, a diagonal subsequence of
positive integer scales makes both its kinetic error and its layer width vanish. -/
theorem exists_recovery_diagonal_scale {e : ℕ → ℕ → ℝ} {T : ℕ → ℝ}
    (he : ∀ j k, 0 ≤ e j k) (het : ∀ j, Tendsto (e j) atTop (𝓝 0))
    (hT : ∀ j, 0 ≤ T j) :
    ∃ n : ℕ → ℕ, (∀ j, j ≤ n j) ∧
      Tendsto (fun j ↦ (n j : ℝ) + 1) atTop atTop ∧
      Tendsto (fun j ↦ e j (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ T j / ((n j : ℝ) + 1)) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoice (j : ℕ) : ∃ k : ℕ,
      j ≤ k ∧ e j k < r j ∧ T j / ((k : ℝ) + 1) < r j := by
    have ht : Tendsto (fun k : ℕ ↦ T j / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [r, mul_zero, mul_one_div] using
        (tendsto_const_nhds (x := T j)).mul hrt
    exact ((eventually_ge_atTop j).and
      (((het j).eventually (gt_mem_nhds (hr j))).and
        (ht.eventually (gt_mem_nhds (hr j))))).exists
  choose n hn he' hT' using hchoice
  refine ⟨n, hn, ?_, squeeze_zero (fun j ↦ he j (n j)) (fun j ↦ (he' j).le) hrt,
    squeeze_zero (fun j ↦ div_nonneg (hT j) (by positivity))
      (fun j ↦ (hT' j).le) hrt⟩
  apply tendsto_atTop_mono (fun j : ℕ ↦ show (j : ℝ) ≤ (n j : ℝ) + 1 by
    exact le_trans (Nat.cast_le.mpr (hn j)) (by linarith))
  exact tendsto_natCast_atTop_atTop

/-- Uniformly bounded graph scales give eventual exact phase values even when
the finite partition and its index type change at every step. -/
theorem RigidityHypotheses.varying_graphRecovery_eventually_eq
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)] {m d : ℕ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    {H : ℝ} {L : (j : ℕ) → ι j → ℝ}
    (hL : ∀ j i, 0 < L j i) (hLH : ∀ j i, L j i ≤ H)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 * H / R j) atTop (𝓝 0))
    {b : Space d → ℝ} {η : (j : ℕ) → ι j → Space (d + 1) → ℝ}
    {x : Space (d + 1)} (hone : ∀ j, ∑ i, η j i x = 1) :
    ∀ᶠ j in atTop,
      partitionRecovery (η j)
        (fun i z ↦ recoveryProfile f (δ j) (R j * graphHeight b z / L j i)) x =
      (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  by_cases hx : 0 < graphHeight b x
  · filter_upwards [hwidth.eventually (gt_mem_nhds hx)] with j hj
    have hq (i : ι j) :
        recoveryProfile f (δ j) (R j * graphHeight b x / L j i) = 1 := by
      apply hr.recoveryProfile_eq_one h (hδ j)
      apply (le_div_iff₀ (hL j i)).mpr
      have ht := hr.recoveryTravelTime_one_pos h (hδ j)
      have hbound := mul_le_mul_of_nonneg_left (hLH j i) ht.le
      have hj' := (div_lt_iff₀ (hR j)).mp hj
      nlinarith
    have hxE : x ∈ epigraph b := sub_pos.mp hx
    simpa only [partitionRecovery, hq, mul_one, Set.indicator_of_mem hxE] using hone j
  · apply Eventually.of_forall
    intro j
    have hq (i : ι j) :
        recoveryProfile f (δ j) (R j * graphHeight b x / L j i) = 0 := by
      apply hr.recoveryProfile_eq_zero h (hδ j)
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (hR j).le (le_of_not_gt hx)) (hL j i).le
    have hxE : x ∉ epigraph b := fun hxE ↦ hx (sub_pos.mpr hxE)
    simp only [partitionRecovery, hq, mul_zero, Finset.sum_const_zero,
      Set.indicator_of_notMem hxE]

/-- Diagonal recovery errors and layer widths can vanish along a prescribed
diverging scale sequence, while the selected indices themselves tend to infinity. -/
theorem exists_recovery_diagonal_subsequence {e : ℕ → ℕ → ℝ} {T R : ℕ → ℝ}
    (he : ∀ j k, 0 ≤ e j k) (het : ∀ j, Tendsto (e j) atTop (𝓝 0))
    (hT : ∀ j, 0 ≤ T j) (hR : ∀ k, 0 < R k) (hRt : Tendsto R atTop atTop) :
    ∃ n : ℕ → ℕ, (∀ j, j ≤ n j) ∧ Tendsto n atTop atTop ∧
      Tendsto (fun j ↦ e j (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ T j / R (n j)) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoice (j : ℕ) : ∃ k : ℕ, j ≤ k ∧ e j k < r j ∧ T j / R k < r j := by
    have ht : Tendsto (fun k ↦ T j / R k) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
        (tendsto_inv_atTop_zero.comp hRt).const_mul (T j)
    exact ((eventually_ge_atTop j).and
      (((het j).eventually (gt_mem_nhds (hr j))).and
        (ht.eventually (gt_mem_nhds (hr j))))).exists
  choose n hn he' hT' using hchoice
  exact ⟨n, hn, tendsto_atTop_mono hn tendsto_id,
    squeeze_zero (fun j ↦ he j (n j)) (fun j ↦ (he' j).le) hrt,
    squeeze_zero (fun j ↦ div_nonneg (hT j) (hR _).le) (fun j ↦ (hT' j).le) hrt⟩

end SerrinEpigraph
