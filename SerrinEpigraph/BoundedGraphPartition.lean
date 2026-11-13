module

public import SerrinEpigraph.CompatibleGraphPartition

/-!
# Uniformly bounded scales for refining graph partitions
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace SerrinEpigraph

/-- A single scale bound works for every sufficiently fine compatible partition
on a fixed compact graph neighborhood. -/
theorem exists_uniformly_bounded_graphPartitions {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {A B : Set (Space d)} (hA : IsCompact A) (hB : IsCompact B)
    (hBA : B ⊆ interior A) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (s : Finset (Space d)) (L : s → ℝ) (w : s → Space d → ℝ),
        (∀ i, 1 ≤ L i ∧ L i ≤ H) ∧ (∀ i, ContDiff ℝ ∞ (w i)) ∧
        (∀ i, HasCompactSupport (w i)) ∧ (∀ i, tsupport (w i) ⊆ A) ∧
        (∀ i y, 0 ≤ w i y) ∧ (∀ y, ∑ i, w i y ≤ 1) ∧
        (∀ y ∈ B, ∑ i, w i y = 1) ∧
        (∀ i y, 0 < w i y →
          graphAreaDensity b y ≤ L i ∧ L i ≤ graphAreaDensity b y + ε) := by
  classical
  obtain ⟨M, hM⟩ := hA.exists_bound_of_continuousOn
    (continuous_graphAreaDensity hb).continuousOn
  let H := max 1 (M + 1)
  have hH : 1 ≤ H := le_max_left _ _
  refine ⟨H, hH, ?_⟩
  intro ε hε hεone
  obtain ⟨s, L, w, hL, hw, hwc, hws, hwpos, hwsum, hwone, hwscale⟩ :=
    exists_compatible_graphPartition hb hA hB hBA hε
  refine ⟨s, fun i ↦ min (L i) H, w, ?_, hw, hwc, hws, hwpos, hwsum, hwone, ?_⟩
  · intro i
    exact ⟨le_min (hL i) hH, min_le_right _ _⟩
  · intro i y hy
    have hym : y ∈ A := hws i (subset_closure
      (show y ∈ Function.support (w i) from ne_of_gt hy))
    have harea : graphAreaDensity b y ≤ M := by
      simpa only [Real.norm_of_nonneg (graphAreaDensity_pos b y).le] using hM y hym
    have hLH : L i ≤ H := calc
      L i ≤ graphAreaDensity b y + ε := (hwscale i y hy).2
      _ ≤ M + 1 := add_le_add harea hεone
      _ ≤ H := le_max_right _ _
    simpa only [min_eq_left hLH] using hwscale i y hy

/-- Partition precision can tend to zero fast enough to absorb any nonnegative
regularization-dependent potential-error coefficients. -/
theorem exists_graphPartition_precision (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun j ↦ a j * ε j) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  let ε : ℕ → ℝ := fun j ↦ r j / (a j + 1)
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hε (j : ℕ) : 0 < ε j := div_pos (hr j) (by linarith [ha j])
  have hbound (j : ℕ) : ε j ≤ r j := div_le_self (hr j).le (by linarith [ha j])
  have hcost (j : ℕ) : a j * ε j ≤ r j := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [ha j] : 0 < a j + 1)).mpr
    nlinarith [hr j]
  have ht : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨ε, fun j ↦ ⟨hε j, (hbound j).trans ?_⟩,
    squeeze_zero (fun j ↦ (hε j).le) hbound ht,
    squeeze_zero (fun j ↦ mul_nonneg (ha j) (hε j).le) hcost ht⟩
  exact div_le_self (by norm_num) (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)

end SerrinEpigraph
