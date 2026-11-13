module

public import SerrinEpigraph.Geometry
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Epigraph rescaling and one-sided bounds at large scales
-/

public section
noncomputable section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- The graph seen at spatial scale R. -/
@[expose] def rescaledGraph {m : ℕ} (g : Space m → ℝ) (R : ℝ) (y : Space m) : ℝ :=
  g (R • y) / R

/-- Rescaling the graph agrees exactly with rescaling its epigraph. -/
theorem mem_epigraph_rescaledGraph_iff {m : ℕ} {g : Space m → ℝ} {R : ℝ}
    (hR : 0 < R) (x : Space (m + 1)) :
    x ∈ epigraph (rescaledGraph g R) ↔ R • x ∈ epigraph g := by
  have hh : horizontal (R • x) = R • horizontal x := by
    ext i
    simp [horizontal]
  change g (R • horizontal x) / R < x (Fin.last m) ↔
    g (horizontal (R • x)) < (R • x) (Fin.last m)
  rw [hh, div_lt_iff₀ hR]
  simp [mul_comm]

/-- A lower linear graph bound rescales with an intercept of order 1/R. -/
theorem rescaledGraph_lower_bound {m : ℕ} {g : Space m → ℝ} {C R : ℝ}
    (hg : ∀ y, -C * (1 + ‖y‖) ≤ g y) (hR : 0 < R) (y : Space m) :
    -C * (1 / R + ‖y‖) ≤ rescaledGraph g R y := by
  have hh := hg (R • y)
  rw [norm_smul, Real.norm_of_nonneg hR.le] at hh
  apply (le_div_iff₀ hR).mpr
  convert hh using 1
  field_simp

/-- The upper linear graph bound has the same vanishing intercept under rescaling. -/
theorem rescaledGraph_upper_bound {m : ℕ} {g : Space m → ℝ} {C R : ℝ}
    (hg : ∀ y, g y ≤ C * (1 + ‖y‖)) (hR : 0 < R) (y : Space m) :
    rescaledGraph g R y ≤ C * (1 / R + ‖y‖) := by
  have hh := hg (R • y)
  rw [norm_smul, Real.norm_of_nonneg hR.le] at hh
  apply (div_le_iff₀ hR).mpr
  convert hh using 1
  field_simp

/-- Every pointwise large-scale graph limit inherits the homogeneous lower cone bound. -/
theorem rescaledGraph_limit_lower_bound {m : ℕ} {g G : Space m → ℝ} {C : ℝ}
    (hg : ∀ y, -C * (1 + ‖y‖) ≤ g y)
    (hlim : ∀ y, Tendsto (fun R : ℝ ↦ rescaledGraph g R y) atTop (𝓝 (G y))) :
    ∀ y, -C * ‖y‖ ≤ G y := by
  intro y
  have hb : Tendsto (fun R : ℝ ↦ -C * (1 / R + ‖y‖)) atTop (𝓝 (-C * ‖y‖)) := by
    simpa only [zero_add, one_div] using
      (tendsto_const_nhds (x := -C)).mul
        ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).add
          (tendsto_const_nhds (x := ‖y‖)))
  apply le_of_tendsto_of_tendsto hb (hlim y)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact rescaledGraph_lower_bound hg hR y

/-- Every pointwise large-scale graph limit inherits the homogeneous upper cone bound. -/
theorem rescaledGraph_limit_upper_bound {m : ℕ} {g G : Space m → ℝ} {C : ℝ}
    (hg : ∀ y, g y ≤ C * (1 + ‖y‖))
    (hlim : ∀ y, Tendsto (fun R : ℝ ↦ rescaledGraph g R y) atTop (𝓝 (G y))) :
    ∀ y, G y ≤ C * ‖y‖ := by
  intro y
  have hb : Tendsto (fun R : ℝ ↦ C * (1 / R + ‖y‖)) atTop (𝓝 (C * ‖y‖)) := by
    simpa only [zero_add, one_div] using
      (tendsto_const_nhds (x := C)).mul
        ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).add
          (tendsto_const_nhds (x := ‖y‖)))
  apply le_of_tendsto_of_tendsto (hlim y) hb
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact rescaledGraph_upper_bound hg hR y

/-- Either one-sided linear hypothesis yields the corresponding homogeneous cone bound
for a pointwise graph limit. This statement does not assume or assert existence of that limit. -/
theorem HasOneSidedLinearBound.rescaledGraph_limit {m : ℕ} {g G : Space m → ℝ}
    (hg : HasOneSidedLinearBound g)
    (hlim : ∀ y, Tendsto (fun R : ℝ ↦ rescaledGraph g R y) atTop (𝓝 (G y))) :
    (∃ C : ℝ, 0 < C ∧ ∀ y, -C * ‖y‖ ≤ G y) ∨
      (∃ C : ℝ, 0 < C ∧ ∀ y, G y ≤ C * ‖y‖) := by
  rcases hg with ⟨C, hC, hbound⟩ | ⟨C, hC, hbound⟩
  · exact Or.inl ⟨C, hC, rescaledGraph_limit_lower_bound hbound hlim⟩
  · exact Or.inr ⟨C, hC, rescaledGraph_limit_upper_bound hbound hlim⟩

end SerrinEpigraph
