module

public import SerrinEpigraph.GraphDivergence
public import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Smooth unit-bounded approximations with unchanged support
-/

public section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- A continuous unit-bounded field has smooth unit-bounded pointwise approximants
whose topological supports stay inside its original topological support. -/
theorem exists_contDiff_unit_field_approx {d : ℕ} {F : Space d → Space d}
    (hF : Continuous F) (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ∃ G : ℕ → Space d → Space d, (∀ j, ContDiff ℝ 1 (G j)) ∧
      (∀ j x, ‖G j x‖ ≤ 1) ∧ (∀ j, tsupport (G j) ⊆ tsupport F) ∧
      ∀ x, Tendsto (fun j ↦ G j x) atTop (𝓝 (F x)) := by
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hg (j : ℕ) := hF.exists_contDiff_approx 1 (ε := fun _ ↦ ε j)
    continuous_const (fun _ ↦ hε j)
  choose g hg hclose hs using hg
  let G := fun j x ↦ (1 + ε j)⁻¹ • g j x
  have hden (j : ℕ) : 0 < 1 + ε j := by linarith [hε j]
  have hnorm (j : ℕ) (x : Space d) : ‖g j x‖ ≤ 1 + ε j := by
    have he := norm_le_norm_add_norm_sub (F x) (g j x)
    rw [norm_sub_rev (F x) (g j x)] at he
    have hd := hclose j x
    rw [dist_eq_norm] at hd
    linarith [hunit x]
  have hG (j : ℕ) : ContDiff ℝ 1 (G j) := by
    have hg1 : ContDiff ℝ 1 (g j) := by simpa using hg j
    exact (contDiff_const (c := (1 + ε j)⁻¹)).smul hg1
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro j x
    simp only [G, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hden j).le)]
    calc
      _ ≤ (1 + ε j)⁻¹ * (1 + ε j) := mul_le_mul_of_nonneg_left (hnorm j x)
        (inv_nonneg.mpr (hden j).le)
      _ = 1 := inv_mul_cancel₀ (hden j).ne'
  · intro j
    apply closure_mono
    intro x hx
    apply hs j
    intro hzero
    exact hx (by simp only [G, hzero, smul_zero])
  · intro x
    have hgt : Tendsto (fun j ↦ g j x) atTop (𝓝 (F x)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ (hclose j x).le) hεt
    have hit : Tendsto (fun j ↦ (1 + ε j)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero, inv_one] using (hεt.const_add 1).inv₀ (by norm_num)
    simpa only [one_smul] using hit.smul hgt

end SerrinEpigraph
