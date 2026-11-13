module

public import SerrinEpigraph.IntegratedGluing
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Choosing the layer count at the diffuse scale
-/

public section

open Filter
open scoped Topology

namespace SerrinEpigraph

/-- A layer count comparable to the spatial scale bounds the mismatch coefficient
uniformly while making the energy coefficient decay. -/
theorem averaged_gluing_cost_le {A E D C W t R n : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (ht : 0 < t) (hR : 0 < R) (hn : R ≤ n) (hn' : n ≤ 2 * R) :
    (A * E + ((C * n / t) ^ 2 / R + 4 * R * W) * D) / n ≤
      A * E / R + (2 * C ^ 2 / t ^ 2 + 4 * W) * D := by
  have hnpos : 0 < n := hR.trans_le hn
  have he := div_le_div_of_nonneg_left (mul_nonneg hA hE) hR hn
  have hnr : n / R ≤ 2 := (div_le_iff₀ hR).mpr hn'
  have hrn : R / n ≤ 1 := (div_le_iff₀ hnpos).mpr (by simpa using hn)
  have hfirst := mul_le_mul_of_nonneg_left hnr
    (div_nonneg (sq_nonneg C) (sq_nonneg t))
  have hsecond := mul_le_mul_of_nonneg_left hrn (show 0 ≤ 4 * W by positivity)
  have hm := mul_le_mul_of_nonneg_right (add_le_add hfirst hsecond) hD
  have hid : (A * E + ((C * n / t) ^ 2 / R + 4 * R * W) * D) / n =
      A * E / n + (C ^ 2 / t ^ 2 * (n / R) + 4 * W * (R / n)) * D := by
    field_simp
  rw [hid]
  convert add_le_add he hm using 1
  ring

/-- The natural ceiling supplies an admissible layer count whenever the scale is at least one. -/
theorem averaged_gluing_cost_ceil_le {A E D C W t R : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (ht : 0 < t) (hR : 1 ≤ R) :
    (A * E + ((C * (⌈R⌉₊ : ℝ) / t) ^ 2 / R + 4 * R * W) * D) / ⌈R⌉₊ ≤
      A * E / R + (2 * C ^ 2 / t ^ 2 + 4 * W) * D := by
  apply averaged_gluing_cost_le hA hE hD hW ht (by linarith) (Nat.le_ceil R)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ R by linarith)
  linarith

/-- Bounded input energy and vanishing squared mismatch imply vanishing averaged
gluing error when the number of layers is the ceiling of the scale. -/
theorem averaged_gluing_cost_tendsto_zero {A C W t B : ℝ} {R E D : ℕ → ℝ}
    (hA : 0 ≤ A) (hW : 0 ≤ W) (ht : 0 < t)
    (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    (hE : ∀ j, 0 ≤ E j) (hEB : ∀ j, E j ≤ B)
    (hD : ∀ j, 0 ≤ D j) (hDzero : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun j ↦
      (A * E j + ((C * (⌈R j⌉₊ : ℝ) / t) ^ 2 / R j + 4 * R j * W) * D j) /
        ⌈R j⌉₊) atTop (𝓝 0) := by
  have hupper : Tendsto (fun j ↦ A * B / R j + (2 * C ^ 2 / t ^ 2 + 4 * W) * D j)
      atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.comp hRtop).const_mul (A * B)).add
      (hDzero.const_mul (2 * C ^ 2 / t ^ 2 + 4 * W))
    simpa only [mul_zero, zero_add, div_eq_mul_inv, Function.comp_def] using hh
  apply squeeze_zero _ _ hupper
  · intro j
    have hr : 0 ≤ R j := le_trans zero_le_one (hR j)
    have he := hE j
    have hd := hD j
    positivity
  · intro j
    have he := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hEB j) hA)
      (le_trans zero_le_one (hR j))
    exact (averaged_gluing_cost_ceil_le hA (hE j) (hD j) hW ht (hR j)).trans
      (add_le_add he le_rfl)

/-- The averaged integral majorant vanishes for bounded-energy normalized inputs whose
squared mismatch tends to zero, with the layer count chosen at the diffuse scale. -/
theorem RigidityHypotheses.gluingCost_average_tendsto_zero
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v : ℕ → Space d → ℝ} (hU : ∀ j, LocallyLipschitz (U j))
    (hv : ∀ j, LocallyLipschitz (v j))
    (hUval : ∀ j x, U j x ∈ Set.Icc (0 : ℝ) 1)
    (hvval : ∀ j x, v j x ∈ Set.Icc (0 : ℝ) 1)
    {K : Set (Space d)} (hK : IsCompact K) {C t B : ℝ} (ht : 0 < t)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    (hEB : ∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in K, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B)
    (hDzero : Tendsto (fun j ↦ ∫ x in K, (v j x - U j x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j ↦
      (∫ x in K, gluingCost f (R j) (C * (⌈R j⌉₊ : ℝ) / t) (U j) (v j) x) /
        ⌈R j⌉₊) atTop (𝓝 0) := by
  have he := fun j ↦ h.integral_gluingCost (hU j) (hv j) (hUval j) (hvval j)
    (R j) (C * (⌈R j⌉₊ : ℝ) / t) hK
  simp_rw [he]
  apply averaged_gluing_cost_tendsto_zero
    (le_trans (show (0 : ℝ) ≤ 2 by norm_num) (le_max_left _ _))
    (hr.normalizedPotential_nonneg h (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num))
    ht hR hRtop _ hEB _ hDzero
  · intro j
    have hj := le_trans zero_le_one (hR j)
    exact add_nonneg
      (MeasureTheory.integral_nonneg (hr.rescaledPhaseEnergyDensity_nonneg h hj (hUval j)))
      (MeasureTheory.integral_nonneg (hr.rescaledPhaseEnergyDensity_nonneg h hj (hvval j)))
  · intro j
    exact MeasureTheory.integral_nonneg (fun x ↦ sq_nonneg _)

end SerrinEpigraph
