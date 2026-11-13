module

public import SerrinEpigraph.GluingScaleChoice
public import SerrinEpigraph.IntegralCauchyApproximation

/-!
# Squared mismatch from a common local integral limit
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- On the normalized interval, squared mismatch is bounded by absolute mismatch. -/
theorem sq_sub_le_norm_sub_of_mem_unit_interval {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (a - b) ^ 2 ≤ ‖a - b‖ := by
  have hab : |a - b| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1, hb.2],
    by linarith [ha.2, hb.1]⟩
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (a - b), abs_nonneg (a - b)]

/-- The local squared mismatch is controlled by the two absolute errors to any common limit. -/
theorem integral_sq_mismatch_le_common_errors {d : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) {U v z : Space d → ℝ} (hU : Continuous U) (hv : Continuous v)
    (hUval : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hz : IntegrableOn z K) :
    (∫ x in K, (v x - U x) ^ 2) ≤
      (∫ x in K, ‖v x - z x‖) + ∫ x in K, ‖U x - z x‖ := by
  have his := ((hv.sub hU).pow 2).continuousOn.integrableOn_compact (μ := volume) hK
  have hin := (hv.sub hU).norm.continuousOn.integrableOn_compact (μ := volume) hK
  have he := integral_mono his hin
    (fun x ↦ sq_sub_le_norm_sub_of_mem_unit_interval (hvval x) (hUval x))
  have ht := integral_norm_sub_triangle (hv.continuousOn.integrableOn_compact hK) hz
    (hU.continuousOn.integrableOn_compact hK)
  simp only [Pi.pow_apply, Pi.sub_apply] at he
  simp_rw [norm_sub_rev (z _) (U _)] at ht
  exact he.trans ht

/-- Normalized continuous sequences with the same local L1 limit have vanishing
squared mismatch on compact sets. -/
theorem integral_sq_mismatch_tendsto_zero {d : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) {U v : ℕ → Space d → ℝ} {z : Space d → ℝ}
    (hU : ∀ j, Continuous (U j)) (hv : ∀ j, Continuous (v j))
    (hUval : ∀ j x, U j x ∈ Icc (0 : ℝ) 1)
    (hvval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1) (hz : IntegrableOn z K)
    (hUz : Tendsto (fun j ↦ ∫ x in K, ‖U j x - z x‖) atTop (𝓝 0))
    (hvz : Tendsto (fun j ↦ ∫ x in K, ‖v j x - z x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K, (v j x - U j x) ^ 2) atTop (𝓝 0) := by
  have ht := hvz.add hUz
  simp only [zero_add] at ht
  exact squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ sq_nonneg _))
    (fun j ↦ integral_sq_mismatch_le_common_errors hK (hU j) (hv j) (hUval j) (hvval j) hz) ht

/-- Common local L1 convergence and bounded energy suffice for the averaged gluing
majorant to vanish; no separate squared-mismatch hypothesis is needed. -/
theorem RigidityHypotheses.gluingCost_average_tendsto_zero_of_common_limit
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {U v : ℕ → Space d → ℝ} {z : Space d → ℝ}
    (hU : ∀ j, LocallyLipschitz (U j)) (hv : ∀ j, LocallyLipschitz (v j))
    (hUval : ∀ j x, U j x ∈ Icc (0 : ℝ) 1)
    (hvval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {K : Set (Space d)} (hK : IsCompact K) (hz : IntegrableOn z K)
    {C t B : ℝ} (ht : 0 < t) {R : ℕ → ℝ}
    (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    (hEB : ∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in K, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B)
    (hUz : Tendsto (fun j ↦ ∫ x in K, ‖U j x - z x‖) atTop (𝓝 0))
    (hvz : Tendsto (fun j ↦ ∫ x in K, ‖v j x - z x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦
      (∫ x in K, gluingCost f (R j) (C * (⌈R j⌉₊ : ℝ) / t) (U j) (v j) x) /
        ⌈R j⌉₊) atTop (𝓝 0) := by
  apply hr.gluingCost_average_tendsto_zero h hU hv hUval hvval hK ht hR hRtop hEB
  exact integral_sq_mismatch_tendsto_zero hK (fun j ↦ (hU j).continuous)
    (fun j ↦ (hv j).continuous) hUval hvval hz hUz hvz

end SerrinEpigraph
