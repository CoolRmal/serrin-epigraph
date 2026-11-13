module

public import SerrinEpigraph.PhaseNontriviality

/-!
# Simultaneous vanishing of bulk discrepancy and radial defect
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- Surface-normalized potential-minus-kinetic energy with a radial weight. -/
@[expose] def bulkEnergyDiscrepancy {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (f q : ℝ → ℝ) (c : Space (m + 1)) (r : ℝ) : ℝ :=
  r ^ (-(m : ℤ)) * ∫ x in epigraph g,
    (normalizedPotential f (u x) - ‖gradient u x‖ ^ 2 / 2) * radialWeight q c r x

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Modica's estimate gives nonnegative bulk discrepancy for nonnegative weights. -/
theorem RigidityHypotheses.bulkEnergyDiscrepancy_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ∀ s : ℝ, 0 ≤ s → 0 ≤ q s) (c : Space (m + 1))
    {r : ℝ} (hr0 : 0 < r) : 0 ≤ bulkEnergyDiscrepancy g u f q c r := by
  apply mul_nonneg (zpow_nonneg hr0.le _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
    with x hx
  exact mul_nonneg (sub_nonneg.mpr (hr.modica_bound h hx)) (hq _ (by positivity))

/-- The logarithmic energy derivative is exactly the sum of the two nonnegative defects. -/
theorem RigidityHypotheses.log_energy_derivative_eq_defects
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (c : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    r * deriv (weightedSurfaceEnergy g u f q c) r =
      bulkEnergyDiscrepancy g u f q c r + radialEnergyDefect g u q c r := by
  have hχ : Continuous (radialWeight q c r) := (contDiff_radialWeight hq c r).continuous
  have hc : HasCompactSupport (radialWeight q c r) :=
    (isCompact_closedBall c (2 * r)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_radialWeight_subset hzero c hr0)
  have hχ' : Continuous (radialWeight (deriv q) c r) :=
    (hq.continuous_deriv le_rfl).comp (show Continuous
      (fun x : Space (m + 1) ↦ ‖x - c‖ ^ 2 / r ^ 2) by fun_prop)
  have hiB := hr.integrableOn_discrepancy_mul h hχ hc
  have hiD : IntegrableOn (fun x ↦ -2 / r ^ 2 * radialWeight (deriv q) c r x *
      (inner ℝ (gradient u x) (x - c)) ^ 2) (epigraph g) := by
    have hh := (h.integrableOn_radialGradient_mul c hχ'
      (hasCompactSupport_radialWeight_deriv hzero c hr0)).const_mul (-2 / r ^ 2)
    exact hh.congr (Eventually.of_forall (fun x ↦ by dsimp only; ring))
  have hp : r ^ (-(m : ℤ)) = r ^ (-(m : ℤ) - 1) * r := by
    calc
      _ = r ^ ((-(m : ℤ) - 1) + 1) := by congr 1; omega
      _ = _ := by rw [zpow_add₀ hr0.ne', zpow_one]
  rw [(hr.weightedSurfaceEnergy_hasDerivAt h hq hzero c hr0).deriv, integral_add hiB hiD]
  unfold bulkEnergyDiscrepancy radialEnergyDefect
  rw [hp]
  ring

/-- The bulk discrepancy is bounded by the logarithmic derivative. -/
theorem RigidityHypotheses.bulkEnergyDiscrepancy_le_log_derivative
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hqanti : Antitone q) (c : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    bulkEnergyDiscrepancy g u f q c r ≤ r * deriv (weightedSurfaceEnergy g u f q c) r := by
  rw [hr.log_energy_derivative_eq_defects h hq hzero c hr0]
  exact le_add_of_nonneg_right (radialEnergyDefect_nonneg hqanti g u c hr0)

/-- One diverging sequence simultaneously controls both defects at every integer multiple. -/
theorem RigidityHypotheses.exists_scales_energy_defects_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hqrange : ∀ s : ℝ, 0 ≤ s → q s ∈ Icc (0 : ℝ) 1) (hqanti : Antitone q) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧ ∀ k : ℕ,
      Tendsto (fun j ↦ radialEnergyDefect g u q 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ bulkEnergyDiscrepancy g u f q 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := hr.weightedSurfaceEnergy_bound h hq hzero hqrange
  have hd (r : ℝ) (hr0 : 0 < r) :
      HasDerivAt (weightedSurfaceEnergy g u f q 0)
        (deriv (weightedSurfaceEnergy g u f q 0) r) r :=
    (hr.weightedSurfaceEnergy_hasDerivAt h hq hzero 0 hr0).differentiableAt.hasDerivAt
  have hD (r : ℝ) (hr0 : 0 < r) := hr.radialEnergyDefect_le_log_derivative h hq hzero
    (fun s hs ↦ (hqrange s hs).1) 0 hr0
  obtain ⟨R, hR, hRt, hlim⟩ := exists_scales_log_derivative_tendsto_zero hd
    (fun r hr0 ↦ (radialEnergyDefect_nonneg hqanti g u 0 hr0).trans (hD r hr0))
    (fun r hr1 ↦ ⟨hr.weightedSurfaceEnergy_nonneg h (fun s hs ↦ (hqrange s hs).1) 0
      (zero_lt_one.trans_le hr1), hb r hr1⟩)
  refine ⟨R, hR, hRt, fun k ↦ ?_⟩
  have hs (j : ℕ) : 0 < (k + 1 : ℝ) * R j :=
    mul_pos (by positivity) (zero_lt_one.trans_le (hR j))
  constructor
  · exact squeeze_zero (fun j ↦ radialEnergyDefect_nonneg hqanti g u 0 (hs j))
      (fun j ↦ hD _ (hs j)) (hlim k)
  · exact squeeze_zero (fun j ↦ hr.bulkEnergyDiscrepancy_nonneg h
      (fun s hs ↦ (hqrange s hs).1) 0 (hs j))
      (fun j ↦ hr.bulkEnergyDiscrepancy_le_log_derivative h hq hzero hqanti 0 (hs j)) (hlim k)

end SerrinEpigraph
