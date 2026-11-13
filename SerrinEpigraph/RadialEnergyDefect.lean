module

public import SerrinEpigraph.SurfaceEnergyLimit
public import SerrinEpigraph.BoundedScaleSelection

/-!
# The radial energy defect is controlled by the logarithmic scale derivative
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- Surface-normalized squared radial derivative, weighted by the negative profile derivative. -/
@[expose] def radialEnergyDefect {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (q : ℝ → ℝ) (c : Space (m + 1)) (r : ℝ) : ℝ :=
  r ^ (-(m : ℤ)) * ∫ x in epigraph g, -2 / r ^ 2 * radialWeight (deriv q) c r x *
    (inner ℝ (gradient u x) (x - c)) ^ 2

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Squared radial derivatives have finite integrals against every compact continuous weight. -/
theorem Hypotheses.integrableOn_radialGradient_mul (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {χ : Space (m + 1) → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) :
    IntegrableOn (fun x ↦ (inner ℝ (gradient u x) (x - c)) ^ 2 * χ x) (epigraph g) := by
  have hA : ContinuousOn (fun x ↦
      (inner ℝ (gradientWithin u (closure (epigraph g)) x) (x - c)) ^ 2)
      (closure (epigraph g)) := (h.closed_gradient_continuousOn.inner
        (continuous_id.sub continuous_const).continuousOn).pow 2
  apply (integrableOn_mul_of_continuousOn_closure
    (isOpen_epigraph h.graph_contDiff.continuous).measurableSet hA hχ hc).congr_fun _
      (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  intro x hx
  dsimp only
  rw [h.closed_gradient_eq hx]

/-- The discrepancy has finite integrals against compact continuous weights. -/
theorem RigidityHypotheses.integrableOn_discrepancy_mul
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    IntegrableOn (fun x ↦ (normalizedPotential f (u x) - ‖gradient u x‖ ^ 2 / 2) * χ x)
      (epigraph g) := by
  have hW := h.normalizedPotential_continuousOn.comp h.solution_contDiffOn_closure.continuousOn
    (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
  have hA := hW.sub ((h.closed_gradient_continuousOn.norm.pow 2).div_const 2)
  apply (integrableOn_mul_of_continuousOn_closure
    (isOpen_epigraph h.graph_contDiff.continuous).measurableSet hA hχ hc).congr_fun _
      (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  intro x hx
  dsimp only [Pi.sub_apply, Pi.pow_apply, Function.comp_def]
  rw [h.closed_gradient_eq hx]

/-- The derivative of surface-scaled weighted energy splits into discrepancy and radial defect. -/
theorem RigidityHypotheses.weightedSurfaceEnergy_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (c : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    HasDerivAt (weightedSurfaceEnergy g u f q c)
      (r ^ (-(m : ℤ) - 1) * ∫ x in epigraph g,
        (normalizedPotential f (u x) - ‖gradient u x‖ ^ 2 / 2) * radialWeight q c r x +
          -2 / r ^ 2 * radialWeight (deriv q) c r x *
            (inner ℝ (gradient u x) (x - c)) ^ 2) r := by
  have hd := hr.radial_energy_hasDerivAt h (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
    hq hzero c (-(m : ℤ)) hr0
  convert hd using 1
  · rfl
  · congr 1
    apply setIntegral_congr_fun (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
    intro x _
    simp only [Int.cast_neg, Int.cast_natCast]
    ring

/-- Decreasing profiles give nonnegative radial defects. -/
theorem radialEnergyDefect_nonneg {q : ℝ → ℝ} (hq : Antitone q)
    (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (c : Space (m + 1))
    {r : ℝ} (hr0 : 0 < r) : 0 ≤ radialEnergyDefect g u q c r := by
  apply mul_nonneg (zpow_nonneg hr0.le _)
  apply integral_nonneg
  intro x
  exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)) hq.deriv_nonpos) (sq_nonneg _)

/-- Modica's bound makes the radial defect no larger than the logarithmic energy derivative. -/
theorem RigidityHypotheses.radialEnergyDefect_le_log_derivative
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hq0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ q s) (c : Space (m + 1))
    {r : ℝ} (hr0 : 0 < r) :
    radialEnergyDefect g u q c r ≤ r * deriv (weightedSurfaceEnergy g u f q c) r := by
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
    apply hh.congr (Eventually.of_forall (fun x ↦ by dsimp only; ring))
  have hB0 : 0 ≤ ∫ x in epigraph g,
      (normalizedPotential f (u x) - ‖gradient u x‖ ^ 2 / 2) * radialWeight q c r x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
      with x hx
    exact mul_nonneg (sub_nonneg.mpr (hr.modica_bound h hx)) (hq0 _ (by positivity))
  have hp : r ^ (-(m : ℤ)) = r ^ (-(m : ℤ) - 1) * r := by
    calc
      _ = r ^ ((-(m : ℤ) - 1) + 1) := by congr 1; omega
      _ = _ := by rw [zpow_add₀ hr0.ne', zpow_one]
  rw [(hr.weightedSurfaceEnergy_hasDerivAt h hq hzero c hr0).deriv, integral_add hiB hiD]
  unfold radialEnergyDefect
  rw [← mul_assoc, mul_comm r (r ^ (-(m : ℤ) - 1)), ← hp]
  have hh := mul_nonneg (zpow_nonneg hr0.le (-(m : ℤ))) hB0
  nlinarith only [hh]

/-- One sequence controls radial defects at every fixed integer multiple of its scale. -/
theorem RigidityHypotheses.exists_scales_radialEnergyDefect_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hqrange : ∀ s : ℝ, 0 ≤ s → q s ∈ Icc (0 : ℝ) 1) (hqanti : Antitone q) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∀ k : ℕ, Tendsto (fun j ↦ radialEnergyDefect g u q 0 ((k + 1 : ℝ) * R j))
        atTop (𝓝 0) := by
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
  apply squeeze_zero (fun j ↦ radialEnergyDefect_nonneg hqanti g u 0
    (mul_pos (by positivity) (zero_lt_one.trans_le (hR j)))) _ (hlim k)
  intro j
  exact hD _ (mul_pos (by positivity) (zero_lt_one.trans_le (hR j)))

end SerrinEpigraph
