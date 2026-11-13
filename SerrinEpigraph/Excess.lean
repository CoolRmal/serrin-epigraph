module

public import SerrinEpigraph.CutoffSupport
public import SerrinEpigraph.Mass
public import SerrinEpigraph.Truncation
public import SerrinEpigraph.SmoothExcess
public import SerrinEpigraph.CutoffDerivative
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Positive excess above a positive threshold

Continuity of the Dirichlet trace keeps each cutoff excess strictly away from the boundary.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The nonnegative excess of a function above a fixed threshold. -/
def excess {X : Type*} (u : X → ℝ) (s₀ : ℝ) (x : X) : ℝ := max (u x - s₀) 0

theorem excess_nonneg {X : Type*} (u : X → ℝ) (s₀ : ℝ) (x : X) :
    0 ≤ excess u s₀ x := le_max_right _ _

theorem excess_eq_zero_iff {X : Type*} {u : X → ℝ} {s₀ : ℝ} {x : X} :
    excess u s₀ x = 0 ↔ u x ≤ s₀ := by
  simp only [excess, max_eq_right_iff, sub_nonpos]

theorem excess_le_self {X : Type*} {u : X → ℝ} {s₀ : ℝ} {x : X}
    (hu : 0 ≤ u x) (hs₀ : 0 ≤ s₀) : excess u s₀ x ≤ u x := by
  exact max_le (sub_le_self _ hs₀) hu

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ s₀ : ℝ}

theorem continuousOn_excess_closure (h : Hypotheses g u f κ) :
    ContinuousOn (excess u s₀) (closure (epigraph g)) := by
  exact (h.solution_contDiffOn_closure.continuousOn.sub continuousOn_const).sup continuousOn_const

theorem solution_eq_zero_of_mem_frontier (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ frontier (epigraph g)) : u x = 0 := by
  have heq : g (horizontal x) = x (Fin.last m) := by
    simpa only [frontier_epigraph h.graph_contDiff.continuous, Set.mem_ofPred_eq] using hx
  simpa only [heq, point_horizontal_last] using h.dirichlet (horizontal x)

/-- The solution stays below a positive threshold locally on the inside of the frontier. -/
theorem eventually_solution_lt_on_epigraph_of_mem_frontier (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {x : Space (m + 1)} (hx : x ∈ frontier (epigraph g)) :
    ∀ᶠ y in 𝓝 x, y ∈ epigraph g → u y < s₀ := by
  have hc := h.solution_contDiffOn_closure.continuousOn x hx.1
  have hev : ∀ᶠ y in 𝓝[closure (epigraph g)] x, u y < s₀ :=
    hc (isOpen_Iio.mem_nhds (by
      simpa only [Set.mem_Iio, solution_eq_zero_of_mem_frontier h hx] using hs₀))
  filter_upwards [eventually_nhdsWithin_iff.1 hev] with y hy hyi
  exact hy (subset_closure hyi)

/-- A positive excess vanishes in an interior neighborhood of every boundary point. -/
theorem eventually_excess_eq_zero_on_epigraph_of_mem_frontier (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {x : Space (m + 1)} (hx : x ∈ frontier (epigraph g)) :
    ∀ᶠ y in 𝓝 x, y ∈ epigraph g → excess u s₀ y = 0 := by
  filter_upwards [eventually_solution_lt_on_epigraph_of_mem_frontier h hs₀ hx] with y hy hyi
  exact excess_eq_zero_iff.mpr (hy hyi).le

/-- Any truncation vanishing below the threshold gives compact interior cutoff support. -/
theorem hasCompactSupport_indicator_truncation_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {T : ℝ → ℝ} (hT : ∀ t, t ≤ 0 → T t = 0)
    {χ : Space (m + 1) → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport ((epigraph g).indicator (fun x ↦ T (u x - s₀) * χ x)) ∧
      tsupport ((epigraph g).indicator (fun x ↦ T (u x - s₀) * χ x)) ⊆ epigraph g := by
  simp only [HasCompactSupport, tsupport, Set.support_indicator]
  apply isCompact_closure_inter_support_subset_of_locally_zero_on_frontier hχ.mul_left
  intro x hx
  filter_upwards [eventually_solution_lt_on_epigraph_of_mem_frontier h hs₀ hx] with y hy hyi
  simp only [Pi.mul_apply, hT _ (sub_nonpos.mpr (hy hyi).le), zero_mul]

/-- A continuously differentiable truncation gives a global test after zero extension. -/
theorem contDiff_indicator_truncation_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {T : ℝ → ℝ} (hT : ∀ t, t ≤ 0 → T t = 0)
    (hTc : ContDiff ℝ 1 T) {χ : Space (m + 1) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ContDiff ℝ 1 ((epigraph g).indicator (fun x ↦ T (u x - s₀) * χ x)) := by
  have hsupp := (hasCompactSupport_indicator_truncation_mul h hs₀ hT hχc).2
  have htest : ContDiffOn ℝ 1
      ((epigraph g).indicator (fun x ↦ T (u x - s₀) * χ x)) (epigraph g) := by
    apply ((hTc.comp_contDiffOn
      ((h.solution_contDiffOn.of_le (by norm_num)).sub contDiffOn_const)).mul hχ.contDiffOn).congr
    intro x hx
    exact Set.indicator_of_mem hx _
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ tsupport ((epigraph g).indicator (fun x ↦ T (u x - s₀) * χ x))
  · exact htest.contDiffAt ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds (hsupp hx))
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.1 hx)

/-- Zero extension is continuous for any continuous truncation vanishing below the threshold. -/
theorem continuous_indicator_truncation_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {T : ℝ → ℝ} (hT : ∀ t, t ≤ 0 → T t = 0)
    (hTc : Continuous T) {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) :
    Continuous ((epigraph g).indicator (fun x ↦ T (u x - s₀) * χ x)) := by
  apply continuous_indicator
  · intro x hx
    rw [solution_eq_zero_of_mem_frontier h hx, hT _ (by linarith), zero_mul]
  · exact (hTc.comp_continuousOn
      (h.solution_contDiffOn_closure.continuousOn.sub continuousOn_const)).mul hχ.continuousOn

theorem hasCompactSupport_indicator_excess_pow_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {k : ℕ} (hk : k ≠ 0)
    {χ : Space (m + 1) → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport ((epigraph g).indicator (fun x ↦ excess u s₀ x ^ k * χ x)) ∧
      tsupport ((epigraph g).indicator (fun x ↦ excess u s₀ x ^ k * χ x)) ⊆ epigraph g := by
  exact hasCompactSupport_indicator_truncation_mul (T := fun t ↦ max t 0 ^ k) h hs₀
    (fun t ht ↦ by simp only [max_eq_right ht, zero_pow hk]) hχ

theorem contDiff_indicator_excess_pow_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {k : ℕ} (hk : 2 ≤ k) {χ : Space (m + 1) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ContDiff ℝ 1 ((epigraph g).indicator (fun x ↦ excess u s₀ x ^ k * χ x)) := by
  exact contDiff_indicator_truncation_mul (T := fun t ↦ max t 0 ^ k) h hs₀
    (fun t ht ↦ by simp only [max_eq_right ht, zero_pow (show k ≠ 0 by omega)])
    (contDiff_positivePart_pow hk) hχ hχc

theorem continuous_indicator_excess_pow_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {k : ℕ} (hk : k ≠ 0)
    {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) :
    Continuous ((epigraph g).indicator (fun x ↦ excess u s₀ x ^ k * χ x)) := by
  exact continuous_indicator_truncation_mul (T := fun t ↦ max t 0 ^ k) h hs₀
    (fun t ht ↦ by simp only [max_eq_right ht, zero_pow hk])
    ((continuous_id.max continuous_const).pow k) hχ

/-- A cutoff makes every positive power of the excess integrable. -/
theorem integrable_indicator_excess_pow_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {k : ℕ} (hk : k ≠ 0) {χ : Space (m + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable ((epigraph g).indicator (fun x ↦ excess u s₀ x ^ k * χ x)) := by
  exact (continuous_indicator_excess_pow_mul h hs₀ hk hχ).integrable_of_hasCompactSupport
    (hasCompactSupport_indicator_excess_pow_mul h hs₀ hk hχc).1

/-- The squared excess times a squared cutoff gradient is an integrable error term. -/
theorem integrable_indicator_excess_sq_gradient_error (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {η : Space (m + 1) → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    Integrable ((epigraph g).indicator
      (fun x ↦ excess u s₀ x ^ 2 * ‖gradient η x‖ ^ 2)) := by
  simp_rw [norm_gradient_eq_norm_fderiv]
  have hc : HasCompactSupport (fun x ↦ ‖fderiv ℝ η x‖ ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (hηc.fderiv ℝ).norm.mul_left
      (f := fun x ↦ ‖fderiv ℝ η x‖)
  exact integrable_indicator_excess_pow_mul h hs₀ (by norm_num)
    ((hη.continuous_fderiv one_ne_zero).norm.pow 2) hc

/-- Smooth excess tests have compact support strictly inside the epigraph. -/
theorem hasCompactSupport_indicator_smoothExcess_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) (ε : ℝ) {χ : Space (m + 1) → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport ((epigraph g).indicator (fun x ↦ smoothExcess ε (u x - s₀) * χ x)) ∧
      tsupport ((epigraph g).indicator (fun x ↦ smoothExcess ε (u x - s₀) * χ x)) ⊆
        epigraph g := by
  exact hasCompactSupport_indicator_truncation_mul h hs₀
    (fun _ ht ↦ smoothExcess_eq_zero_of_nonpos ε ht) hχc

/-- The smooth excess cutoff is globally continuously differentiable. -/
theorem contDiff_indicator_smoothExcess_mul (h : Hypotheses g u f κ)
    (hs₀ : 0 < s₀) {ε : ℝ} (hε : 0 < ε) {χ : Space (m + 1) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ContDiff ℝ 1
      ((epigraph g).indicator (fun x ↦ smoothExcess ε (u x - s₀) * χ x)) := by
  exact contDiff_indicator_truncation_mul h hs₀
    (fun _ ht ↦ smoothExcess_eq_zero_of_nonpos ε ht) (contDiff_smoothExcess hε) hχ hχc

theorem integrableOn_excess_sq_epigraph_inter_ball (h : Hypotheses g u f κ) (R : ℝ) :
    IntegrableOn (fun x ↦ excess u s₀ x ^ 2) (epigraph g ∩ Metric.ball 0 R) := by
  exact integrableOn_sq_epigraph_inter_ball (continuousOn_excess_closure h) R

/-- The truncated square is bounded by the solution mass on every bounded region. -/
theorem integral_excess_sq_le_squareMass (h : Hypotheses g u f κ) (hs₀ : 0 ≤ s₀) (R : ℝ) :
    (∫ x in epigraph g ∩ Metric.ball 0 R, excess u s₀ x ^ 2) ≤ squareMass g u R := by
  apply setIntegral_mono_on (integrableOn_excess_sq_epigraph_inter_ball h R)
    (integrableOn_sq_epigraph_inter_ball h.solution_contDiffOn_closure.continuousOn R)
    ((isOpen_epigraph h.graph_contDiff.continuous).measurableSet.inter measurableSet_ball)
  intro x hx
  exact pow_le_pow_left₀ (excess_nonneg u s₀ x)
    (excess_le_self (h.positive x hx.1).le hs₀) 2

end SerrinEpigraph
