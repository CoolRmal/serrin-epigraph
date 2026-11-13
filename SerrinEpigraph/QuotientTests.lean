module

public import SerrinEpigraph.CutoffSupport
public import SerrinEpigraph.Truncation

/-!
# Continuously differentiable quotient test functions

Powers at least two remove the corner of the negative part at zero. Their cutoff extensions
are globally continuously differentiable and supported strictly inside the epigraph.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace SerrinEpigraph

variable {m k : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

theorem contDiffOn_negativeVerticalRatio (h : Hypotheses g u f κ) :
    ContDiffOn ℝ 1 (fun x ↦ -verticalDerivative u x / u x) (epigraph g) := by
  have hd := h.solution_contDiffOn.fderiv_of_isOpen
    (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num)
  have hv : ContDiffOn ℝ 1 (verticalDerivative u) (epigraph g) := hd.clm_apply contDiffOn_const
  exact hv.neg.div (h.solution_contDiffOn.of_le (by norm_num))
    (fun x hx ↦ (h.positive x hx).ne')

/-- Powers at least two of the negative quotient are continuously differentiable in Ω. -/
theorem contDiffOn_negativeQuotient_pow (h : Hypotheses g u f κ) (hk : 2 ≤ k) :
    ContDiffOn ℝ 1 (fun x ↦ negativeQuotient u x ^ k) (epigraph g) := by
  exact (contDiff_positivePart_pow hk).comp_contDiffOn (contDiffOn_negativeVerticalRatio h)

/-- The power chain rule holds even at zeros of the negative quotient. -/
theorem hasFDerivAt_negativeQuotient_pow (h : Hypotheses g u f κ) (hk : 2 ≤ k)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    HasFDerivAt (fun y ↦ negativeQuotient u y ^ k)
      ((k * negativeQuotient u x ^ (k - 1)) •
        fderiv ℝ (fun y ↦ -verticalDerivative u y / u y) x) x := by
  have hd := ((contDiffOn_negativeVerticalRatio h).contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)).differentiableAt (by norm_num)
  have hh := (hasDerivAt_positivePart_pow hk (-verticalDerivative u x / u x)).comp_hasFDerivAt x
    hd.hasFDerivAt
  simpa only [Function.comp_def, negativeQuotient] using hh

/-- Cutoff powers of the negative quotient have compact support strictly inside Ω. -/
theorem hasCompactSupport_indicator_negativeQuotient_pow_mul (h : Hypotheses g u f κ)
    (hk : k ≠ 0) {χ : Space (m + 1) → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport ((epigraph g).indicator (fun x ↦ negativeQuotient u x ^ k * χ x)) ∧
      tsupport ((epigraph g).indicator (fun x ↦ negativeQuotient u x ^ k * χ x)) ⊆ epigraph g := by
  simp only [HasCompactSupport, tsupport, Set.support_indicator]
  apply isCompact_closure_inter_support_subset_of_locally_zero_on_frontier
    (hχ.mul_left (f := fun x ↦ negativeQuotient u x ^ k))
  intro x hx
  filter_upwards [eventually_negativeQuotient_eq_zero_on_epigraph_of_mem_frontier h hx]
    with z hz hzi
  simp only [Pi.mul_apply, hz hzi, zero_pow hk, zero_mul]

/-- Zero extension preserves the continuously differentiable cutoff test. -/
theorem contDiff_indicator_negativeQuotient_pow_mul (h : Hypotheses g u f κ)
    (hk : 2 ≤ k) {χ : Space (m + 1) → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hcχ : HasCompactSupport χ) :
    ContDiff ℝ 1 ((epigraph g).indicator (fun x ↦ negativeQuotient u x ^ k * χ x)) := by
  have hsupp :=
    (hasCompactSupport_indicator_negativeQuotient_pow_mul (k := k) h (by omega) hcχ).2
  have htest : ContDiffOn ℝ 1
      ((epigraph g).indicator (fun x ↦ negativeQuotient u x ^ k * χ x)) (epigraph g) := by
    apply ((contDiffOn_negativeQuotient_pow h hk).mul hχ.contDiffOn).congr
    intro x hx
    exact Set.indicator_of_mem hx _
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ tsupport ((epigraph g).indicator (fun x ↦ negativeQuotient u x ^ k * χ x))
  · exact htest.contDiffAt ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds (hsupp hx))
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.1 hx)

end SerrinEpigraph
