module

public import SerrinEpigraph.ZeroExtension
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth normalized approximations of the zero extension
-/

public section
noncomputable section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution

namespace SerrinEpigraph

/-- A sequence of smooth averaging kernels with radii tending to zero. -/
@[expose] def averagingBump (d n : ℕ) : ContDiffBump (0 : Space d) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- Convolution with the normalized averaging kernel. -/
@[expose] def mollify {d : ℕ} (v : Space d → ℝ) (n : ℕ) : Space d → ℝ :=
  (averagingBump d n).normed volume ⋆[lsmul ℝ ℝ, volume] v

/-- A small contraction ensures that the smooth approximation remains strictly below one. -/
@[expose] def normalizedMollify {d : ℕ} (v : Space d → ℝ) (n : ℕ) : Space d → ℝ :=
  fun x ↦ (1 - 1 / ((n : ℝ) + 2)) * mollify v n x

/-- Each average of a continuous function is smooth. -/
theorem mollify_contDiff {d : ℕ} {v : Space d → ℝ} (hv : Continuous v) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify v n) :=
  (averagingBump d n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (averagingBump d n).contDiff_normed hv.locallyIntegrable

/-- The averaging sequence converges at every continuity point of a continuous function. -/
theorem mollify_tendsto {d : ℕ} {v : Space d → ℝ} (hv : Continuous v) (x : Space d) :
    Tendsto (fun n ↦ mollify v n x) atTop (𝓝 (v x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous
    (φ := averagingBump d) tendsto_one_div_add_atTop_nhds_zero_nat hv x

/-- Nonnegative functions have nonnegative averages. -/
theorem mollify_nonneg {d : ℕ} {v : Space d → ℝ} (hv : ∀ x, 0 ≤ v x)
    (n : ℕ) (x : Space d) : 0 ≤ mollify v n x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg ((averagingBump d n).nonneg_normed y) (hv (x - y))

/-- A constant upper bound is preserved by averaging. -/
theorem mollify_le {d : ℕ} {v : Space d → ℝ} (hv : Continuous v) {b : ℝ}
    (hb : ∀ x, v x ≤ b) (n : ℕ) (x : Space d) : mollify v n x ≤ b := by
  have he := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume)
    (lsmul ℝ ℝ) (averagingBump d n).continuous_normed hv.locallyIntegrable
  have hc := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (μ := volume)
    (lsmul ℝ ℝ) (averagingBump d n).continuous_normed
    (continuous_const (y := b)).locallyIntegrable
  have hm := convolution_mono_right (he x) (hc x) (averagingBump d n).nonneg_normed hb
  rw [(averagingBump d n).normed_convolution_eq_right
    (g := fun _ : Space d ↦ b) (fun _ _ ↦ rfl)] at hm
  exact hm

/-- The contraction coefficient lies strictly between zero and one. -/
theorem mollify_contraction_mem_Ioo (n : ℕ) :
    1 - 1 / ((n : ℝ) + 2) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hp : 0 < (n : ℝ) + 2 := by positivity
  have hlt : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one hp).mpr (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hpos : 0 < 1 / ((n : ℝ) + 2) := by positivity
  constructor <;> linarith

/-- The normalized averages are smooth. -/
theorem normalizedMollify_contDiff {d : ℕ} {v : Space d → ℝ} (hv : Continuous v) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedMollify v n) :=
  contDiff_const.mul (mollify_contDiff hv n)

/-- Normalized averages of functions in the unit interval remain nonnegative and below one. -/
theorem normalizedMollify_mem_Ico {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (x : Space d) :
    normalizedMollify v n x ∈ Set.Ico (0 : ℝ) 1 := by
  have hc := mollify_contraction_mem_Ioo n
  have h0 := mollify_nonneg (fun x ↦ (hval x).1) n x
  have h1 := mollify_le hv (fun x ↦ (hval x).2) n x
  change (1 - 1 / ((n : ℝ) + 2)) * mollify v n x ∈ Set.Ico (0 : ℝ) 1
  exact ⟨mul_nonneg hc.1.le h0, (mul_le_of_le_one_right hc.1.le h1).trans_lt hc.2⟩

/-- The contraction vanishes in the limit, so the normalized averages recover the function. -/
theorem normalizedMollify_tendsto {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (x : Space d) : Tendsto (fun n ↦ normalizedMollify v n x) atTop (𝓝 (v x)) := by
  have ht : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have he := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hs := he.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs
  have hm := ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul (mollify_tendsto hv x)
  simpa only [normalizedMollify, sub_zero, one_mul] using hm

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The zero extension has an explicit smooth sequence with normalized range and pointwise limit. -/
theorem RigidityHypotheses.zeroExtension_smooth_approximation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    (∀ n, ContDiff ℝ (⊤ : ℕ∞) (normalizedMollify (zeroExtension g u) n)) ∧
    (∀ n x, normalizedMollify (zeroExtension g u) n x ∈ Set.Ico (0 : ℝ) 1) ∧
    (∀ x, Tendsto (fun n ↦ normalizedMollify (zeroExtension g u) n x) atTop
      (𝓝 (zeroExtension g u x))) := by
  exact ⟨normalizedMollify_contDiff h.zeroExtension_continuous,
    normalizedMollify_mem_Ico h.zeroExtension_continuous
      (fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩),
    normalizedMollify_tendsto h.zeroExtension_continuous⟩

end SerrinEpigraph
