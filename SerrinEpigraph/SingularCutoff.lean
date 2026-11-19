module

public import SerrinEpigraph.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Capacity cutoffs near small singular sets, and connectivity of complements

This file provides two elementary tools used in the alternative proof of the splitting theorem
for directed minimal cones (blueprint `docs/rigidity-proof/one-sided.md`, §5A, steps A and D).

## Step A: capacity cutoffs

Let `μ` be a measure on a finite-dimensional real inner product space `E` with an upper growth
bound `μ (closedBall x r) ≤ A r ^ k` (`0 < r ≤ r₀`) at the points `x` of a compact set `S` with
`μH[k - 2] S = 0`, where `2 < k`. Then for every `ε > 0` and every open `U ⊇ S` there is a smooth
`η : E → [0, 1]` vanishing on a neighbourhood of `S`, equal to one off a compact subset of `U`,
with `∫ ‖Dη‖² dμ ≤ ε` (`exists_smooth_cutoff_of_hausdorffMeasure_eq_zero`).

The construction covers `S` by finitely many balls `B(cᵢ, rᵢ)` with `∑ rᵢ ^ (k - 2)` small
(`exists_finite_ball_cover_of_hausdorffMeasure_eq_zero`), takes smooth radial cutoffs `aᵢ`
(`0` on `B(cᵢ, rᵢ)`, `1` off `B(cᵢ, 2rᵢ)`, slope `≲ 1 / rᵢ`) and combines them by a *soft
minimum* `m = -β⁻¹ log (e^{-β} + ∑ e^{-β aᵢ})`. The gradient of `m` is a sub-convex combination
of the gradients of the `aᵢ`, so `‖Dm‖² ≤ ∑ ‖Daᵢ‖²` (`norm_fderiv_softMin_sq_le`), exactly as
for the (nonsmooth) minimum; with `β = 4 log (N + 1) + 4` the soft minimum is `≤ 0` on the small
balls and `≥ 3/4` off the doubled balls. Composing with a smooth step gives the cutoff
`capacityCutoff`, whose energy is at most `C A ∑ rᵢ ^ (k - 2)`
(`lintegral_norm_fderiv_capacityCutoff_sq_le`). The gradient is the ambient Fréchet derivative,
so the bound controls any tangential gradient along a submanifold carrying `μ`.

The sequence form (`exists_smooth_cutoff_seq_of_hausdorffMeasure_eq_zero`) takes `ε = 1/(j+1)`
and `U = thickening (1/(j+1)) S`; then `ηⱼ → 1` pointwise off `S` and the energies tend to zero.

## Step D: connectivity of complements

If `C` is a subset of a real inner product space of dimension `k ≥ 2` with `μH[k - 1] C = 0`
(for instance if `dimH C < k - 1`), then `Cᶜ` is path connected
(`isPathConnected_compl_of_hausdorffMeasure_eq_zero`, `isPathConnected_compl_of_dimH_lt`). For
`p, q ∉ C`, the midpoints `z` on the hyperplane bisecting `[p, q]` for which `[p, z]` or `[z, q]`
meets `C` lie in the images of `C` under the central projections from `p` and `q`, which are
differentiable maps; by the Luzin `N` property of differentiable maps for Hausdorff measures
(`DifferentiableOn.hausdorffMeasure_image_eq_zero`) these images are `μH[k - 1]`-null, so some
admissible midpoint exists. No closedness of `C` is needed. The hyperplane version
(`isPathConnected_hyperplane_diff_of_hausdorffMeasure_eq_zero`) removes a set of vanishing
`μH[n - 2]` measure from `{x | ⟪ν, x⟫ = 0}` in dimension `n ≥ 3`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

section SmoothStep

/-- The derivative of `Real.smoothTransition` vanishes to the left of `0`. -/
private theorem deriv_smoothTransition_of_neg {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of `Real.smoothTransition` vanishes to the right of `1`. -/
private theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of `Real.smoothTransition` is uniformly bounded. -/
theorem exists_cutoffStepDerivBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have := hC t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have hzero : deriv Real.smoothTransition t = 0 := by
      rcases not_and_or.mp ht with h | h
      · exact deriv_smoothTransition_of_neg (not_le.mp h)
      · exact deriv_smoothTransition_of_one_lt (not_le.mp h)
    rw [hzero, abs_zero]
    exact le_max_right _ _

/-- A fixed uniform bound for `|deriv Real.smoothTransition|`. -/
def cutoffStepDerivBound : ℝ :=
  Classical.choose exists_cutoffStepDerivBound

theorem cutoffStepDerivBound_nonneg : 0 ≤ cutoffStepDerivBound :=
  (Classical.choose_spec exists_cutoffStepDerivBound).1

theorem abs_deriv_smoothTransition_le_cutoffStepDerivBound (t : ℝ) :
    |deriv Real.smoothTransition t| ≤ cutoffStepDerivBound :=
  (Classical.choose_spec exists_cutoffStepDerivBound).2 t

private theorem hasDerivAt_smoothTransition (t : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt

end SmoothStep

section RadialCutoff

variable {E : Type*} [NormedAddCommGroup E]

/-- The quadratic radial profile `(‖x - c‖² - r²) / (3 r²)`. It is nonpositive on
`closedBall c r` and at least one off `ball c (2 r)`. -/
def doubledBallProfile (c : E) (r : ℝ) (x : E) : ℝ :=
  (3 * r ^ 2)⁻¹ * (‖x - c‖ ^ 2 - r ^ 2)

/-- A smooth radial cutoff: it vanishes on `closedBall c r` and equals one off `ball c (2 r)`. -/
def doubledBallCutoff (c : E) (r : ℝ) (x : E) : ℝ :=
  Real.smoothTransition (doubledBallProfile c r x)

section Smooth

variable [InnerProductSpace ℝ E]

theorem contDiff_doubledBallProfile (c : E) (r : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (doubledBallProfile c r) :=
  contDiff_const.mul
    (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const)

theorem contDiff_doubledBallCutoff (c : E) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (doubledBallCutoff c r) :=
  Real.smoothTransition.contDiff.comp (contDiff_doubledBallProfile c r)

end Smooth

theorem doubledBallCutoff_nonneg (c : E) (r : ℝ) (x : E) : 0 ≤ doubledBallCutoff c r x :=
  Real.smoothTransition.nonneg _

theorem doubledBallCutoff_le_one (c : E) (r : ℝ) (x : E) : doubledBallCutoff c r x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem doubledBallCutoff_eq_zero {c x : E} {r : ℝ} (hr : 0 < r) (hx : ‖x - c‖ ≤ r) :
    doubledBallCutoff c r x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : ‖x - c‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h2 : 0 ≤ (3 * r ^ 2)⁻¹ := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos h2 (by linarith)

theorem one_lt_doubledBallProfile {c x : E} {r : ℝ} (hr : 0 < r) (hx : 2 * r < ‖x - c‖) :
    1 < doubledBallProfile c r x := by
  have h1 : (2 * r) ^ 2 < ‖x - c‖ ^ 2 := pow_lt_pow_left₀ hx (by positivity) two_ne_zero
  have h3 : 0 < 3 * r ^ 2 := by positivity
  unfold doubledBallProfile
  rw [← div_eq_inv_mul, one_lt_div h3]
  nlinarith

theorem one_le_doubledBallProfile {c x : E} {r : ℝ} (hr : 0 < r) (hx : 2 * r ≤ ‖x - c‖) :
    1 ≤ doubledBallProfile c r x := by
  have h1 : (2 * r) ^ 2 ≤ ‖x - c‖ ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
  have h3 : 0 < 3 * r ^ 2 := by positivity
  unfold doubledBallProfile
  rw [← div_eq_inv_mul, one_le_div h3]
  nlinarith

theorem doubledBallCutoff_eq_one {c x : E} {r : ℝ} (hr : 0 < r) (hx : 2 * r ≤ ‖x - c‖) :
    doubledBallCutoff c r x = 1 :=
  Real.smoothTransition.one_of_one_le (one_le_doubledBallProfile hr hx)

section Smooth

variable [InnerProductSpace ℝ E]

theorem hasFDerivAt_doubledBallProfile (c : E) (r : ℝ) (x : E) :
    HasFDerivAt (doubledBallProfile c r)
      ((3 * r ^ 2)⁻¹ • (2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E))) x :=
  ((((hasFDerivAt_id x).sub_const c).norm_sq).sub_const (r ^ 2)).const_mul (3 * r ^ 2)⁻¹

theorem norm_fderiv_doubledBallProfile_le (c : E) {r : ℝ} (x : E) :
    ‖fderiv ℝ (doubledBallProfile c r) x‖ ≤ (3 * r ^ 2)⁻¹ * (2 * ‖x - c‖) := by
  rw [(hasFDerivAt_doubledBallProfile c r x).fderiv]
  have h3 : 0 ≤ (3 * r ^ 2)⁻¹ := by positivity
  rw [norm_smul, Real.norm_of_nonneg h3]
  gcongr
  calc ‖(2 : ℕ) • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E)‖
      ≤ 2 * ‖(innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E)‖ := by
        rw [two_nsmul, two_mul]; exact norm_add_le _ _
    _ ≤ 2 * ‖x - c‖ := by
        gcongr
        calc ‖(innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E)‖
            ≤ ‖innerSL ℝ (x - c)‖ * ‖ContinuousLinearMap.id ℝ E‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖x - c‖ * 1 := by
              gcongr
              · exact (innerSL_apply_norm ℝ (x - c)).le
              · exact ContinuousLinearMap.norm_id_le
          _ = ‖x - c‖ := mul_one _

theorem hasFDerivAt_doubledBallCutoff (c : E) (r : ℝ) (x : E) :
    HasFDerivAt (doubledBallCutoff c r)
      (deriv Real.smoothTransition (doubledBallProfile c r x) •
        fderiv ℝ (doubledBallProfile c r) x) x :=
  (hasDerivAt_smoothTransition _).comp_hasFDerivAt x
    ((contDiff_doubledBallProfile c r (n := 1)).differentiable one_ne_zero x).hasFDerivAt

/-- Pointwise gradient bound for the radial cutoff, supported in `closedBall c (2 r)`. -/
theorem norm_fderiv_doubledBallCutoff_le {c : E} {r : ℝ} (hr : 0 < r) (x : E) :
    ‖fderiv ℝ (doubledBallCutoff c r) x‖ ≤
      (closedBall c (2 * r)).indicator (fun _ => 2 * cutoffStepDerivBound / r) x := by
  rw [(hasFDerivAt_doubledBallCutoff c r x).fderiv, norm_smul, Real.norm_eq_abs]
  by_cases hx : x ∈ closedBall c (2 * r)
  · rw [indicator_of_mem hx]
    have hxc : ‖x - c‖ ≤ 2 * r := by rwa [mem_closedBall, dist_eq_norm] at hx
    have hB := abs_deriv_smoothTransition_le_cutoffStepDerivBound (doubledBallProfile c r x)
    have hD := norm_fderiv_doubledBallProfile_le c (r := r) x
    have hD' : ‖fderiv ℝ (doubledBallProfile c r) x‖ ≤ 2 / r := by
      refine hD.trans ?_
      have h1 : (3 * r ^ 2)⁻¹ * (2 * ‖x - c‖) ≤ (3 * r ^ 2)⁻¹ * (2 * (2 * r)) := by gcongr
      have h2 : (3 * r ^ 2)⁻¹ * (2 * (2 * r)) = 4 / (3 * r) := by field_simp; ring
      have h3 : 4 / (3 * r) ≤ 2 / r := by
        rw [div_le_div_iff₀ (by positivity) hr]; nlinarith
      linarith
    calc |deriv Real.smoothTransition (doubledBallProfile c r x)| *
          ‖fderiv ℝ (doubledBallProfile c r) x‖
        ≤ cutoffStepDerivBound * (2 / r) :=
          mul_le_mul hB hD' (norm_nonneg _) cutoffStepDerivBound_nonneg
      _ = 2 * cutoffStepDerivBound / r := by ring
  · rw [indicator_of_notMem hx]
    have hxc : 2 * r < ‖x - c‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hx; exact hx
    rw [deriv_smoothTransition_of_one_lt (one_lt_doubledBallProfile hr hxc), abs_zero, zero_mul]

end Smooth

end RadialCutoff

section SoftMin

variable {E : Type*}

/-- The partition sum `exp (-β) + ∑ i ∈ t, exp (-β a_i)` of the soft minimum. The extra term
`exp (-β)` corresponds to a dummy function identically equal to one. -/
def softMinSum (β : ℝ) (t : Finset ℕ) (a : ℕ → E → ℝ) (x : E) : ℝ :=
  Real.exp (-β) + ∑ i ∈ t, Real.exp (-β * a i x)

/-- The soft minimum `-β⁻¹ log (exp (-β) + ∑ i ∈ t, exp (-β a_i))` of `1` and the `a_i`. -/
def softMin (β : ℝ) (t : Finset ℕ) (a : ℕ → E → ℝ) (x : E) : ℝ :=
  -β⁻¹ * Real.log (softMinSum β t a x)

theorem softMinSum_pos (β : ℝ) (t : Finset ℕ) (a : ℕ → E → ℝ) (x : E) :
    0 < softMinSum β t a x :=
  add_pos_of_pos_of_nonneg (Real.exp_pos _)
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

theorem contDiff_softMin [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞} (β : ℝ)
    (t : Finset ℕ) {a : ℕ → E → ℝ}
    (ha : ∀ i ∈ t, ContDiff ℝ n (a i)) : ContDiff ℝ n (softMin β t a) := by
  have hS : ContDiff ℝ n (softMinSum β t a) :=
    contDiff_const.add (ContDiff.sum fun i hi => (contDiff_const.mul (ha i hi)).exp)
  exact contDiff_const.mul (hS.log fun x => (softMinSum_pos β t a x).ne')

theorem hasFDerivAt_softMin [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ} (hβ : β ≠ 0)
    (t : Finset ℕ) {a : ℕ → E → ℝ} {x : E}
    (ha : ∀ i ∈ t, DifferentiableAt ℝ (a i) x) :
    HasFDerivAt (softMin β t a)
      (∑ i ∈ t, (Real.exp (-β * a i x) / softMinSum β t a x) • fderiv ℝ (a i) x) x := by
  have hS : HasFDerivAt (softMinSum β t a)
      (∑ i ∈ t, Real.exp (-β * a i x) • ((-β) • fderiv ℝ (a i) x)) x := by
    have h := HasFDerivAt.fun_sum (u := t) (A := fun i y => Real.exp (-β * a i y))
      (fun i hi => ((ha i hi).hasFDerivAt.const_mul (-β)).exp)
    exact h.const_add (Real.exp (-β))
  have hL : HasFDerivAt (softMin β t a) ((-β⁻¹) • ((softMinSum β t a x)⁻¹ •
      ∑ i ∈ t, Real.exp (-β * a i x) • ((-β) • fderiv ℝ (a i) x))) x :=
    (hS.log (softMinSum_pos β t a x).ne').const_mul (-β⁻¹)
  refine hL.congr_fderiv ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **Gradient of the soft minimum.** Its squared norm is at most the sum of the squared norms of
the gradients of the `a_i`, independently of the number of functions. -/
theorem norm_fderiv_softMin_sq_le [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ} (hβ : 0 < β)
    (t : Finset ℕ) {a : ℕ → E → ℝ} {x : E}
    (ha : ∀ i ∈ t, DifferentiableAt ℝ (a i) x) :
    ‖fderiv ℝ (softMin β t a) x‖ ^ 2 ≤ ∑ i ∈ t, ‖fderiv ℝ (a i) x‖ ^ 2 := by
  rw [(hasFDerivAt_softMin hβ.ne' t ha).fderiv]
  set S := softMinSum β t a x with hS_def
  have hS : 0 < S := softMinSum_pos β t a x
  set w : ℕ → ℝ := fun i => Real.exp (-β * a i x) / S with hw_def
  have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (Real.exp_pos _).le hS.le
  have hwsum : ∑ i ∈ t, w i ≤ 1 := by
    rw [hw_def, ← Finset.sum_div, div_le_one hS, hS_def, softMinSum]
    linarith [Real.exp_pos (-β)]
  have hw1 : ∀ i ∈ t, w i ≤ 1 := fun i hi =>
    (Finset.single_le_sum (fun j _ => hw0 j) hi).trans hwsum
  have h1 : ‖∑ i ∈ t, w i • fderiv ℝ (a i) x‖ ≤ ∑ i ∈ t, w i * ‖fderiv ℝ (a i) x‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hw0 i)]
  have h2 : (∑ i ∈ t, w i * ‖fderiv ℝ (a i) x‖) ^ 2 ≤
      (∑ i ∈ t, w i) * ∑ i ∈ t, w i * ‖fderiv ℝ (a i) x‖ ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun i _ => hw0 i)
      (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))
  calc ‖∑ i ∈ t, w i • fderiv ℝ (a i) x‖ ^ 2
      ≤ (∑ i ∈ t, w i * ‖fderiv ℝ (a i) x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i ∈ t, w i) * ∑ i ∈ t, w i * ‖fderiv ℝ (a i) x‖ ^ 2 := h2
    _ ≤ 1 * ∑ i ∈ t, ‖fderiv ℝ (a i) x‖ ^ 2 := by
        apply mul_le_mul hwsum _ (Finset.sum_nonneg fun i _ =>
          mul_nonneg (hw0 i) (sq_nonneg _)) zero_le_one
        exact Finset.sum_le_sum fun i hi => mul_le_of_le_one_left (sq_nonneg _) (hw1 i hi)
    _ = ∑ i ∈ t, ‖fderiv ℝ (a i) x‖ ^ 2 := one_mul _

/-- The soft minimum is nonpositive as soon as one of the `a_i` vanishes. -/
theorem softMin_nonpos {β : ℝ} (hβ : 0 < β) {t : Finset ℕ} {a : ℕ → E → ℝ} {x : E} {i : ℕ}
    (hi : i ∈ t) (hai : a i x = 0) : softMin β t a x ≤ 0 := by
  have h1 : 1 ≤ softMinSum β t a x := by
    have hle : Real.exp (-β * a i x) ≤ ∑ j ∈ t, Real.exp (-β * a j x) :=
      Finset.single_le_sum (f := fun j => Real.exp (-β * a j x))
        (fun j _ => (Real.exp_pos _).le) hi
    rw [hai, mul_zero, Real.exp_zero] at hle
    unfold softMinSum
    linarith [Real.exp_pos (-β)]
  have hlog : 0 ≤ Real.log (softMinSum β t a x) := Real.log_nonneg h1
  have hβinv : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ.le
  unfold softMin
  nlinarith

/-- When all the `a_i` equal one, the soft minimum equals `1 - log (card t + 1) / β`. -/
theorem softMin_of_forall_eq_one {β : ℝ} (hβ : β ≠ 0) {t : Finset ℕ} {a : ℕ → E → ℝ} {x : E}
    (ha : ∀ i ∈ t, a i x = 1) :
    softMin β t a x = 1 - Real.log (t.card + 1) / β := by
  have hS : softMinSum β t a x = (t.card + 1) * Real.exp (-β) := by
    unfold softMinSum
    rw [Finset.sum_congr rfl fun i hi => by rw [ha i hi, mul_one], Finset.sum_const,
      nsmul_eq_mul]
    ring
  unfold softMin
  rw [hS, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

end SoftMin

section Cover

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set of vanishing `μH[s]` measure has countable covers by sets of diameter at most `R` with
arbitrarily small `s`-sum. -/
theorem exists_countable_cover_of_hausdorffMeasure_eq_zero {s : ℝ} {S : Set X}
    (hS : μH[s] S = 0) {R c : ℝ≥0∞} (hR : 0 < R) (hc : 0 < c) :
    ∃ T : ℕ → Set X, S ⊆ ⋃ n, T n ∧ (∀ n, ediam (T n) ≤ R) ∧
      ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ s < c := by
  have h := Measure.hausdorffMeasure_apply s S
  rw [hS] at h
  have hle : (⨅ (T : ℕ → Set X) (_ : S ⊆ ⋃ n, T n) (_ : ∀ n, ediam (T n) ≤ R),
      ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ s) ≤ 0 := by
    rw [h]
    exact le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) => ⨅ (T : ℕ → Set X) (_ : S ⊆ ⋃ n, T n)
      (_ : ∀ n, ediam (T n) ≤ r), ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ s) R hR
  have hlt := hle.trans_lt hc
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T, hST, hT, hsum⟩ := hlt
  exact ⟨T, hST, hT, hsum⟩

/-- **Finite ball covers of a compact `μH[s]`-null set.** A compact set of vanishing `μH[s]`
measure (`0 < s`) is covered by finitely many open balls centred in the set, with radii at most
`ρ` and arbitrarily small `∑ rᵢ ^ s`. -/
theorem exists_finite_ball_cover_of_hausdorffMeasure_eq_zero [Nonempty X]
    {s : ℝ} (hs : 0 < s) {S : Set X} (hS : IsCompact S) (hSnull : μH[s] S = 0)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ (t : Finset ℕ) (c : ℕ → X) (r : ℕ → ℝ),
      (∀ i ∈ t, c i ∈ S) ∧ (∀ i ∈ t, 0 < r i ∧ r i ≤ ρ) ∧
      S ⊆ ⋃ i ∈ t, ball (c i) (r i) ∧ ∑ i ∈ t, r i ^ s < δ := by
  classical
  -- Step 1: a countable cover by sets of small diameter with small `s`-sum.
  set δ' : ℝ := δ / (2 ^ s + 2) with hδ'_def
  have h2s : 0 < (2 : ℝ) ^ s := by positivity
  have hδ' : 0 < δ' := by positivity
  obtain ⟨T, hST, hTdiam, hTsum⟩ := exists_countable_cover_of_hausdorffMeasure_eq_zero hSnull
    (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < ρ / 2)) (ENNReal.ofReal_pos.2 hδ')
  have hfin : ∀ n, ediam (T n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hTdiam n)
  -- Step 2: radii and centres.
  set D : ℕ → ℝ := fun n => (ediam (T n)).toReal with hD
  have hD_nonneg : ∀ n, 0 ≤ D n := fun n => ENNReal.toReal_nonneg
  have hD_le : ∀ n, D n ≤ ρ / 2 := fun n => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hTdiam n)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  set κ : ℕ → ℝ := fun n => min ρ ((δ' / 2 ^ (n + 1)) ^ s⁻¹) with hκ
  have hκ_pos : ∀ n, 0 < κ n := fun n => lt_min hρ (Real.rpow_pos_of_pos (by positivity) _)
  have hκ_pow : ∀ n, κ n ^ s ≤ δ' / 2 ^ (n + 1) := fun n => by
    calc κ n ^ s ≤ ((δ' / 2 ^ (n + 1)) ^ s⁻¹) ^ s :=
          Real.rpow_le_rpow (hκ_pos n).le (min_le_right _ _) hs.le
      _ = δ' / 2 ^ (n + 1) := Real.rpow_inv_rpow (by positivity) hs.ne'
  set r : ℕ → ℝ := fun n => max (2 * D n) (κ n) with hr
  have hr_pos : ∀ n, 0 < r n := fun n => lt_max_of_lt_right (hκ_pos n)
  have hr_le : ∀ n, r n ≤ ρ := fun n => max_le (by linarith [hD_le n]) (min_le_left _ _)
  have hD_lt : ∀ n, D n < r n := fun n => by
    rcases (hD_nonneg n).lt_or_eq with h | h
    · exact lt_max_of_lt_left (by linarith)
    · rw [← h]; exact hr_pos n
  set x₀ : X := Classical.arbitrary X
  set c : ℕ → X := fun n => if h : (T n ∩ S).Nonempty then h.some else x₀ with hc
  have hc_mem : ∀ n, (T n ∩ S).Nonempty → c n ∈ T n ∩ S := fun n h => by
    simp only [hc, dite_eq_left h]
    exact h.some_mem
  -- Step 3: an open cover and compactness.
  set O : ℕ → Set X := fun n => if (T n ∩ S).Nonempty then ball (c n) (r n) else ∅ with hO
  have hO_open : ∀ n, IsOpen (O n) := fun n => by
    simp only [hO]
    split_ifs
    exacts [isOpen_ball, isOpen_empty]
  have hSO : S ⊆ ⋃ n, O n := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hST hx)
    have hne : (T n ∩ S).Nonempty := ⟨x, hn, hx⟩
    refine mem_iUnion.2 ⟨n, ?_⟩
    simp only [hO, ite_eq_left hne]
    have hcn := hc_mem n hne
    rw [mem_ball]
    have hed : edist x (c n) ≤ ediam (T n) := edist_le_ediam_of_mem hn hcn.1
    have hdist : dist x (c n) ≤ D n := by
      rw [dist_edist]
      exact ENNReal.toReal_mono (hfin n) hed
    exact hdist.trans_lt (hD_lt n)
  obtain ⟨t₀, ht₀⟩ := hS.elim_finite_subcover O hO_open hSO
  set t := t₀.filter fun n => (T n ∩ S).Nonempty with ht
  have ht_ne : ∀ i ∈ t, (T i ∩ S).Nonempty := fun i hi => (Finset.mem_filter.1 hi).2
  refine ⟨t, c, r, fun i hi => (hc_mem i (ht_ne i hi)).2, fun i _ => ⟨hr_pos i, hr_le i⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht₀ hx)
    by_cases hne : (T i ∩ S).Nonempty
    · simp only [hO, ite_eq_left hne] at hxi
      exact mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩, hxi⟩
    · simp only [hO, ite_eq_right hne] at hxi
      exact absurd hxi (notMem_empty x)
  · -- the `s`-sum of the radii
    have hsumD : ∑ i ∈ t, D i ^ s < δ' := by
      have h1 : ENNReal.ofReal (∑ i ∈ t, D i ^ s) = ∑ i ∈ t, ediam (T i) ^ s := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (hD_nonneg i) _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← ENNReal.ofReal_rpow_of_nonneg (hD_nonneg i) hs.le, ENNReal.ofReal_toReal (hfin i)]
      have h2 : ∑ i ∈ t, ediam (T i) ^ s ≤ ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ s := by
        calc ∑ i ∈ t, ediam (T i) ^ s = ∑ i ∈ t, ⨆ _ : (T i).Nonempty, ediam (T i) ^ s := by
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [iSup_pos ((ht_ne i hi).mono inter_subset_left)]
          _ ≤ ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ s := ENNReal.sum_le_tsum _
      have h3 : ENNReal.ofReal (∑ i ∈ t, D i ^ s) < ENNReal.ofReal δ' := by
        rw [h1]
        exact h2.trans_lt hTsum
      exact (ENNReal.ofReal_lt_ofReal_iff hδ').1 h3
    have hsumκ : ∑ i ∈ t, κ i ^ s ≤ δ' := by
      obtain ⟨N, hN⟩ : ∃ N, t ⊆ Finset.range N :=
        ⟨t.sup id + 1, fun i hi => Finset.mem_range.2
          (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
      calc ∑ i ∈ t, κ i ^ s ≤ ∑ i ∈ t, δ' / 2 ^ (i + 1) :=
            Finset.sum_le_sum fun i _ => hκ_pow i
        _ ≤ ∑ i ∈ Finset.range N, δ' / 2 ^ (i + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
        _ = δ' / 2 * ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [pow_succ, one_div_pow]
            field_simp
        _ ≤ δ' / 2 * 2 := by
            gcongr
            exact sum_geometric_two_le N
        _ = δ' := by ring
    have hterm : ∀ i ∈ t, r i ^ s ≤ 2 ^ s * D i ^ s + κ i ^ s := fun i _ => by
      have h2D : (2 * D i) ^ s = 2 ^ s * D i ^ s := Real.mul_rpow (by norm_num) (hD_nonneg i)
      have hκs : 0 ≤ κ i ^ s := Real.rpow_nonneg (hκ_pos i).le _
      have hDs : 0 ≤ 2 ^ s * D i ^ s := by positivity
      rcases le_total (2 * D i) (κ i) with h | h
      · rw [show r i = κ i from max_eq_right h]
        linarith
      · rw [show r i = 2 * D i from max_eq_left h, h2D]
        linarith
    calc ∑ i ∈ t, r i ^ s ≤ ∑ i ∈ t, (2 ^ s * D i ^ s + κ i ^ s) := Finset.sum_le_sum hterm
      _ = 2 ^ s * ∑ i ∈ t, D i ^ s + ∑ i ∈ t, κ i ^ s := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 ^ s * δ' + δ' := by
          have := mul_le_mul_of_nonneg_left hsumD.le h2s.le
          linarith
      _ < δ := by
          have hδeq : (2 ^ s + 2) * δ' = δ := by
            rw [hδ'_def]
            field_simp
          nlinarith

end Cover

section CapacityCutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The soft-minimum parameter `4 log (N + 1) + 4` used for `N` balls. -/
def softMinParam (N : ℕ) : ℝ :=
  4 * Real.log (N + 1) + 4

theorem softMinParam_pos (N : ℕ) : 0 < softMinParam N := by
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  unfold softMinParam
  linarith

/-- The capacity cutoff attached to the balls `ball (c i) (r i)`, `i ∈ t`: a smooth step applied
to the soft minimum of the doubled-ball cutoffs `doubledBallCutoff (c i) (r i)`. -/
def capacityCutoff (t : Finset ℕ) (c : ℕ → E) (r : ℕ → ℝ) (x : E) : ℝ :=
  Real.smoothTransition
    (2 * softMin (softMinParam t.card) t (fun i => doubledBallCutoff (c i) (r i)) x - 1 / 2)

theorem contDiff_capacityCutoff (t : Finset ℕ) (c : ℕ → E) (r : ℕ → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (capacityCutoff t c r) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_softMin _ t
    fun i _ => contDiff_doubledBallCutoff (c i) (r i))).sub contDiff_const)

omit [InnerProductSpace ℝ E] in
theorem capacityCutoff_nonneg (t : Finset ℕ) (c : ℕ → E) (r : ℕ → ℝ) (x : E) :
    0 ≤ capacityCutoff t c r x :=
  Real.smoothTransition.nonneg _

omit [InnerProductSpace ℝ E] in
theorem capacityCutoff_le_one (t : Finset ℕ) (c : ℕ → E) (r : ℕ → ℝ) (x : E) :
    capacityCutoff t c r x ≤ 1 :=
  Real.smoothTransition.le_one _

omit [InnerProductSpace ℝ E] in
/-- The capacity cutoff vanishes on each small ball. -/
theorem capacityCutoff_eq_zero {t : Finset ℕ} {c : ℕ → E} {r : ℕ → ℝ} {x : E} {i : ℕ}
    (hi : i ∈ t) (hri : 0 < r i) (hx : x ∈ ball (c i) (r i)) : capacityCutoff t c r x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h0 : doubledBallCutoff (c i) (r i) x = 0 := by
    rw [mem_ball, dist_eq_norm] at hx
    exact doubledBallCutoff_eq_zero hri hx.le
  have hm := softMin_nonpos (a := fun j => doubledBallCutoff (c j) (r j))
    (softMinParam_pos t.card) hi h0
  linarith

omit [InnerProductSpace ℝ E] in
/-- The capacity cutoff equals one off the doubled balls. -/
theorem capacityCutoff_eq_one {t : Finset ℕ} {c : ℕ → E} {r : ℕ → ℝ} {x : E}
    (hr : ∀ i ∈ t, 0 < r i) (hx : ∀ i ∈ t, 2 * r i ≤ ‖x - c i‖) : capacityCutoff t c r x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h1 : ∀ i ∈ t, doubledBallCutoff (c i) (r i) x = 1 := fun i hi =>
    doubledBallCutoff_eq_one (hr i hi) (hx i hi)
  rw [softMin_of_forall_eq_one (a := fun j => doubledBallCutoff (c j) (r j))
    (softMinParam_pos t.card).ne' h1]
  have hβ := softMinParam_pos t.card
  have hquarter : Real.log ((t.card : ℝ) + 1) / softMinParam t.card ≤ 1 / 4 := by
    rw [div_le_iff₀ hβ]
    unfold softMinParam
    linarith
  linarith

/-- **Pointwise gradient bound for the capacity cutoff.** -/
theorem norm_fderiv_capacityCutoff_sq_le {t : Finset ℕ} {c : ℕ → E} {r : ℕ → ℝ}
    (hr : ∀ i ∈ t, 0 < r i) (x : E) :
    ‖fderiv ℝ (capacityCutoff t c r) x‖ ^ 2 ≤
      ∑ i ∈ t, (closedBall (c i) (2 * r i)).indicator
        (fun _ => 16 * cutoffStepDerivBound ^ 4 / r i ^ 2) x := by
  set B := cutoffStepDerivBound with hB_def
  have hB0 : 0 ≤ B := cutoffStepDerivBound_nonneg
  set a : ℕ → E → ℝ := fun i => doubledBallCutoff (c i) (r i) with ha_def
  have ha : ∀ i ∈ t, DifferentiableAt ℝ (a i) x := fun i _ =>
    (contDiff_doubledBallCutoff (c i) (r i)).differentiable (by simp) x
  set m : E → ℝ := softMin (softMinParam t.card) t a with hm_def
  have hm : DifferentiableAt ℝ m x :=
    (hasFDerivAt_softMin (softMinParam_pos t.card).ne' t ha).differentiableAt
  have hinner : HasFDerivAt (fun y => 2 * m y - 1 / 2) ((2 : ℝ) • fderiv ℝ m x) x :=
    (hm.hasFDerivAt.const_mul 2).sub_const (1 / 2)
  have hη : HasFDerivAt (capacityCutoff t c r)
      (deriv Real.smoothTransition (2 * m x - 1 / 2) • ((2 : ℝ) • fderiv ℝ m x)) x :=
    (hasDerivAt_smoothTransition _).comp_hasFDerivAt x hinner
  rw [hη.fderiv]
  have h1 : ‖deriv Real.smoothTransition (2 * m x - 1 / 2) • ((2 : ℝ) • fderiv ℝ m x)‖ ^ 2 ≤
      4 * B ^ 2 * ‖fderiv ℝ m x‖ ^ 2 := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
    have hb := abs_deriv_smoothTransition_le_cutoffStepDerivBound (2 * m x - 1 / 2)
    have hb0 := abs_nonneg (deriv Real.smoothTransition (2 * m x - 1 / 2))
    calc (|deriv Real.smoothTransition (2 * m x - 1 / 2)| * (2 * ‖fderiv ℝ m x‖)) ^ 2
        = 4 * |deriv Real.smoothTransition (2 * m x - 1 / 2)| ^ 2 * ‖fderiv ℝ m x‖ ^ 2 := by
          ring
      _ ≤ 4 * B ^ 2 * ‖fderiv ℝ m x‖ ^ 2 := by gcongr
  have h2 : ∀ i ∈ t, ‖fderiv ℝ (a i) x‖ ^ 2 ≤
      (closedBall (c i) (2 * r i)).indicator (fun _ => 4 * B ^ 2 / r i ^ 2) x := by
    intro i hi
    have hle := norm_fderiv_doubledBallCutoff_le (c := c i) (hr i hi) x
    by_cases hx : x ∈ closedBall (c i) (2 * r i)
    · rw [indicator_of_mem hx] at hle ⊢
      calc ‖fderiv ℝ (a i) x‖ ^ 2 ≤ (2 * B / r i) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = 4 * B ^ 2 / r i ^ 2 := by ring
    · rw [indicator_of_notMem hx] at hle ⊢
      have hzero : ‖fderiv ℝ (a i) x‖ = 0 := le_antisymm hle (norm_nonneg _)
      rw [hzero]
      norm_num
  have hsm := norm_fderiv_softMin_sq_le (softMinParam_pos t.card) t ha
  calc ‖deriv Real.smoothTransition (2 * m x - 1 / 2) • ((2 : ℝ) • fderiv ℝ m x)‖ ^ 2
      ≤ 4 * B ^ 2 * ‖fderiv ℝ m x‖ ^ 2 := h1
    _ ≤ 4 * B ^ 2 * ∑ i ∈ t, ‖fderiv ℝ (a i) x‖ ^ 2 := by gcongr
    _ ≤ 4 * B ^ 2 * ∑ i ∈ t,
          (closedBall (c i) (2 * r i)).indicator (fun _ => 4 * B ^ 2 / r i ^ 2) x := by
        gcongr with i hi
        exact h2 i hi
    _ = ∑ i ∈ t, (closedBall (c i) (2 * r i)).indicator (fun _ => 16 * B ^ 4 / r i ^ 2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hx : x ∈ closedBall (c i) (2 * r i)
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          ring
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- **Energy of the capacity cutoff.** If each doubled ball carries `μ`-mass at most
`A (2 rᵢ) ^ k`, then `∫ ‖Dη‖² dμ ≤ 16 B⁴ |A| 2 ^ k ∑ rᵢ ^ (k - 2)`, where `B` bounds the
derivative of the smooth step. -/
theorem lintegral_norm_fderiv_capacityCutoff_sq_le [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {A k : ℝ} {t : Finset ℕ} {c : ℕ → E} {r : ℕ → ℝ} (hr : ∀ i ∈ t, 0 < r i)
    (hμ : ∀ i ∈ t, μ (closedBall (c i) (2 * r i)) ≤ ENNReal.ofReal (A * (2 * r i) ^ k)) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ (capacityCutoff t c r) x‖ ^ 2) ∂μ ≤
      ENNReal.ofReal
        (16 * cutoffStepDerivBound ^ 4 * |A| * 2 ^ k * ∑ i ∈ t, r i ^ (k - 2)) := by
  set B := cutoffStepDerivBound with hB_def
  have hpt : ∀ x, ENNReal.ofReal (‖fderiv ℝ (capacityCutoff t c r) x‖ ^ 2) ≤
      ∑ i ∈ t, (closedBall (c i) (2 * r i)).indicator
        (fun _ => ENNReal.ofReal (16 * B ^ 4 / r i ^ 2)) x := by
    intro x
    refine (ENNReal.ofReal_le_ofReal (norm_fderiv_capacityCutoff_sq_le hr x)).trans
      (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => indicator_nonneg (fun _ _ => by positivity) _]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ closedBall (c i) (2 * r i)
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
  calc ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ (capacityCutoff t c r) x‖ ^ 2) ∂μ
      ≤ ∫⁻ x, ∑ i ∈ t, (closedBall (c i) (2 * r i)).indicator
          (fun _ => ENNReal.ofReal (16 * B ^ 4 / r i ^ 2)) x ∂μ := lintegral_mono hpt
    _ = ∑ i ∈ t, ENNReal.ofReal (16 * B ^ 4 / r i ^ 2) * μ (closedBall (c i) (2 * r i)) := by
        rw [lintegral_finsetSum _ fun i _ => measurable_const.indicator measurableSet_closedBall]
        exact Finset.sum_congr rfl fun i _ => lintegral_indicator_const measurableSet_closedBall _
    _ ≤ ∑ i ∈ t, ENNReal.ofReal (16 * B ^ 4 * |A| * 2 ^ k * r i ^ (k - 2)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hri := hr i hi
        have hμ' : μ (closedBall (c i) (2 * r i)) ≤ ENNReal.ofReal (|A| * (2 * r i) ^ k) :=
          (hμ i hi).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg (by positivity) _)))
        calc ENNReal.ofReal (16 * B ^ 4 / r i ^ 2) * μ (closedBall (c i) (2 * r i))
            ≤ ENNReal.ofReal (16 * B ^ 4 / r i ^ 2) * ENNReal.ofReal (|A| * (2 * r i) ^ k) := by
              gcongr
          _ = ENNReal.ofReal (16 * B ^ 4 / r i ^ 2 * (|A| * (2 * r i) ^ k)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal (16 * B ^ 4 * |A| * 2 ^ k * r i ^ (k - 2)) := by
              congr 1
              rw [Real.mul_rpow (by norm_num) hri.le, Real.rpow_sub hri, Real.rpow_two]
              field_simp
    _ = ENNReal.ofReal (16 * B ^ 4 * |A| * 2 ^ k * ∑ i ∈ t, r i ^ (k - 2)) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        have := hr i hi
        positivity

end CapacityCutoff

section MainCutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Step A: capacity cutoffs near a small compact set.** Let `μ` satisfy the upper growth bound
`μ (closedBall x ρ) ≤ A ρ ^ k` for `x ∈ S` and `0 < ρ ≤ r₀`, where `2 < k`, and let the compact
set `S` have `μH[k - 2] S = 0`. Then for every open `U ⊇ S` and every `ε > 0` there is a smooth
`η` with values in `[0, 1]`, vanishing on an open neighbourhood of `S`, equal to one off a compact
subset of `U`, whose (ambient) Dirichlet energy with respect to `μ` is at most `ε`. -/
theorem exists_smooth_cutoff_of_hausdorffMeasure_eq_zero (μ : Measure E) {A r₀ k : ℝ}
    (hk : 2 < k) (hr₀ : 0 < r₀) {S : Set E}
    (hgrowth : ∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
      μ (closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ k))
    (hS : IsCompact S) (hSnull : μH[k - 2] S = 0) {U : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∃ V, IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, η x = 0) ∧
      (∃ K, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, η x = 1) ∧ (∀ x ∉ U, η x = 1) ∧
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ η x‖ ^ 2) ∂μ ≤ ENNReal.ofReal ε ∧
      Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2) μ ∧ ∫ x, ‖fderiv ℝ η x‖ ^ 2 ∂μ ≤ ε := by
  obtain ⟨δU, hδU, hthick⟩ := hS.exists_thickening_subset_open hU hSU
  set B := cutoffStepDerivBound with hB_def
  set Kc : ℝ := 16 * B ^ 4 * |A| * 2 ^ k with hKc_def
  have hKc0 : 0 ≤ Kc := by positivity
  set ρ : ℝ := min (r₀ / 2) (δU / 4) with hρ_def
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ₁ : ρ ≤ r₀ / 2 := min_le_left _ _
  have hρ₂ : ρ ≤ δU / 4 := min_le_right _ _
  obtain ⟨t, c, r, hcS, hr, hcover, hsum⟩ := exists_finite_ball_cover_of_hausdorffMeasure_eq_zero
    (by linarith : (0 : ℝ) < k - 2) hS hSnull hρ (show 0 < ε / (Kc + 1) by positivity)
  have hr0 : ∀ i ∈ t, 0 < r i := fun i hi => (hr i hi).1
  have hμ : ∀ i ∈ t, μ (closedBall (c i) (2 * r i)) ≤ ENNReal.ofReal (A * (2 * r i) ^ k) :=
    fun i hi => hgrowth (c i) (hcS i hi) (2 * r i) (by linarith [hr0 i hi])
      (by linarith [(hr i hi).2])
  set η : E → ℝ := capacityCutoff t c r with hη_def
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := contDiff_capacityCutoff t c r
  have hlin : ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ η x‖ ^ 2) ∂μ ≤ ENNReal.ofReal ε := by
    refine (lintegral_norm_fderiv_capacityCutoff_sq_le μ hr0 hμ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hs0 : 0 ≤ ∑ i ∈ t, r i ^ (k - 2) :=
      Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hr0 i hi).le _
    calc Kc * ∑ i ∈ t, r i ^ (k - 2) ≤ Kc * (ε / (Kc + 1)) := by gcongr
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  -- the region where `η ≠ 1`
  set K : Set E := ⋃ i ∈ t, closedBall (c i) (2 * r i) with hK_def
  have hK_compact : IsCompact K := t.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hKU : K ⊆ U := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨c i, hcS i hi, ?_⟩
    rw [mem_closedBall] at hyi
    linarith [(hr i hi).2]
  have hK_one : ∀ x ∉ K, η x = 1 := by
    intro x hx
    refine capacityCutoff_eq_one hr0 fun i hi => ?_
    have hxi : x ∉ closedBall (c i) (2 * r i) := fun h => hx (mem_iUnion₂.2 ⟨i, hi, h⟩)
    rw [mem_closedBall, dist_eq_norm, not_le] at hxi
    exact hxi.le
  have hcont : Continuous fun x => ‖fderiv ℝ η x‖ ^ 2 :=
    ((hη_smooth.continuous_fderiv (by simp)).norm).pow 2
  have hint : Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2) μ := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨η, hη_smooth, fun x => ⟨capacityCutoff_nonneg t c r x, capacityCutoff_le_one t c r x⟩,
    ⟨⋃ i ∈ t, ball (c i) (r i), isOpen_biUnion fun i _ => isOpen_ball, hcover, ?_⟩,
    ⟨K, hK_compact, hKU, hK_one⟩, fun x hx => hK_one x fun hxK => hx (hKU hxK), hlin, hint, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx
    exact capacityCutoff_eq_zero hi (hr0 i hi) hxi
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
      hcont.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hlin

/-- **Step A, sequence form.** Cutoffs `ηⱼ` with energy at most `1 / (j + 1)`, vanishing near
`S` and equal to one off `thickening (1 / (j + 1)) S`. In particular `ηⱼ → 1` pointwise off `S`
(each point off `S` eventually has `ηⱼ = 1`) and the energies tend to zero. -/
theorem exists_smooth_cutoff_seq_of_hausdorffMeasure_eq_zero (μ : Measure E) {A r₀ k : ℝ}
    (hk : 2 < k) (hr₀ : 0 < r₀) {S : Set E}
    (hgrowth : ∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
      μ (closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ k))
    (hS : IsCompact S) (hSnull : μH[k - 2] S = 0) :
    ∃ η : ℕ → E → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (η j)) ∧ (∀ j x, 0 ≤ η j x ∧ η j x ≤ 1) ∧
      (∀ j, ∃ V, IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, η j x = 0) ∧
      (∀ j : ℕ, ∃ K, IsCompact K ∧ K ⊆ thickening (1 / ((j : ℝ) + 1)) S ∧
        ∀ x ∉ K, η j x = 1) ∧
      (∀ j : ℕ, ∀ x ∉ thickening (1 / ((j : ℝ) + 1)) S, η j x = 1) ∧
      (∀ j : ℕ, ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ (η j) x‖ ^ 2) ∂μ ≤
        ENNReal.ofReal (1 / ((j : ℝ) + 1))) ∧
      (∀ j, Integrable (fun x => ‖fderiv ℝ (η j) x‖ ^ 2) μ) ∧
      Tendsto (fun j : ℕ => ∫ x, ‖fderiv ℝ (η j) x‖ ^ 2 ∂μ) atTop (𝓝 0) ∧
      (∀ x ∉ S, ∀ᶠ j : ℕ in atTop, η j x = 1) ∧
      (∀ x ∉ S, Tendsto (fun j : ℕ => η j x) atTop (𝓝 1)) := by
  have hmain : ∀ j : ℕ, ∃ η : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∃ V, IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, η x = 0) ∧
      (∃ K, IsCompact K ∧ K ⊆ thickening (1 / ((j : ℝ) + 1)) S ∧ ∀ x ∉ K, η x = 1) ∧
      (∀ x ∉ thickening (1 / ((j : ℝ) + 1)) S, η x = 1) ∧
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ η x‖ ^ 2) ∂μ ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) ∧
      Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2) μ ∧
      ∫ x, ‖fderiv ℝ η x‖ ^ 2 ∂μ ≤ 1 / ((j : ℝ) + 1) := fun j =>
    exists_smooth_cutoff_of_hausdorffMeasure_eq_zero μ hk hr₀ hgrowth hS hSnull
      isOpen_thickening (self_subset_thickening (by positivity) S) (by positivity)
  choose η hsmooth hbound hzero hK hone hlin hint hbochner using hmain
  have hev : ∀ x ∉ S, ∀ᶠ j : ℕ in atTop, η j x = 1 := by
    intro x hx
    have hxcl : x ∉ closure S := by rwa [hS.isClosed.closure_eq]
    rw [closure_eq_iInter_thickening] at hxcl
    simp only [mem_iInter, not_forall] at hxcl
    obtain ⟨δ, hδ, hxδ⟩ := hxcl
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine eventually_atTop.2 ⟨n, fun j hj => hone j x fun hxj => hxδ ?_⟩
    have hjn : 1 / ((j : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
    exact thickening_mono (hjn.trans hn.le) S hxj
  refine ⟨η, hsmooth, hbound, hzero, hK, hone, hlin, hint, ?_, hev, fun x hx => ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun j => ?_) (fun j => hbochner j)
    exact integral_nonneg fun x => sq_nonneg _
  · exact tendsto_const_nhds.congr' ((hev x hx).mono fun j hj => hj.symm)

end MainCutoff

section Shadow

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The central projection from `a` onto the screen `{z | ℓ (z - a) = 1}`. -/
def screenProjection (a : F) (ℓ : F →L[ℝ] ℝ) (c : F) : F :=
  a + (ℓ (c - a))⁻¹ • (c - a)

theorem screenProjection_self_add_smul (a : F) (ℓ : F →L[ℝ] ℝ) {z : F} (hz : ℓ (z - a) = 1)
    {θ : ℝ} (hθ : θ ≠ 0) : screenProjection a ℓ (a + θ • (z - a)) = z := by
  have hℓ : ℓ (a + θ • (z - a) - a) = θ := by
    rw [add_sub_cancel_left, map_smul, hz, smul_eq_mul, mul_one]
  rw [screenProjection, hℓ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hθ, one_smul,
    add_sub_cancel]

theorem differentiableAt_screenProjection (a : F) (ℓ : F →L[ℝ] ℝ) {c : F}
    (hc : ℓ (c - a) ≠ 0) : DifferentiableAt ℝ (screenProjection a ℓ) c := by
  have h1 : DifferentiableAt ℝ (fun c => ℓ (c - a)) c :=
    ℓ.differentiableAt.comp c (differentiableAt_id.sub_const a)
  have h2 : DifferentiableAt ℝ (fun c => (ℓ (c - a))⁻¹) c := h1.inv hc
  exact (h2.smul (differentiableAt_id.sub_const a)).const_add a

/-- **Shadow lemma.** The points of the screen `{z | ℓ (z - a) = 1}` whose segment to `a` meets a
`μH[d]`-null set `C ∌ a` form a `μH[d]`-null set. -/
theorem hausdorffMeasure_shadow_eq_zero [MeasurableSpace F] [BorelSpace F] {C : Set F} {a : F}
    (ha : a ∉ C) (ℓ : F →L[ℝ] ℝ)
    {d : ℝ} (hd : 0 ≤ d) (hC : μH[d] C = 0) :
    μH[d] {z : F | ℓ (z - a) = 1 ∧ (segment ℝ a z ∩ C).Nonempty} = 0 := by
  set t : Set F := C ∩ {c | 0 < ℓ (c - a)} with ht_def
  have hsub : {z : F | ℓ (z - a) = 1 ∧ (segment ℝ a z ∩ C).Nonempty} ⊆
      screenProjection a ℓ '' t := by
    rintro z ⟨hz1, c, hcseg, hcC⟩
    rw [segment_eq_image'] at hcseg
    obtain ⟨θ, ⟨hθ0, -⟩, rfl⟩ := hcseg
    have hθpos : 0 < θ := by
      rcases hθ0.lt_or_eq with h | h
      · exact h
      · subst h
        simp only [zero_smul, add_zero] at hcC
        exact absurd hcC ha
    have hℓ : ℓ (a + θ • (z - a) - a) = θ := by
      rw [add_sub_cancel_left, map_smul, hz1, smul_eq_mul, mul_one]
    refine ⟨a + θ • (z - a), ⟨hcC, ?_⟩, screenProjection_self_add_smul a ℓ hz1 hθpos.ne'⟩
    change 0 < ℓ (a + θ • (z - a) - a)
    rw [hℓ]
    exact hθpos
  have hdiff : DifferentiableOn ℝ (screenProjection a ℓ) t := fun c hc =>
    (differentiableAt_screenProjection a ℓ hc.2.ne').differentiableWithinAt
  have ht : μH[d] t = 0 := measure_mono_null inter_subset_left hC
  exact measure_mono_null hsub (hdiff.hausdorffMeasure_image_eq_zero hd ht)

end Shadow

section NullComplement

/-- In a finite-dimensional real normed space of dimension `m`, a `μH[m]`-null set is not the
whole space. -/
theorem exists_notMem_of_hausdorffMeasure_finrank_eq_zero
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] {A : Set G}
    (hA : μH[(Module.finrank ℝ G : ℝ)] A = 0) : ∃ w, w ∉ A := by
  by_contra! h
  have hAu : A = univ := eq_univ_of_forall h
  set m := Module.finrank ℝ G with hm
  let e : G ≃L[ℝ] (Fin m → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [m])
  have h1 : μH[(m : ℝ)] ((e : G → Fin m → ℝ) '' A) = 0 := by
    have := (e : G →L[ℝ] (Fin m → ℝ)).lipschitzWith.hausdorffMeasure_image_le
      (d := (m : ℝ)) (Nat.cast_nonneg _) A
    rw [hA, mul_zero] at this
    exact nonpos_iff_eq_zero.mp this
  have h2 : (e : G → Fin m → ℝ) '' A = univ := by
    rw [hAu, image_univ, e.surjective.range_eq]
  rw [h2] at h1
  have h3 : (μH[(Fintype.card (Fin m) : ℝ)] : Measure (Fin m → ℝ)) = volume :=
    hausdorffMeasure_pi_real
  rw [Fintype.card_fin] at h3
  rw [h3] at h1
  exact (IsOpen.measure_ne_zero volume isOpen_univ univ_nonempty) h1

end NullComplement


section Connectivity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Connectivity of complements.** In a finite-dimensional real inner product space of
dimension at least two, the complement of a set of vanishing codimension-one Hausdorff measure is
path connected. -/
theorem isPathConnected_compl_of_hausdorffMeasure_eq_zero
    (hF : 2 ≤ Module.finrank ℝ F) {C : Set F}
    (hC : μH[(Module.finrank ℝ F : ℝ) - 1] C = 0) : IsPathConnected Cᶜ := by
  set n := Module.finrank ℝ F - 1 with hn
  have hFn : Module.finrank ℝ F = n + 1 := by omega
  have hdn : (Module.finrank ℝ F : ℝ) - 1 = n := by rw [hFn]; push_cast; ring
  rw [hdn] at hC
  have hd : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [isPathConnected_iff]
  refine ⟨?_, ?_⟩
  · have h0 : μH[(Module.finrank ℝ F : ℝ)] C = 0 := by
      refine nonpos_iff_eq_zero.mp ?_
      calc μH[(Module.finrank ℝ F : ℝ)] C ≤ μH[(n : ℝ)] C :=
            Measure.hausdorffMeasure_mono (by rw [hFn]; push_cast; linarith) C
        _ = 0 := hC
    obtain ⟨w, hw⟩ := exists_notMem_of_hausdorffMeasure_finrank_eq_zero h0
    exact ⟨w, hw⟩
  · intro p hp q hq
    rcases eq_or_ne p q with rfl | hpq
    · exact JoinedIn.refl hp
    set v : F := q - p with hv_def
    have hv : v ≠ 0 := sub_ne_zero.mpr hpq.symm
    have : Fact (Module.finrank ℝ F = n + 1) := ⟨hFn⟩
    set G : Submodule ℝ F := (ℝ ∙ v)ᗮ with hG_def
    have hGdim : Module.finrank ℝ G = n := Submodule.finrank_orthogonal_span_singleton hv
    have hvv : 0 < ‖v‖ ^ 2 := by positivity
    set ℓ : F →L[ℝ] ℝ := (2 / ‖v‖ ^ 2) • innerSL ℝ v with hℓ_def
    have hℓ_apply : ∀ y, ℓ y = 2 / ‖v‖ ^ 2 * inner ℝ v y := fun y => by simp [hℓ_def]
    set mid : F := p + (1 / 2 : ℝ) • v with hmid
    set ψ : G → F := fun w => mid + (w : F) with hψ
    have hψ_isom : Isometry ψ := (IsometryEquiv.addLeft mid).isometry.comp isometry_subtype_coe
    have hscreen_p : ∀ w : G, ℓ (ψ w - p) = 1 := by
      intro w
      have hw : inner ℝ v (w : F) = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
      rw [hℓ_apply]
      simp only [hψ, hmid]
      rw [show p + (1 / 2 : ℝ) • v + (w : F) - p = (1 / 2 : ℝ) • v + (w : F) by abel]
      rw [inner_add_right, inner_smul_right, hw, real_inner_self_eq_norm_sq]
      field_simp
      ring
    have hℓv : ℓ v = 2 := by
      rw [hℓ_apply, real_inner_self_eq_norm_sq]
      field_simp
    have hscreen_q : ∀ w : G, (-ℓ) (ψ w - q) = 1 := by
      intro w
      have h1 := hscreen_p w
      rw [neg_apply, show ψ w - q = (ψ w - p) - v by rw [hv_def]; abel,
        map_sub, h1, hℓv]
      norm_num
    set Bp : Set F := {z | ℓ (z - p) = 1 ∧ (segment ℝ p z ∩ C).Nonempty} with hBp_def
    set Bq : Set F := {z | (-ℓ) (z - q) = 1 ∧ (segment ℝ q z ∩ C).Nonempty} with hBq_def
    have hBp : μH[(n : ℝ)] Bp = 0 := hausdorffMeasure_shadow_eq_zero hp ℓ hd hC
    have hBq : μH[(n : ℝ)] Bq = 0 := hausdorffMeasure_shadow_eq_zero hq (-ℓ) hd hC
    have hA : μH[(Module.finrank ℝ G : ℝ)] (ψ ⁻¹' (Bp ∪ Bq)) = 0 := by
      rw [hGdim, hψ_isom.hausdorffMeasure_preimage (Or.inl hd)]
      exact measure_mono_null inter_subset_left (measure_union_null hBp hBq)
    obtain ⟨w, hw⟩ := exists_notMem_of_hausdorffMeasure_finrank_eq_zero hA
    simp only [mem_preimage, mem_union, not_or] at hw
    have hsegp : segment ℝ p (ψ w) ⊆ Cᶜ := by
      intro x hx hxC
      exact hw.1 ⟨hscreen_p w, x, hx, hxC⟩
    have hsegq : segment ℝ q (ψ w) ⊆ Cᶜ := by
      intro x hx hxC
      exact hw.2 ⟨hscreen_q w, x, hx, hxC⟩
    exact (JoinedIn.of_segment_subset hsegp).trans (JoinedIn.of_segment_subset hsegq).symm

/-- The complement of a set of Hausdorff dimension less than `dim F - 1` is path connected. -/
theorem isPathConnected_compl_of_dimH_lt (hF : 2 ≤ Module.finrank ℝ F) {C : Set F}
    (hC : dimH C < ((Module.finrank ℝ F - 1 : ℕ) : ℝ≥0∞)) : IsPathConnected Cᶜ := by
  apply isPathConnected_compl_of_hausdorffMeasure_eq_zero hF
  have h := hausdorffMeasure_of_dimH_lt (d := ((Module.finrank ℝ F - 1 : ℕ) : ℝ≥0))
    (by exact_mod_cast hC)
  have hcast : (((Module.finrank ℝ F - 1 : ℕ) : ℝ≥0) : ℝ) = (Module.finrank ℝ F : ℝ) - 1 := by
    rw [NNReal.coe_natCast, Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ F), Nat.cast_one]
  rw [hcast] at h
  exact h

/-- A linear subspace of dimension at least two, with a set of vanishing codimension-one
Hausdorff measure (relative to the subspace) removed, is path connected. -/
theorem isPathConnected_submodule_diff_of_hausdorffMeasure_eq_zero (P : Submodule ℝ F)
    (hP : 2 ≤ Module.finrank ℝ P) {C : Set F}
    (hC : μH[(Module.finrank ℝ P : ℝ) - 1] C = 0) : IsPathConnected ((P : Set F) \ C) := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Module.finrank ℝ P := by exact_mod_cast hP
    linarith
  have hC' : μH[(Module.finrank ℝ P : ℝ) - 1] ((Subtype.val : P → F) ⁻¹' C) = 0 := by
    rw [isometry_subtype_coe.hausdorffMeasure_preimage (Or.inl hd)]
    exact measure_mono_null inter_subset_left hC
  have h := (isPathConnected_compl_of_hausdorffMeasure_eq_zero hP hC').image
    continuous_subtype_val
  convert h using 1
  ext x
  simp only [Set.mem_sdiff, mem_image, mem_compl_iff, mem_preimage]
  constructor
  · rintro ⟨hxP, hxC⟩
    exact ⟨⟨x, hxP⟩, hxC, rfl⟩
  · rintro ⟨y, hyC, rfl⟩
    exact ⟨y.2, hyC⟩

/-- **Connectivity of a hyperplane minus a small set.** For `ν ≠ 0` in a space of dimension at
least three, the hyperplane `ν^⊥` minus a set of vanishing `μH[dim F - 2]` measure is path
connected. -/
theorem isPathConnected_hyperplane_diff_of_hausdorffMeasure_eq_zero {ν : F} (hν : ν ≠ 0)
    (hF : 3 ≤ Module.finrank ℝ F) {C : Set F}
    (hC : μH[(Module.finrank ℝ F : ℝ) - 2] C = 0) :
    IsPathConnected ({x : F | inner ℝ ν x = 0} \ C) := by
  have hset : {x : F | inner ℝ ν x = 0} = ((ℝ ∙ ν)ᗮ : Set F) := by
    ext x
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have : Fact (Module.finrank ℝ F = (Module.finrank ℝ F - 1) + 1) := ⟨by omega⟩
  have hdim : Module.finrank ℝ (ℝ ∙ ν)ᗮ = Module.finrank ℝ F - 1 :=
    Submodule.finrank_orthogonal_span_singleton hν
  rw [hset]
  apply isPathConnected_submodule_diff_of_hausdorffMeasure_eq_zero
  · omega
  · rw [hdim, Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ F), Nat.cast_one]
    rw [show (Module.finrank ℝ F : ℝ) - 1 - 1 = (Module.finrank ℝ F : ℝ) - 2 by ring]
    exact hC

/-- Hyperplane version with a dimension hypothesis `dimH C < dim F - 2`. -/
theorem isPathConnected_hyperplane_diff_of_dimH_lt {ν : F} (hν : ν ≠ 0)
    (hF : 3 ≤ Module.finrank ℝ F) {C : Set F}
    (hC : dimH C < ((Module.finrank ℝ F - 2 : ℕ) : ℝ≥0∞)) :
    IsPathConnected ({x : F | inner ℝ ν x = 0} \ C) := by
  apply isPathConnected_hyperplane_diff_of_hausdorffMeasure_eq_zero hν hF
  have h := hausdorffMeasure_of_dimH_lt (d := ((Module.finrank ℝ F - 2 : ℕ) : ℝ≥0))
    (by exact_mod_cast hC)
  have hcast : (((Module.finrank ℝ F - 2 : ℕ) : ℝ≥0) : ℝ) = (Module.finrank ℝ F : ℝ) - 2 := by
    rw [NNReal.coe_natCast, Nat.cast_sub (by omega : 2 ≤ Module.finrank ℝ F), Nat.cast_ofNat]
  rwa [hcast] at h

/-- **Affine hyperplane version.** For `ν ≠ 0` and any `b`, the affine hyperplane
`{x | ⟪ν, x⟫ = b}` minus a set of vanishing `μH[dim F - 2]` measure is path connected. -/
theorem isPathConnected_affineHyperplane_diff_of_hausdorffMeasure_eq_zero {ν : F} (hν : ν ≠ 0)
    (b : ℝ) (hF : 3 ≤ Module.finrank ℝ F) {C : Set F}
    (hC : μH[(Module.finrank ℝ F : ℝ) - 2] C = 0) :
    IsPathConnected ({x : F | inner ℝ ν x = b} \ C) := by
  set p₀ : F := (b / ‖ν‖ ^ 2) • ν with hp₀_def
  have hν2 : ‖ν‖ ^ 2 ≠ 0 := by positivity
  have hp₀ : inner ℝ ν p₀ = b := by
    rw [hp₀_def, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hC' : μH[(Module.finrank ℝ F : ℝ) - 2] ((fun x => p₀ + x) ⁻¹' C) = 0 := by
    rw [show (fun x => p₀ + x) ⁻¹' C = (IsometryEquiv.addLeft p₀) ⁻¹' C from rfl,
      IsometryEquiv.hausdorffMeasure_preimage]
    exact hC
  have hcont : Continuous fun x : F => p₀ + x := continuous_const.add continuous_id
  have h := (isPathConnected_hyperplane_diff_of_hausdorffMeasure_eq_zero hν hF hC').image hcont
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    refine ⟨x - p₀, ⟨?_, ?_⟩, by simp⟩
    · change inner ℝ ν (x - p₀) = 0
      rw [inner_sub_right, hp₀]
      exact sub_eq_zero.mpr hx
    · change p₀ + (x - p₀) ∉ C
      simpa using hxC
  · rintro ⟨y, ⟨hy, hyC⟩, rfl⟩
    refine ⟨?_, hyC⟩
    change inner ℝ ν (p₀ + y) = b
    have hy' : inner ℝ ν y = 0 := hy
    rw [inner_add_right, hp₀, hy', add_zero]

/-- Affine hyperplane version with a dimension hypothesis `dimH C < dim F - 2`. -/
theorem isPathConnected_affineHyperplane_diff_of_dimH_lt {ν : F} (hν : ν ≠ 0) (b : ℝ)
    (hF : 3 ≤ Module.finrank ℝ F) {C : Set F}
    (hC : dimH C < ((Module.finrank ℝ F - 2 : ℕ) : ℝ≥0∞)) :
    IsPathConnected ({x : F | inner ℝ ν x = b} \ C) := by
  apply isPathConnected_affineHyperplane_diff_of_hausdorffMeasure_eq_zero hν b hF
  have h := hausdorffMeasure_of_dimH_lt (d := ((Module.finrank ℝ F - 2 : ℕ) : ℝ≥0))
    (by exact_mod_cast hC)
  have hcast : (((Module.finrank ℝ F - 2 : ℕ) : ℝ≥0) : ℝ) = (Module.finrank ℝ F : ℝ) - 2 := by
    rw [NNReal.coe_natCast, Nat.cast_sub (by omega : 2 ≤ Module.finrank ℝ F), Nat.cast_ofNat]
  rwa [hcast] at h

end Connectivity

section SpaceForms

/-- Step A on `Space d`. -/
theorem exists_smooth_cutoff_space {d : ℕ} (μ : Measure (Space d)) {A r₀ k : ℝ}
    (hk : 2 < k) (hr₀ : 0 < r₀) {S : Set (Space d)}
    (hgrowth : ∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r₀ →
      μ (closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ k))
    (hS : IsCompact S) (hSnull : μH[k - 2] S = 0) {U : Set (Space d)} (hU : IsOpen U)
    (hSU : S ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∃ V, IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, η x = 0) ∧
      (∃ K, IsCompact K ∧ K ⊆ U ∧ ∀ x ∉ K, η x = 1) ∧ (∀ x ∉ U, η x = 1) ∧
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ η x‖ ^ 2) ∂μ ≤ ENNReal.ofReal ε ∧
      Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2) μ ∧ ∫ x, ‖fderiv ℝ η x‖ ^ 2 ∂μ ≤ ε :=
  exists_smooth_cutoff_of_hausdorffMeasure_eq_zero μ hk hr₀ hgrowth hS hSnull hU hSU hε

/-- Step D on `Space k`: the complement of a set of vanishing `μH[k - 1]` measure is path
connected when `k ≥ 2`. -/
theorem isPathConnected_compl_space {k : ℕ} (hk : 2 ≤ k) {C : Set (Space k)}
    (hC : μH[(k : ℝ) - 1] C = 0) : IsPathConnected Cᶜ := by
  apply isPathConnected_compl_of_hausdorffMeasure_eq_zero
  · rw [finrank_euclideanSpace_fin]
    exact hk
  · rw [finrank_euclideanSpace_fin]
    exact hC

/-- Step D on `Space k` with a dimension hypothesis. -/
theorem isPathConnected_compl_space_of_dimH_lt {k : ℕ} (hk : 2 ≤ k) {C : Set (Space k)}
    (hC : dimH C < ((k - 1 : ℕ) : ℝ≥0∞)) : IsPathConnected Cᶜ := by
  apply isPathConnected_compl_of_dimH_lt
  · rw [finrank_euclideanSpace_fin]
    exact hk
  · rw [finrank_euclideanSpace_fin]
    exact hC

/-- Step D for a linear hyperplane `ν^⊥ ⊆ Space n`, `n ≥ 3`: removing a set of vanishing
`μH[n - 2]` measure leaves a path-connected set. -/
theorem isPathConnected_hyperplane_diff_space {n : ℕ} (hn : 3 ≤ n) {ν : Space n} (hν : ν ≠ 0)
    {C : Set (Space n)} (hC : μH[(n : ℝ) - 2] C = 0) :
    IsPathConnected ({x : Space n | inner ℝ ν x = 0} \ C) := by
  apply isPathConnected_hyperplane_diff_of_hausdorffMeasure_eq_zero hν
  · rw [finrank_euclideanSpace_fin]
    exact hn
  · rw [finrank_euclideanSpace_fin]
    exact hC

/-- Step D for a linear hyperplane `ν^⊥ ⊆ Space n`, `n ≥ 3`, with a dimension hypothesis
`dimH C < n - 2`. -/
theorem isPathConnected_hyperplane_diff_space_of_dimH_lt {n : ℕ} (hn : 3 ≤ n) {ν : Space n}
    (hν : ν ≠ 0) {C : Set (Space n)} (hC : dimH C < ((n - 2 : ℕ) : ℝ≥0∞)) :
    IsPathConnected ({x : Space n | inner ℝ ν x = 0} \ C) := by
  apply isPathConnected_hyperplane_diff_of_dimH_lt hν
  · rw [finrank_euclideanSpace_fin]
    exact hn
  · rw [finrank_euclideanSpace_fin]
    exact hC

/-- Step D for an affine hyperplane `{x | ⟪ν, x⟫ = b} ⊆ Space n`, `n ≥ 3`, with a dimension
hypothesis `dimH C < n - 2`. -/
theorem isPathConnected_affineHyperplane_diff_space_of_dimH_lt {n : ℕ} (hn : 3 ≤ n)
    {ν : Space n} (hν : ν ≠ 0) (b : ℝ) {C : Set (Space n)}
    (hC : dimH C < ((n - 2 : ℕ) : ℝ≥0∞)) :
    IsPathConnected ({x : Space n | inner ℝ ν x = b} \ C) := by
  apply isPathConnected_affineHyperplane_diff_of_dimH_lt hν b
  · rw [finrank_euclideanSpace_fin]
    exact hn
  · rw [finrank_euclideanSpace_fin]
    exact hC

end SpaceForms

end SerrinEpigraph
