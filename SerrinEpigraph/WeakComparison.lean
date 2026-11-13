module

public import SerrinEpigraph.WeakEquation
public import SerrinEpigraph.Truncation

/-!
# Weak comparison with compactly supported negative part

Testing a weak supersolution of `-Δw + M w ≥ 0` with the cube of its negative part proves
nonnegativity when `M > 0`. The cubic truncation is continuously differentiable, so the argument
requires no second derivatives of the supersolution.
-/

public section

open MeasureTheory InnerProductSpace

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Weak supersolution inequality for `-Δw + M w`, tested against nonnegative interior `C¹`
functions of compact support. -/
@[expose]
def IsWeakSupersolution (μ : Measure E) (Ω : Set E) (M : ℝ) (w : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (gradient w x) (gradient φ x) + M * w x * φ x ∂μ

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivative pairing for a cubic negative-part test has the favorable sign. -/
theorem inner_gradient_negativePart_cube {w : E → ℝ} {x : E}
    (hw : DifferentiableAt ℝ w x) :
    inner ℝ (gradient w x) (gradient (fun y ↦ max (-w y) 0 ^ 3) x) =
      -(3 * max (-w x) 0 ^ 2 * ‖gradient w x‖ ^ 2) := by
  have hd := (hasDerivAt_positivePart_pow (k := 3) (by norm_num) (-w x)).comp_hasFDerivAt x
    hw.hasFDerivAt.neg
  simp only [Function.comp_def, Pi.neg_apply] at hd
  rw [inner_gradient_right, hd.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul, RCLike.conj_to_real, Nat.cast_ofNat]
  rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
  norm_num

/-- A locally `C¹` weak supersolution with compactly supported negative part is nonnegative. -/
theorem IsWeakSupersolution.nonneg_of_hasCompactSupport_negativePart
    {Ω : Set E} {M : ℝ} {w : E → ℝ} (hweak : IsWeakSupersolution μ Ω M w)
    (hΩ : IsOpen Ω) (hM : 0 < M) (hw : ContDiffOn ℝ 1 w Ω)
    (hc : HasCompactSupport (fun x ↦ max (-w x) 0))
    (hsub : tsupport (fun x ↦ max (-w x) 0) ⊆ Ω) : ∀ x, 0 ≤ w x := by
  let z : E → ℝ := fun x ↦ max (-w x) 0
  let φ : E → ℝ := fun x ↦ z x ^ 3
  have hφc : HasCompactSupport φ := hc.comp_left (g := fun t : ℝ ↦ t ^ 3) (by simp)
  have hφsub : tsupport φ ⊆ Ω :=
    (tsupport_comp_subset (g := fun t : ℝ ↦ t ^ 3) (by simp) z).trans hsub
  have hφ : ContDiff ℝ 1 φ := by
    apply contDiff_iff_contDiffAt.2
    intro x
    by_cases hx : x ∈ Ω
    · exact (contDiff_positivePart_pow (k := 3) (by norm_num)).contDiffAt.comp x
        (hw.contDiffAt (hΩ.mem_nhds hx)).neg
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 (fun hx' ↦ hx (hφsub hx')))
  have hz : ∀ x, 0 ≤ z x := fun x ↦ le_max_right _ _
  have htest := hweak φ hφ hφc hφsub (fun x ↦ pow_nonneg (hz x) _)
  have hpair : Integrable (fun x ↦ inner ℝ (gradient w x) (gradient φ x)) μ :=
    integrable_inner_gradient_of_hasCompactSupport hΩ hw hφ hφc hφsub
  have hmul : Integrable (fun x ↦ M * w x * φ x) μ := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport φ))).mp
    exact ((continuousOn_const.mul (hw.continuousOn.mono hφsub)).mul
      hφ.continuous.continuousOn).integrableOn_compact hφc
  rw [integral_add hpair hmul] at htest
  have hpair_nonpos : (∫ x, inner ℝ (gradient w x) (gradient φ x) ∂μ) ≤ 0 := by
    apply integral_nonpos
    intro x
    by_cases hx : x ∈ Ω
    · change inner ℝ (gradient w x) (gradient (fun y ↦ max (-w y) 0 ^ 3) x) ≤ 0
      rw [inner_gradient_negativePart_cube
        ((hw.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx))]
      exact neg_nonpos.mpr (by positivity)
    · have hx' : x ∉ tsupport φ := fun hx' ↦ hx (hφsub hx')
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx']
  have hpoint (x : E) : M * w x * φ x = -(M * z x ^ 4) := by
    change M * w x * max (-w x) 0 ^ 3 = -(M * max (-w x) 0 ^ 4)
    by_cases hx : w x < 0
    · rw [max_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by linarith)]
      simp
  simp_rw [hpoint, integral_neg, integral_const_mul] at htest
  have hint_le : (∫ x, z x ^ 4 ∂μ) ≤ 0 := by nlinarith
  have hzcont : Continuous z :=
    continuous_of_tsupport fun x hx ↦
      ((hw.continuousOn.continuousAt (hΩ.mem_nhds (hsub hx))).neg.max continuousAt_const)
  have hzc : HasCompactSupport (fun x ↦ z x ^ 4) :=
    hc.comp_left (g := fun t : ℝ ↦ t ^ 4) (by simp)
  intro x
  by_contra hx
  have hx' : w x < 0 := lt_of_not_ge hx
  have hzx : z x ^ 4 ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (neg_pos.2 hx')
    (le_max_left _ _)))
  have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := μ) (hzcont.pow 4)
    ((hzcont.pow 4).integrable_of_hasCompactSupport hzc) (fun y ↦ pow_nonneg (hz y) 4) hzx
  exact (not_lt_of_ge hint_le) hpos

end SerrinEpigraph
