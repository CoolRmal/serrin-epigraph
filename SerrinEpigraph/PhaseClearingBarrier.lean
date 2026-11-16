module

public import SerrinEpigraph.RadialHessian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# An explicit annular supersolution for low-phase clearing

An exponential radial profile replaces the exact radial Poisson solution. Its
outer boundary value is at least the prescribed amplitude, its negative
Laplacian dominates the reaction bound, and its inner slope has the required
amplitude-over-radius estimate.
-/

public section
noncomputable section

open Set InnerProductSpace Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- A radial exponential profile vanishing at the inner radius. -/
@[expose] def phaseClearingProfile (A b s ρ : ℝ) : ℝ :=
  A * (1 - Real.exp (-b * (ρ - s)))

/-- The derivative of the exponential profile. -/
@[expose] def phaseClearingSlope (A b s ρ : ℝ) : ℝ :=
  A * b * Real.exp (-b * (ρ - s))

theorem phaseClearingProfile_contDiff (A b s : ℝ) :
    ContDiff ℝ ⊤ (phaseClearingProfile A b s) := by
  unfold phaseClearingProfile
  fun_prop

theorem phaseClearingProfile_hasDerivAt (A b s ρ : ℝ) :
    HasDerivAt (phaseClearingProfile A b s) (phaseClearingSlope A b s ρ) ρ := by
  have he := (((hasDerivAt_id ρ).sub_const s).const_mul (-b)).exp
  convert ((hasDerivAt_const ρ (1 : ℝ)).sub he).const_mul A using 1
  all_goals first | rfl | (dsimp [phaseClearingSlope]; ring)

theorem phaseClearingSlope_hasDerivAt (A b s ρ : ℝ) :
    HasDerivAt (phaseClearingSlope A b s) (-b * phaseClearingSlope A b s ρ) ρ := by
  have he := (((hasDerivAt_id ρ).sub_const s).const_mul (-b)).exp
  convert he.const_mul (A * b) using 1
  all_goals first | rfl | (dsimp [phaseClearingSlope]; ring)

theorem phaseClearingProfile_inner (A b s : ℝ) :
    phaseClearingProfile A b s s = 0 := by
  simp [phaseClearingProfile]

theorem phaseClearingProfile_nonneg {A b s ρ : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hρ : s ≤ ρ) :
    0 ≤ phaseClearingProfile A b s ρ := by
  apply mul_nonneg hA
  have he : Real.exp (-b * (ρ - s)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact sub_nonneg.mpr he

theorem phaseClearingSlope_nonneg {A b s ρ : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    0 ≤ phaseClearingSlope A b s ρ := by
  unfold phaseClearingSlope
  positivity

/-- The amplitude chosen for the half-radius annulus. -/
@[expose] def phaseClearingAmplitude (m : ℕ) (δ F r : ℝ) : ℝ :=
  Real.exp ((m : ℝ) + 1) * (δ + F * r ^ 2)

/-- The radial decay rate for the half-radius annulus. -/
@[expose] def phaseClearingRate (m : ℕ) (r : ℝ) : ℝ :=
  2 * ((m : ℝ) + 1) / r

/-- A dimension-only constant for the inner boundary slope. -/
@[expose] def phaseClearingSlopeConstant (m : ℕ) : ℝ :=
  2 * ((m : ℝ) + 1) * Real.exp ((m : ℝ) + 1)

theorem phaseClearingSlopeConstant_pos (m : ℕ) :
    0 < phaseClearingSlopeConstant m := by
  unfold phaseClearingSlopeConstant
  positivity

theorem phaseClearingAmplitude_nonneg (m : ℕ) {δ F r : ℝ}
    (hδ : 0 ≤ δ) (hF : 0 ≤ F) : 0 ≤ phaseClearingAmplitude m δ F r := by
  unfold phaseClearingAmplitude
  positivity

theorem phaseClearingRate_pos (m : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < phaseClearingRate m r := by
  unfold phaseClearingRate
  positivity

/-- The outer barrier value dominates the small amplitude prescribed for the solution. -/
theorem phaseClearingProfile_outer_ge (m : ℕ) {δ F r : ℝ}
    (hδ : 0 ≤ δ) (hF : 0 ≤ F) (hr : 0 < r) :
    δ ≤ phaseClearingProfile (phaseClearingAmplitude m δ F r)
      (phaseClearingRate m r) (r / 2) r := by
  have hexp : -(phaseClearingRate m r) * (r - r / 2) = -((m : ℝ) + 1) := by
    unfold phaseClearingRate
    field_simp
    ring
  have heprod : Real.exp ((m : ℝ) + 1) * Real.exp (-((m : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add]
    simp
  have he : 2 ≤ Real.exp ((m : ℝ) + 1) := by
    have hx := Real.add_one_le_exp ((m : ℝ) + 1)
    linarith [Nat.cast_nonneg (α := ℝ) m]
  unfold phaseClearingProfile phaseClearingAmplitude
  rw [hexp]
  nlinarith [mul_nonneg hF (sq_nonneg r)]

/-- The derivative on the inner sphere has the exact required scale. -/
theorem phaseClearingSlope_inner (m : ℕ) {δ F r : ℝ} (hr : 0 < r) :
    phaseClearingSlope (phaseClearingAmplitude m δ F r)
      (phaseClearingRate m r) (r / 2) (r / 2) =
      phaseClearingSlopeConstant m * (δ / r + F * r) := by
  simp only [phaseClearingSlope, sub_self, mul_zero, Real.exp_zero, mul_one]
  unfold phaseClearingAmplitude phaseClearingRate phaseClearingSlopeConstant
  field_simp

/-- The exponential factor has a uniform lower bound throughout the annulus. -/
theorem phaseClearing_exp_lower (m : ℕ) {r ρ : ℝ} (hr : 0 < r) (hρ : ρ ≤ r) :
    Real.exp (-((m : ℝ) + 1)) ≤
      Real.exp (-phaseClearingRate m r * (ρ - r / 2)) := by
  apply Real.exp_le_exp.mpr
  have hb := (phaseClearingRate_pos m hr).le
  have he : phaseClearingRate m r * (r - r / 2) = (m : ℝ) + 1 := by
    unfold phaseClearingRate
    field_simp
    ring
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hρ (r / 2)) hb
  linarith

/-- The radial derivative dominates the forcing contribution. -/
theorem phaseClearingSlope_forcing_lower (m : ℕ) {δ F r ρ : ℝ}
    (hδ : 0 ≤ δ) (hF : 0 ≤ F) (hr : 0 < r) (hρ : ρ ≤ r) :
    2 * ((m : ℝ) + 1) * F * r ≤
      phaseClearingSlope (phaseClearingAmplitude m δ F r)
        (phaseClearingRate m r) (r / 2) ρ := by
  have he := phaseClearing_exp_lower m hr hρ
  have hA := phaseClearingAmplitude_nonneg m (r := r) hδ hF
  have hb := (phaseClearingRate_pos m hr).le
  have hexp : Real.exp ((m : ℝ) + 1) * Real.exp (-((m : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ ≤ 2 * ((m : ℝ) + 1) * (δ / r + F * r) := by
      have hd : 0 ≤ δ / r := div_nonneg hδ hr.le
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    _ = phaseClearingAmplitude m δ F r * phaseClearingRate m r *
        Real.exp (-((m : ℝ) + 1)) := by
      unfold phaseClearingAmplitude phaseClearingRate
      field_simp
      rw [mul_assoc, hexp, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hA hb)

/-- The radial curvature term does not consume the forcing supplied by the barrier. -/
theorem phaseClearing_radial_operator_lower (m : ℕ) {δ F r ρ : ℝ}
    (hδ : 0 ≤ δ) (hF : 0 ≤ F) (hr : 0 < r) (hρ : ρ ∈ Icc (r / 2) r) :
    F ≤ (phaseClearingRate m r - (m : ℝ) / ρ) *
      phaseClearingSlope (phaseClearingAmplitude m δ F r)
        (phaseClearingRate m r) (r / 2) ρ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (by positivity) hρ.1
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcoef : 2 / r ≤ phaseClearingRate m r - (m : ℝ) / ρ := by
    have hh : (m : ℝ) / ρ ≤ 2 * (m : ℝ) / r := by
      apply (div_le_div_iff₀ hρpos hr).mpr
      nlinarith [hρ.1]
    calc
      2 / r = phaseClearingRate m r - 2 * (m : ℝ) / r := by
        unfold phaseClearingRate
        ring
      _ ≤ _ := sub_le_sub_left hh _
  have hs := phaseClearingSlope_forcing_lower m hδ hF hr hρ.2
  have hsn := phaseClearingSlope_nonneg (s := r / 2) (ρ := ρ)
    (phaseClearingAmplitude_nonneg m (r := r) hδ hF) (phaseClearingRate_pos m hr).le
  calc
    F ≤ 4 * ((m : ℝ) + 1) * F := by nlinarith
    _ = (2 / r) * (2 * ((m : ℝ) + 1) * F * r) := by field_simp; ring
    _ ≤ (2 / r) * phaseClearingSlope (phaseClearingAmplitude m δ F r)
        (phaseClearingRate m r) (r / 2) ρ :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hsn

/-- The exponential radial profile viewed as a spatial function. -/
@[expose] def phaseClearingSpatial {d : ℕ} (A b s : ℝ) (c x : Space d) : ℝ :=
  phaseClearingProfile A b s ‖x - c‖

theorem phaseClearingSpatial_hasGradientAt {d : ℕ} (A b s : ℝ) {c x : Space d}
    (hx : x ≠ c) :
    HasGradientAt (phaseClearingSpatial A b s c)
      ((phaseClearingSlope A b s ‖x - c‖ / ‖x - c‖) • (x - c)) x := by
  have hn := (hasFDerivAt_euclidean_norm (sub_ne_zero.mpr hx)).comp x
    ((hasFDerivAt_id x).sub_const c)
  have he := (phaseClearingProfile_hasDerivAt A b s ‖x - c‖).comp_hasFDerivAt x hn
  rw [hasGradientAt_iff_hasFDerivAt]
  convert he using 1
  · rfl
  · ext y
    simp [InnerProductSpace.toDual_apply_apply, div_eq_mul_inv, mul_assoc]

theorem phaseClearingSlope_ratio_hasDerivAt (A b s : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    HasDerivAt (fun t ↦ phaseClearingSlope A b s t / t)
      ((-b * phaseClearingSlope A b s ρ - phaseClearingSlope A b s ρ / ρ) / ρ) ρ := by
  convert (phaseClearingSlope_hasDerivAt A b s ρ).div (hasDerivAt_id ρ) hρ using 1
  · rfl
  · simp only [id_eq]
    field_simp

theorem phaseClearingSpatial_gradient_hasFDerivAt {d : ℕ} (A b s : ℝ)
    {c x : Space d} (hx : x ≠ c) :
    HasFDerivAt (gradient (phaseClearingSpatial A b s c))
      ((phaseClearingSlope A b s ‖x - c‖ / ‖x - c‖) •
          ContinuousLinearMap.id ℝ (Space d) +
        ((-b * phaseClearingSlope A b s ‖x - c‖ -
            phaseClearingSlope A b s ‖x - c‖ / ‖x - c‖) / ‖x - c‖ ^ 2) •
          (innerSL ℝ (x - c)).smulRight (x - c)) x := by
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hd := hasFDerivAt_radial_vectorField hx
    (phaseClearingSlope_ratio_hasDerivAt A b s hn)
  have heq : gradient (phaseClearingSpatial A b s c) =ᶠ[𝓝 x]
      (fun y ↦ (phaseClearingSlope A b s ‖y - c‖ / ‖y - c‖) • (y - c)) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact (phaseClearingSpatial_hasGradientAt A b s hy).gradient
  convert hd.congr_of_eventuallyEq heq using 1
  congr 1
  congr 1
  rw [div_div, pow_two]

/-- The negative spatial Laplacian equals the radial supersolution operator. -/
theorem phaseClearingSpatial_laplacian (m : ℕ) (A b s : ℝ)
    {c x : Space (m + 1)} (hx : x ≠ c) :
    -(Δ (phaseClearingSpatial A b s c)) x =
      (b - (m : ℝ) / ‖x - c‖) * phaseClearingSlope A b s ‖x - c‖ := by
  have hd := phaseClearingSpatial_gradient_hasFDerivAt A b s hx
  rw [laplacian_eq_sum_gradient_derivative_of_differentiable hd.differentiableAt
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ), hd.fderiv, radial_hessian_trace]
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The chosen spatial barrier dominates the reaction bound on the full closed annulus. -/
theorem phaseClearingSpatial_supersolution (m : ℕ) {δ F r : ℝ}
    (hδ : 0 ≤ δ) (hF : 0 ≤ F) (hr : 0 < r) {c x : Space (m + 1)}
    (hx : ‖x - c‖ ∈ Icc (r / 2) r) :
    F ≤ -(Δ (phaseClearingSpatial (phaseClearingAmplitude m δ F r)
      (phaseClearingRate m r) (r / 2) c)) x := by
  have hne : x ≠ c := sub_ne_zero.mp (norm_pos_iff.mp
    (lt_of_lt_of_le (by positivity) hx.1))
  rw [phaseClearingSpatial_laplacian m _ _ _ hne]
  exact phaseClearing_radial_operator_lower m hδ hF hr hx

end SerrinEpigraph
