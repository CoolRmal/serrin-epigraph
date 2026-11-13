module

public import SerrinEpigraph.RadialFlux
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Nonsingular integral operator for radial initial value problems
-/

public section
noncomputable section
open MeasureTheory Set

namespace SerrinEpigraph

/-- Weighted average on the unit interval, including at radius zero. -/
@[expose] def radialAverage (m : ℕ) (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s ^ m * F (r * s)

/-- Integral form of the regular radial initial value problem. -/
@[expose] def radialPicard (m : ℕ) (f : ℝ → ℝ) (a : ℝ) (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  a - ∫ t in (0 : ℝ)..r, t * radialAverage m (f ∘ q) t

/-- Averaging preserves continuity, with no division by the radius. -/
theorem radialAverage_continuous (m : ℕ) {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (radialAverage m F) := by
  have hc : Continuous (Function.uncurry (fun r s : ℝ ↦ s ^ m * F (r * s))) := by
    fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hc
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  change Continuous (fun r ↦ ∫ s in (0 : ℝ)..1, s ^ m * F (r * s))
  simpa only [ intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hi

/-- A uniform forcing bound gives the dimension-dependent average bound. -/
theorem radialAverage_norm_le (m : ℕ) {F : ℝ → ℝ} {r M : ℝ}
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, ‖F (r * s)‖ ≤ M) :
    ‖radialAverage m F r‖ ≤ M / (m + 1 : ℝ) := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ s ^ m * M) volume 0 1 :=
    (by fun_prop : Continuous (fun s : ℝ ↦ s ^ m * M)).intervalIntegrable 0 1
  have he := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun s : ℝ ↦ s ^ m * F (r * s)) (zero_le_one : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun s (hs : s ∈ Ioc (0 : ℝ) 1) ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1.le m)]
      exact mul_le_mul_of_nonneg_left (hF s ⟨hs.1.le, hs.2⟩) (pow_nonneg hs.1.le m))) hi
  change ‖∫ s in (0 : ℝ)..1, s ^ m * F (r * s)‖ ≤ _
  convert he using 1
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp [div_eq_mul_inv, mul_comm]

/-- The integral operator has the prescribed center value. -/
theorem radialPicard_zero (m : ℕ) (f : ℝ → ℝ) (a : ℝ) (q : ℝ → ℝ) :
    radialPicard m f a q 0 = a := by
  simp [radialPicard]

/-- Continuous forcing gives the radial derivative of the integral operator. -/
theorem radialPicard_hasDerivAt (m : ℕ) {f q : ℝ → ℝ} (a r : ℝ)
    (hfq : Continuous (f ∘ q)) :
    HasDerivAt (radialPicard m f a q) (-r * radialAverage m (f ∘ q) r) r := by
  have hc : Continuous (fun t : ℝ ↦ t * radialAverage m (f ∘ q) t) :=
    continuous_id.mul (radialAverage_continuous m hfq)
  change HasDerivAt (fun x ↦ a - ∫ t in (0 : ℝ)..x,
    t * radialAverage m (f ∘ q) t) _ r
  convert (hasDerivAt_const r a).sub (hc.integral_hasStrictDerivAt 0 r).hasDerivAt using 1
  ring

/-- The radial derivative vanishes at the center. -/
theorem radialPicard_hasDerivAt_zero (m : ℕ) {f q : ℝ → ℝ} (a : ℝ)
    (hfq : Continuous (f ∘ q)) : HasDerivAt (radialPicard m f a q) 0 0 := by
  simpa using radialPicard_hasDerivAt m a 0 hfq

/-- The integral operator moves the initial value by at most a quadratic amount. -/
theorem radialPicard_norm_sub_le (m : ℕ) {f q : ℝ → ℝ} {a r M : ℝ}
    (hr : 0 ≤ r) (hf : ∀ t ∈ Icc (0 : ℝ) r, ‖f (q t)‖ ≤ M) :
    ‖radialPicard m f a q r - a‖ ≤ r ^ 2 / 2 * (M / (m + 1 : ℝ)) := by
  have hb : ∀ t ∈ Ioc (0 : ℝ) r,
      ‖t * radialAverage m (f ∘ q) t‖ ≤ t * (M / (m + 1 : ℝ)) := by
    intro t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
    apply mul_le_mul_of_nonneg_left _ ht.1.le
    apply radialAverage_norm_le
    intro s hs
    exact hf (t * s) ⟨mul_nonneg ht.1.le hs.1,
      (mul_le_of_le_one_right ht.1.le hs.2).trans ht.2⟩
  have hi : IntervalIntegrable (fun t : ℝ ↦ t * (M / (m + 1 : ℝ))) volume 0 r :=
    (by fun_prop : Continuous (fun t : ℝ ↦ t * (M / (m + 1 : ℝ)))).intervalIntegrable 0 r
  have he := intervalIntegral.norm_integral_le_of_norm_le hr
    (Filter.Eventually.of_forall hb) hi
  have heq : (∫ t in (0 : ℝ)..r, t * (M / (m + 1 : ℝ))) =
      r ^ 2 / 2 * (M / (m + 1 : ℝ)) := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    simp
  rw [heq] at he
  simpa only [radialPicard, sub_sub_cancel_left, norm_neg] using he

/-- The weighted average is linear under subtraction of continuous forcings. -/
theorem radialAverage_sub (m : ℕ) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) (r : ℝ) :
    radialAverage m (F - G) r = radialAverage m F r - radialAverage m G r := by
  have hFi : IntervalIntegrable (fun s : ℝ ↦ s ^ m * F (r * s)) volume 0 1 :=
    (by fun_prop : Continuous (fun s : ℝ ↦ s ^ m * F (r * s))).intervalIntegrable 0 1
  have hGi : IntervalIntegrable (fun s : ℝ ↦ s ^ m * G (r * s)) volume 0 1 :=
    (by fun_prop : Continuous (fun s : ℝ ↦ s ^ m * G (r * s))).intervalIntegrable 0 1
  simp only [radialAverage, Pi.sub_apply, mul_sub]
  exact intervalIntegral.integral_sub hFi hGi

/-- A forcing difference bound gives the quadratic Picard difference estimate. -/
theorem radialPicard_norm_sub_picard_le (m : ℕ) {f q w : ℝ → ℝ} {a r M : ℝ}
    (hq : Continuous (f ∘ q)) (hw : Continuous (f ∘ w)) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc (0 : ℝ) r, ‖f (q t) - f (w t)‖ ≤ M) :
    ‖radialPicard m f a q r - radialPicard m f a w r‖ ≤
      r ^ 2 / 2 * (M / (m + 1 : ℝ)) := by
  have hqi : IntervalIntegrable (fun t : ℝ ↦ t * radialAverage m (f ∘ q) t)
      volume 0 r := (continuous_id.mul (radialAverage_continuous m hq)).intervalIntegrable 0 r
  have hwi : IntervalIntegrable (fun t : ℝ ↦ t * radialAverage m (f ∘ w) t)
      volume 0 r := (continuous_id.mul (radialAverage_continuous m hw)).intervalIntegrable 0 r
  have he := radialPicard_norm_sub_le m (f := (f ∘ q) - (f ∘ w)) (q := id)
    (a := 0) hr hf
  have hid : ((f ∘ q) - (f ∘ w)) ∘ id = (f ∘ q) - (f ∘ w) := rfl
  simp only [radialPicard, hid, radialAverage_sub m hq hw, mul_sub,
    intervalIntegral.integral_sub hqi hwi, zero_sub, sub_zero, norm_neg] at he
  simpa only [radialPicard, sub_sub_sub_cancel_left, norm_sub_rev] using he

end SerrinEpigraph
