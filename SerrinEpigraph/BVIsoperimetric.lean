module

public import SerrinEpigraph.BVTranslation

/-!
# A nonsharp isoperimetric estimate from translations

Averaging the translation estimate on a ball avoids a coordinate Sobolev inequality.
The overlap of a phase with any translated averaging ball is bounded by its total volume.
-/

public section

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Averaging translations gives the volume-perimeter interpolation estimate. -/
theorem phase_volume_perimeter_interpolation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    (hE : MeasurableSet E) (hEV : volume E ≠ ⊤) {B r : ℝ} (hB : 0 ≤ B)
    (hP : variationalPerimeter b E univ ≤ ENNReal.ofReal B) :
    volume.real E * (volume.real (ball (0 : Space d) r) - volume.real E) ≤
      r * B * volume.real (ball (0 : Space d) r) := by
  let χ := E.indicator (fun _ : Space d ↦ (1 : ℝ))
  let S := ball (0 : Space d) r
  let : IsFiniteMeasure (volume.restrict S) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Space d) r).measure_lt_top
  let H : Space d × Space d → ℝ := fun p ↦ χ p.1 * (1 - χ (p.1 + p.2))
  have hχ : Measurable χ := measurable_const.indicator hE
  have hχi : Integrable χ volume :=
    (integrableOn_const (C := (1 : ℝ)) hEV).integrable_indicator hE
  have hχrange (x : Space d) : χ x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ E <;> simp [χ, hx]
  have hχnorm (x : Space d) : ‖χ x‖ = χ x := Real.norm_of_nonneg (hχrange x).1
  have hχmass : (∫ x, χ x) = volume.real E := by
    simp [χ, integral_indicator hE, measureReal_def]
  have hH : Measurable H := (hχ.comp measurable_fst).mul
    (measurable_const.sub (hχ.comp (measurable_fst.add measurable_snd)))
  have hHi : Integrable H (volume.prod (volume.restrict S)) := by
    apply (hχi.comp_fst (volume.restrict S)).mono' hH.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      change ‖χ p.1 * (1 - χ (p.1 + p.2))‖ ≤ χ p.1
      rw [norm_mul, hχnorm, Real.norm_of_nonneg (sub_nonneg.mpr (hχrange _).2)]
      nlinarith [(hχrange p.1).1, (hχrange (p.1 + p.2)).1]
  have hupper (z : Space d) (hz : z ∈ S) : (∫ x, H (x, z)) ≤ r * B := by
    have hzi := (measurePreserving_add_right volume z).integrable_comp_of_integrable hχi
    have hHzi : Integrable (fun x ↦ H (x, z)) volume := by
      apply hχi.mono' (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      exact Eventually.of_forall fun x ↦ by
        change ‖χ x * (1 - χ (x + z))‖ ≤ χ x
        rw [norm_mul, hχnorm, Real.norm_of_nonneg (sub_nonneg.mpr (hχrange _).2)]
        nlinarith [(hχrange x).1, (hχrange (x + z)).1]
    have hle : (∫ x, H (x, z)) ≤ ∫ x, ‖χ (x + z) - χ x‖ := by
      apply integral_mono hHzi (hzi.sub hχi).norm
      intro x
      by_cases hx : x ∈ E
      · change χ x * (1 - χ (x + z)) ≤ |χ (x + z) - χ x|
        have hxχ : χ x = 1 := indicator_of_mem hx _
        rw [hxχ, one_mul, abs_sub_comm]
        exact le_abs_self _
      · simp [H, χ, hx]
    apply hle.trans
    apply (integral_phase_translation_le_global_perimeter_bound b hE hEV hB hP z).trans
    exact mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hz).le hB
  have htotalUpper : (∫ z in S, ∫ x, H (x, z)) ≤ r * B * volume.real S := by
    have hbound := setIntegral_mono_on hHi.integral_prod_right
      (integrableOn_const (μ := volume) (s := S) (C := r * B)) measurableSet_ball hupper
    simpa only [setIntegral_const, smul_eq_mul, mul_comm (volume.real S)] using hbound
  have hlower (x : Space d) : χ x * (volume.real S - volume.real E) ≤
      ∫ z in S, H (x, z) := by
    have hxi : Integrable (fun z ↦ χ (x + z)) volume :=
      (measurePreserving_add_left volume x).integrable_comp_of_integrable hχi
    have hxiMass : (∫ z, χ (x + z)) = volume.real E :=
      (integral_add_left_eq_self (μ := volume) χ x).trans hχmass
    have hpart : (∫ z in S, χ (x + z)) ≤ volume.real E := by
      rw [← hxiMass]
      exact setIntegral_le_integral hxi (Eventually.of_forall fun z ↦ (hχrange _).1)
    change χ x * (volume.real S - volume.real E) ≤
      ∫ z in S, χ x * (1 - χ (x + z))
    rw [integral_const_mul, integral_sub
      (integrableOn_const (μ := volume) (s := S) (C := (1 : ℝ))) hxi.integrableOn]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hpart _) (hχrange x).1
  have htotalLower := integral_mono (hχi.mul_const (volume.real S - volume.real E))
    hHi.integral_prod_left hlower
  rw [integral_mul_const, hχmass, integral_integral_swap hHi] at htotalLower
  exact htotalLower.trans htotalUpper

/-- A nonsharp Euclidean isoperimetric inequality, in an equivalent integer-power form.
The constant is explicit and depends only on the ambient dimension. -/
theorem finite_perimeter_isoperimetric_pow {m : ℕ} (hm : 0 < m)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E) (hEV : volume E ≠ ⊤)
    {B : ℝ} (hB : 0 ≤ B) (hP : variationalPerimeter b E univ ≤ ENNReal.ofReal B) :
    volume.real (ball (0 : Space (m + 1)) 1) * volume.real E ^ m ≤
      2 ^ (m + 2) * B ^ (m + 1) := by
  let V := volume.real E
  let ω := volume.real (ball (0 : Space (m + 1)) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne'
    measure_ball_ne_top
  have hV0 : 0 ≤ V := measureReal_nonneg
  by_cases hV : V = 0
  · change ω * V ^ m ≤ _
    rw [hV, zero_pow hm.ne', mul_zero]
    positivity
  have hVpos : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hV)
  let r := (2 * V / ω) ^ (((m + 1 : ℕ) : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num) hVpos) hω) _
  have hrpow : r ^ (m + 1) = 2 * V / ω :=
    Real.rpow_inv_natCast_pow (div_nonneg (mul_nonneg (by norm_num) hV0) hω.le)
      (Nat.succ_ne_zero m)
  have hball : volume.real (ball (0 : Space (m + 1)) r) = 2 * V := by
    change (volume (ball (0 : Space (m + 1)) r)).toReal = _
    rw [volume.addHaar_ball_of_pos _ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    simp only [Space, finrank_euclideanSpace_fin]
    change r ^ (m + 1) * ω = 2 * V
    rw [hrpow, div_mul_cancel₀ _ hω.ne']
  have hinter := phase_volume_perimeter_interpolation b hE hEV hB hP (r := r)
  rw [hball] at hinter
  change V * (2 * V - V) ≤ r * B * (2 * V) at hinter
  have hlinear : V ≤ 2 * r * B := by nlinarith
  have hpower := pow_le_pow_left₀ hV0 hlinear (m + 1)
  have hscaled := mul_le_mul_of_nonneg_left hpower hω.le
  rw [mul_pow, mul_pow, hrpow] at hscaled
  have halgebra : ω * ((2 : ℝ) ^ (m + 1) * (2 * V / ω) * B ^ (m + 1)) =
      V * (2 ^ (m + 2) * B ^ (m + 1)) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    field_simp
    ring
  rw [halgebra, pow_succ] at hscaled
  have hfinal : V * (ω * V ^ m) ≤ V * (2 ^ (m + 2) * B ^ (m + 1)) := by
    convert hscaled using 1
    ring
  exact (mul_le_mul_iff_right₀ hVpos).mp hfinal

/-- The preceding integer-power estimate gives the usual volume exponent `(n - 1) / n`. -/
theorem finite_perimeter_isoperimetric {m : ℕ} (hm : 0 < m)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E) (hEV : volume E ≠ ⊤)
    {B : ℝ} (hB : 0 ≤ B) (hP : variationalPerimeter b E univ ≤ ENNReal.ofReal B) :
    volume.real E ^ ((m : ℝ) / (m + 1)) ≤
      ((2 : ℝ) ^ (m + 2) / volume.real (ball (0 : Space (m + 1)) 1)) ^
        ((m : ℝ) + 1)⁻¹ * B := by
  have hω : 0 < volume.real (ball (0 : Space (m + 1)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hpower := finite_perimeter_isoperimetric_pow hm b hE hEV hB hP
  have hdiv : volume.real E ^ m ≤
      ((2 : ℝ) ^ (m + 2) / volume.real (ball (0 : Space (m + 1)) 1)) * B ^ (m + 1) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hω).mpr
    simpa only [mul_comm (volume.real E ^ m)] using hpower
  have hexp : 0 ≤ ((m : ℝ) + 1)⁻¹ := by positivity
  have hroot := Real.rpow_le_rpow (pow_nonneg measureReal_nonneg _) hdiv hexp
  rw [Real.mul_rpow (div_nonneg (by positivity) hω.le) (pow_nonneg hB _),
    show ((m : ℝ) + 1)⁻¹ = (((m + 1 : ℕ) : ℝ))⁻¹ by simp,
    Real.pow_rpow_inv_natCast hB (Nat.succ_ne_zero m)] at hroot
  simpa only [← Real.rpow_natCast, ← Real.rpow_mul measureReal_nonneg,
    Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hroot

end SerrinEpigraph
