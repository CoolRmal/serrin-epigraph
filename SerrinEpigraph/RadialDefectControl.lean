module

public import SerrinEpigraph.RadialDefectProfile
public import SerrinEpigraph.RescaledPhaseEnergy

/-!
# Radial defect control on balls and under rescaling
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- Squared derivative in the unnormalized radial direction. -/
@[expose] def radialGradientDensity {d : ℕ} (v : Space d → ℝ) (c x : Space d) : ℝ :=
  (inner ℝ (gradient v x) (x - c)) ^ 2

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The radial density of the zero extension is an indicator of a continuous density on the
closed domain. -/
theorem Hypotheses.radialGradient_zeroExtension_eq_indicator (h : Hypotheses g u f κ)
    (c : Space (m + 1)) :
    radialGradientDensity (zeroExtension g u) c = (epigraph g).indicator
      (fun x ↦ (inner ℝ (gradientWithin u (closure (epigraph g)) x) (x - c)) ^ 2) := by
  funext x
  by_cases hx : x ∈ epigraph g
  · simp only [radialGradientDensity, indicator_of_mem hx,
      h.gradient_zeroExtension hx, h.closed_gradient_eq hx]
  · simp [radialGradientDensity, indicator_of_notMem hx, h.gradient_zeroExtension_of_notMem hx]

/-- The zero extension's radial density is integrable on every compact set. -/
theorem Hypotheses.integrableOn_radialGradient_zeroExtension (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (radialGradientDensity (zeroExtension g u) c) K := by
  rw [h.radialGradient_zeroExtension_eq_indicator c]
  apply (integrableOn_indicator_iff (isOpen_epigraph h.graph_contDiff.continuous).measurableSet).mpr
  have hA : ContinuousOn (fun x ↦
      (inner ℝ (gradientWithin u (closure (epigraph g)) x) (x - c)) ^ 2)
      (closure (epigraph g)) := (h.closed_gradient_continuousOn.inner
        (continuous_id.sub continuous_const).continuousOn).pow 2
  have hi := (hA.mono inter_subset_right).integrableOn_compact (μ := volume)
    (hK.inter_right isClosed_closure)
  exact hi.mono_set (fun x hx ↦ ⟨hx.2, subset_closure hx.1⟩)

/-- A weighted radial density agrees with its interior integral. -/
theorem Hypotheses.integral_radialGradient_zeroExtension_mul (h : Hypotheses g u f κ)
    (c : Space (m + 1)) (χ : Space (m + 1) → ℝ) :
    (∫ x, radialGradientDensity (zeroExtension g u) c x * χ x) =
      ∫ x in epigraph g, (inner ℝ (gradient u x) (x - c)) ^ 2 * χ x := by
  have he : (fun x ↦ radialGradientDensity (zeroExtension g u) c x * χ x) =
      (epigraph g).indicator (fun x ↦ (inner ℝ (gradient u x) (x - c)) ^ 2 * χ x) := by
    funext x
    by_cases hx : x ∈ epigraph g
    · simp only [radialGradientDensity, indicator_of_mem hx, h.gradient_zeroExtension hx]
    · simp [radialGradientDensity, indicator_of_notMem hx, h.gradient_zeroExtension_of_notMem hx]
  rw [he, integral_indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]

/-- The same weighted density is integrable for compact continuous weights. -/
theorem Hypotheses.integrable_radialGradient_zeroExtension_mul (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {χ : Space (m + 1) → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) :
    Integrable (fun x ↦ radialGradientDensity (zeroExtension g u) c x * χ x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport χ))).mp
  exact (h.integrableOn_radialGradient_zeroExtension c hc).mul_continuousOn hχ.continuousOn hc

/-- The fixed profile controls the squared radial derivative on its inner half-ball. -/
theorem Hypotheses.radialGradient_halfBall_le_defect (h : Hypotheses g u f κ)
    {r : ℝ} (hr0 : 0 < r) :
    r ^ (-(m : ℤ)) * (3 / r ^ 2 * ∫ x in closedBall 0 (r / 2),
      radialGradientDensity (zeroExtension g u) 0 x) ≤
      radialEnergyDefect g u radialDefectProfile 0 r := by
  let χ := fun x : Space (m + 1) ↦ -2 / r ^ 2 * radialWeight (deriv radialDefectProfile) 0 r x
  have hχ : Continuous χ := continuous_const.mul
    ((radialDefectProfile_contDiff.continuous_deriv le_rfl).comp (show Continuous
      (fun x : Space (m + 1) ↦ ‖x - 0‖ ^ 2 / r ^ 2) by fun_prop))
  have hc : HasCompactSupport χ :=
    (hasCompactSupport_radialWeight_deriv
      (fun _ hs ↦ radialDefectProfile_zero (by linarith)) 0 hr0).mul_left
  have hχ0 (x : Space (m + 1)) : 0 ≤ χ x :=
    mul_nonneg_of_nonpos_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
      radialDefectProfile_antitone.deriv_nonpos
  have hχlower {x : Space (m + 1)} (hx : x ∈ closedBall 0 (r / 2)) : 3 / r ^ 2 ≤ χ x := by
    have hn : ‖x - 0‖ ≤ r / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hratio : ‖x - 0‖ ^ 2 / r ^ 2 ≤ 1 / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
      nlinarith [norm_nonneg (x - 0)]
    have hh := mul_le_mul_of_nonneg_left (radialDefectProfile_neg_deriv_lower hratio)
      (by positivity : 0 ≤ 2 / r ^ 2)
    dsimp only [χ, radialWeight]
    convert hh using 1 <;> ring
  have hiA := h.integrableOn_radialGradient_zeroExtension 0 (isCompact_closedBall 0 (r / 2))
  have hiχ : Integrable (fun x ↦ χ x * radialGradientDensity (zeroExtension g u) 0 x) := by
    simpa only [mul_comm] using h.integrable_radialGradient_zeroExtension_mul 0 hχ hc
  have hle : 3 / r ^ 2 * (∫ x in closedBall 0 (r / 2),
      radialGradientDensity (zeroExtension g u) 0 x) ≤
      ∫ x, χ x * radialGradientDensity (zeroExtension g u) 0 x := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on (hiA.const_mul _) hiχ.integrableOn
      isClosed_closedBall.measurableSet (fun x hx ↦
        mul_le_mul_of_nonneg_right (hχlower hx) (sq_nonneg _))).trans ?_
    exact setIntegral_le_integral hiχ (Eventually.of_forall (fun x ↦
      mul_nonneg (hχ0 x) (sq_nonneg _)))
  have he : radialEnergyDefect g u radialDefectProfile 0 r =
      r ^ (-(m : ℤ)) * ∫ x, χ x * radialGradientDensity (zeroExtension g u) 0 x := by
    unfold radialEnergyDefect
    congr 1
    rw [show (fun x ↦ χ x * radialGradientDensity (zeroExtension g u) 0 x) =
      (fun x ↦ radialGradientDensity (zeroExtension g u) 0 x * χ x) from
        funext (fun _ ↦ mul_comm _ _),
      h.integral_radialGradient_zeroExtension_mul]
    apply setIntegral_congr_fun (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
    intro x _
    dsimp only [χ]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hle (zpow_nonneg hr0.le _)

/-- Radial directional derivatives commute with dilation, including the factor in the direction. -/
theorem radialGradientDensity_dilation {d : ℕ} (U : Space d → ℝ) (R : ℝ) (x : Space d) :
    radialGradientDensity (fun y ↦ U (R • y)) 0 x = radialGradientDensity U 0 (R • x) := by
  simp only [radialGradientDensity, gradient_comp_dilation, sub_zero,
    real_inner_smul_left, real_inner_smul_right]

/-- Change of variables for the radial density on a ball. -/
theorem integral_radialGradientDensity_dilation {d : ℕ} (U : Space d → ℝ)
    {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r, radialGradientDensity (fun y ↦ U (R • y)) 0 x) =
      (R ^ d)⁻¹ * ∫ x in closedBall 0 (R * r), radialGradientDensity U 0 x := by
  simp_rw [radialGradientDensity_dilation]
  rw [Measure.setIntegral_comp_smul_of_pos volume _ _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]

/-- The rescaled radial derivative on a fixed ball is bounded by the defect at twice that radius. -/
theorem Hypotheses.rescaled_radialGradient_le_defect (h : Hypotheses g u f κ)
    {R r : ℝ} (hR : 0 < R) (hr0 : 0 < r) :
    (∫ x in closedBall 0 r,
      radialGradientDensity (fun y ↦ zeroExtension g u (R • y)) 0 x) / R ≤
      (2 * r) ^ (m + 2) / 3 * radialEnergyDefect g u radialDefectProfile 0 (2 * r * R) := by
  have hs : 0 < 2 * r * R := by positivity
  have hb := h.radialGradient_halfBall_le_defect hs
  have hradius : 2 * r * R / 2 = R * r := by ring
  rw [hradius] at hb
  rw [integral_radialGradientDensity_dilation _ hR r]
  have he (I : ℝ) : (2 * r) ^ (m + 2) / 3 *
      ((2 * r * R) ^ (-(m : ℤ)) * (3 / (2 * r * R) ^ 2 * I)) =
      ((R ^ (m + 1))⁻¹ * I) / R := by
    rw [zpow_neg, zpow_natCast]
    simp only [pow_add, mul_pow, pow_one]
    field_simp
  rw [← he]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Vanishing defects at integer multiples control the rescaled radial derivative on every
fixed integer-radius ball, along the same sequence. -/
theorem Hypotheses.rescaled_radialGradient_tendsto_zero (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hD : ∀ k : ℕ, Tendsto (fun j ↦
      radialEnergyDefect g u radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    (k : ℕ) :
    Tendsto (fun j ↦ (∫ x in closedBall 0 (k + 1 : ℝ),
      radialGradientDensity (fun y ↦ zeroExtension g u (R j • y)) 0 x) / R j) atTop (𝓝 0) := by
  have hlim := (hD (2 * k + 1)).const_mul ((2 * (k + 1 : ℝ)) ^ (m + 2) / 3)
  have he : (fun j ↦ (2 * (k + 1 : ℝ)) ^ (m + 2) / 3 *
      radialEnergyDefect g u radialDefectProfile 0 (((2 * k + 1 : ℕ) + 1 : ℝ) * R j)) =
      fun j ↦ (2 * (k + 1 : ℝ)) ^ (m + 2) / 3 *
        radialEnergyDefect g u radialDefectProfile 0 (2 * (k + 1 : ℝ) * R j) := by
    funext j
    congr 2
    push_cast
    ring
  rw [he, mul_zero] at hlim
  apply squeeze_zero (fun j ↦ div_nonneg
    (integral_nonneg (fun x ↦ sq_nonneg _)) (hR j).le) _ hlim
  intro j
  exact h.rescaled_radialGradient_le_defect (hR j) (by positivity)

end SerrinEpigraph
