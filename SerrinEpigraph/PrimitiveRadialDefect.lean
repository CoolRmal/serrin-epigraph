module

public import SerrinEpigraph.RadialDefectControl
public import SerrinEpigraph.CauchyEnergy

/-!
# Vanishing radial variation of the phase primitives
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- The radial gradient density of a locally Lipschitz function is locally integrable. -/
theorem integrableOn_radialGradient_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (radialGradientDensity v 0) K := by
  have hi := (integrableOn_gradient_sq_of_locallyLipschitz hv hK).mul_continuousOn
    (continuous_id.norm.pow 2).continuousOn hK
  unfold radialGradientDensity
  simp only [sub_zero]
  apply hi.mono'
    (((measurable_gradient v).inner (𝕜 := ℝ) measurable_id).pow_const 2).aestronglyMeasurable
  filter_upwards with x
  simp only [Real.norm_of_nonneg (sq_nonneg _)]
  have hh := sq_le_sq₀ (abs_nonneg (inner ℝ (gradient v x) x))
    (mul_nonneg (norm_nonneg (gradient v x)) (norm_nonneg x))
  simpa only [sq_abs, mul_pow, id_eq, Pi.pow_apply] using
    hh.mpr (abs_real_inner_le_norm (gradient v x) x)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The radial derivative of the primitive factors through the positive-phase potential. -/
theorem RigidityHypotheses.rescaledPrimitive_radial_factorization
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℝ) (x : Space (m + 1)) :
    ‖inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x) x‖ =
      |inner ℝ (gradient (fun y ↦ zeroExtension g u (R • y)) x) x| *
        Real.sqrt (2 * phasePotentialDensity f (zeroExtension g u) (R • x)) := by
  rw [gradient_comp_dilation (fun y ↦ phasePrimitive f (zeroExtension g u y)),
    hr.gradient_phasePrimitive_zeroExtension h, gradient_comp_dilation]
  by_cases hx : R • x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff _).mpr hx
    simp only [phasePotentialDensity, indicator_apply, mem_ofPred_eq, hp, ite_true,
      real_inner_smul_left,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    ring
  · have hp : ¬0 < zeroExtension g u (R • x) := fun hp ↦
      hx ((h.zeroExtension_pos_iff _).mp hp)
    simp [phasePotentialDensity, hp, h.gradient_zeroExtension_of_notMem hx]

/-- The radial variation is bounded by the square root of the radial defect and the uniform
potential-energy bound. -/
theorem RigidityHypotheses.rescaledPrimitive_radial_integral_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 1 ≤ R * r →
      (∫ x in closedBall 0 r,
        ‖inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R • y))) x) x‖) ≤
      Real.sqrt ((∫ x in closedBall 0 r,
        radialGradientDensity (fun y ↦ zeroExtension g u (R • y)) 0 x) / R) *
          Real.sqrt (2 * C * r ^ m) := by
  obtain ⟨C, hC, hbound⟩ := hr.rescaledPotential_bound h
  refine ⟨C, hC, fun R r hR hRr ↦ ?_⟩
  let v := fun y ↦ zeroExtension g u (R • y)
  let P := fun x ↦ phasePotentialDensity f (zeroExtension g u) (R • x)
  have hv : LocallyLipschitz v := h.zeroExtension_locallyLipschitz.comp
    (lipschitzWith_smul R).locallyLipschitz
  have hP0 (x : Space (m + 1)) : 0 ≤ P x := (hr.phasePotential_bounds h _).1
  have hP : IntegrableOn P (closedBall 0 r) := by
    have hc : Continuous (fun x ↦ normalizedPotential f (v x)) :=
      h.normalizedPotential_continuousOn.comp_continuous hv.continuous
        (fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).indicator
      (isOpen_lt continuous_const hv.continuous).measurableSet
  have hA := integrableOn_radialGradient_of_locallyLipschitz hv (isCompact_closedBall 0 r)
  have ha : IntegrableOn (fun x ↦ |inner ℝ (gradient v x) x| ^ 2) (closedBall 0 r) := by
    convert hA using 1
    ext x
    simp [radialGradientDensity]
  have hb : IntegrableOn (fun x ↦ Real.sqrt (2 * P x) ^ 2) (closedBall 0 r) := by
    have he : (fun x ↦ Real.sqrt (2 * P x) ^ 2) = fun x ↦ 2 * P x :=
      funext (fun x ↦ Real.sq_sqrt (mul_nonneg (by norm_num) (hP0 x)))
    rw [he]
    exact hP.const_mul 2
  have hcs := (le_abs_self _).trans (abs_integral_mul_le_sqrt ha hb)
  simp only [sq_abs, Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hP0 _)),
    integral_const_mul] at hcs
  have hA0 : 0 ≤ ∫ x in closedBall 0 r, radialGradientDensity v 0 x :=
    integral_nonneg (fun x ↦ sq_nonneg _)
  calc
    _ = ∫ x in closedBall 0 r, |inner ℝ (gradient v x) x| * Real.sqrt (2 * P x) := by
      apply integral_congr_ae
      exact Eventually.of_forall (hr.rescaledPrimitive_radial_factorization h R)
    _ ≤ Real.sqrt (∫ x in closedBall 0 r, radialGradientDensity v 0 x) *
        Real.sqrt (2 * ∫ x in closedBall 0 r, P x) := by
      simpa only [radialGradientDensity, sub_zero] using hcs
    _ ≤ Real.sqrt (∫ x in closedBall 0 r, radialGradientDensity v 0 x) *
        Real.sqrt (2 * (C * r ^ m / R)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (hbound R r hR hRr) (by norm_num))) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.sqrt_mul hA0, ← Real.sqrt_mul (div_nonneg hA0 hR.le)]
      congr 1
      ring

/-- Vanishing radial energy defects force the radial variation of the rescaled primitives
to vanish on each fixed integer-radius ball. -/
theorem RigidityHypotheses.rescaledPrimitive_radial_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j)
    (hD : ∀ k : ℕ, Tendsto (fun j ↦
      radialEnergyDefect g u radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    (k : ℕ) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
      ‖inner ℝ (gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x) x‖)
        atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := hr.rescaledPrimitive_radial_integral_bound h
  have hR0 (j : ℕ) : 0 < R j := lt_of_lt_of_le zero_lt_one (hR j)
  have ht := ((h.rescaled_radialGradient_tendsto_zero hR0 hD k).sqrt).mul_const
    (Real.sqrt (2 * C * (k + 1 : ℝ) ^ m))
  simp only [Real.sqrt_zero, zero_mul] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
  intro j
  exact hbound (R j) (k + 1) (hR0 j)
    (one_le_mul_of_one_le_of_one_le (hR j) (by linarith [Nat.cast_nonneg (α := ℝ) k]))

end SerrinEpigraph
