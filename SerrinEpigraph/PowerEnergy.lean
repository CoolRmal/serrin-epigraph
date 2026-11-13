module

public import SerrinEpigraph.GradientPowerTests
public import SerrinEpigraph.QuotientTests
public import SerrinEpigraph.WeakQuotient
public import SerrinEpigraph.WeakLinearization
public import SerrinEpigraph.PowerIntegrability

/-!
# Energy of quotient powers

The linearized equation and the reaction inequality give the favorable sign of the quotient
test. The power-test identity then bounds its weighted gradient energy by the cutoff error.
-/

public section

open MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- On an open set the gradient of the zero extension agrees with the original gradient. -/
theorem gradient_indicator_of_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Ω : Set E} {φ : E → ℝ}
    (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω) :
    gradient (Ω.indicator φ) x = gradient φ x := by
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [hΩ.mem_nhds hx] with y hy
  exact Set.indicator_of_mem hy φ

/-- A locally continuous weight times the energy of an interior compact test is integrable. -/
theorem integrable_weight_mul_norm_gradient_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E} {w φ : E → ℝ}
    (hw : ContinuousOn w Ω) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) : Integrable (fun x ↦ w x * ‖gradient φ x‖ ^ 2) μ := by
  have hgrad : Continuous (gradient φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hsupp : Function.support (fun x ↦ w x * ‖gradient φ x‖ ^ 2) ⊆ tsupport φ := by
    intro x hx
    by_contra hx'
    apply hx
    simp [gradient, fderiv_of_notMem_tsupport ℝ hx']
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (((hw.mono hs).mul (hgrad.norm.pow 2).continuousOn).integrableOn_compact hc)

/-- The sign forced by the reaction structure for every compact quotient test. -/
theorem Hypotheses.negativeRatio_test_nonpos (h : Hypotheses g u f κ)
    {ψ : Space (m + 1) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ epigraph g)
    (hsign : ∀ x ∈ epigraph g, verticalDerivative u x * ψ x ≤ 0) :
    (∫ x, u x ^ 2 * inner ℝ (gradient (fun y ↦ -verticalDerivative u y / u y) x)
      (gradient ψ x)) ≤ 0 := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hv : ContDiffOn ℝ 1 (verticalDerivative u) (epigraph g) :=
    (h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply
      contDiffOn_const
  have hF : ContinuousOn (fun x ↦ f (u x)) (epigraph g) :=
    h.reaction_contDiffOn.continuousOn.comp hu.continuousOn (fun x hx ↦ (h.positive x hx).le)
  have ha : ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) :=
    ((h.reaction_contDiffOn.mono Set.Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp hu.continuousOn (fun x hx ↦ h.positive x hx)
  have heq := weak_quotient_identity hΩ hu hv hF ha h.positive
    (fun φ hφ hc hs ↦ h.weak_equation hφ hc hs)
    (fun φ hφ hc hs ↦ h.weak_vertical_equation hφ hc hs) hψ hψc hsub
  have hnonneg : 0 ≤ ∫ x, (deriv f (u x) * u x - f (u x)) * verticalDerivative u x * ψ x := by
    apply integral_nonneg
    intro x
    change (0 : ℝ) ≤ _
    by_cases hx : x ∈ epigraph g
    · have hcoef : deriv f (u x) * u x - f (u x) ≤ 0 := by
        nlinarith [h.reaction_structure (u x) (h.positive x hx)]
      simpa only [mul_assoc] using mul_nonneg_of_nonpos_of_nonpos hcoef (hsign x hx)
    · have hz : ψ x = 0 := Function.notMem_support.mp fun hy ↦ hx (hsub (subset_tsupport ψ hy))
      simp [hz]
  have hgrad (x : Space (m + 1)) :
      gradient (fun y ↦ -verticalDerivative u y / u y) x =
        -gradient (fun y ↦ verticalDerivative u y / u y) x := by
    simp only [neg_div, gradient, fderiv_fun_neg, map_neg]
  simp_rw [hgrad, inner_neg_left, mul_neg, integral_neg]
  linarith

/-- Positive quotient powers multiplied by a square give a nonpositive quotient test. -/
theorem Hypotheses.negativeRatio_power_test_nonpos (h : Hypotheses g u f κ)
    (n : ℕ) {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) :
    (∫ x, u x ^ 2 * inner ℝ (gradient (fun y ↦ -verticalDerivative u y / u y) x)
      (gradient ((epigraph g).indicator
        (fun y ↦ negativeQuotient u y ^ (2 * n + 3) * η y ^ 2)) x)) ≤ 0 := by
  have hη2 : ContDiff ℝ 1 (fun x ↦ η x ^ 2) := hη.pow 2
  have hc2 : HasCompactSupport (fun x ↦ η x ^ 2) :=
    hηc.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  obtain ⟨hc, hs⟩ := hasCompactSupport_indicator_negativeQuotient_pow_mul h
    (k := 2 * n + 3) (by omega) hc2
  apply h.negativeRatio_test_nonpos
    (contDiff_indicator_negativeQuotient_pow_mul h (by omega) hη2 hc2) hc hs
  intro x hx
  rw [Set.indicator_of_mem hx]
  rw [← mul_assoc, verticalDerivative_mul_negativeQuotient_pow (h.positive x hx) (by omega)]
  have hz := negativeQuotient_nonneg u x
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (h.positive x hx).le) (pow_nonneg hz _))
    (sq_nonneg _)

/-- Integrating the power identity converts the signed weak test into a gradient estimate. -/
theorem Hypotheses.power_energy_of_integrable_cutoff_error (h : Hypotheses g u f κ)
    (n : ℕ) {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η)
    (hE : Integrable ((epigraph g).indicator
      (fun x ↦ u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) * ‖gradient η x‖ ^ 2))) :
    (∫ x, u x ^ 2 * ‖gradient ((epigraph g).indicator
        (fun y ↦ negativeQuotient u y ^ (n + 2) * η y)) x‖ ^ 2) ≤
      ∫ x in epigraph g, u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) *
        ‖gradient η x‖ ^ 2 := by
  let Ψ := (epigraph g).indicator (fun y ↦ negativeQuotient u y ^ (n + 2) * η y)
  let φ := (epigraph g).indicator (fun y ↦ negativeQuotient u y ^ (2 * n + 3) * η y ^ 2)
  let Q := fun x ↦ u x ^ 2 * inner ℝ
    (gradient (fun y ↦ -verticalDerivative u y / u y) x) (gradient φ x)
  let E := (epigraph g).indicator
    (fun x ↦ u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) * ‖gradient η x‖ ^ 2)
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hη2 : ContDiff ℝ 1 (fun x ↦ η x ^ 2) := hη.pow 2
  have hc2 : HasCompactSupport (fun x ↦ η x ^ 2) :=
    hηc.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  obtain ⟨hΨc, hΨs⟩ := hasCompactSupport_indicator_negativeQuotient_pow_mul h
    (k := n + 2) (by omega) hηc
  obtain ⟨hφc, hφs⟩ := hasCompactSupport_indicator_negativeQuotient_pow_mul h
    (k := 2 * n + 3) (by omega) hc2
  have hΨ : ContDiff ℝ 1 Ψ := contDiff_indicator_negativeQuotient_pow_mul h (by omega) hη hηc
  have hφ : ContDiff ℝ 1 φ := contDiff_indicator_negativeQuotient_pow_mul h (by omega) hη2 hc2
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hv : ContDiffOn ℝ 1 (verticalDerivative u) (epigraph g) :=
    (h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply
      contDiffOn_const
  have hG := integrable_weight_mul_norm_gradient_sq (μ := volume)
    (hu.continuousOn.pow 2) hΨ hΨc hΨs
  have hQ : Integrable Q := integrable_sq_mul_inner_gradient_quotient hΩ hu hv.neg
    hφ hφc hφs h.positive
  have hQsign : (∫ x, Q x) ≤ 0 := h.negativeRatio_power_test_nonpos n hη hηc
  have hpoint (x : Space (m + 1)) :
      u x ^ 2 * ‖gradient Ψ x‖ ^ 2 ≤ ((n : ℝ) + 2) * Q x + E x := by
    by_cases hx : x ∈ epigraph g
    · have ht := ((contDiffOn_negativeVerticalRatio h).differentiableOn_one x hx).differentiableAt
        (hΩ.mem_nhds hx)
      have hid := gradient_power_test_identity n ht (hη.differentiable_one x)
      have hrem : 0 ≤ ((n : ℝ) + 2) * (n + 1) *
          negativeQuotient u x ^ (2 * n + 2) * η x ^ 2 *
            ‖gradient (fun y ↦ -verticalDerivative u y / u y) x‖ ^ 2 := by
        have hz := negativeQuotient_nonneg u x
        positivity
      dsimp only [Ψ, Q, φ, E]
      rw [gradient_indicator_of_mem hΩ hx, gradient_indicator_of_mem hΩ hx,
        Set.indicator_of_mem hx]
      have hi : ‖gradient (fun y ↦ negativeQuotient u y ^ (n + 2) * η y) x‖ ^ 2 ≤
          ((n : ℝ) + 2) * inner ℝ (gradient (fun y ↦ -verticalDerivative u y / u y) x)
            (gradient (fun y ↦ negativeQuotient u y ^ (2 * n + 3) * η y ^ 2) x) +
              negativeQuotient u x ^ (2 * n + 4) * ‖gradient η x‖ ^ 2 := by
        simp only [negativeQuotient] at hrem ⊢
        linarith [hid]
      have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg (u x))
      nlinarith
    · have hxΨ : x ∉ tsupport Ψ := fun hy ↦ hx (hΨs hy)
      have hxφ : x ∉ tsupport φ := fun hy ↦ hx (hφs hy)
      simp [Q, E, gradient, fderiv_of_notMem_tsupport ℝ hxΨ,
        fderiv_of_notMem_tsupport ℝ hxφ, Set.indicator_of_notMem hx]
  have hbound := integral_mono hG ((hQ.const_mul ((n : ℝ) + 2)).add hE) hpoint
  simp only [Pi.add_apply, Pi.pow_apply] at hbound
  rw [integral_add (hQ.const_mul _) hE, integral_const_mul] at hbound
  have hlast : ((n : ℝ) + 2) * (∫ x, Q x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hQsign
  have hfinal : (∫ x, u x ^ 2 * ‖gradient Ψ x‖ ^ 2) ≤ ∫ x, E x := by linarith
  simpa only [E, integral_indicator hΩ.measurableSet] using hfinal

/-- The actual weighted energy estimate for every compactly supported `C¹` cutoff. -/
theorem Hypotheses.power_energy (h : Hypotheses g u f κ)
    (n : ℕ) {η : Space (m + 1) → ℝ} (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) :
    (∫ x, u x ^ 2 * ‖gradient ((epigraph g).indicator
        (fun y ↦ negativeQuotient u y ^ (n + 2) * η y)) x‖ ^ 2) ≤
      ∫ x in epigraph g, u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) *
        ‖gradient η x‖ ^ 2 :=
  h.power_energy_of_integrable_cutoff_error n hη hηc
    (integrable_indicator_power_gradient_error h (by omega) hη hηc)

end SerrinEpigraph
