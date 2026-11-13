module

public import SerrinEpigraph.ScaledRadialWeight
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Exact scale derivative of the radially weighted phase energy
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace

namespace SerrinEpigraph

/-- A continuous coefficient on a closed domain is integrable after multiplication
by a continuous compactly supported test and restriction to the domain. -/
theorem integrableOn_mul_of_continuousOn_closure {d : ℕ} {Ω : Set (Space d)}
    (hΩ : MeasurableSet Ω) {A χ : Space d → ℝ} (hA : ContinuousOn A (closure Ω))
    (hχ : Continuous χ) (hc : HasCompactSupport χ) : IntegrableOn (fun x ↦ A x * χ x) Ω := by
  let K := tsupport χ ∩ closure Ω
  have hK : IsCompact K := hc.inter_right isClosed_closure
  have hi : IntegrableOn (fun x ↦ A x * χ x) K :=
    ((hA.mul hχ.continuousOn).mono inter_subset_right).integrableOn_compact hK
  have hi' : IntegrableOn (Ω.indicator (fun x ↦ A x * χ x)) K := hi.indicator hΩ
  apply (integrable_indicator_iff hΩ).mp
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp hi'
  intro x hx
  have hxΩ : x ∈ Ω := by
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  refine ⟨?_, subset_closure hxΩ⟩
  by_contra hn
  exact hx (by rw [indicator_of_mem hxΩ, image_eq_zero_of_notMem_tsupport hn, mul_zero])

/-- The derivative profile also has compact radial support. -/
theorem hasCompactSupport_radialWeight_deriv {d : ℕ} {q : ℝ → ℝ}
    (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0) (c : Space d) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialWeight (deriv q) c R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c (2 * R))
  intro x hx
  by_contra hn
  have hdist : 2 * R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
  have hratio : 2 < ‖x - c‖ ^ 2 / R ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [norm_nonneg (x - c)]
  exact hx (deriv_eq_zero_of_zero_above hzero hratio)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Weighted whole-space phase energy equals its interior integral. -/
theorem Hypotheses.integral_phaseEnergy_mul (h : Hypotheses g u f κ)
    (χ : Space (m + 1) → ℝ) :
    (∫ x, phaseEnergyDensity f 0 (zeroExtension g u) x * χ x) =
      ∫ x in epigraph g, (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * χ x := by
  have he : (fun x ↦ phaseEnergyDensity f 0 (zeroExtension g u) x * χ x) =
      (epigraph g).indicator (fun x ↦
        (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * χ x) := by
    funext x
    rw [h.phaseEnergyDensity_zeroExtension]
    by_cases hx : x ∈ epigraph g
    · simp only [indicator_of_mem hx, add_zero, h.closed_gradient_eq hx]
    · simp only [indicator_of_notMem hx, zero_mul]
  rw [he, integral_indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]

/-- Interior energy times any continuous compact test is integrable. -/
theorem RigidityHypotheses.integrableOn_energy_mul
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    IntegrableOn (fun x ↦ (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * χ x)
      (epigraph g) := by
  have hW := h.normalizedPotential_continuousOn.comp
    h.solution_contDiffOn_closure.continuousOn (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
  have hA : ContinuousOn (fun x ↦
      ‖gradientWithin u (closure (epigraph g)) x‖ ^ 2 / 2 + normalizedPotential f (u x))
      (closure (epigraph g)) :=
    ((h.closed_gradient_continuousOn.norm.pow 2).div_const 2).add hW
  apply (integrableOn_mul_of_continuousOn_closure
    (isOpen_epigraph h.graph_contDiff.continuous).measurableSet hA hχ hc).congr_fun _
      (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  intro x hx
  dsimp only
  rw [h.closed_gradient_eq hx]

/-- The exact scale derivative retains the discrepancy term; no gradient estimate
is assumed in this identity. The integer exponent permits both surface and Dirichlet scaling. -/
theorem RigidityHypotheses.radial_energy_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (c : Space (m + 1)) (a : ℤ) {R : ℝ} (hR : 0 < R) :
    HasDerivAt (fun r ↦ r ^ a * ∫ x in epigraph g,
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * radialWeight q c r x)
      (R ^ (a - 1) * ∫ x in epigraph g,
        (((a : ℝ) + m - 1) / 2 * ‖gradient u x‖ ^ 2 +
          ((a : ℝ) + m + 1) * normalizedPotential f (u x)) * radialWeight q c R x -
        2 / R ^ 2 * radialWeight (deriv q) c R x *
          (inner ℝ (gradient u x) (x - c)) ^ 2) R := by
  let E := fun x ↦ ‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)
  let φ := radialWeight q c R
  let ψ := radialWeightScaleDerivative q c R
  let J := fun x ↦
    (((a : ℝ) + m - 1) / 2 * ‖gradient u x‖ ^ 2 +
      ((a : ℝ) + m + 1) * normalizedPotential f (u x)) * φ x -
    2 / R ^ 2 * radialWeight (deriv q) c R x * (inner ℝ (gradient u x) (x - c)) ^ 2
  have hφ : ContDiff ℝ 1 φ := contDiff_radialWeight hq c R
  have hφc : HasCompactSupport φ := (isCompact_closedBall c (2 * R)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_radialWeight_subset hzero c hR)
  have hψ : Continuous ψ := by
    have hn : Continuous (fun x : Space (m + 1) ↦ ‖x - c‖ ^ 2) := by fun_prop
    exact ((continuous_const.mul hn).div_const (R ^ 3)).mul
      ((hq.continuous_deriv le_rfl).comp (hn.div_const (R ^ 2)))
  have hψc : HasCompactSupport ψ := (isCompact_closedBall c (2 * R)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_radialWeightScaleDerivative_subset hzero c hR)
  have hiφ : IntegrableOn (fun x ↦ E x * φ x) (epigraph g) :=
    hr.integrableOn_energy_mul h hφ.continuous hφc
  have hiψ : IntegrableOn (fun x ↦ E x * ψ x) (epigraph g) :=
    hr.integrableOn_energy_mul h hψ hψc
  have hiJ : IntegrableOn J (epigraph g) := by
    have hp := h.closed_gradient_continuousOn
    have hW := h.normalizedPotential_continuousOn.comp
      h.solution_contDiffOn_closure.continuousOn (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
    have hA : ContinuousOn (fun x ↦ ((a : ℝ) + m - 1) / 2 *
        ‖gradientWithin u (closure (epigraph g)) x‖ ^ 2 +
        ((a : ℝ) + m + 1) * normalizedPotential f (u x)) (closure (epigraph g)) :=
      (continuousOn_const.mul (hp.norm.pow 2)).add (continuousOn_const.mul hW)
    have hB : ContinuousOn (fun x ↦ 2 / R ^ 2 *
        (inner ℝ (gradientWithin u (closure (epigraph g)) x) (x - c)) ^ 2)
        (closure (epigraph g)) :=
      continuousOn_const.mul ((hp.inner (continuous_id.sub continuous_const).continuousOn).pow 2)
    have hq' : Continuous (radialWeight (deriv q) c R) :=
      (hq.continuous_deriv le_rfl).comp (show Continuous
        (fun x : Space (m + 1) ↦ ‖x - c‖ ^ 2 / R ^ 2) by fun_prop)
    have hiA := integrableOn_mul_of_continuousOn_closure
      (isOpen_epigraph h.graph_contDiff.continuous).measurableSet hA hφ.continuous hφc
    have hiB := integrableOn_mul_of_continuousOn_closure
      (isOpen_epigraph h.graph_contDiff.continuous).measurableSet hB hq'
      (hasCompactSupport_radialWeight_deriv hzero c hR)
    apply (hiA.sub hiB).congr_fun _ (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
    intro x hx
    dsimp only [J, Pi.sub_apply]
    rw [h.closed_gradient_eq hx]
    ring
  have hstation : (∫ x in epigraph g,
      J x - (a : ℝ) * (E x * φ x) - R * (E x * ψ x)) = 0 := by
    rw [← hr.integral_dilation_stationarity h basis hφ hφc c]
    apply setIntegral_congr_fun (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
    intro x _
    dsimp only [J, E, φ, ψ]
    rw [fderiv_radialWeight hq.differentiable_one,
      fderiv_radialWeight hq.differentiable_one]
    simp only [radialWeight, radialWeightScaleDerivative, real_inner_self_eq_norm_sq,
      real_inner_comm (gradient u x) (x - c)]
    field_simp
    ring
  have hiSub : IntegrableOn (fun x ↦ J x - (a : ℝ) * (E x * φ x)) (epigraph g) :=
    hiJ.sub (hiφ.const_mul (a : ℝ))
  rw [integral_sub hiSub (hiψ.const_mul R), integral_sub hiJ (hiφ.const_mul (a : ℝ)),
    integral_const_mul, integral_const_mul] at hstation
  have hd := hasDerivAt_integral_mul_radialWeight hq hzero c hR
    (w := phaseEnergyDensity f 0 (zeroExtension g u))
    (fun _ hK ↦ hr.integrableOn_phaseEnergy_zeroExtension h 0 hK)
  simp only [h.integral_phaseEnergy_mul] at hd
  have hprod := (hasDerivAt_zpow a R (Or.inl hR.ne')).mul hd
  convert hprod using 1
  have hp : R ^ a = R ^ (a - 1) * R := by
    calc
      R ^ a = R ^ ((a - 1) + 1) := by congr 1; omega
      _ = R ^ (a - 1) * R := by rw [zpow_add₀ hR.ne', zpow_one]
  rw [hp]
  change R ^ (a - 1) * (∫ x in epigraph g, J x) = _
  have hstation' : (∫ x in epigraph g, J x) =
      (a : ℝ) * (∫ x in epigraph g, E x * φ x) + R * (∫ x in epigraph g, E x * ψ x) := by
    linarith
  rw [hstation']
  dsimp only [E, φ, ψ]
  ring

end SerrinEpigraph
