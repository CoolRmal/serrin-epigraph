module

public import SerrinEpigraph.WeakEquation
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The weak equation for a quotient

The two weak equations are explicit hypotheses. This file does not assume or prove weak
linearization of the nonlinear equation.
-/

public section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- An interior compact test can be multiplied by a coefficient that is only locally `C¹`. -/
theorem contDiff_mul_of_tsupport_subset {c ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hc : ContDiffOn ℝ 1 c Ω) (hψ : ContDiff ℝ 1 ψ)
    (hsub : tsupport ψ ⊆ Ω) : ContDiff ℝ 1 (fun x ↦ c x * ψ x) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ Ω
  · exact (hc.contDiffAt (hΩ.mem_nhds hx)).mul hψ.contDiffAt
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hz := notMem_tsupport_iff_eventuallyEq.1 (fun hx' ↦ hx (hsub hx'))
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, mul_zero]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A continuous local coefficient times an interior compact test is integrable. -/
theorem integrable_mul_of_tsupport_subset {c ψ : E → ℝ} {Ω : Set E}
    (hc : ContinuousOn c Ω) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ Ω) : Integrable (fun x ↦ c x * ψ x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right c ψ).trans (subset_tsupport ψ))).mp
  exact ((hc.mono hsub).mul hψ.continuousOn).integrableOn_compact hψc

omit [MeasurableSpace E] [BorelSpace E] in
private theorem quotient_pairing_identity_at {u v ψ : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hψ : DifferentiableAt ℝ ψ x) (hux : u x ≠ 0) :
    inner ℝ (gradient v x) (gradient (fun y ↦ u y * ψ y) x) -
      inner ℝ (gradient u x) (gradient (fun y ↦ v y * ψ y) x) =
      u x ^ 2 * inner ℝ (gradient (fun y ↦ v y / u y) x) (gradient ψ x) := by
  have hi := (hasDerivAt_inv hux).comp_hasFDerivAt x hu.hasFDerivAt
  have hq := hv.hasFDerivAt.mul hi
  let b := stdOrthonormalBasis ℝ E
  simp_rw [inner_gradient_eq_sum_fderiv b]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_mul hu hψ, fderiv_fun_mul hv hψ]
  have hq' : fderiv ℝ (fun y ↦ v y / u y) x =
      v x • (-(u x ^ 2)⁻¹ • fderiv ℝ u x) + (u x)⁻¹ • fderiv ℝ v x := by
    simpa only [Function.comp_def, Pi.mul_def, div_eq_mul_inv] using hq.fderiv
  rw [hq']
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp
  ring

omit [MeasurableSpace E] [BorelSpace E] in
private theorem quotient_pairing_identity {u v ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hψ : ContDiff ℝ 1 ψ) (hsub : tsupport ψ ⊆ Ω) (hupos : ∀ x ∈ Ω, 0 < u x) (x : E) :
    inner ℝ (gradient v x) (gradient (fun y ↦ u y * ψ y) x) -
      inner ℝ (gradient u x) (gradient (fun y ↦ v y * ψ y) x) =
      u x ^ 2 * inner ℝ (gradient (fun y ↦ v y / u y) x) (gradient ψ x) := by
  by_cases hx : x ∈ Ω
  · exact quotient_pairing_identity_at
      ((hu.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx))
      ((hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx))
      (hψ.differentiable_one x) (hupos x hx).ne'
  · have hz : x ∉ tsupport ψ := fun hx' ↦ hx (hsub hx')
    have hzu : x ∉ tsupport (fun y ↦ u y * ψ y) := fun hx' ↦ hz (tsupport_mul_subset_right hx')
    have hzv : x ∉ tsupport (fun y ↦ v y * ψ y) := fun hx' ↦ hz (tsupport_mul_subset_right hx')
    simp only [gradient, fderiv_of_notMem_tsupport ℝ hz, fderiv_of_notMem_tsupport ℝ hzu,
      fderiv_of_notMem_tsupport ℝ hzv, map_zero, inner_zero_right, sub_self, mul_zero]

/-- The weighted quotient-gradient pairing is integrable for every interior compact test. -/
theorem integrable_sq_mul_inner_gradient_quotient {u v ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω)
    (hupos : ∀ x ∈ Ω, 0 < u x) :
    Integrable
      (fun x ↦ u x ^ 2 * inner ℝ (gradient (fun y ↦ v y / u y) x) (gradient ψ x)) μ := by
  have hA := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ hv
    (contDiff_mul_of_tsupport_subset hΩ hu hψ hsub) hψc.mul_left
    (tsupport_mul_subset_right.trans hsub)
  have hB := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ hu
    (contDiff_mul_of_tsupport_subset hΩ hv hψ hsub) hψc.mul_left
    (tsupport_mul_subset_right.trans hsub)
  exact (hA.sub hB).congr
    (Filter.Eventually.of_forall (quotient_pairing_identity hΩ hu hv hψ hsub hupos))

/-- Subtracting the two weak equations gives the divergence-form weak equation for `v / u`. -/
theorem weak_quotient_identity {u v F a ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hF : ContinuousOn F Ω) (ha : ContinuousOn a Ω) (hupos : ∀ x ∈ Ω, 0 < u x)
    (hwu : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, inner ℝ (gradient u x) (gradient φ x) ∂μ) = ∫ x, F x * φ x ∂μ)
    (hwv : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, inner ℝ (gradient v x) (gradient φ x) ∂μ) = ∫ x, a x * v x * φ x ∂μ)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) :
    (∫ x, u x ^ 2 * inner ℝ (gradient (fun y ↦ v y / u y) x) (gradient ψ x) ∂μ) =
      ∫ x, (a x * u x - F x) * v x * ψ x ∂μ := by
  have htu := contDiff_mul_of_tsupport_subset hΩ hu hψ hsub
  have htv := contDiff_mul_of_tsupport_subset hΩ hv hψ hsub
  have hsu : tsupport (fun x ↦ u x * ψ x) ⊆ Ω := tsupport_mul_subset_right.trans hsub
  have hsv : tsupport (fun x ↦ v x * ψ x) ⊆ Ω := tsupport_mul_subset_right.trans hsub
  have hA := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ hv htu hψc.mul_left hsu
  have hB := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ hu htv hψc.mul_left hsv
  have hAv := integrable_mul_of_tsupport_subset (μ := μ)
    ((ha.mul hv.continuousOn).mul hu.continuousOn) hψ.continuous hψc hsub
  have hBu := integrable_mul_of_tsupport_subset (μ := μ)
    (hF.mul hv.continuousOn) hψ.continuous hψc hsub
  calc
    _ = (∫ x, inner ℝ (gradient v x) (gradient (fun y ↦ u y * ψ y) x) -
        inner ℝ (gradient u x) (gradient (fun y ↦ v y * ψ y) x) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x ↦ (quotient_pairing_identity hΩ hu hv hψ hsub hupos x).symm)
    _ = (∫ x, a x * v x * (u x * ψ x) ∂μ) - ∫ x, F x * (v x * ψ x) ∂μ := by
      rw [integral_sub hA hB, hwv _ htu hψc.mul_left hsu, hwu _ htv hψc.mul_left hsv]
    _ = ∫ x, (a x * u x - F x) * v x * ψ x ∂μ := by
      rw [← integral_sub (by simpa only [Pi.mul_apply, mul_assoc] using hAv)
        (by simpa only [Pi.mul_apply, mul_assoc] using hBu)]
      apply integral_congr_ae
      filter_upwards with x
      ring

end SerrinEpigraph
