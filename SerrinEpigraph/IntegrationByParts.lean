module

public import SerrinEpigraph.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Tactic

/-!
# Compactly supported integration by parts

The coefficient needs to be continuously differentiable only on an open neighborhood of the
test function's topological support. In particular, no extension of a PDE solution beyond its
domain is required.
-/

public section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_of_support_subset_compact {F : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hsub : Function.support F ⊆ K) :
    Integrable F μ :=
  (integrableOn_iff_integrable_of_support_subset hsub).mp (hF.integrableOn_compact hK)

/-- Directional integration by parts with a compactly supported test function and a coefficient
that is `C¹` on a neighborhood of its support. -/
theorem integral_mul_fderiv_eq_neg_of_hasCompactSupport {u ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) (v : E) :
    (∫ x, u x * fderiv ℝ ψ x v ∂μ) = -∫ x, fderiv ℝ u x v * ψ x ∂μ := by
  have hu0 := hu.continuousOn.mono hsub
  have hu1 := (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub
  have hψ1 : Continuous (fun x ↦ fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · apply integrable_of_support_subset_compact hψc
      ((hu1.clm_apply continuousOn_const).mul hψ.continuous.continuousOn)
    exact (Function.support_mul_subset_right _ _).trans (subset_tsupport ψ)
  · apply integrable_of_support_subset_compact hψc (hu0.mul hψ1.continuousOn)
    exact (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v))
  · apply integrable_of_support_subset_compact hψc (hu0.mul hψ.continuous.continuousOn)
    exact (Function.support_mul_subset_right _ _).trans (subset_tsupport ψ)
  · exact fun x hx ↦ (hu.differentiableOn_one x (hsub hx)).differentiableAt
      (hΩ.mem_nhds (hsub hx))
  · exact fun x _ ↦ hψ.differentiable_one x

/-- The weighted vertical integration-by-parts identity, valid in any fixed direction. -/
theorem integral_sq_mul_mul_fderiv_eq_neg {u ψ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) (v : E) :
    (∫ x, u x ^ 2 * ψ x * fderiv ℝ ψ x v ∂μ) =
      -∫ x, u x * fderiv ℝ u x v * ψ x ^ 2 ∂μ := by
  have hsquare : tsupport (fun x ↦ ψ x ^ 2) ⊆ tsupport ψ := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := ψ) (g := ψ))
  have hc : HasCompactSupport (fun x ↦ ψ x ^ 2) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) hsquare
  have h := integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := μ) hΩ (hu.pow 2)
    (hψ.pow 2) hc (hsquare.trans hsub) v
  have hleft : ∀ x, u x ^ 2 * fderiv ℝ (fun y ↦ ψ y ^ 2) x v =
      2 * (u x ^ 2 * ψ x * fderiv ℝ ψ x v) := by
    intro x
    rw [fderiv_fun_pow 2 (hψ.differentiable_one x)]
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, nsmul_eq_mul,
      smul_apply, smul_eq_mul]
    ring
  have hright : ∀ x, fderiv ℝ (fun y ↦ u y ^ 2) x v * ψ x ^ 2 =
      2 * (u x * fderiv ℝ u x v * ψ x ^ 2) := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [fderiv_fun_pow 2 ((hu.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx))]
      simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, nsmul_eq_mul,
        smul_apply, smul_eq_mul]
      ring
    · have hz : ψ x = 0 := Function.notMem_support.mp
        (fun hx' ↦ hx (hsub (subset_tsupport ψ hx')))
      simp [hz]
  simp_rw [hleft, hright, integral_const_mul] at h
  linarith

/-- The preceding identity for the ambient vertical derivative used in the epigraph problem. -/
theorem integral_sq_mul_mul_verticalDerivative_eq_neg {m : ℕ}
    {u ψ : Space (m + 1) → ℝ} {Ω : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) :
    (∫ x, u x ^ 2 * ψ x * verticalDerivative ψ x) =
      -∫ x, u x * verticalDerivative u x * ψ x ^ 2 :=
  integral_sq_mul_mul_fderiv_eq_neg hΩ hu hψ hψc hsub (verticalDirection m)

end SerrinEpigraph
