module

public import SerrinEpigraph.WeakEquation
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The second derivative test for the Laplacian
-/

public section

open Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- A continuous scalar function at a local minimum has nonnegative second derivative
whenever the total second derivative is evaluated in Lean's derivative convention. -/
theorem second_deriv_nonneg_of_localMin {v : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin v t) (hc : ContinuousAt v t) : 0 ≤ deriv (deriv v) t := by
  by_contra hn
  have hmax := isLocalMax_of_deriv_deriv_neg (lt_of_not_ge hn) hmin.deriv_eq_zero hc
  have heq : v =ᶠ[𝓝 t] (fun _ ↦ v t) := by
    filter_upwards [hmin, hmax] with s hs₁ hs₂
    exact le_antisymm hs₂ hs₁
  have hz : deriv (deriv v) t = 0 := by simpa using heq.deriv.deriv_eq
  exact hn (by rw [hz])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At an interior local minimum, every repeated directional derivative is nonnegative. -/
theorem second_directional_nonneg_of_localMin {u : E → ℝ} {Ω : Set E} {x : E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hx : x ∈ Ω)
    (hmin : IsLocalMin u x) (v : E) :
    0 ≤ fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v := by
  let γ : ℝ → E := fun t ↦ x + t • v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const v).const_add x
  have hγzero : γ 0 = x := by simp [γ]
  have hstay : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ Ω :=
    (hγ 0).continuousAt (by simpa [hγzero] using hΩ.mem_nhds hx)
  have hfirst : deriv (fun t ↦ u (γ t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ fderiv ℝ u (γ t) v) := by
    filter_upwards [hstay] with t ht
    have hd := (hu.differentiableOn (by norm_num) (γ t) ht).differentiableAt (hΩ.mem_nhds ht)
    exact (hd.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hdu : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y v) Ω :=
    (hu.fderiv_of_isOpen hΩ (by norm_num)).clm_apply contDiffOn_const
  have hd := (hdu.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
  have hdx : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y v) (γ 0) := by
    simpa only [hγzero] using hd
  have hsecond : deriv (fun t ↦ fderiv ℝ u (γ t) v) 0 =
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v := by
    simpa only [hγzero, Function.comp_def] using (hdx.hasFDerivAt.comp_hasDerivAt 0 (hγ 0)).deriv
  have hminline : IsLocalMin (fun t ↦ u (γ t)) 0 := by
    have hm : IsLocalMin u (γ 0) := by simpa only [hγzero] using hmin
    exact hm.comp_continuous (hγ 0).continuousAt
  have hcline : ContinuousAt (fun t ↦ u (γ t)) 0 :=
    (hu.continuousOn.continuousAt (hΩ.mem_nhds (by simpa only [hγzero] using hx))).comp
      (hγ 0).continuousAt
  have hn := second_deriv_nonneg_of_localMin hminline hcline
  rwa [hfirst.deriv_eq, hsecond] at hn

variable [FiniteDimensional ℝ E]

/-- The Laplacian is nonnegative at an interior local minimum of a C² function. -/
theorem laplacian_nonneg_of_localMin {u : E → ℝ} {Ω : Set E} {x : E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hx : x ∈ Ω)
    (hmin : IsLocalMin u x) : 0 ≤ (Δ u) x := by
  let b := stdOrthonormalBasis ℝ E
  have hdw := (hu.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).differentiableOn_one x hx
  have hd := hdw.differentiableAt (hΩ.mem_nhds hx)
  rw [laplacian_eq_sum_fderiv b hd]
  exact Finset.sum_nonneg (fun i _ ↦ second_directional_nonneg_of_localMin hΩ hu hx hmin (b i))

/-- A positive supersolution cannot touch a scaled comparison function from above where its
reaction coefficient strictly exceeds the comparison function's coefficient. -/
theorem not_localMin_at_positive_contact {u ψ : E → ℝ} {Ω : Set E} {x : E}
    {c ℓ τ : ℝ} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hψ : ContDiffOn ℝ 2 ψ Ω) (hx : x ∈ Ω) (hτ : 0 < τ) (hgap : ℓ < c)
    (hupos : 0 < u x) (hcontact : u x = τ * ψ x)
    (huineq : c * u x ≤ -(Δ u) x) (hψineq : -(Δ ψ) x ≤ ℓ * ψ x) :
    ¬ IsLocalMin (fun y ↦ u y - τ * ψ y) x := by
  intro hmin
  have hnonneg := laplacian_nonneg_of_localMin hΩ (hu.sub (contDiffOn_const.mul hψ)) hx hmin
  have hua : ContDiffAt ℝ 2 u x := (hu x hx).contDiffAt (hΩ.mem_nhds hx)
  have hψa : ContDiffAt ℝ 2 ψ x := (hψ x hx).contDiffAt (hΩ.mem_nhds hx)
  have hlap : (Δ (fun y ↦ u y - τ * ψ y)) x = (Δ u) x - τ * (Δ ψ) x := by
    change (Δ (u - τ • ψ)) x = _
    have hscale : ContDiffAt ℝ 2 (τ • ψ) x := by
      change ContDiffAt ℝ 2 (fun y ↦ τ * ψ y) x
      exact contDiffAt_const.mul hψa
    rw [hua.laplacian_sub hscale, laplacian_smul τ hψa]
    rfl
  rw [hlap] at hnonneg
  have hb := mul_le_mul_of_nonneg_left hψineq hτ.le
  have hstrict := mul_pos (sub_pos.mpr hgap) hupos
  rw [hcontact] at huineq hstrict
  nlinarith

end SerrinEpigraph
