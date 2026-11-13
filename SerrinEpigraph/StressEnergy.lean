module

public import SerrinEpigraph.FoliationEquation
public import SerrinEpigraph.GraphDivergence
public import SerrinEpigraph.AnnularSlopeComparison
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Stress energy of the Serrin solution
-/

public section

noncomputable section

open InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

/-- The energy stress tensor applied to a spatial variation vector. -/
@[expose] def stressVector {d : ℕ} (V : ℝ) (p ξ : Space d) : Space d :=
  (‖p‖ ^ 2 / 2 + V) • ξ - inner ℝ p ξ • p

/-- The stress flux associated with a spatial test field. -/
@[expose] def solutionStress {d : ℕ} (u : Space d → ℝ) (f : ℝ → ℝ)
    (X : Space d → Space d) (x : Space d) : Space d :=
  stressVector (normalizedPotential f (u x)) (gradient u x) (X x)

/-- Expanding a linear functional in an orthonormal basis. -/
theorem sum_inner_mul_linear {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (L : Space d →L[ℝ] ℝ) (v : Space d) :
    (∑ i, inner ℝ (b i) v * L (b i)) = L v := by
  have he := congrArg L (b.sum_repr' v)
  simpa only [map_sum, map_smul, smul_eq_mul] using he

/-- Product differentiation of the energy stress flux, before using a field equation. -/
theorem fieldDivergence_energy_flux {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {e : Space d → ℝ}
    {p X : Space d → Space d} {x : Space d}
    (he : DifferentiableAt ℝ e x) (hp : DifferentiableAt ℝ p x)
    (hX : DifferentiableAt ℝ X x) :
    fieldDivergence b (fun y ↦ e y • X y - inner ℝ (p y) (X y) • p y) x =
      e x * fieldDivergence b X x + fderiv ℝ e x (X x) -
        inner ℝ (p x) (fderiv ℝ X x (p x)) -
        inner ℝ (fderiv ℝ p x (p x)) (X x) -
        inner ℝ (p x) (X x) * fieldDivergence b p x := by
  have hd := (he.hasFDerivAt.smul hX.hasFDerivAt).sub
    ((hp.hasFDerivAt.inner ℝ hX.hasFDerivAt).smul hp.hasFDerivAt)
  change HasFDerivAt (fun y ↦ e y • X y - inner ℝ (p y) (X y) • p y) _ x at hd
  have hdv (v : Space d) := congrArg (fun L : Space d →L[ℝ] Space d ↦ L v) hd.fderiv
  have hsumE := sum_inner_mul_linear b (fderiv ℝ e x) (X x)
  have hsumX := sum_inner_mul_linear b ((innerSL ℝ (p x)).comp (fderiv ℝ X x)) (p x)
  have hsumP := sum_inner_mul_linear b ((innerSL ℝ (X x)).comp (fderiv ℝ p x)) (p x)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hsumX hsumP
  unfold fieldDivergence
  simp_rw [hdv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, inner_sub_right, inner_add_right, real_inner_smul_right,
    add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  simp_rw [mul_comm (fderiv ℝ e x _),
    mul_comm (inner ℝ (p x) (fderiv ℝ X x _)),
    mul_comm (inner ℝ (fderiv ℝ p x _) (X x)),
    real_inner_comm (X x) (fderiv ℝ p x _)]
  rw [hsumE, hsumX, hsumP]
  ring

/-- The Hessian expressed through the gradient is symmetric. -/
theorem gradient_derivative_inner_symm {d : ℕ} {u : Space d → ℝ} {x : Space d}
    (hu : ContDiffAt ℝ 2 u x) (a b : Space d) :
    inner ℝ (fderiv ℝ (gradient u) x a) b =
      inner ℝ (fderiv ℝ (gradient u) x b) a := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space d)).symm.contDiff.contDiffAt.comp x hd).differentiableAt
      (by norm_num)
  have hR := (toDual ℝ (Space d)).toContinuousLinearMap.hasFDerivAt.comp x hg.hasFDerivAt
  have hR' : HasFDerivAt (fderiv ℝ u)
      ((toDual ℝ (Space d)).toContinuousLinearMap.comp (fderiv ℝ (gradient u) x)) x := by
    change HasFDerivAt ((toDual ℝ (Space d)) ∘ gradient u) _ x at hR
    simpa only [toDual_comp_gradient] using hR
  have hpair (v w : Space d) :
      fderiv ℝ (fderiv ℝ u) x v w = inner ℝ (fderiv ℝ (gradient u) x v) w := by
    rw [hR'.fderiv]
    rfl
  rw [← hpair, ← hpair]
  exact (hu.isSymmSndFDerivAt (by norm_num)).eq a b

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The PDE cancels the reaction term in the interior stress divergence. -/
theorem Hypotheses.solutionStress_divergence (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {X : Space (m + 1) → Space (m + 1)} {x : Space (m + 1)}
    (hx : x ∈ epigraph g) (hX : DifferentiableAt ℝ X x) :
    fieldDivergence b (solutionStress u f X) x =
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * fieldDivergence b X x -
        inner ℝ (gradient u x) (fderiv ℝ X x (gradient u x)) := by
  have hu : ContDiffAt ℝ 2 u x := h.solution_contDiffOn.contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp x hd).differentiableAt
      (by norm_num)
  have hW := (h.normalizedPotential_hasDerivAt (h.positive x hx)).comp_hasFDerivAt x
    (hu.differentiableAt (by norm_num)).hasFDerivAt
  have he := ((hg.hasFDerivAt.norm_sq).smul_const (1 / 2 : ℝ)).add hW
  change HasFDerivAt (fun y ↦ ‖gradient u y‖ ^ 2 * (1 / 2) +
    normalizedPotential f (u y)) _ x at he
  simp only [one_div, ← div_eq_mul_inv] at he
  have he' : DifferentiableAt ℝ
      (fun y ↦ ‖gradient u y‖ ^ 2 / 2 + normalizedPotential f (u y)) x := by
    exact he.differentiableAt
  have heval : fderiv ℝ (fun y ↦ ‖gradient u y‖ ^ 2 / 2 +
      normalizedPotential f (u y)) x (X x) =
        inner ℝ (gradient u x) (fderiv ℝ (gradient u) x (X x)) -
          f (u x) * inner ℝ (gradient u x) (X x) := by
    have hh := congrArg (fun L : Space (m + 1) →L[ℝ] ℝ ↦ L (X x)) he.fderiv
    rw [hh]
    simp [ContinuousLinearMap.comp_apply, inner_gradient_left]
    ring
  have hlap : fieldDivergence b (gradient u) x = -f (u x) := by
    have htrace := h.laplacian_eq_sum_gradient_derivative hx b
    have hpde := h.equation x hx
    simp_rw [real_inner_comm] at htrace
    change (Δ u) x = fieldDivergence b (gradient u) x at htrace
    linarith
  unfold solutionStress stressVector
  rw [fieldDivergence_energy_flux b he' hg hX, heval, hlap]
  rw [real_inner_comm (fderiv ℝ (gradient u) x (X x)) (gradient u x),
    gradient_derivative_inner_symm hu (X x) (gradient u x)]
  ring

/-- The prescribed Neumann gradient and its energy identity cancel the boundary stress flux. -/
theorem RigidityHypotheses.solutionStress_boundary_flux_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (y : Space m) (ξ : Space (m + 1)) :
    inner ℝ (outwardNormal g y)
      (stressVector (normalizedPotential f (u (point y (g y))))
        (gradientWithin u (closure (epigraph g)) (point y (g y))) ξ) = 0 := by
  rw [h.dirichlet y, h.boundary_gradient_eq y]
  have hn : inner ℝ (outwardNormal g y) (outwardNormal g y) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_outwardNormal]
    norm_num
  have hκ := hr.kappa_sq_eq_twice_potential h
  have hW : normalizedPotential f 0 = κ ^ 2 / 2 := by linarith
  simp only [stressVector, norm_smul, norm_outwardNormal, mul_one, norm_neg,
    Real.norm_eq_abs, sq_abs, inner_sub_right, real_inner_smul_right,
    real_inner_smul_left, hn]
  rw [hW]
  ring

end SerrinEpigraph
