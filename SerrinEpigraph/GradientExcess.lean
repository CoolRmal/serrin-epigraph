module

public import SerrinEpigraph.WeakBochner
public import SerrinEpigraph.ShiftedStressFlux

/-!
# The weak equation for the gradient excess

The perturbed excess is half the squared gradient minus the potential plus a small
multiple of the squared solution. All identities use only the original C2 regularity.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped ContDiff

namespace SerrinEpigraph

/-- The squared norm of a finite linear combination satisfies the scalar Cauchy bound. -/
theorem norm_sum_smul_sq_le {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (v : ι → Space d) :
    ‖∑ i, a i • v i‖ ^ 2 ≤ (∑ i, a i ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  have hn : ‖∑ i, a i • v i‖ ≤ ∑ i, |a i| * ‖v i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i ↦ a i • v i)
  have hs : 0 ≤ ∑ i, |a i| * ‖v i‖ :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _)
  calc
    _ ≤ (∑ i, |a i| * ‖v i‖) ^ 2 := by nlinarith [norm_nonneg (∑ i, a i • v i)]
    _ ≤ _ := by simpa only [sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ |a i|) (fun i ↦ ‖v i‖)

/-- Differentiating the coordinate expansion of half the squared gradient. -/
theorem gradient_half_gradient_norm_sq_eq_sum {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {u : Space d → ℝ} {x : Space d}
    (hu : ContDiffAt ℝ 2 u x) :
    gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x =
      ∑ i, fderiv ℝ u x (b i) • gradient (fun y ↦ fderiv ℝ u y (b i)) x := by
  have hvc (i : Fin d) : ContDiffAt ℝ 1 (fun y ↦ fderiv ℝ u y (b i)) x :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hv (i : Fin d) : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y (b i)) x :=
    (hvc i).differentiableAt (by norm_num)
  have hk (i : Fin d) : DifferentiableAt ℝ (fun y ↦ (fderiv ℝ u y (b i)) ^ 2 / 2) x := by
    have hd := ((hv i).hasFDerivAt.pow 2).smul_const (1 / 2 : ℝ)
    change HasFDerivAt (fun y ↦ (fderiv ℝ u y (b i)) ^ 2 * (1 / 2)) _ x at hd
    simpa only [one_div, ← div_eq_mul_inv] using hd.differentiableAt
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hk i).hasFDerivAt)
  have he : (fun y ↦ ‖gradient u y‖ ^ 2 / 2) =
      fun y ↦ ∑ i, (fderiv ℝ u y (b i)) ^ 2 / 2 := by
    funext y
    exact half_gradient_norm_sq_eq_sum b u y
  rw [he]
  change (toDual ℝ (Space d)).symm _ = _
  rw [hsum.fderiv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact gradient_half_sq_at (hv i)

/-- The Hessian controls the gradient of the kinetic energy. -/
theorem norm_gradient_half_gradient_norm_sq_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {u : Space d → ℝ} {x : Space d}
    (hu : ContDiffAt ℝ 2 u x) :
    ‖gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x‖ ^ 2 ≤
      ‖gradient u x‖ ^ 2 * hessianSquare b u x := by
  rw [gradient_half_gradient_norm_sq_eq_sum b hu]
  have he := half_gradient_norm_sq_eq_sum b u x
  rw [← Finset.sum_div] at he
  have hs : (∑ i, (fderiv ℝ u x (b i)) ^ 2) = ‖gradient u x‖ ^ 2 := by linarith
  simpa only [hs, hessianSquare] using norm_sum_smul_sq_le
    (fun i ↦ fderiv ℝ u x (b i)) (fun i ↦ gradient (fun y ↦ fderiv ℝ u y (b i)) x)

/-- Gradient excess with a quadratic perturbation. -/
@[expose] def gradientExcess {d : ℕ} (u : Space d → ℝ) (f : ℝ → ℝ)
    (ε : ℝ) (x : Space d) : ℝ :=
  ‖gradient u x‖ ^ 2 / 2 - normalizedPotential f (u x) + ε * u x ^ 2

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The gradient excess is C1 in the solution domain. -/
theorem Hypotheses.gradientExcess_contDiffOn (h : Hypotheses g u f κ) (ε : ℝ) :
    ContDiffOn ℝ 1 (gradientExcess u f ε) (epigraph g) := by
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hg : ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
      (h.solution_contDiffOn.fderiv_of_isOpen
        (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num))
  exact (((hg.norm_sq (𝕜 := ℝ)).div_const 2).sub
    (h.normalizedPotential_contDiffOn_positive.comp hu h.positive)).add
      (contDiffOn_const.mul (hu.pow 2))

/-- The gradient excess has the expected first derivative without a third derivative of u. -/
theorem Hypotheses.gradient_gradientExcess (h : Hypotheses g u f κ)
    (ε : ℝ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    gradient (gradientExcess u f ε) x =
      gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x +
        (f (u x) + 2 * ε * u x) • gradient u x := by
  have hu := h.solution_contDiffOn.contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hud := hu.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp x
      (hu.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2))).differentiableAt (by norm_num)
  have hk : DifferentiableAt ℝ (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x := by
    have hd := (hg.hasFDerivAt.norm_sq).smul_const (1 / 2 : ℝ)
    change HasFDerivAt (fun y ↦ ‖gradient u y‖ ^ 2 * (1 / 2)) _ x at hd
    simpa only [one_div, ← div_eq_mul_inv] using hd.differentiableAt
  have hW := (h.normalizedPotential_hasDerivAt (h.positive x hx)).comp_hasFDerivAt x
    hud.hasFDerivAt
  have he := (hk.hasFDerivAt.sub hW).add ((hud.hasFDerivAt.pow 2).const_mul ε)
  change HasFDerivAt (gradientExcess u f ε) _ x at he
  simp only [gradient, he.fderiv, map_add, map_sub, map_smul]
  module

/-- A variable multiple of the solution gradient can be tested using the original equation. -/
theorem Hypotheses.weak_gradient_multiple (h : Hypotheses g u f κ)
    {c φ : Space (m + 1) → ℝ} (hcoef : ContDiffOn ℝ 1 c (epigraph g))
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ epigraph g) :
    (∫ x, c x * inner ℝ (gradient u x) (gradient φ x)) =
      ∫ x, (f (u x) * c x - inner ℝ (gradient u x) (gradient c x)) * φ x := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hp : ContinuousOn (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hcp : ContinuousOn (gradient c) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hcoef.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hF : ContinuousOn (fun x ↦ f (u x)) (epigraph g) :=
    h.reaction_contDiffOn.continuousOn.comp hu.continuousOn (fun x hx ↦ (h.positive x hx).le)
  have htest := contDiff_mul_of_tsupport_subset hΩ hcoef hφ hs
  have htests : tsupport (fun x ↦ c x * φ x) ⊆ epigraph g :=
    tsupport_mul_subset_right.trans hs
  have hiTest := integrable_inner_gradient_of_hasCompactSupport (μ := volume)
    hΩ hu htest hc.mul_left htests
  have hiPair := integrable_mul_of_tsupport_subset (μ := volume)
    (hp.inner hcp) hφ.continuous hc hs
  have hiSource : Integrable (fun x ↦ f (u x) * c x * φ x) :=
    integrable_mul_of_tsupport_subset (hF.mul hcoef.continuousOn) hφ.continuous hc hs
  have hpoint (x : Space (m + 1)) :
      c x * inner ℝ (gradient u x) (gradient φ x) =
        inner ℝ (gradient u x) (gradient (fun y ↦ c y * φ y) x) -
          inner ℝ (gradient u x) (gradient c x) * φ x := by
    by_cases hx : x ∈ epigraph g
    · rw [gradient_mul_at ((hcoef.differentiableOn_one x hx).differentiableAt
        (hΩ.mem_nhds hx)) (hφ.differentiable_one x)]
      simp only [inner_add_right, real_inner_smul_right]
      ring
    · have hxφ : x ∉ tsupport φ := fun hh ↦ hx (hs hh)
      have hxt : x ∉ tsupport (fun y ↦ c y * φ y) := fun hh ↦ hx (htests hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hxφ, fderiv_of_notMem_tsupport ℝ hxt,
        image_eq_zero_of_notMem_tsupport hxφ]
  simp_rw [hpoint]
  rw [integral_sub hiTest hiPair, h.weak_equation htest hc.mul_left htests]
  simp_rw [← mul_assoc]
  rw [← integral_sub hiSource hiPair]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by dsimp only; ring)

/-- The squared Hessian norm is continuous with the original two derivatives of the solution. -/
theorem Hypotheses.hessianSquare_continuousOn (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) :
    ContinuousOn (hessianSquare b u) (epigraph g) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  apply continuousOn_finsetSum
  intro i _
  have hv : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (b i)) (epigraph g) :=
    (h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const
  exact ((toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
    (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl)).norm.pow 2

/-- The weak Laplacian of the perturbed excess. The reaction derivative cancels. -/
theorem Hypotheses.weak_gradientExcess_identity (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (ε : ℝ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ epigraph g) :
    (∫ x, inner ℝ (gradient (gradientExcess u f ε) x) (gradient φ x)) =
      ∫ x, (f (u x) ^ 2 - hessianSquare b u x + 2 * ε * u x * f (u x) -
        2 * ε * ‖gradient u x‖ ^ 2) * φ x := by
  let c := fun x ↦ f (u x) + 2 * ε * u x
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hp : ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
      (h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num))
  have hF : ContDiffOn ℝ 1 (fun x ↦ f (u x)) (epigraph g) :=
    h.reaction_contDiffOn.comp hu (fun x hx ↦ (h.positive x hx).le)
  have hcoef : ContDiffOn ℝ 1 c (epigraph g) := hF.add (contDiffOn_const.mul hu)
  have hcp : ContinuousOn (gradient c) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (hcoef.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have ha : ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) :=
    ((h.reaction_contDiffOn.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp hu.continuousOn h.positive
  have hdc {x : Space (m + 1)} (hx : x ∈ epigraph g) :
      gradient c x = (deriv f (u x) + 2 * ε) • gradient u x := by
    have hud := (hu.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
    have hfd :=
      (h.reaction_contDiffOn.differentiableOn_one (u x) (h.positive x hx).le).differentiableAt
        (Ici_mem_nhds (h.positive x hx))
    have hd := (hfd.hasDerivAt.comp_hasFDerivAt x hud.hasFDerivAt).add
      (hud.hasFDerivAt.const_mul (2 * ε))
    change HasFDerivAt c _ x at hd
    simp only [gradient, hd.fderiv, map_add, map_smul]
    module
  have hpoint (x : Space (m + 1)) :
      inner ℝ (gradient (gradientExcess u f ε) x) (gradient φ x) =
        inner ℝ (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) (gradient φ x) +
          c x * inner ℝ (gradient u x) (gradient φ x) := by
    by_cases hx : x ∈ epigraph g
    · rw [h.gradient_gradientExcess ε hx, inner_add_left, real_inner_smul_left]
    · have hxφ : x ∉ tsupport φ := fun hh ↦ hx (hs hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hxφ]
  have hiK := integrable_inner_gradient_of_hasCompactSupport (μ := volume) hΩ
    ((hp.norm_sq (𝕜 := ℝ)).div_const 2) hφ hc hs
  have hiP := integrable_inner_gradient_of_hasCompactSupport (μ := volume) hΩ
    (h.gradientExcess_contDiffOn ε) hφ hc hs
  have hiC : Integrable (fun x ↦ c x * inner ℝ (gradient u x) (gradient φ x)) :=
    (hiP.sub hiK).congr (Eventually.of_forall (fun x ↦ by
      dsimp only [Pi.sub_apply]
      rw [hpoint]
      ring))
  have hiB : Integrable (fun x ↦
      (deriv f (u x) * ‖gradient u x‖ ^ 2 - hessianSquare b u x) * φ x) :=
    integrable_mul_of_tsupport_subset
      ((ha.mul (hp.continuousOn.norm.pow 2)).sub (h.hessianSquare_continuousOn b))
      hφ.continuous hc hs
  have hiD : Integrable (fun x ↦
      (f (u x) * c x - inner ℝ (gradient u x) (gradient c x)) * φ x) :=
    integrable_mul_of_tsupport_subset
      ((hF.continuousOn.mul hcoef.continuousOn).sub (hp.continuousOn.inner hcp))
      hφ.continuous hc hs
  simp_rw [hpoint]
  rw [integral_add hiK hiC, h.weak_bochner_identity b hφ hc hs,
    h.weak_gradient_multiple hcoef hφ hc hs, ← integral_add hiB hiD]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ by
    dsimp only
    by_cases hx : x ∈ epigraph g
    · rw [hdc hx, real_inner_smul_right, real_inner_self_eq_norm_sq]
      dsimp only [c]
      ring
    · simp [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))])

/-- The Hessian Cauchy inequality gives the differential inequality for the perturbed excess. -/
theorem Hypotheses.gradientExcess_differential_inequality (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (ε : ℝ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    ‖gradient (gradientExcess u f ε) x‖ ^ 2 + 2 * ε * ‖gradient u x‖ ^ 4 +
        (2 * ε * u x * f (u x) + 4 * ε ^ 2 * u x ^ 2) * ‖gradient u x‖ ^ 2 ≤
      ‖gradient u x‖ ^ 2 * (hessianSquare b u x - f (u x) ^ 2 +
        2 * ε * ‖gradient u x‖ ^ 2 - 2 * ε * u x * f (u x)) +
        2 * (f (u x) + 2 * ε * u x) *
          inner ℝ (gradient u x) (gradient (gradientExcess u f ε) x) := by
  have hu := h.solution_contDiffOn.contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hC := norm_gradient_half_gradient_norm_sq_le b hu
  have he : gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x =
      gradient (gradientExcess u f ε) x - (f (u x) + 2 * ε * u x) • gradient u x := by
    rw [h.gradient_gradientExcess ε hx, add_sub_cancel_right]
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right,
    real_inner_comm (gradient u x) (gradient (gradientExcess u f ε) x)] at hC
  nlinarith only [hC]

/-- Positivity of the reaction discards the nonnegative remainder in the excess inequality. -/
theorem RigidityHypotheses.gradientExcess_differential_inequality
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {ε : ℝ} (hε : 0 ≤ ε)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    ‖gradient (gradientExcess u f ε) x‖ ^ 2 + 2 * ε * ‖gradient u x‖ ^ 4 ≤
      ‖gradient u x‖ ^ 2 * (hessianSquare b u x - f (u x) ^ 2 +
        2 * ε * ‖gradient u x‖ ^ 2 - 2 * ε * u x * f (u x)) +
        2 * (f (u x) + 2 * ε * u x) *
          inner ℝ (gradient u x) (gradient (gradientExcess u f ε) x) := by
  have hu : 0 < u x := h.positive x hx
  have hf : 0 < f (u x) := hr.reaction_pos (u x) ⟨hu, hr.solution_lt_one x hx⟩
  have hrem : 0 ≤ (2 * ε * u x * f (u x) + 4 * ε ^ 2 * u x ^ 2) *
      ‖gradient u x‖ ^ 2 := by positivity
  linarith [h.gradientExcess_differential_inequality b ε hx]

end SerrinEpigraph
