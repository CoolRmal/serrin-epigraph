module

public import SerrinEpigraph.ClosedGraphFlux
public import SerrinEpigraph.PlaneTiltIntegral

/-!
# The distributional inequality across the free boundary

The negative outward Neumann derivative gives a nonpositive boundary term in
the gradient formulation. The zero extension therefore retains the required
global distributional subsolution inequality.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- Product divergence of a scalar and a vector field. -/
theorem fieldDivergence_fun_smul {d : ℕ}
    (basis : OrthonormalBasis (Fin d) ℝ (Space d)) {φ : Space d → ℝ}
    {F : Space d → Space d} {x : Space d}
    (hφ : DifferentiableAt ℝ φ x) (hF : DifferentiableAt ℝ F x) :
    fieldDivergence basis (fun y ↦ φ y • F y) x =
      φ x * fieldDivergence basis F x + inner ℝ (gradient φ x) (F x) := by
  have he := fieldDivergence_energy_flux basis hφ
    (differentiableAt_const (c := (0 : Space d))) hF
  simpa [fieldDivergence, inner_gradient_left] using he

/-- The solution-gradient flux has its classical source in the positive phase. -/
theorem Hypotheses.fieldDivergence_test_gradient
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (hφ : ContDiff ℝ 1 φ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    fieldDivergence basis (fun y ↦ φ y • gradient u y) x =
      inner ℝ (gradient u x) (gradient φ x) - f (u x) * φ x := by
  have hu := h.solution_contDiffOn.contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp x
      (hu.fderiv_right (m := 1) (by norm_num))).differentiableAt (by norm_num)
  rw [fieldDivergence_fun_smul basis (hφ.differentiable_one x) hg]
  have hlap := h.laplacian_eq_sum_gradient_derivative hx basis
  simp_rw [real_inner_comm] at hlap
  change (Δ u) x = fieldDivergence basis (gradient u) x at hlap
  rw [← hlap, real_inner_comm (gradient φ x) (gradient u x)]
  have hpde := h.equation x hx
  have heq : (Δ u) x = -f (u x) := by linarith
  rw [heq]
  ring

/-- The closed solution gradient points inward at the graph. -/
theorem Hypotheses.closed_gradient_graph_flux_nonpos
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (y : Space m) :
    inner ℝ (point (gradient g y) (-1))
      (gradientWithin u (closure (epigraph g)) (point y (g y))) ≤ 0 := by
  rw [h.boundary_gradient_eq, real_inner_smul_right]
  apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h.kappa_pos.le)
  simp only [outwardNormal, real_inner_smul_right]
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (real_inner_self_nonneg)

/-- The integrated weak residual has the nonpositive boundary flux required
for the distributional inequality of the zero extension. -/
theorem RigidityHypotheses.integral_epigraph_weak_residual_nonpos
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x in epigraph g, inner ℝ (gradient u x) (gradient φ x) - f (u x) * φ x) ≤ 0 := by
  let p := gradientWithin u (closure (epigraph g))
  let F := fun x ↦ φ x • gradient u x
  let Fbar := fun x ↦ φ x • p x
  let D := fun x ↦ inner ℝ (p x) (gradient φ x) - f (u x) * φ x
  let basis := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hgrad : ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
      (h.solution_contDiffOn.fderiv_of_isOpen hΩ (by norm_num))
  have hF : ContDiffOn ℝ 1 F (epigraph g) := hφ.contDiffOn.smul hgrad
  have hcF : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_left φ (gradient u))
  have hbar : ContinuousOn Fbar (closure (epigraph g)) :=
    hφ.continuous.continuousOn.smul h.closed_gradient_continuousOn
  have hcbar : HasCompactSupport Fbar := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_left φ p)
  have heq : EqOn Fbar F (epigraph g) := by
    intro x hx
    simp only [Fbar, F, p, h.closed_gradient_eq hx]
  have hD : ContinuousOn D (closure (epigraph g)) := by
    have hf := h.reaction_contDiffOn.continuousOn.comp
      h.solution_contDiffOn_closure.continuousOn
      (fun x hx ↦ (hr.solution_mem_Icc_closure h hx).1)
    have hφgrad : Continuous (gradient φ) :=
      (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
    exact (h.closed_gradient_continuousOn.inner hφgrad.continuousOn).sub
      (hf.mul hφ.continuous.continuousOn)
  have hcD : HasCompactSupport D := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    apply hx
    simp [D, gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn]
  have hdiv : EqOn (fieldDivergence basis F) D (epigraph g) := by
    intro x hx
    simpa only [D, p, h.closed_gradient_eq hx] using
      h.fieldDivergence_test_gradient basis hφ hx
  have hGauss := integral_epigraph_divergence_of_continuous_trace basis h.graph_contDiff
    hF hcF hbar hcbar heq hD hcD hdiv
  have hres : (∫ x in epigraph g, D x) ≤ 0 := by
    rw [hGauss]
    apply integral_nonpos
    intro y
    change inner ℝ (point (gradient g y) (-1)) (φ (point y (g y)) • p (point y (g y))) ≤ 0
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (hφ0 _) (h.closed_gradient_graph_flux_nonpos y)
  have he : (∫ x in epigraph g, D x) =
      ∫ x in epigraph g, inner ℝ (gradient u x) (gradient φ x) - f (u x) * φ x := by
    apply setIntegral_congr_fun hΩ.measurableSet
    intro x hx
    simp only [D, p, h.closed_gradient_eq hx]
  rwa [he] at hres

/-- The global weak residual is integrable for every compact C1 test. -/
theorem Hypotheses.integrable_zeroExtension_weak_residual
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x ↦ inner ℝ (gradient (zeroExtension g u) x) (gradient φ x) -
      f (zeroExtension g u x) * φ x) := by
  have hφgrad : Continuous (gradient φ) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  obtain ⟨C, hC⟩ := gradient_bound_of_locallyLipschitz h.zeroExtension_locallyLipschitz hc
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuousOn hφgrad.continuousOn
  have hi : IntegrableOn (fun x ↦ inner ℝ (gradient (zeroExtension g u) x) (gradient φ x))
      (tsupport φ) := by
    apply (continuousOn_const.integrableOn_compact hc
      (f := fun _ : Space (m + 1) ↦ (C : ℝ) * D)).mono'
        ((measurable_gradient _).inner (𝕜 := ℝ) hφgrad.measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul (hC x hx) (hD x hx) (norm_nonneg _) C.coe_nonneg)
  have hf : Continuous (fun x ↦ f (zeroExtension g u x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous h.zeroExtension_continuous
      (fun x ↦ h.zeroExtension_nonneg x)
  have hit := hi.sub ((hf.mul hφ.continuous).continuousOn.integrableOn_compact hc)
  apply hit.integrable_of_forall_notMem_eq_zero
  intro x hx
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]

/-- The Neumann sign gives the weak inequality on all of Euclidean space. -/
theorem RigidityHypotheses.integral_zeroExtension_weak_residual_nonpos
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x, inner ℝ (gradient (zeroExtension g u) x) (gradient φ x) -
      f (zeroExtension g u x) * φ x) ≤ 0 := by
  have hΩ := (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  rw [← integral_add_compl hΩ (h.integrable_zeroExtension_weak_residual hφ hc)]
  apply add_nonpos
  · have he : (∫ x in epigraph g,
        inner ℝ (gradient (zeroExtension g u) x) (gradient φ x) -
          f (zeroExtension g u x) * φ x) =
        ∫ x in epigraph g, inner ℝ (gradient u x) (gradient φ x) - f (u x) * φ x := by
      apply setIntegral_congr_fun hΩ
      intro x hx
      dsimp only
      rw [h.gradient_zeroExtension hx, zeroExtension_of_mem hx]
    rw [he]
    exact hr.integral_epigraph_weak_residual_nonpos h hφ hc hφ0
  · apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem hΩ.compl] with x hx
    rw [h.gradient_zeroExtension_of_notMem hx, inner_zero_left, zeroExtension_of_notMem hx]
    exact sub_nonpos.mpr (mul_nonneg
      (reaction_nonneg_zero h.reaction_contDiffOn h.reaction_structure) (hφ0 x))

/-- Both derivatives can be moved onto a compact test across a nonsmooth
interface of a bounded locally Lipschitz function. -/
theorem integral_mul_laplacian_eq_neg_inner_gradient_of_locallyLipschitz
    {d : ℕ} {v φ : Space d → ℝ} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc 0 B) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) :
    (∫ x, v x * (Δ φ) x) = -∫ x, inner ℝ (gradient v x) (gradient φ x) := by
  let basis := EuclideanSpace.basisFun (Fin d) ℝ
  have hgrad : ContDiff ℝ 1 (gradient φ) :=
    (toDual ℝ (Space d)).symm.contDiff.comp (hφ.fderiv_right (by norm_num))
  have hs : tsupport (gradient φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    exact hx (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  have hcgrad : HasCompactSupport (gradient φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hs
  have hd : fieldDivergence basis (gradient φ) = Δ φ := by
    funext x
    have hh := laplacian_eq_sum_gradient_derivative_of_differentiable
      (hgrad.differentiable_one x) basis
    simpa only [fieldDivergence, real_inner_comm] using hh.symm
  have hi := setIntegral_mul_divergence_eq_neg_inner_of_locallyLipschitz basis hv hval
    hgrad hcgrad hc hs
  rw [hd, setIntegral_mul_laplacian_test] at hi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by simp [gradient, fderiv_of_notMem_tsupport ℝ hx])] at hi
  exact hi

/-- The zero extension satisfies the global distributional inequality
`Δ U ≥ -f(U)`, including the free boundary. -/
theorem RigidityHypotheses.zeroExtension_distributional_inequality
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∫ x, f (zeroExtension g u x) * φ x) ≤ ∫ x, zeroExtension g u x * (Δ φ) x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf : Continuous (fun x ↦ f (zeroExtension g u x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous h.zeroExtension_continuous
      (fun x ↦ h.zeroExtension_nonneg x)
  have his : Integrable (fun x ↦ f (zeroExtension g u x) * φ x) :=
    (hf.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hir := h.integrable_zeroExtension_weak_residual hφ1 hc
  have hig : Integrable (fun x ↦ inner ℝ (gradient (zeroExtension g u) x) (gradient φ x)) := by
    apply (hir.add his).congr
    filter_upwards with x
    change (inner ℝ (gradient (zeroExtension g u) x) (gradient φ x) -
      f (zeroExtension g u x) * φ x) + f (zeroExtension g u x) * φ x =
      inner ℝ (gradient (zeroExtension g u) x) (gradient φ x)
    ring
  have hw := hr.integral_zeroExtension_weak_residual_nonpos h hφ1 hc hφ0
  rw [integral_sub hig his] at hw
  rw [integral_mul_laplacian_eq_neg_inner_gradient_of_locallyLipschitz
    h.zeroExtension_locallyLipschitz
    (fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩) hφ hc]
  linarith

end SerrinEpigraph
