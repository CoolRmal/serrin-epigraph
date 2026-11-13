module

public import SerrinEpigraph.DistributionalEquation
public import SerrinEpigraph.TranslateIntegrals

/-!
# The distributional equation of the vertical limit
-/

public section

noncomputable section

open Filter MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Laplacian of a twice continuously differentiable scalar function is continuous. -/
theorem continuous_laplacian_of_contDiff {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (Δ φ) := by
  let b := stdOrthonormalBasis ℝ E
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have heq : (Δ φ) = fun x ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ φ y (b i)) x (b i) := by
    funext x
    exact laplacian_eq_sum_fderiv b (hd.differentiable_one x)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  exact (((hd.clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply continuous_const)

/-- The Laplacian vanishes outside the topological support of the function. -/
theorem laplacian_zero_off_tsupport (φ : E → ℝ) {x : E} (hx : x ∉ tsupport φ) :
    (Δ φ) x = 0 := by
  have hz : iteratedFDeriv ℝ 2 φ x = 0 := Function.notMem_support.mp
    (fun hmem ↦ hx (support_iteratedFDeriv_subset (𝕜 := ℝ) 2 hmem))
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hz,
    zero_apply, Finset.sum_const_zero]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A product weighted by the test can be integrated on its compact support. -/
theorem setIntegral_mul_test (v φ : E → ℝ) :
    (∫ x in tsupport φ, v x * φ x ∂μ) = ∫ x, v x * φ x ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

omit [BorelSpace E] in
/-- A product weighted by the test Laplacian has the same support restriction. -/
theorem setIntegral_mul_laplacian_test (v φ : E → ℝ) :
    (∫ x in tsupport φ, v x * (Δ φ) x ∂μ) = ∫ x, v x * (Δ φ) x ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [laplacian_zero_off_tsupport φ hx, mul_zero]

/-- The horizontal ray limit, lifted to ambient space, satisfies the original semilinear
PDE in distributional form against every compactly supported twice differentiable test. -/
theorem RigidityHypotheses.limit_distributional_equation {m : ℕ} {g : Space m → ℝ}
    {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, hr.verticalLimitProfile h (horizontal x) * (Δ φ) x) =
      -∫ x, f (hr.verticalLimitProfile h (horizontal x)) * φ x := by
  have hleft := hr.tendsto_integral_solution_translate h hφc
    (continuous_laplacian_of_contDiff hφ).continuousOn
  have hright := hr.tendsto_integral_reaction_translate h hφc hφ.continuous.continuousOn
  simp only [setIntegral_mul_laplacian_test] at hleft
  simp only [setIntegral_mul_test] at hright
  obtain ⟨T, hT⟩ := h.eventually_translated_distributional_equation hφ hφc
  apply tendsto_nhds_unique hleft
  apply hright.neg.congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (hT t ht).symm

/-- The lifted limit is superharmonic in the distributional sense. -/
theorem RigidityHypotheses.limit_distributionally_superharmonic {m : ℕ}
    {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφnonneg : ∀ x, 0 ≤ φ x) :
    (∫ x, hr.verticalLimitProfile h (horizontal x) * (Δ φ) x) ≤ 0 := by
  rw [hr.limit_distributional_equation h hφ hφc]
  apply neg_nonpos.mpr
  apply integral_nonneg
  intro x
  apply mul_nonneg _ (hφnonneg x)
  have hspec := hr.verticalLimitProfile_spec h (horizontal x)
  rcases lt_or_eq_of_le hspec.2.1 with hlt | heq
  · exact (hr.reaction_pos _ ⟨hspec.1, hlt⟩).le
  · rw [heq, hr.reaction_one]

end SerrinEpigraph
