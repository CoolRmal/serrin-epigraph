module

public import SerrinEpigraph.IntegrationByParts
public import SerrinEpigraph.Geometry

/-!
# The weak equation for compactly supported tests

Only two derivatives of the solution and one derivative of the compactly supported test are
used. All derivatives are ambient derivatives at interior points of the open domain.
-/

public section

open MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The native Laplacian is the sum of repeated directional derivatives in an orthonormal basis. -/
theorem laplacian_eq_sum_fderiv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    (Δ u) x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  apply Finset.sum_congr rfl
  intro i _
  simp [iteratedFDeriv_two_apply, fderiv_clm_apply hu (differentiableAt_const (b i))]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Parseval's identity expressed using directional derivatives of scalar functions. -/
theorem inner_gradient_eq_sum_fderiv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u φ : E → ℝ) (x : E) :
    inner ℝ (gradient u x) (gradient φ x) =
      ∑ i, fderiv ℝ u x (b i) * fderiv ℝ φ x (b i) := by
  simpa using (b.sum_inner_mul_inner (gradient u x) (gradient φ x)).symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_supported_aux {F ψ : E → ℝ}
    (hψc : HasCompactSupport ψ) (hF : ContinuousOn F (tsupport ψ))
    (hsub : Function.support F ⊆ tsupport ψ) : Integrable F μ :=
  (integrableOn_iff_integrable_of_support_subset hsub).mp (hF.integrableOn_compact hψc)

omit [FiniteDimensional ℝ E] in
private theorem integrable_fderiv_mul_fderiv_aux {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) (v : E) :
    Integrable (fun x ↦ fderiv ℝ u x v * fderiv ℝ φ x v) μ := by
  apply integrable_supported_aux hφc
  · exact (((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub).clm_apply
      continuousOn_const).mul
      (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
  · exact (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v))

omit [FiniteDimensional ℝ E] in
private theorem integrable_fderiv_mul_aux {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) (v : E) :
    Integrable (fun x ↦ fderiv ℝ u x v * φ x) μ := by
  apply integrable_supported_aux hφc
  · exact (((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub).clm_apply
      continuousOn_const).mul hφ.continuous.continuousOn
  · exact (Function.support_mul_subset_right _ _).trans (subset_tsupport _)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem sum_secondDeriv_mul_eq_aux {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hsub : tsupport φ ⊆ Ω) (x : E) :
    (∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) * φ x) = (Δ u) x * φ x := by
  by_cases hx : x ∈ Ω
  · rw [← Finset.sum_mul, laplacian_eq_sum_fderiv b]
    have hd : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
    exact (hd.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
  · have hzero : φ x = 0 := Function.notMem_support.mp
      (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
    simp [hzero]

/-- The gradient pairing with an interior compactly supported test is integrable. -/
theorem integrable_inner_gradient_of_hasCompactSupport {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    Integrable (fun x ↦ inner ℝ (gradient u x) (gradient φ x)) μ := by
  let b := stdOrthonormalBasis ℝ E
  simp_rw [inner_gradient_eq_sum_fderiv b u φ]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_fderiv_mul_fderiv_aux hΩ hu hφ hφc hsub (b i)

/-- The Laplacian multiplied by an interior compactly supported test is integrable. -/
theorem integrable_laplacian_mul_of_hasCompactSupport {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    Integrable (fun x ↦ (Δ u) x * φ x) μ := by
  let b := stdOrthonormalBasis ℝ E
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hint := integrable_finsetSum Finset.univ fun i _ ↦
    integrable_fderiv_mul_aux (μ := μ) hΩ
      (hd.clm_apply (contDiffOn_const (c := b i))) hφ hφc hsub (b i)
  exact hint.congr (Filter.Eventually.of_forall (sum_secondDeriv_mul_eq_aux b hΩ hu hsub))

/-- Green's identity for a `C²` solution and a compactly supported `C¹` test on an open domain. -/
theorem integral_inner_gradient_eq_neg_laplacian_mul {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    (∫ x, inner ℝ (gradient u x) (gradient φ x) ∂μ) = -∫ x, (Δ u) x * φ x ∂μ := by
  let b := stdOrthonormalBasis ℝ E
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hdu : ∀ i, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (b i)) Ω := fun i ↦
    hd.clm_apply contDiffOn_const
  have hint := fun i ↦ integrable_fderiv_mul_fderiv_aux (μ := μ) hΩ
    (hu.of_le (by norm_num)) hφ hφc hsub (b i)
  have hsecond := fun i ↦ integrable_fderiv_mul_aux (μ := μ) hΩ (hdu i) hφ hφc hsub (b i)
  simp_rw [inner_gradient_eq_sum_fderiv b u φ]
  rw [integral_finsetSum _ (fun i _ ↦ hint i)]
  simp_rw [integral_mul_fderiv_eq_neg_of_hasCompactSupport hΩ (hdu _) hφ hφc hsub]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hsecond i)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (sum_secondDeriv_mul_eq_aux b hΩ hu hsub)

/-- The weak form of `-Δu = F`, with no regularity assumption on `F` beyond the equation. -/
theorem integral_inner_gradient_eq_source_mul {u φ F : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω)
    (heq : ∀ x ∈ Ω, -(Δ u) x = F x) :
    (∫ x, inner ℝ (gradient u x) (gradient φ x) ∂μ) = ∫ x, F x * φ x ∂μ := by
  rw [integral_inner_gradient_eq_neg_laplacian_mul hΩ hu hφ hφc hsub, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [← neg_mul, heq x hx]
  · have hzero : φ x = 0 := Function.notMem_support.mp
      (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
    simp [hzero]

/-- The classical semilinear epigraph solution satisfies its weak equation for interior tests. -/
theorem Hypotheses.weak_equation {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ epigraph g) :
    (∫ x, inner ℝ (gradient u x) (gradient φ x)) = ∫ x, f (u x) * φ x :=
  integral_inner_gradient_eq_source_mul (isOpen_epigraph h.graph_contDiff.continuous)
    h.solution_contDiffOn hφ hφc hsub h.equation

end SerrinEpigraph
