module

public import SerrinEpigraph.WeakEquation

/-!
# Integration by parts for a vector field near a compact test support
-/

public section

open MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem compact_integrable {A : E → ℝ} {K : Set E} (hK : IsCompact K)
    (hA : ContinuousOn A K) (hs : Function.support A ⊆ K) : Integrable A μ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp (hA.integrableOn_compact hK)

/-- A continuously differentiable vector field can be integrated by parts against a compact test. -/
theorem integral_inner_field_gradient {F : E → E} {φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    (∫ x, inner ℝ (F x) (gradient φ x) ∂μ) =
      -∫ x, (∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i)) * φ x ∂μ := by
  let A : ι → E → ℝ := fun i x ↦ inner ℝ (b i) (F x)
  have hA (i : ι) : ContDiffOn ℝ 1 (A i) Ω :=
    (innerSL ℝ (b i)).contDiff.comp_contDiffOn hF
  have hleft (i : ι) : Integrable (fun x ↦ A i x * fderiv ℝ φ x (b i)) μ := by
    apply compact_integrable hφc
      (((hA i).continuousOn.mono hsub).mul
        (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn))
    exact (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ (b i)))
  have hright (i : ι) : Integrable (fun x ↦ fderiv ℝ (A i) x (b i) * φ x) μ := by
    apply compact_integrable hφc
      ((((hA i).continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub).clm_apply
        continuousOn_const |>.mul hφ.continuous.continuousOn)
    exact (Function.support_mul_subset_right _ _).trans (subset_tsupport φ)
  have hpair (x : E) : inner ℝ (F x) (gradient φ x) =
      ∑ i, A i x * fderiv ℝ φ x (b i) := by
    have he := b.sum_inner_mul_inner (F x) (gradient φ x)
    simpa only [A, real_inner_comm, inner_gradient_left] using he.symm
  simp_rw [hpair]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i)]
  simp_rw [integral_mul_fderiv_eq_neg_of_hasCompactSupport hΩ (hA _) hφ hφc hsub]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hright i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [← Finset.sum_mul]
  by_cases hx : x ∈ Ω
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hd := (innerSL ℝ (b i)).hasFDerivAt.comp x
      ((hF.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)).hasFDerivAt
    have he := congrArg (fun L : E →L[ℝ] ℝ ↦ L (b i)) hd.fderiv
    calc
      _ = inner ℝ (b i) (fderiv ℝ F x (b i)) := by
        simpa [A, Function.comp_def] using he
      _ = _ := real_inner_comm _ _
  · have hz : φ x = 0 := Function.notMem_support.mp
      (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
    simp [hz]

/-- A field with zero trace derivative has zero pairing with every interior compact test gradient. -/
theorem integral_inner_field_gradient_eq_zero {F : E → E} {φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (hzero : ∀ x ∈ Ω, ∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i) = 0) :
    (∫ x, inner ℝ (F x) (gradient φ x) ∂μ) = 0 := by
  rw [integral_inner_field_gradient hΩ hF hφ hφc hsub b]
  have he : (fun x ↦ (∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i)) * φ x) = 0 := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hzero x hx]
    · have hz : φ x = 0 := Function.notMem_support.mp
        (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
      simp [hz]
  rw [he]
  simp

/-- The sum of the field-test pairing and its trace term has zero integral. -/
theorem integral_field_variation_eq_zero {F : E → E} {φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    (∫ x, inner ℝ (F x) (gradient φ x) +
      (∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i)) * φ x ∂μ) = 0 := by
  have hg : Continuous (gradient φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hleft : Integrable (fun x ↦ inner ℝ (F x) (gradient φ x)) μ := by
    apply compact_integrable hφc
      ((hF.continuousOn.mono hsub).inner hg.continuousOn)
    intro x hx
    by_contra hn
    have hz : gradient φ x = 0 := by
      simp [gradient, fderiv_of_notMem_tsupport ℝ hn]
    exact hx (by simp [hz])
  have hright : Integrable
      (fun x ↦ (∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i)) * φ x) μ := by
    have hd := (hF.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub
    apply compact_integrable hφc
    · exact (continuousOn_finsetSum _ (fun i _ ↦
        (hd.clm_apply continuousOn_const).inner continuousOn_const)).mul
          hφ.continuous.continuousOn
    · exact (Function.support_mul_subset_right _ _).trans (subset_tsupport φ)
  rw [integral_add hleft hright, integral_inner_field_gradient hΩ hF hφ hφc hsub b]
  ring

end SerrinEpigraph
