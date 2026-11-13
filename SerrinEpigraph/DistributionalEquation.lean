module

public import SerrinEpigraph.WeakEquation
public import SerrinEpigraph.TranslatedDomain

/-!
# Moving both derivatives to a compactly supported test
-/

public section

open MeasureTheory InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A continuous product supported on a compact test support is integrable. -/
private theorem integrable_test_product {F ψ : E → ℝ} (hψ : HasCompactSupport ψ)
    (hc : ContinuousOn F (tsupport ψ)) (hs : Function.support F ⊆ tsupport ψ) :
    Integrable F μ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp (hc.integrableOn_compact hψ)

/-- Integration by parts with the Laplacian on the test and only one derivative on the solution. -/
theorem integral_mul_laplacian_eq_neg_inner_gradient {u φ : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    (∫ x, u x * (Δ φ) x ∂μ) = -∫ x, inner ℝ (gradient u x) (gradient φ x) ∂μ := by
  let b := stdOrthonormalBasis ℝ E
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hψ (i) : ContDiff ℝ 1 (fun x ↦ fderiv ℝ φ x (b i)) :=
    hd.clm_apply contDiff_const
  have hleft (i) : Integrable
      (fun x ↦ u x * fderiv ℝ (fun y ↦ fderiv ℝ φ y (b i)) x (b i)) μ := by
    apply integrable_test_product hφc
    · exact (hu.continuousOn.mono hsub).mul
        (((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
    · exact (Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans
          (tsupport_fderiv_apply_subset ℝ _)))
  have hright (i) : Integrable (fun x ↦ fderiv ℝ u x (b i) * fderiv ℝ φ x (b i)) μ := by
    apply integrable_test_product hφc
    · exact (((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub).clm_apply
        continuousOn_const).mul (hψ i).continuous.continuousOn
    · exact (Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _))
  have hlap (x) : (Δ φ) x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ φ y (b i)) x (b i) :=
    laplacian_eq_sum_fderiv b (hd.differentiable_one x)
  simp_rw [hlap, Finset.mul_sum, inner_gradient_eq_sum_fderiv b u φ]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i),
    integral_finsetSum _ (fun i _ ↦ hright i)]
  simp_rw [integral_mul_fderiv_eq_neg_of_hasCompactSupport hΩ hu (hψ _)
    (hφc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hsub)]
  simp only [Finset.sum_neg_distrib]

/-- The classical PDE holds with both derivatives transferred to the test function. -/
theorem integral_mul_laplacian_eq_neg_source_mul {u φ F : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω)
    (heq : ∀ x ∈ Ω, -(Δ u) x = F x) :
    (∫ x, u x * (Δ φ) x ∂μ) = -∫ x, F x * φ x ∂μ := by
  rw [integral_mul_laplacian_eq_neg_inner_gradient hΩ (hu.of_le (by norm_num)) hφ hφc hsub,
    integral_inner_gradient_eq_source_mul hΩ hu (hφ.of_le (by norm_num)) hφc hsub heq]

/-- The epigraph solution satisfies its distributional equation for interior compact tests. -/
theorem Hypotheses.distributional_equation {m : ℕ} {g : Space m → ℝ}
    {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ epigraph g) :
    (∫ x, u x * (Δ φ) x) = -∫ x, f (u x) * φ x :=
  integral_mul_laplacian_eq_neg_source_mul (isOpen_epigraph h.graph_contDiff.continuous)
    h.solution_contDiffOn hφ hφc hsub h.equation

omit [MeasurableSpace E] [BorelSpace E] in
/-- The Laplacian commutes with translation. -/
theorem laplacian_comp_translation (v : E → ℝ) (a x : E) :
    (Δ (fun y ↦ v (y + a))) x = (Δ v) (x + a) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_comp_add_right]

/-- Every fixed compact test satisfies the translated distributional equation once the
translation is sufficiently high. -/
theorem Hypotheses.eventually_translated_distributional_equation {m : ℕ}
    {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (∫ x, u (x + t • verticalDirection m) * (Δ φ) x) =
        -∫ x, f (u (x + t • verticalDirection m)) * φ x := by
  obtain ⟨T, hT⟩ := compact_eventually_in_epigraph h.graph_contDiff.continuous hφc
  refine ⟨T, fun t ht ↦ ?_⟩
  let Ω := (fun x : Space (m + 1) ↦ x + t • verticalDirection m) ⁻¹' epigraph g
  have hΩ : IsOpen Ω := (isOpen_epigraph h.graph_contDiff.continuous).preimage
    (continuous_id.add continuous_const)
  have hu : ContDiffOn ℝ 2 (fun x ↦ u (x + t • verticalDirection m)) Ω :=
    h.solution_contDiffOn.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hx ↦ hx)
  apply integral_mul_laplacian_eq_neg_source_mul hΩ hu hφ hφc (hT t ht)
  intro x hx
  rw [laplacian_comp_translation]
  exact h.equation _ hx

end SerrinEpigraph
