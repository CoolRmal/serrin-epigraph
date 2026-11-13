module

public import SerrinEpigraph.PerimeterLowerSemicontinuity

/-!
# Divergence testing with the exact gradient-mass constant
-/

public section

open MeasureTheory Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Compact vector integration by parts pairs divergence with the full gradient. -/
theorem setIntegral_mul_divergence_eq_neg_inner {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    {F : Space d → Space d} (hv : ContDiff ℝ 1 v) (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) {K : Set (Space d)} (hK : IsCompact K)
    (hs : tsupport F ⊆ K) :
    (∫ x in K, v x * fieldDivergence b F x) =
      -∫ x in K, inner ℝ (gradient v x) (F x) := by
  let ψ : Fin d → Space d → ℝ := fun i x ↦ inner ℝ (b i) (F x)
  have hψ (i : Fin d) : ContDiff ℝ 1 (ψ i) := (innerSL ℝ (b i)).contDiff.comp hF
  have hsupport (i : Fin d) : tsupport (ψ i) ⊆ tsupport F :=
    tsupport_comp_subset (by simp : inner ℝ (b i) (0 : Space d) = 0) F
  have hcompact (i : Fin d) : HasCompactSupport (ψ i) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (hsupport i)
  have hd (i : Fin d) (x : Space d) :
      fderiv ℝ (ψ i) x (b i) = inner ℝ (b i) (fderiv ℝ F x (b i)) := by
    have he := (innerSL ℝ (b i)).hasFDerivAt.comp x (hF.differentiable_one x).hasFDerivAt
    exact congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (b i)) he.fderiv
  have hl (i : Fin d) : IntegrableOn (fun x ↦ v x * fderiv ℝ (ψ i) x (b i)) K :=
    (hv.continuous.mul (((hψ i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).continuousOn.integrableOn_compact hK
  have hr (i : Fin d) : IntegrableOn (fun x ↦ fderiv ℝ v x (b i) * ψ i x) K :=
    ((((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (hψ i).continuous).continuousOn.integrableOn_compact hK)
  have hp (x : Space d) : (∑ i, fderiv ℝ v x (b i) * ψ i x) =
      inner ℝ (gradient v x) (F x) := by
    simpa only [ψ, inner_gradient_left] using b.sum_inner_mul_inner (gradient v x) (F x)
  unfold fieldDivergence
  simp_rw [← hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hl i)]
  simp_rw [setIntegral_mul_fderiv_eq_neg hv (hψ _) (hcompact _) ((hsupport _).trans hs)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hr i)]
  simp_rw [hp]

/-- A unit-bounded vector divergence test is controlled by gradient mass without dimension loss. -/
theorem norm_setIntegral_mul_divergence_le_gradient {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    {F : Space d → Space d} (hv : ContDiff ℝ 1 v) (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) {K : Set (Space d)} (hK : IsCompact K)
    (hs : tsupport F ⊆ K) (hb : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x in K, v x * fieldDivergence b F x‖ ≤ ∫ x in K, ‖gradient v x‖ := by
  rw [setIntegral_mul_divergence_eq_neg_inner b hv hF hc hK hs, norm_neg]
  have hg : Continuous (gradient v) := by
    exact (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  calc
    _ ≤ ∫ x in K, ‖inner ℝ (gradient v x) (F x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in K, ‖gradient v x‖ := by
      apply integral_mono
        ((hg.inner hF.continuous).norm.continuousOn.integrableOn_compact hK)
        (hg.norm.continuousOn.integrableOn_compact hK)
      intro x
      exact (norm_inner_le_norm (𝕜 := ℝ) (gradient v x) (F x)).trans
        ((mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_one _))

/-- The exact vector test bound extends to bounded nonnegative locally Lipschitz coefficients. -/
theorem norm_setIntegral_mul_divergence_le_gradient_of_locallyLipschitz {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    {F : Space d → Space d} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) B)
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) {K : Set (Space d)}
    (hK : IsCompact K) (hs : tsupport F ⊆ K) (hb : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x in K, v x * fieldDivergence b F x‖ ≤ ∫ x in K, ‖gradient v x‖ := by
  have hcont := fieldDivergence_continuous b hF
  have hsupport : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hcompact : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have ht := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict K)
    (normalizedMollify v) v (fieldDivergence b F) C
    (fun n ↦ (normalizedMollify_contDiff hv.continuous n).continuous.continuousOn.integrableOn_compact hK)
    (hv.continuous.continuousOn.integrableOn_compact hK) hcont.aestronglyMeasurable hC
    (normalizedMollify_integral_error_tendsto hv.continuous hval hK)
  apply le_of_tendsto_of_tendsto ht.norm (normalizedMollify_integral_gradient_norm_tendsto hv hK)
  exact Filter.Eventually.of_forall (fun n ↦ norm_setIntegral_mul_divergence_le_gradient b
    ((normalizedMollify_contDiff hv.continuous n).of_le (by simp)) hF hc hK hs hb)

end SerrinEpigraph
