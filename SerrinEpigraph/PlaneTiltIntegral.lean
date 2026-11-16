module

public import SerrinEpigraph.PrimitivePerimeterMass
public import SerrinEpigraph.LipschitzDirectionalTest
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Oriented gradient defects and compact directional flux
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Local Lipschitz regularity makes the totalized gradient integrable on compact sets. -/
theorem integrableOn_gradient_of_locallyLipschitz {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (gradient v) K := by
  obtain ⟨C, hC⟩ := gradient_bound_of_locallyLipschitz hv hK
  apply (continuousOn_const.integrableOn_compact hK
    (f := fun _ : Space d ↦ (C : ℝ))).mono' (measurable_gradient v).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

/-- Compact directional flux has the exact integration-by-parts identity for bounded
locally Lipschitz functions, including across their free boundaries. -/
theorem setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
    {d : ℕ} {v ψ : Space d → ℝ} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) B)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K : Set (Space d)} (hK : IsCompact K) (hs : tsupport ψ ⊆ K) (e : Space d) :
    (∫ x in K, inner ℝ (gradient v x) e * ψ x) =
      -∫ x in K, v x * fderiv ℝ ψ x e := by
  obtain ⟨C, hC⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hv hK
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hψ.continuous
  have ht : Tendsto (fun j ↦ ∫ x in K,
      inner ℝ (gradient (normalizedMollify v j) x) e * ψ x) atTop
      (𝓝 (∫ x in K, inner ℝ (gradient v x) e * ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (C : ℝ) * ‖e‖ * M)
    · intro j
      exact (((measurable_gradient _).inner (𝕜 := ℝ) measurable_const).mul
        hψ.continuous.measurable).aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro j
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul
        ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul_of_nonneg_right (hC j x hx) (norm_nonneg e)))
        (hM x) (norm_nonneg _) (mul_nonneg C.coe_nonneg (norm_nonneg e))
    · filter_upwards [ae_restrict_of_ae
        (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hv)] with x hx
      exact (hx.inner tendsto_const_nhds).mul tendsto_const_nhds
  have hd : HasCompactSupport (fun x ↦ fderiv ℝ ψ x e) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ e)
  obtain ⟨D, hD⟩ := hd.exists_bound_of_continuous
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hr := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict K)
    (normalizedMollify v) v (fun x ↦ fderiv ℝ ψ x e) D
    (fun j ↦ (normalizedMollify_contDiff hv.continuous j).continuous.continuousOn
      |>.integrableOn_compact hK)
    (hv.continuous.continuousOn.integrableOn_compact hK)
    (((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
    hD (normalizedMollify_integral_error_tendsto hv.continuous hval hK)
  apply tendsto_nhds_unique ht
  apply hr.neg.congr'
  apply Eventually.of_forall
  intro j
  have he := setIntegral_mul_fderiv_eq_neg
    ((normalizedMollify_contDiff hv.continuous j).of_le (by simp)) hψ hc hs e
  simpa only [inner_gradient_left, neg_neg] using congrArg Neg.neg he

/-- Exact signed vector integration by parts also holds for bounded locally Lipschitz
coefficients, with no smoothness across the zero set. -/
theorem setIntegral_mul_divergence_eq_neg_inner_of_locallyLipschitz {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    {F : Space d → Space d} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) B)
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    {K : Set (Space d)} (hK : IsCompact K) (hs : tsupport F ⊆ K) :
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
  have hr (i : Fin d) : IntegrableOn
      (fun x ↦ inner ℝ (gradient v x) (b i) * ψ i x) K := by
    have hi : IntegrableOn (fun x ↦ inner ℝ (gradient v x) (b i)) K :=
      (integrableOn_gradient_of_locallyLipschitz hv hK).inner_const (b i)
    exact hi.mul_continuousOn (hψ i).continuous.continuousOn hK
  have hp (x : Space d) :
      (∑ i, inner ℝ (gradient v x) (b i) * ψ i x) =
        inner ℝ (gradient v x) (F x) := b.sum_inner_mul_inner _ _
  have he (i : Fin d) : (∫ x in K, v x * fderiv ℝ (ψ i) x (b i)) =
      -∫ x in K, inner ℝ (gradient v x) (b i) * ψ i x := by
    have hh := setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
      hv hval (hψ i) (hcompact i) hK ((hsupport i).trans hs) (b i)
    linarith
  unfold fieldDivergence
  simp_rw [← hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hl i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hr i)]
  simp_rw [hp]

/-- The oriented gradient defect with respect to a unit vector is nonnegative. -/
theorem oriented_gradient_defect_nonneg {d : ℕ} (q : Space d) {e : Space d}
    (he : ‖e‖ = 1) : 0 ≤ ‖q‖ - inner ℝ q e := by
  have hh := real_inner_le_norm q e
  rw [he, mul_one] at hh
  exact sub_nonneg.mpr hh

/-- A cutoff equal to one on a compact subset bounds its oriented defect by total mass
on the larger compact set minus the exact compact directional flux. -/
theorem integral_oriented_gradient_defect_le_mass_add_test
    {d : ℕ} {v ψ : Space d → ℝ} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) B)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K L : Set (Space d)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hs : tsupport ψ ⊆ L) (hψval : ∀ x, ψ x ∈ Icc (0 : ℝ) 1)
    (hψone : ∀ x ∈ K, ψ x = 1) {e : Space d} (he : ‖e‖ = 1) :
    (∫ x in K, ‖gradient v x‖ - inner ℝ (gradient v x) e) ≤
      (∫ x in L, ‖gradient v x‖) + ∫ x in L, v x * fderiv ℝ ψ x e := by
  have hg := integrableOn_gradient_of_locallyLipschitz hv hL
  have hi₀ : IntegrableOn (fun x ↦ inner ℝ (gradient v x) e) L := hg.inner_const e
  have hi := hi₀.mul_continuousOn hψ.continuous.continuousOn hL
  have hnonneg (x : Space d) : 0 ≤ ‖gradient v x‖ -
      inner ℝ (gradient v x) e * ψ x := by
    have hd := oriented_gradient_defect_nonneg (gradient v x) he
    have hh := mul_nonneg (hψval x).1 hd
    have hn := mul_nonneg (sub_nonneg.mpr (hψval x).2) (norm_nonneg (gradient v x))
    nlinarith
  calc
    _ = ∫ x in K, ‖gradient v x‖ - inner ℝ (gradient v x) e * ψ x := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      rw [hψone x hx, mul_one]
    _ ≤ ∫ x in L, ‖gradient v x‖ - inner ℝ (gradient v x) e * ψ x :=
      setIntegral_mono_set (hg.norm.sub hi) (Eventually.of_forall hnonneg)
        (Eventually.of_forall hKL)
    _ = _ := by
      rw [integral_sub hg.norm hi,
        setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz hv hval hψ hc hL hs,
        sub_neg_eq_add]

/-- Local integral convergence identifies compact directional fluxes of the actual
locally Lipschitz gradients, without a smoothness assumption across interfaces. -/
theorem integral_cutoff_gradient_tendsto_of_integral_norm_sub_tendsto
    {d : ℕ} {v : ℕ → Space d → ℝ} {p ψ : Space d → ℝ}
    (hv : ∀ j, LocallyLipschitz (v j)) {B : ℕ → ℝ}
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) (B j))
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K : Set (Space d)} (hK : IsCompact K) (hs : tsupport ψ ⊆ K)
    (hp : IntegrableOn p K) (e : Space d)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖v j x - p x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K, inner ℝ (gradient (v j) x) e * ψ x) atTop
      (𝓝 (-∫ x in K, p x * fderiv ℝ ψ x e)) := by
  have hd : HasCompactSupport (fun x ↦ fderiv ℝ ψ x e) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ e)
  obtain ⟨C, hC⟩ := hd.exists_bound_of_continuous
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hl := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict K)
    v p (fun x ↦ fderiv ℝ ψ x e) C
    (fun j ↦ (hv j).continuous.continuousOn.integrableOn_compact hK) hp
    (((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
    hC ht
  simpa only [setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
    (hv _) (hval _) hψ hc hK hs] using hl.neg

/-- A compact test vanishing on a set bounds its energy by the surrounding total
energy minus calibrated gradient flux. Only the pointwise gradient bound is needed. -/
theorem integral_density_le_mass_add_test_of_test_zero
    {d : ℕ} {v ψ q : Space d → ℝ} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) B)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K L : Set (Space d)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hs : tsupport ψ ⊆ L) (hψval : ∀ x, ψ x ∈ Icc (0 : ℝ) 1)
    (hzero : ∀ x ∈ K, ψ x = 0) {e : Space d} (he : ‖e‖ = 1)
    (hi : IntegrableOn q L) (hq : ∀ x, ‖gradient v x‖ ≤ q x) :
    (∫ x in K, q x) ≤ (∫ x in L, q x) + ∫ x in L, v x * fderiv ℝ ψ x e := by
  have hg := integrableOn_gradient_of_locallyLipschitz hv hL
  have hi₀ : IntegrableOn (fun x ↦ inner ℝ (gradient v x) e) L := hg.inner_const e
  have hgi := hi₀.mul_continuousOn hψ.continuous.continuousOn hL
  have hnonneg (x : Space d) : 0 ≤ q x - inner ℝ (gradient v x) e * ψ x := by
    have hd := oriented_gradient_defect_nonneg (gradient v x) he
    have hh := mul_nonneg (hψval x).1 hd
    have hn := mul_nonneg (sub_nonneg.mpr (hψval x).2) (norm_nonneg (gradient v x))
    have hb := hq x
    nlinarith
  calc
    _ = ∫ x in K, q x - inner ℝ (gradient v x) e * ψ x := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      rw [hzero x hx, mul_zero, sub_zero]
    _ ≤ ∫ x in L, q x - inner ℝ (gradient v x) e * ψ x :=
      setIntegral_mono_set (hi.sub hgi) (Eventually.of_forall hnonneg)
        (Eventually.of_forall hKL)
    _ = _ := by
      rw [integral_sub hi hgi,
        setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz hv hval hψ hc hL hs,
        sub_neg_eq_add]

end SerrinEpigraph
