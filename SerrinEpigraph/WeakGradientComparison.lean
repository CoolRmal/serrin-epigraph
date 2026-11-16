module

public import SerrinEpigraph.WeakLipschitzTest

/-!
# Comparing gradients of uniformly close weak subsolutions

The nonnegative tests formed from a small constant plus or minus the difference
give a direct local energy estimate. It remains valid at the free boundaries.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The pointwise algebra behind the two nonnegative comparison tests. -/
theorem gradient_comparison_pointwise {d : ℕ} (q r G : Space d)
    {a b η δ t₁ t₂ L A D : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hq : ‖q‖ ≤ L) (hr : ‖r‖ ≤ L) (hG : ‖G‖ ≤ D)
    (ha : |a| ≤ A) (hb : |b| ≤ A) (hη : η ∈ Icc 0 1)
    (ht₁ : t₁ ∈ Icc 0 (2 * δ)) (ht₂ : t₂ ∈ Icc 0 (2 * δ)) :
    η * ‖q - r‖ ^ 2 ≤
      (inner ℝ q (η • (q - r) + t₁ • G) - a * (t₁ * η)) +
      (inner ℝ r (η • (r - q) + t₂ • G) - b * (t₂ * η)) +
      4 * δ * (L * D + A) := by
  have hqG : |inner ℝ q G| ≤ L * D :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hq hG (norm_nonneg _) hL)
  have hrG : |inner ℝ r G| ≤ L * D :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hr hG (norm_nonneg _) hL)
  have hbound (c t : ℝ) (hc : |c| ≤ L * D) (ht : t ∈ Icc 0 (2 * δ)) :
      -(2 * δ * (L * D)) ≤ t * c := by
    have hc' : -(L * D) ≤ c := (abs_le.mp hc).1
    have hh := mul_le_mul_of_nonneg_left hc' ht.1
    have hu := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hL hD)
    nlinarith
  have hsource (c t : ℝ) (hc : |c| ≤ A) (ht : t ∈ Icc 0 (2 * δ)) :
      c * (t * η) ≤ 2 * δ * A := by
    have hct : c * (t * η) ≤ A * (t * η) :=
      mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) hc) (mul_nonneg ht.1 hη.1)
    have htη : t * η ≤ 2 * δ :=
      (mul_le_of_le_one_right ht.1 hη.2).trans ht.2
    nlinarith [mul_le_mul_of_nonneg_left htη hA]
  have h₁ := hbound _ _ hqG ht₁
  have h₂ := hbound _ _ hrG ht₂
  have h₃ := hsource _ _ ha ht₁
  have h₄ := hsource _ _ hb ht₂
  simp only [inner_add_right, real_inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_sub_sq_real]
  rw [real_inner_comm r q]
  nlinarith

/-- Uniform closeness controls the local squared gradient difference of two
bounded-flux subsolutions, even across their free boundaries. -/
theorem integral_gradient_sub_sq_le_of_weak_inequalities
    {d : ℕ} {v w a b φ : Space d → ℝ} {L : NNReal} {A D δ : ℝ}
    (hv : LipschitzWith L v) (hw : LipschitzWith L w)
    (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ x, ‖a x‖ ≤ A) (hB : ∀ x, ‖b x‖ ≤ A) (hD : 0 ≤ D)
    (hweakv : ∀ ψ : Space d → ℝ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → (∫ x, inner ℝ (gradient v x) (gradient ψ x) - a x * ψ x) ≤ 0)
    (hweakw : ∀ ψ : Space d → ℝ, LocallyLipschitz ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → (∫ x, inner ℝ (gradient w x) (gradient ψ x) - b x * ψ x) ≤ 0)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφval : ∀ x, φ x ∈ Icc 0 1)
    (hφgrad : ∀ x, ‖gradient φ x‖ ≤ D)
    (hclose : ∀ x ∈ tsupport φ, |v x - w x| ≤ δ) :
    (∫ x in tsupport φ, φ x * ‖gradient v x - gradient w x‖ ^ 2) ≤
      4 * δ * ((L : ℝ) * D + A) * volume.real (tsupport φ) := by
  let ψv := fun x ↦ (v x - w x + δ) * φ x
  let ψw := fun x ↦ (w x - v x + δ) * φ x
  have hmul : LocallyLipschitz (fun p : ℝ × ℝ ↦ p.1 * p.2) :=
    (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 _).locallyLipschitz
  have hlv : LocallyLipschitz ψv := hmul.comp
    (((hv.locallyLipschitz.sub hw.locallyLipschitz).add (LocallyLipschitz.const δ)).prodMk
      hφ.locallyLipschitz)
  have hlw : LocallyLipschitz ψw := hmul.comp
    (((hw.locallyLipschitz.sub hv.locallyLipschitz).add (LocallyLipschitz.const δ)).prodMk
      hφ.locallyLipschitz)
  have hcv : HasCompactSupport ψv := hc.mul_left
  have hcw : HasCompactSupport ψw := hc.mul_left
  have hn (x : Space d) : 0 ≤ ψv x ∧ 0 ≤ ψw x := by
    by_cases hx : x ∈ tsupport φ
    · have hh := abs_le.mp (hclose x hx)
      exact ⟨mul_nonneg (by linarith) (hφval x).1,
        mul_nonneg (by linarith) (hφval x).1⟩
    · simp [ψv, ψw, image_eq_zero_of_notMem_tsupport hx]
  have hgv (x : Space d) : ‖gradient v x‖ ≤ L := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      norm_fderiv_le_of_lipschitz ℝ hv (x₀ := x)
  have hgw (x : Space d) : ‖gradient w x‖ ≤ L := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      norm_fderiv_le_of_lipschitz ℝ hw (x₀ := x)
  let Rv := fun x ↦ inner ℝ (gradient v x) (gradient ψv x) - a x * ψv x
  let Rw := fun x ↦ inner ℝ (gradient w x) (gradient ψw x) - b x * ψw x
  have hiv : Integrable Rv := integrable_weak_residual_of_locallyLipschitz_test
    (measurable_gradient v) ha hgv hA hlv hcv
  have hiw : Integrable Rw := integrable_weak_residual_of_locallyLipschitz_test
    (measurable_gradient w) hb hgw hB hlw hcw
  have hzv (x : Space d) (hx : x ∉ tsupport φ) : Rv x = 0 := by
    have hn' : x ∉ tsupport ψv := fun hh ↦ hx (tsupport_mul_subset_right hh)
    simp [Rv, gradient, fderiv_of_notMem_tsupport ℝ hn', image_eq_zero_of_notMem_tsupport hn']
  have hzw (x : Space d) (hx : x ∉ tsupport φ) : Rw x = 0 := by
    have hn' : x ∉ tsupport ψw := fun hh ↦ hx (tsupport_mul_subset_right hh)
    simp [Rw, gradient, fderiv_of_notMem_tsupport ℝ hn', image_eq_zero_of_notMem_tsupport hn']
  have hiv0 : (∫ x in tsupport φ, Rv x) ≤ 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzv]
    exact hweakv _ hlv hcv (fun x ↦ (hn x).1)
  have hiw0 : (∫ x in tsupport φ, Rw x) ≤ 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzw]
    exact hweakw _ hlw hcw (fun x ↦ (hn x).2)
  have hiE : IntegrableOn (fun x ↦ φ x * ‖gradient v x - gradient w x‖ ^ 2)
      (tsupport φ) := by
    apply (continuousOn_const.integrableOn_compact hc
      (f := fun _ : Space d ↦ (2 * (L : ℝ)) ^ 2)).mono'
      (hφ.continuous.measurable.mul
        (((measurable_gradient v).sub (measurable_gradient w)).norm.pow_const 2)).aestronglyMeasurable
    filter_upwards with x
    change ‖φ x * ‖gradient v x - gradient w x‖ ^ 2‖ ≤ (2 * (L : ℝ)) ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (hφval x).1 (sq_nonneg _))]
    apply (mul_le_of_le_one_left (sq_nonneg _) (hφval x).2).trans
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by linarith [hgv x, hgw x])
  have hiC : IntegrableOn (fun _ : Space d ↦ 4 * δ * ((L : ℝ) * D + A))
      (tsupport φ) := continuousOn_const.integrableOn_compact hc
  have hineq : ∀ᵐ x ∂volume.restrict (tsupport φ),
      φ x * ‖gradient v x - gradient w x‖ ^ 2 ≤
        Rv x + Rw x + 4 * δ * ((L : ℝ) * D + A) := by
    filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet,
      ae_restrict_of_ae hv.ae_differentiableAt, ae_restrict_of_ae hw.ae_differentiableAt]
      with x hx hvx hwx
    have hgrad₁ : gradient ψv x =
        φ x • (gradient v x - gradient w x) + (v x - w x + δ) • gradient φ x := by
      rw [gradient_mul_at (v := fun y ↦ v y - w y + δ)
        ((hvx.sub hwx).add_const δ) (hφ.differentiable_one x)]
      simp only [gradient, fderiv_add_const, fderiv_fun_sub hvx hwx, map_sub]
    have hgrad₂ : gradient ψw x =
        φ x • (gradient w x - gradient v x) + (w x - v x + δ) • gradient φ x := by
      rw [gradient_mul_at (v := fun y ↦ w y - v y + δ)
        ((hwx.sub hvx).add_const δ) (hφ.differentiable_one x)]
      simp only [gradient, fderiv_add_const, fderiv_fun_sub hwx hvx, map_sub]
    dsimp only [Rv, Rw]
    rw [hgrad₁, hgrad₂]
    have ht := abs_le.mp (hclose x hx)
    exact gradient_comparison_pointwise _ _ _ L.coe_nonneg
      ((norm_nonneg _).trans (hA x)) hD (hgv x) (hgw x) (hφgrad x)
      (hA x) (hB x) (hφval x) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hi := integral_mono_ae hiE ((hiv.integrableOn.add hiw.integrableOn).add hiC) hineq
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun x ↦ Rv x + Rw x) (hiv.integrableOn.add hiw.integrableOn) hiC,
    integral_add hiv.integrableOn hiw.integrableOn, integral_const] at hi
  simp only [Measure.real, smul_eq_mul, Measure.restrict_apply_univ] at hi ⊢
  nlinarith

end SerrinEpigraph
