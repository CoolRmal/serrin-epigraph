module

public import SerrinEpigraph.PhysicalTranslationInequality
public import SerrinEpigraph.MollificationSupport

/-!
# Compact Lipschitz tests for a bounded weak inequality

Smoothing a nonnegative compact Lipschitz test preserves its sign. Uniform
support and gradient bounds allow passage to the limit in the weak residual.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- A bounded measurable flux paired with a compact Lipschitz test is integrable. -/
theorem integrable_weak_residual_of_locallyLipschitz_test
    {d : ℕ} {q : Space d → Space d} {a ψ : Space d → ℝ}
    (hq : Measurable q) (ha : Measurable a) {Q A : ℝ}
    (hQ : ∀ x, ‖q x‖ ≤ Q) (hA : ∀ x, ‖a x‖ ≤ A)
    (hψ : LocallyLipschitz ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x ↦ inner ℝ (q x) (gradient ψ x) - a x * ψ x) := by
  obtain ⟨C, hC⟩ := gradient_bound_of_locallyLipschitz hψ hc
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hi : IntegrableOn (fun x ↦ inner ℝ (q x) (gradient ψ x) - a x * ψ x)
      (tsupport ψ) := by
    apply (continuousOn_const.integrableOn_compact hc
      (f := fun _ : Space d ↦ Q * C + A * B)).mono'
      ((hq.inner (𝕜 := ℝ) (measurable_gradient _)).sub
        (ha.mul hψ.continuous.measurable)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (isClosed_tsupport ψ).measurableSet] with x hx
    apply (norm_sub_le _ _).trans
    apply add_le_add
    · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hQ x) (hC x hx) (norm_nonneg _)
          ((norm_nonneg _).trans (hQ x)))
    · change ‖a x * ψ x‖ ≤ A * B
      rw [norm_mul]
      exact mul_le_mul (hA x) (hB x) (norm_nonneg _) ((norm_nonneg _).trans (hA x))
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]

/-- A bounded measurable weak flux can be tested against compact nonnegative
locally Lipschitz functions, with their actual almost-everywhere derivatives. -/
theorem integral_weak_residual_nonpos_of_locallyLipschitz_test
    {d : ℕ} {q : Space d → Space d} {a ψ : Space d → ℝ}
    (hq : Measurable q) (ha : Measurable a) {Q A : ℝ}
    (hQ : ∀ x, ‖q x‖ ≤ Q) (hA : ∀ x, ‖a x‖ ≤ A)
    (hweak : ∀ φ : Space d → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → (∫ x, inner ℝ (q x) (gradient φ x) - a x * φ x) ≤ 0)
    (hψ : LocallyLipschitz ψ) (hc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    (∫ x, inner ℝ (q x) (gradient ψ x) - a x * ψ x) ≤ 0 := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : Space d)
  let K := closedBall (0 : Space d) (R + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hψK : tsupport ψ ⊆ K := hR.trans (closedBall_subset_closedBall (by linarith))
  have hmK (j : ℕ) : tsupport (normalizedMollify ψ j) ⊆ K :=
    normalizedMollify_tsupport_subset hR j
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hval (x : Space d) : ψ x ∈ Icc 0 B :=
    ⟨hψ0 x, (le_abs_self _).trans (hB x)⟩
  have hmval (j : ℕ) (x : Space d) :=
    normalizedMollify_mem_Icc_of_bounds hψ.continuous hval j x
  obtain ⟨C, hC⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hψ hK
  have hlim : Tendsto (fun j ↦ ∫ x in K,
      inner ℝ (q x) (gradient (normalizedMollify ψ j) x) -
        a x * normalizedMollify ψ j x) atTop
      (𝓝 (∫ x in K, inner ℝ (q x) (gradient ψ x) - a x * ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ Q * C + A * B)
    · intro j
      exact ((hq.inner (𝕜 := ℝ) (measurable_gradient _)).sub
        (ha.mul (normalizedMollify_contDiff hψ.continuous j).continuous.measurable)).aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro j
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      apply (norm_sub_le _ _).trans
      apply add_le_add
      · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hQ x) (hC j x hx) (norm_nonneg _)
            ((norm_nonneg _).trans (hQ x)))
      · rw [norm_mul, Real.norm_of_nonneg (hmval j x).1]
        exact mul_le_mul (hA x) (hmval j x).2 (hmval j x).1
          ((norm_nonneg _).trans (hA x))
    · filter_upwards [ae_restrict_of_ae
        (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hψ)] with x hx
      exact (tendsto_const_nhds.inner hx).sub
        (tendsto_const_nhds.mul (normalizedMollify_tendsto hψ.continuous x))
  have hnonpos (j : ℕ) : (∫ x in K,
      inner ℝ (q x) (gradient (normalizedMollify ψ j) x) -
        a x * normalizedMollify ψ j x) ≤ 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hn : x ∉ tsupport (normalizedMollify ψ j) := fun hh ↦ hx (hmK j hh)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn])]
    exact hweak _ ((normalizedMollify_contDiff hψ.continuous j).of_le (by simp))
      (hK.of_isClosed_subset (isClosed_tsupport _) (hmK j)) (fun x ↦ (hmval j x).1)
  have hle := le_of_tendsto' hlim hnonpos
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
    have hn : x ∉ tsupport ψ := fun hh ↦ hx (hψK hh)
    simp [gradient, fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn])] at hle

/-- The limiting boundary inequality permits actual compact Lipschitz tests,
including truncations and differences of two translation limits. -/
theorem RigidityHypotheses.physical_translation_limit_lipschitz_test
    {m : ℕ} {g : Space m → ℝ} {u V ψ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} {L : NNReal} (hV : LipschitzWith L V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ x, Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝 (V x)))
    (hψ : LocallyLipschitz ψ) (hc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    (∫ x, inner ℝ (gradient V x) (gradient ψ x) - f (V x) * ψ x) ≤ 0 := by
  have hf : Continuous (fun x ↦ f (V x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hV.continuous (fun x ↦ (hval x).1)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hgrad (x : Space (m + 1)) : ‖gradient V x‖ ≤ L := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      norm_fderiv_le_of_lipschitz ℝ hV (x₀ := x)
  apply integral_weak_residual_nonpos_of_locallyLipschitz_test (measurable_gradient V)
    hf.measurable hgrad (fun x ↦ hA _ (hval x)) ?_ hψ hc hψ0
  intro φ hφ hcφ hφ0
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have his : Integrable (fun x ↦ f (V x) * φ x) :=
    (hf.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left
  have hig : Integrable (fun x ↦ inner ℝ (gradient V x) (gradient φ x)) := by
    have hi := integrable_weak_residual_of_locallyLipschitz_test (measurable_gradient V)
      (measurable_const (a := (0 : ℝ))) hgrad (fun _ ↦ le_rfl)
      hφ1.locallyLipschitz hcφ
    simpa using hi
  have hi := hr.physical_translation_limit_distributional_inequality h hval hlim hφ hcφ hφ0
  rw [integral_mul_laplacian_eq_neg_inner_gradient_of_locallyLipschitz
    hV.locallyLipschitz hval hφ hcφ] at hi
  rw [integral_sub hig his]
  linarith

end SerrinEpigraph
