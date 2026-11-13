module

public import SerrinEpigraph.GraphPerimeterLower
public import SerrinEpigraph.SharpDivergenceBound
public import Mathlib.Topology.UrysohnsLemma

/-!
# Gradient mass controlled by divergence tests
-/

public section

noncomputable section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- A bound for smooth divergence tests also bounds pairing the gradient with
continuous compact unit fields. -/
theorem norm_integral_gradient_inner_le_of_divergence_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {Ω : Set (Space d)} {B : ℝ}
    (htest : ∀ F : Space d → Space d, ContDiff ℝ 1 F → HasCompactSupport F →
      tsupport F ⊆ Ω → (∀ x, ‖F x‖ ≤ 1) → ‖∫ x, v x * fieldDivergence b F x‖ ≤ B)
    {F : Space d → Space d} (hF : Continuous F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ Ω) (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x, inner ℝ (gradient v x) (F x)‖ ≤ B := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  obtain ⟨G, hG, hGu, hGs, hGt⟩ := exists_contDiff_unit_field_approx hF hunit
  have heF : (∫ x in tsupport F, inner ℝ (gradient v x) (F x)) =
      ∫ x, inner ℝ (gradient v x) (F x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  have heG (j : ℕ) : (∫ x in tsupport F, inner ℝ (gradient v x) (G j x)) =
      ∫ x, inner ℝ (gradient v x) (G j x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hGs j hh)), inner_zero_right]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict (tsupport F))
    (F := fun j x ↦ inner ℝ (gradient v x) (G j x))
    (f := fun x ↦ inner ℝ (gradient v x) (F x)) (fun x ↦ ‖gradient v x‖)
    (fun j ↦ (hg.inner (hG j).continuous).aestronglyMeasurable)
    (hg.norm.continuousOn.integrableOn_compact hc)
    (fun j ↦ Eventually.of_forall (fun x ↦
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hGu j x))))
    (Eventually.of_forall (fun x ↦ tendsto_const_nhds.inner (hGt x)))
  simp only [heG, heF] at ht
  apply le_of_tendsto ht.norm
  apply Eventually.of_forall
  intro j
  have hcG : HasCompactSupport (G j) := hc.of_isClosed_subset (isClosed_tsupport _) (hGs j)
  have heD : (∫ x in tsupport F, v x * fieldDivergence b (G j) x) =
      ∫ x, v x * fieldDivergence b (G j) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fieldDivergence_zero_of_notMem_tsupport b (G j) (fun hh ↦ hx (hGs j hh)), mul_zero]
  have he := setIntegral_mul_divergence_eq_neg_inner b hv (hG j) hcG hc (hGs j)
  rw [heD, heG] at he
  have hb := htest (G j) (hG j) hcG ((hGs j).trans hs) (hGu j)
  rwa [he, norm_neg] at hb

/-- Every compact cutoff gives a weighted gradient-mass lower bound for the
supremum of smooth unit divergence tests. -/
theorem integral_cutoff_gradient_le_of_divergence_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {Ω : Set (Space d)} {B : ℝ}
    (htest : ∀ F : Space d → Space d, ContDiff ℝ 1 F → HasCompactSupport F →
      tsupport F ⊆ Ω → (∀ x, ‖F x‖ ≤ 1) → ‖∫ x, v x * fieldDivergence b F x‖ ≤ B)
    {χ : Space d → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω) (hval : ∀ x, χ x ∈ Icc (0 : ℝ) 1) :
    (∫ x, χ x * ‖gradient v x‖) ≤ B := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F := fun j x ↦ (χ x / (‖gradient v x‖ + ε j)) • gradient v x
  have hden (j : ℕ) (x : Space d) : 0 < ‖gradient v x‖ + ε j :=
    add_pos_of_nonneg_of_pos (norm_nonneg _) (hε j)
  have hF (j : ℕ) : Continuous (F j) :=
    (hχ.div (hg.norm.add continuous_const) (fun x ↦ (hden j x).ne')).smul hg
  have hFs (j : ℕ) : tsupport (F j) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp only [F, hz, zero_div, zero_smul])
  have hFc (j : ℕ) : HasCompactSupport (F j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (hFs j)
  have hunit (j : ℕ) (x : Space d) : ‖F j x‖ ≤ 1 := by
    rw [show F j x = (χ x / (‖gradient v x‖ + ε j)) • gradient v x from rfl,
      norm_smul, Real.norm_of_nonneg (div_nonneg (hval x).1 (hden j x).le)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (hden j x)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans (by linarith [hε j])
  have he (j : ℕ) (x : Space d) : inner ℝ (gradient v x) (F j x) =
      χ x * ‖gradient v x‖ ^ 2 / (‖gradient v x‖ + ε j) := by
    simp only [F, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hpair (x : Space d) : Tendsto (fun j ↦ inner ℝ (gradient v x) (F j x))
      atTop (𝓝 (χ x * ‖gradient v x‖)) := by
    simp only [he]
    by_cases hz : ‖gradient v x‖ = 0
    · simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_div]
      exact tendsto_const_nhds
    · have ht := (tendsto_const_nhds (x := χ x * ‖gradient v x‖ ^ 2)).div
        ((tendsto_const_nhds (x := ‖gradient v x‖)).add hεt) (by simpa only [add_zero] using hz)
      convert ht using 1
      simp only [add_zero]
      field_simp
  have heF (j : ℕ) : (∫ x in tsupport χ, inner ℝ (gradient v x) (F j x)) =
      ∫ x, inner ℝ (gradient v x) (F j x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hFs j hh)), inner_zero_right]
  have heχ : (∫ x in tsupport χ, χ x * ‖gradient v x‖) =
      ∫ x, χ x * ‖gradient v x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict (tsupport χ))
    (F := fun j x ↦ inner ℝ (gradient v x) (F j x))
    (f := fun x ↦ χ x * ‖gradient v x‖) (fun x ↦ ‖gradient v x‖)
    (fun j ↦ (hg.inner (hF j)).aestronglyMeasurable)
    (hg.norm.continuousOn.integrableOn_compact hc)
    (fun j ↦ Eventually.of_forall (fun x ↦
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hunit j x))))
    (Eventually.of_forall hpair)
  simp only [heF, heχ] at ht
  apply le_of_tendsto ht
  exact Eventually.of_forall (fun j ↦ (Real.le_norm_self _).trans
    (norm_integral_gradient_inner_le_of_divergence_bound b hv htest (hF j) (hFc j)
      ((hFs j).trans hs) (hunit j)))

/-- Smooth unit divergence tests control gradient mass on every compact subset
of the open test domain. -/
theorem compact_integral_gradient_le_of_divergence_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {Ω : Set (Space d)} (hΩ : IsOpen Ω) {B : ℝ}
    (htest : ∀ F : Space d → Space d, ContDiff ℝ 1 F → HasCompactSupport F →
      tsupport F ⊆ Ω → (∀ x, ‖F x‖ ≤ 1) → ‖∫ x, v x * fieldDivergence b F x‖ ≤ B)
    {K : Set (Space d)} (hK : IsCompact K) (hs : K ⊆ Ω) :
    (∫ x in K, ‖gradient v x‖) ≤ B := by
  obtain ⟨χ, hχK, hc, hχs, hχval⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hΩ hs
  have hcc : HasCompactSupport (χ : Space d → ℝ) := hc
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hi : Integrable (fun x ↦ χ x * ‖gradient v x‖) :=
    (χ.continuous.mul hg.norm).integrable_of_hasCompactSupport hcc.mul_right
  have he : (∫ x in K, ‖gradient v x‖) = ∫ x in K, χ x * ‖gradient v x‖ := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    dsimp only
    rw [hχK hx]
    simp
  rw [he]
  exact (setIntegral_le_integral hi (Eventually.of_forall
    (fun x ↦ mul_nonneg (hχval x).1 (norm_nonneg _)))).trans
    (integral_cutoff_gradient_le_of_divergence_bound b hv htest χ.continuous hc hχs hχval)

/-- Inner regularity converts compact gradient-mass bounds into a bound on
the whole open test domain. -/
theorem lintegral_gradient_le_of_divergence_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {Ω : Set (Space d)} (hΩ : IsOpen Ω) {B : ℝ}
    (htest : ∀ F : Space d → Space d, ContDiff ℝ 1 F → HasCompactSupport F →
      tsupport F ⊆ Ω → (∀ x, ‖F x‖ ≤ 1) → ‖∫ x, v x * fieldDivergence b F x‖ ≤ B) :
    (∫⁻ x in Ω, ENNReal.ofReal ‖gradient v x‖) ≤ ENNReal.ofReal B := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  let μ := volume.withDensity (fun x ↦ ENNReal.ofReal ‖gradient v x‖)
  have : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_ofReal hg.norm
  rw [← withDensity_apply _ hΩ.measurableSet]
  change μ Ω ≤ _
  rw [hΩ.measure_eq_iSup_isCompact μ]
  refine iSup_le (fun K ↦ iSup_le (fun hKΩ ↦ iSup_le (fun hK ↦ ?_)))
  change volume.withDensity (fun x ↦ ENNReal.ofReal ‖gradient v x‖) K ≤ _
  rw [withDensity_apply _ hK.measurableSet, ← ofReal_integral_eq_lintegral_ofReal
    (hg.norm.continuousOn.integrableOn_compact hK)
    (Eventually.of_forall (fun x ↦ norm_nonneg _))]
  exact ENNReal.ofReal_le_ofReal
    (compact_integral_gradient_le_of_divergence_bound b hv hΩ htest hK hKΩ)

end SerrinEpigraph
