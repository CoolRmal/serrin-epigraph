module

public import SerrinEpigraph.PerimeterRadonPolar
public import SerrinEpigraph.UnitFieldApproximation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Localization of the perimeter representation

The representing measure charges no points outside the test region. Continuous unit tests
are controlled by the original smooth divergence supremum through support-preserving smoothing.
-/

public section

open MeasureTheory
open scoped Topology CompactlySupported

namespace SerrinEpigraph

/-- A distribution-gradient representation bounds local perimeter by local variation. -/
theorem variationalPerimeter_le_variation_of_representation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hΩ : MeasurableSet Ω) (σ : VectorMeasure (Space d) (Space d))
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ᵛ x, F x ∂[innerSL ℝ; σ]) :
    variationalPerimeter b E Ω ≤ σ.variation Ω := by
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
    iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
  let Fc : C_c(Space d, Space d) := ⟨⟨F, hF.continuous⟩, hc⟩
  have he := hdist Fc hF hs
  have hfi : Ω.indicator F = F := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
      simp [hx, hz]
  have hir : (∫ᵛ x, Fc x ∂[innerSL ℝ; σ]) =
      ∫ᵛ x, F x ∂[innerSL ℝ; σ.restrict Ω] := by
    change (∫ᵛ x, F x ∂[innerSL ℝ; σ]) = _
    nth_rw 1 [← hfi]
    exact VectorMeasure.integral_indicator hΩ
  have hb := enorm_vector_inner_integral_le_variation (σ.restrict Ω) hunit
  rw [VectorMeasure.variation_restrict hΩ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at hb
  change ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
    fieldDivergence b F x‖ ≤ σ.variation Ω
  rw [← norm_neg (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x)]
  change ENNReal.ofReal ‖-(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
    fieldDivergence b Fc x)‖ ≤ σ.variation Ω
  rw [he, hir, ofReal_norm]
  exact hb

/-- The constructed measure is concentrated on its measurable test region. -/
theorem exists_perimeter_vector_measure_concentrated {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hΩ : MeasurableSet Ω) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ σ : VectorMeasure (Space d) (Space d),
      σ.variation Set.univ = variationalPerimeter b E Ω ∧
      σ.variation Ω = variationalPerimeter b E Ω ∧ σ.variation Ωᶜ = 0 ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ Ω →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ᵛ x, F x ∂[innerSL ℝ; σ] := by
  obtain ⟨σ, hmass, hdist⟩ := exists_perimeter_vector_measure b hE hP
  have hlocal : σ.variation Ω = variationalPerimeter b E Ω :=
    le_antisymm ((measure_mono (Set.subset_univ Ω)).trans_eq hmass)
      (variationalPerimeter_le_variation_of_representation b hΩ σ hdist)
  have hc : σ.variation Ωᶜ = 0 := by
    have hsum := measure_add_measure_compl (μ := σ.variation) hΩ
    rw [hmass, hlocal] at hsum
    exact (ENNReal.add_right_inj hP).mp (by simpa using hsum)
  exact ⟨σ, hmass, hlocal, hc, hdist⟩

/-- The smooth divergence supremum also bounds every continuous compact unit vector test. -/
theorem continuous_vector_pairing_le_variationalPerimeter {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω U : Set (Space d)}
    (σ : VectorMeasure (Space d) (Space d)) [IsFiniteMeasure σ.variation]
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ᵛ x, F x ∂[innerSL ℝ; σ])
    (hU : U ⊆ Ω) {F : Space d → Space d} (hF : Continuous F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ U) (hu : ∀ x, ‖F x‖ ≤ 1) :
    ENNReal.ofReal ‖∫ᵛ x, F x ∂[innerSL ℝ; σ]‖ ≤ variationalPerimeter b E U := by
  by_cases hP : variationalPerimeter b E U = ⊤
  · simp [hP]
  obtain ⟨G, hG, hGu, hGs, hGt⟩ := exists_contDiff_unit_field_approx hF hu
  have ht := VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := σ) (B := innerSL ℝ) (fun _ : Space d ↦ (1 : ℝ))
    (fun j ↦ (hG j).continuous.aestronglyMeasurable) (integrable_const 1)
    (fun j ↦ Filter.Eventually.of_forall (hGu j)) (Filter.Eventually.of_forall hGt)
  apply (ENNReal.ofReal_le_iff_le_toReal hP).mpr
  apply le_of_tendsto ht.norm
  apply Filter.Eventually.of_forall
  intro j
  have hGc : HasCompactSupport (G j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (hGs j)
  let Gj : C_c(Space d, Space d) := ⟨⟨G j, (hG j).continuous⟩, hGc⟩
  have he := hdist Gj (hG j) ((hGs j).trans (hs.trans hU))
  apply (ENNReal.ofReal_le_iff_le_toReal hP).mp
  change ENNReal.ofReal ‖∫ᵛ x, Gj x ∂[innerSL ℝ; σ]‖ ≤ variationalPerimeter b E U
  rw [← he, norm_neg]
  exact le_iSup_of_le (G j) (le_iSup_of_le (hG j) (le_iSup_of_le hGc
    (le_iSup_of_le ((hGs j).trans hs) (le_iSup_of_le (hGu j) le_rfl))))

/-- Radial truncation to the closed Euclidean unit ball. -/
@[expose] noncomputable def perimeterUnitTrunc {d : ℕ} (v : Space d) : Space d :=
  (max 1 ‖v‖)⁻¹ • v

theorem continuous_perimeterUnitTrunc {d : ℕ} :
    Continuous (perimeterUnitTrunc (d := d)) := by
  change Continuous (fun v : Space d ↦ (max 1 ‖v‖)⁻¹ • v)
  exact ((continuous_const.max continuous_norm).inv₀
    (fun v ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖v‖)))).smul continuous_id

theorem norm_perimeterUnitTrunc_le {d : ℕ} (v : Space d) : ‖perimeterUnitTrunc v‖ ≤ 1 := by
  have hp : 0 < max 1 ‖v‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [perimeterUnitTrunc, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  calc
    (max 1 ‖v‖)⁻¹ * ‖v‖ ≤ (max 1 ‖v‖)⁻¹ * max 1 ‖v‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

/-- Truncation loses at most a factor two in distance from any vector in the unit ball. -/
theorem norm_sub_perimeterUnitTrunc_le {d : ℕ} (v w : Space d) (hv : ‖v‖ ≤ 1) :
    ‖v - perimeterUnitTrunc w‖ ≤ 2 * ‖v - w‖ := by
  by_cases hw : ‖w‖ ≤ 1
  · simp only [perimeterUnitTrunc, max_eq_left hw, inv_one, one_smul]
    linarith [norm_nonneg (v - w)]
  have hw1 : 1 < ‖w‖ := lt_of_not_ge hw
  have hw0 : 0 < ‖w‖ := zero_lt_one.trans hw1
  have hcoef : 0 ≤ 1 - ‖w‖⁻¹ := by
    have h := (inv_le_one₀ hw0).mpr hw1.le
    linarith
  have hdiff : ‖w - perimeterUnitTrunc w‖ = ‖w‖ - 1 := by
    rw [perimeterUnitTrunc, max_eq_right hw1.le,
      show w - ‖w‖⁻¹ • w = (1 - ‖w‖⁻¹) • w by rw [sub_smul, one_smul],
      norm_smul, Real.norm_of_nonneg hcoef, sub_mul, one_mul, inv_mul_cancel₀ hw0.ne']
  have hn := norm_sub_norm_le w v
  rw [norm_sub_rev w v] at hn
  calc
    ‖v - perimeterUnitTrunc w‖ ≤ ‖v - w‖ + ‖w - perimeterUnitTrunc w‖ :=
      by simpa only [sub_add_sub_cancel] using norm_add_le (v - w) (w - perimeterUnitTrunc w)
    _ = ‖v - w‖ + (‖w‖ - 1) := by rw [hdiff]
    _ ≤ 2 * ‖v - w‖ := by linarith

/-- Continuous unit tests recover the mass of every compact cutoff of a unit polar measure. -/
theorem integral_cutoff_le_of_unit_polar_tests {d : ℕ} {μ : Measure (Space d)}
    [IsFiniteMeasure μ] [μ.Regular] {ν : Space d → Space d} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) {U : Set (Space d)} {B : ℝ}
    (htest : ∀ F : Space d → Space d, Continuous F → HasCompactSupport F →
      tsupport F ⊆ U → (∀ x, ‖F x‖ ≤ 1) → ‖∫ x, inner ℝ (F x) (ν x) ∂μ‖ ≤ B)
    {χ : Space d → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) (hχv : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x, χ x ∂μ ≤ B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g, -, hgerr, hg, hgi⟩ :=
    hν.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  let F : Space d → Space d := fun x ↦ χ x • perimeterUnitTrunc (g x)
  have hFc : Continuous F := hχ.smul (continuous_perimeterUnitTrunc.comp hg)
  have hFs : tsupport F ⊆ tsupport χ := tsupport_smul_subset_left χ _
  have hFcomp : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport _) hFs
  have hFu (x : Space d) : ‖F x‖ ≤ 1 := by
    change ‖χ x • perimeterUnitTrunc (g x)‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (hχv x).1]
    exact (mul_le_mul_of_nonneg_left (norm_perimeterUnitTrunc_le (g x))
      (hχv x).1).trans (by simpa only [mul_one] using (hχv x).2)
  have hFi : Integrable (fun x ↦ inner ℝ (F x) (ν x)) μ := by
    apply hν.norm.mono' (hFc.aestronglyMeasurable.inner hν.aestronglyMeasurable)
    filter_upwards [] with x
    exact (norm_inner_le_norm _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hFu x) (norm_nonneg (ν x)))
  have herr : ∀ᵐ x ∂μ, χ x - inner ℝ (F x) (ν x) ≤ 2 * ‖ν x - g x‖ := by
    filter_upwards [hνunit] with x hx
    have hi := real_inner_le_norm (ν x - perimeterUnitTrunc (g x)) (ν x)
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one] at hi
    have hmul := mul_le_mul_of_nonneg_left hi (hχv x).1
    have hcut := mul_le_mul_of_nonneg_right (hχv x).2
      (norm_nonneg (ν x - perimeterUnitTrunc (g x)))
    have htrunc := norm_sub_perimeterUnitTrunc_le (ν x) (g x) hx.le
    change χ x - inner ℝ (χ x • perimeterUnitTrunc (g x)) (ν x) ≤ _
    rw [real_inner_smul_left]
    nlinarith
  have hχi := hχ.integrable_of_hasCompactSupport (μ := μ) hc
  have hErrI := (hν.sub hgi).norm.const_mul 2
  have hint := integral_mono_ae (hχi.sub hFi) hErrI herr
  change (∫ x, χ x - inner ℝ (F x) (ν x) ∂μ) ≤
    ∫ x, 2 * ‖ν x - g x‖ ∂μ at hint
  rw [integral_sub hχi hFi, integral_const_mul] at hint
  have hpair := htest F hFc hFcomp (hFs.trans hs) hFu
  have hpair' : (∫ x, inner ℝ (F x) (ν x) ∂μ) ≤ B :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hpair)
  linarith

/-- Compact cutoffs and regularity recover the full mass of an open set from polar tests. -/
theorem measure_open_le_of_unit_polar_tests {d : ℕ} {μ : Measure (Space d)}
    [IsFiniteMeasure μ] [μ.Regular] {ν : Space d → Space d} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) {U : Set (Space d)} (hU : IsOpen U) {B : ℝ}
    (htest : ∀ F : Space d → Space d, Continuous F → HasCompactSupport F →
      tsupport F ⊆ U → (∀ x, ‖F x‖ ≤ 1) → ‖∫ x, inner ℝ (F x) (ν x) ∂μ‖ ≤ B) :
    μ U ≤ ENNReal.ofReal B := by
  rw [hU.measure_eq_iSup_isCompact]
  refine iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦ ?_
  obtain ⟨χ, hχK, hχc, hχs, hχv⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hcut := integral_cutoff_le_of_unit_polar_tests hν hνunit htest
    χ.continuous hχc hχs hχv
  have hχi := χ.continuous.integrable_of_hasCompactSupport (μ := μ) hχc
  have hle := setIntegral_le_integral (s := K) hχi
    (Filter.Eventually.of_forall fun x ↦ (hχv x).1)
  have he : (∫ x in K, χ x ∂μ) = (μ K).toReal := by
    calc
      (∫ x in K, χ x ∂μ) = ∫ _ in K, (1 : ℝ) ∂μ :=
        setIntegral_congr_fun hK.measurableSet (fun x hx ↦ hχK hx)
      _ = (μ K).toReal := by simp [Measure.real]
  rw [he] at hle
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ K)]
  exact ENNReal.ofReal_le_ofReal (hle.trans hcut)

/-- On every open subregion the Euclidean variation is exactly the original perimeter,
not merely bounded by its total mass. -/
theorem variation_eq_variationalPerimeter_of_representation {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω U : Set (Space d)}
    (σ : VectorMeasure (Space d) (Space d)) [IsFiniteMeasure σ.variation]
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ᵛ x, F x ∂[innerSL ℝ; σ])
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) :
    σ.variation U = variationalPerimeter b E U := by
  apply le_antisymm
  · by_cases hP : variationalPerimeter b E U = ⊤
    · simp [hP]
    have hi := integrable_vectorPolarDensity b σ
    have hn := norm_vectorPolarDensity_ae b σ
    have hb : σ.variation U ≤ ENNReal.ofReal (variationalPerimeter b E U).toReal := by
      apply measure_open_le_of_unit_polar_tests hi hn hU
      intro F hF hc hs hu
      have he : (∫ᵛ x, F x ∂[innerSL ℝ; σ]) =
          ∫ x, inner ℝ (F x) (vectorPolarDensity b σ x) ∂σ.variation := by
        nth_rw 1 [← withDensity_vectorPolarDensity b σ]
        exact integral_withDensity_inner_of_ae_bounded hi (hn.mono fun _ h ↦ h.le)
          hF.measurable zero_le_one hu
      have hp := continuous_vector_pairing_le_variationalPerimeter b σ hdist hUΩ hF hc hs hu
      rw [he] at hp
      exact (ENNReal.ofReal_le_iff_le_toReal hP).mp hp
    exact hb.trans_eq (ENNReal.ofReal_toReal hP)
  · exact variationalPerimeter_le_variation_of_representation b hU.measurableSet σ
      (fun F hF hs ↦ hdist F hF (hs.trans hUΩ))

/-- The full finite-region perimeter–Radon bridge: an actual regular measure, its unit polar
vector, exact values on all open subregions, and the distributional gradient identity. -/
theorem exists_localized_perimeter_polar_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ (μ : Measure (Space d)) (ν : Space d → Space d),
      IsFiniteMeasure μ ∧ μ.Regular ∧ μ Set.univ = variationalPerimeter b E Ω ∧
      (∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U) ∧
      Integrable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ Ω →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν x) ∂μ := by
  obtain ⟨σ, hmass, hdist⟩ := exists_perimeter_vector_measure b hE hP
  let : IsFiniteMeasure σ.variation := ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hP⟩
  have hi := integrable_vectorPolarDensity b σ
  have hn := norm_vectorPolarDensity_ae b σ
  refine ⟨σ.variation, vectorPolarDensity b σ, inferInstance, inferInstance, hmass,
    (fun U hU hs ↦ variation_eq_variationalPerimeter_of_representation b σ hdist hU hs),
    hi, hn, ?_⟩
  intro F hF hs
  refine (hdist F hF hs).trans ?_
  nth_rw 1 [← withDensity_vectorPolarDensity b σ]
  exact integral_withDensity_inner_of_ae_bounded hi (hn.mono fun _ h ↦ h.le)
    F.continuous.measurable (norm_nonneg F.toBoundedContinuousFunction)
    F.toBoundedContinuousFunction.norm_coe_le_norm

end SerrinEpigraph
