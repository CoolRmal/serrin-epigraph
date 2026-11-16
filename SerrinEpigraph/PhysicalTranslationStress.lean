module

public import SerrinEpigraph.PhysicalTranslationEnergyLimit
public import SerrinEpigraph.MollificationDuality

/-!
# Spatial stationarity of physical translation limits

The actual energy and quadratic gradient flux converge strongly. Consequently
the stress identity passes across the limiting free boundary.
-/

public section

noncomputable section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Spatial stationarity written on the whole space for the zero extension. -/
theorem RigidityHypotheses.integral_zeroExtension_stress_stationarity
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    (∫ x, phaseEnergyDensity f 0 (zeroExtension g u) x * fieldDivergence basis X x -
      inner ℝ (gradient (zeroExtension g u) x) (fderiv ℝ X x (gradient (zeroExtension g u) x))) = 0 := by
  have he : (fun x ↦ phaseEnergyDensity f 0 (zeroExtension g u) x * fieldDivergence basis X x -
        inner ℝ (gradient (zeroExtension g u) x) (fderiv ℝ X x (gradient (zeroExtension g u) x))) =
      (epigraph g).indicator (fun x ↦
        (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * fieldDivergence basis X x -
          inner ℝ (gradient u x) (fderiv ℝ X x (gradient u x))) := by
    funext x
    by_cases hx : x ∈ epigraph g
    · simp only [phaseEnergyDensity, indicator_of_mem hx,
        indicator_of_mem (s := {y | 0 < zeroExtension g u y}) ((h.zeroExtension_pos_iff x).mpr hx),
        h.gradient_zeroExtension hx, zeroExtension_of_mem hx, add_zero]
    · have hp : ¬0 < zeroExtension g u x := by rw [zeroExtension_of_notMem hx]; exact lt_irrefl 0
      simp [phaseEnergyDensity, indicator_of_notMem hx,
        indicator_of_notMem (s := {y | 0 < zeroExtension g u y}) hp,
        h.gradient_zeroExtension_of_notMem hx]
  rw [he, integral_indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
  exact hr.integral_stress_stationarity h basis hX hc

/-- The energy density commutes with translation, including its phase set. -/
theorem phaseEnergyDensity_comp_add_left {d : ℕ} (f : ℝ → ℝ) (v : Space d → ℝ)
    (c : ℝ) (p x : Space d) :
    phaseEnergyDensity f c (fun y ↦ v (p + y)) x = phaseEnergyDensity f c v (p + x) := by
  simp only [phaseEnergyDensity, indicator_apply, mem_ofPred_eq, gradient, fderiv_comp_add_left]

/-- Physical translates retain exact spatial stationarity. -/
theorem RigidityHypotheses.translated_zeroExtension_stress_stationarity
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (p : Space (m + 1))
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    (∫ x, phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p + y)) x * fieldDivergence basis X x -
      inner ℝ (gradient (zeroExtension g u) (p + x))
        (fderiv ℝ X x (gradient (zeroExtension g u) (p + x)))) = 0 := by
  let Y := fun x ↦ X (x + -p)
  have hY : ContDiff ℝ 1 Y := hX.comp (contDiff_id.add contDiff_const)
  have hcY : HasCompactSupport Y :=
    hc.comp_isClosedEmbedding (isometry_add_right (-p)).isClosedEmbedding
  have hi := hr.integral_zeroExtension_stress_stationarity h basis hY hcY
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x ↦ phaseEnergyDensity f 0 (zeroExtension g u) x * fieldDivergence basis Y x -
      inner ℝ (gradient (zeroExtension g u) x) (fderiv ℝ Y x (gradient (zeroExtension g u) x))) p
  rw [← ht] at hi
  simp only [Y, fieldDivergence_translate basis hX, fderiv_comp_add_right,
    add_neg_cancel_right] at hi
  simpa only [phaseEnergyDensity_comp_add_left, add_comm] using hi

/-- Physical translation limits retain the complete stress identity, with
the actual limiting phase and actual limiting gradient. -/
theorem RigidityHypotheses.physical_translation_limit_stress_stationarity
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    (∫ x, phaseEnergyDensity f 0 V x * fieldDivergence basis X x -
      inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) = 0 := by
  let U := fun j x ↦ zeroExtension g u (p j + x)
  let q := fun j x ↦ gradient (zeroExtension g u) (p j + x)
  let Q := fun r : Space (m + 1) → Space (m + 1) ↦
    fun x ↦ inner ℝ (r x) (fderiv ℝ X x (r x))
  have hDX := hX.continuous_fderiv one_ne_zero
  obtain ⟨D, hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hDX
  have hdiv := fieldDivergence_continuous basis hX
  have hcdiv : HasCompactSupport (fieldDivergence basis X) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport X)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport basis X hn)
  obtain ⟨C, hC⟩ := hcdiv.exists_bound_of_continuous hdiv
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    h.zeroExtension_locallyLipschitz.comp (isometry_add_left (p j)).lipschitzWith.locallyLipschitz
  have hUv (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hiE (j : ℕ) := h.integrableOn_lipschitz_phaseEnergy (hU j) (hUv j) 0 hc
  have hiV := h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0 hc
  have hq (j : ℕ) : Measurable (q j) :=
    (measurable_gradient _).comp (continuous_const.add continuous_id).measurable
  have hqbound (j : ℕ) (x : Space (m + 1)) : ‖q j x‖ ≤ κ :=
    hr.gradient_zeroExtension_norm_le_kappa h _
  have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hV
  have hiQ (j : ℕ) : IntegrableOn (Q (q j)) (tsupport X) :=
    integrableOn_inner_linear_of_bounds (hq j) hDX (hqbound j) hD hc
  have hiQV : IntegrableOn (Q (gradient V)) (tsupport X) :=
    integrableOn_inner_linear_of_bounds (measurable_gradient V) hDX hVbound hD hc
  have htE := integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict (tsupport X)) (fun j ↦ phaseEnergyDensity f 0 (U j))
    (phaseEnergyDensity f 0 V) (fieldDivergence basis X) C hiE hiV
    hdiv.aestronglyMeasurable hC (hr.physical_translation_energy_tendsto h hV hval hlim hc)
  have htQ := integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict (tsupport X)) (fun j ↦ Q (q j)) (Q (gradient V)) (fun _ ↦ 1) 1
    hiQ hiQV aestronglyMeasurable_const (fun _ ↦ by norm_num)
    (hr.physical_translation_quadratic_tendsto h hV hval hlim hDX hD hc)
  simp only [mul_one] at htQ
  have hcut (E : Space (m + 1) → ℝ) (r : Space (m + 1) → Space (m + 1)) :
      (∫ x in tsupport X, E x * fieldDivergence basis X x - Q r x) =
        ∫ x, E x * fieldDivergence basis X x - Q r x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [Q, fieldDivergence_zero_of_notMem_tsupport basis X hx, fderiv_of_notMem_tsupport ℝ hx]
  have hiEj (j : ℕ) : IntegrableOn
      (fun x ↦ phaseEnergyDensity f 0 (U j) x * fieldDivergence basis X x) (tsupport X) :=
    (hiE j).mul_bdd hdiv.aestronglyMeasurable (Eventually.of_forall hC)
  have hiEV : IntegrableOn
      (fun x ↦ phaseEnergyDensity f 0 V x * fieldDivergence basis X x) (tsupport X) :=
    hiV.mul_bdd hdiv.aestronglyMeasurable (Eventually.of_forall hC)
  have hz (j : ℕ) : (∫ x in tsupport X, phaseEnergyDensity f 0 (U j) x *
      fieldDivergence basis X x) - (∫ x in tsupport X, Q (q j) x) = 0 := by
    rw [← integral_sub (hiEj j) (hiQ j), hcut]
    exact hr.translated_zeroExtension_stress_stationarity h basis (p j) hX hc
  have ht := htE.sub htQ
  have he := tendsto_nhds_unique (tendsto_const_nhds.congr'
    (Eventually.of_forall (fun j ↦ (hz j).symm))) ht
  rw [← hcut (phaseEnergyDensity f 0 V) (gradient V), integral_sub hiEV hiQV]
  exact he.symm

end SerrinEpigraph
