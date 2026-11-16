module

public import SerrinEpigraph.PlaneTiltTranslatedEnergyAway
public import SerrinEpigraph.PhaseClearingUniformLimit

/-!
# Clearing and interface exclusion for moving centers
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- Translation carries every centered ball integral to its translated ball. -/
theorem setIntegral_closedBall_comp_add_left_center {d : ℕ} (v : Space d → ℝ)
    (c x : Space d) (r : ℝ) :
    (∫ y in closedBall x r, v (c + y)) = ∫ y in closedBall (c + x) r, v y := by
  have hp : (fun y : Space d ↦ c + y) ⁻¹' closedBall (c + x) r = closedBall x r := by
    ext y
    simp only [mem_preimage, mem_closedBall, dist_add_left]
  have ht := ((measurePreserving_add_left volume c).restrict_preimage
    (s := closedBall (c + x) r) measurableSet_closedBall).integral_comp
      (Homeomorph.addLeft c).measurableEmbedding v
  simpa only [hp] using ht

/-- Exact energy change of variables about an arbitrary diffuse center. -/
theorem integral_rescaledPhaseEnergyDensity_translate_center {m : ℕ} (f : ℝ → ℝ)
    (U : Space (m + 1) → ℝ) (c x : Space (m + 1)) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ y in closedBall x r, rescaledPhaseEnergyDensity f R (fun z ↦ U (c + R • z)) y) =
      (R ^ m)⁻¹ * ∫ y in closedBall (c + R • x) (R * r),
        phaseEnergyDensity f 0 U y := by
  simp_rw [rescaledPhaseEnergyDensity_translate_dilation f U c hR]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume
    (fun z ↦ phaseEnergyDensity f 0 U (c + z)) _ hR]
  simp only [smul_closedBall' hR.ne', Real.norm_eq_abs, abs_of_pos hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [setIntegral_closedBall_comp_add_left_center, pow_succ]
  field_simp

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Physical clearing is uniform under arbitrary translation and dilation. -/
theorem RigidityHypotheses.exists_translated_phase_clearing_constants
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ a R₀ : ℝ, 0 < a ∧ 0 < R₀ ∧
      ∀ (c : Space (m + 1)) (T : ℝ), 0 < T →
        ∀ (x : Space (m + 1)) (r : ℝ), 0 < r → T * r ≤ R₀ →
          (∀ y ∈ ball x r, zeroExtension g u (c + T • y) ≤ a * (T * r)) →
            EqOn (fun y ↦ zeroExtension g u (c + T • y)) 0 (ball x (r / 2)) := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_phase_clearing_constants h
  refine ⟨a, R₀, ha, hR₀, ?_⟩
  intro c T hT x r hrad hTr hsmall
  have hphysical : ∀ y ∈ ball (c + T • x) (T * r),
      zeroExtension g u y ≤ a * (T * r) := by
    intro y hy
    let z := T⁻¹ • (y - c)
    have hz : c + T • z = y := by simp [z, smul_smul, hT.ne']
    have hdist : dist (c + T • z) (c + T • x) = T * dist z x := by
      rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hT.le]
    have hzb : z ∈ ball x r := by
      rw [mem_ball, ← mul_lt_mul_iff_right₀ hT, ← hdist, hz]
      exact hy
    simpa only [hz] using hsmall z hzb
  have hz := hclear (c + T • x) (T * r) (mul_pos hT hrad) hTr hphysical
  intro y hy
  apply hz
  rw [mem_ball, dist_add_left, dist_smul₀, Real.norm_of_nonneg hT.le]
  simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hy hT

/-- Every fixed interior level has a uniform energy density at translated scales. -/
theorem RigidityHypotheses.exists_translated_level_energy_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ (c : Space (m + 1)) (T : ℝ), 0 < T → ∀ x : Space (m + 1),
        zeroExtension g u (c + T • x) ∈ Icc a b → ∀ r : ℝ, ρ ≤ T * r →
          c₀ * r ^ m ≤ ∫ y in closedBall x r,
            rescaledPhaseEnergyDensity f T (fun z ↦ zeroExtension g u (c + T • z)) y := by
  obtain ⟨ρ, c₀, hρ, hc₀, hbound⟩ := hr.exists_level_surface_energy_lower_bound h ha hb
  refine ⟨ρ, c₀, hρ, hc₀, ?_⟩
  intro c T hT x hx r hradius
  have he := hbound (c + T • x) hx (T * r) hradius
  rw [integral_rescaledPhaseEnergyDensity_translate_center f _ c x hT]
  have hi := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (pow_nonneg hT.le m))
  calc
    c₀ * r ^ m = (T ^ m)⁻¹ * (c₀ * (T * r) ^ m) := by rw [mul_pow]; field_simp
    _ ≤ _ := hi

/-- The free-boundary density bound is also uniform under arbitrary translations. -/
theorem RigidityHypotheses.exists_translated_freeBoundary_energy_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ (c : Space (m + 1)) (T : ℝ), 0 < T → ∀ x : Space (m + 1),
        c + T • x ∈ frontier (epigraph g) → ∀ r : ℝ, ρ ≤ T * r →
          c₀ * r ^ m ≤ ∫ y in closedBall x r,
            rescaledPhaseEnergyDensity f T (fun z ↦ zeroExtension g u (c + T • z)) y := by
  obtain ⟨ρ, c₀, hρ, hc₀, hbound⟩ := hr.exists_freeBoundary_surface_energy_lower_bound h
  refine ⟨ρ, c₀, hρ, hc₀, ?_⟩
  intro c T hT x hx r hradius
  have he := hbound (c + T • x) hx (T * r) hradius
  rw [integral_rescaledPhaseEnergyDensity_translate_center f _ c x hT]
  have hi := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (pow_nonneg hT.le m))
  calc
    c₀ * r ^ m = (T ^ m)⁻¹ * (c₀ * (T * r) ^ m) := by rw [mul_pow]; field_simp
    _ ≤ _ := hi

/-- Local energy vanishing on an open set excludes every fixed compact interval
of interior phase values on its compact subsets. -/
theorem RigidityHypotheses.translated_eventually_no_interior_levels_of_energy_vanishes
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (c j + T j • y)) x) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ j in atTop, ∀ x ∈ K, zeroExtension g u (c j + T j • x) ∉ Icc a b := by
  obtain ⟨ρ, C, hρ, hC, hbound⟩ := hr.exists_translated_level_energy_lower_bound h ha hb
  obtain ⟨r, hradius, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening r K
  have hL : IsCompact L := hK.cthickening
  have hc : 0 < C * r ^ m := mul_pos hC (pow_pos hradius _)
  have hevent := (henergy L hL hthick).eventually (gt_mem_nhds hc)
  have hlarge : ∀ᶠ j in atTop, ρ ≤ T j * r := by
    filter_upwards [hTt.eventually (eventually_ge_atTop (ρ / r))] with j hj
    exact (div_le_iff₀ hradius).mp hj
  filter_upwards [hevent, hlarge] with j hj hjlarge
  intro x hx hval
  have hlo := hbound (c j) (T j) (hT j) x hval r hjlarge
  have hU : LocallyLipschitz (fun y ↦ zeroExtension g u (c j + T j • y)) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (T j)
  have hUv (y : Space (m + 1)) : zeroExtension g u (c j + T j • y) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hmono := setIntegral_mono_set (h.integrableOn_rescaledPhaseEnergy hU hUv (T j) hL)
    (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hT j).le hUv))
    (Eventually.of_forall (closedBall_subset_cthickening hx r))
  exact (not_lt_of_ge (hlo.trans hmono)) hj

/-- Local energy vanishing excludes the entire rescaled free boundary on every
compact subset, without assuming any regularity of a limiting free boundary. -/
theorem RigidityHypotheses.translated_eventually_no_freeBoundary_of_energy_vanishes
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (c j + T j • y)) x) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ᶠ j in atTop, ∀ x ∈ K, c j + T j • x ∉ frontier (epigraph g) := by
  obtain ⟨ρ, C, hρ, hC, hbound⟩ := hr.exists_translated_freeBoundary_energy_lower_bound h
  obtain ⟨r, hradius, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening r K
  have hL : IsCompact L := hK.cthickening
  have hc : 0 < C * r ^ m := mul_pos hC (pow_pos hradius _)
  have hevent := (henergy L hL hthick).eventually (gt_mem_nhds hc)
  have hlarge : ∀ᶠ j in atTop, ρ ≤ T j * r := by
    filter_upwards [hTt.eventually (eventually_ge_atTop (ρ / r))] with j hj
    exact (div_le_iff₀ hradius).mp hj
  filter_upwards [hevent, hlarge] with j hj hjlarge
  intro x hx hval
  have hlo := hbound (c j) (T j) (hT j) x hval r hjlarge
  have hU : LocallyLipschitz (fun y ↦ zeroExtension g u (c j + T j • y)) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (T j)
  have hUv (y : Space (m + 1)) : zeroExtension g u (c j + T j • y) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hmono := setIntegral_mono_set (h.integrableOn_rescaledPhaseEnergy hU hUv (T j) hL)
    (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hT j).le hUv))
    (Eventually.of_forall (closedBall_subset_cthickening hx r))
  exact (not_lt_of_ge (hlo.trans hmono)) hj

end SerrinEpigraph
