module

public import SerrinEpigraph.PlaneTiltTranslatedEnergy

/-!
# Two-phase approximation for arbitrary translated dilation families
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The translated potential is integrable on every compact set. -/
theorem RigidityHypotheses.integrableOn_translated_phasePotential
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) (R : ℝ) {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ phasePotentialDensity f (zeroExtension g u) (c + R • x)) K := by
  have hc := (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c R).continuous
  have hW : Continuous (fun x ↦ normalizedPotential f (zeroExtension g u (c + R • x))) :=
    h.normalizedPotential_continuousOn.comp_continuous hc
      (fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
  exact (hW.continuousOn.integrableOn_compact hK).indicator
    (isOpen_lt continuous_const hc).measurableSet

/-- The solution-to-indicator error is locally integrable after arbitrary translation and dilation. -/
theorem Hypotheses.integrableOn_translated_phaseIndicatorError
    (h : Hypotheses g u f κ) (c : Space (m + 1)) (R : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ phaseIndicatorError (zeroExtension g u) (c + R • x)) K := by
  have hc := (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c R).continuous
  have hi : IntegrableOn ({x | 0 < zeroExtension g u (c + R • x)}.indicator
      (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator
      (isOpen_lt continuous_const hc).measurableSet
  exact (hi.sub (hc.continuousOn.integrableOn_compact hK)).abs

/-- The primitive-to-indicator error is locally integrable after arbitrary translation and dilation. -/
theorem RigidityHypotheses.integrableOn_translated_primitiveIndicatorError
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) (R : ℝ) {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ primitiveIndicatorError f (zeroExtension g u) (c + R • x)) K := by
  have hc := (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c R).continuous
  have hi : IntegrableOn ({x | 0 < zeroExtension g u (c + R • x)}.indicator
      (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator
      (isOpen_lt continuous_const hc).measurableSet
  have hp := (locallyLipschitz_comp_translate_dilation
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h) c R).continuous
  exact ((hi.const_mul (phasePrimitive f 1)).sub (hp.continuousOn.integrableOn_compact hK)).abs

/-- The all-center energy estimate gives inverse-scale decay of the translated potential. -/
theorem RigidityHypotheses.translated_potential_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : Space (m + 1)) {R r : ℝ} (hR : 0 < R) (hradius : 0 < r) :
    (∫ x in closedBall 0 r, phasePotentialDensity f (zeroExtension g u) (c + R • x)) ≤
      L * r ^ m / R := by
  apply (le_div_iff₀ hR).2
  rw [mul_comm, ← integral_const_mul,
    setIntegral_closedBall_translate_dilation_weighted _ c hR]
  have hi := integral_mono (hr.integrableOn_phasePotential h (isCompact_closedBall c (R * r)))
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall c (R * r)))
    (fun x ↦ (hr.phasePotential_bounds h x).2)
  have hh := mul_le_mul_of_nonneg_left (hi.trans (hbound c (R * r) (mul_pos hR hradius)))
    (inv_nonneg.mpr (pow_nonneg hR.le m))
  convert hh using 1
  rw [mul_pow]
  field_simp

/-- The potential tends to zero locally along every diverging scale sequence and
arbitrary sequence of centers. -/
theorem RigidityHypotheses.translated_potential_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hRt : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      phasePotentialDensity f (zeroExtension g u) (c j + R j • x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j ↦ integral_nonneg
    (fun x ↦ (hr.phasePotential_bounds h _).1))
    (fun j ↦ hr.translated_potential_bound h hbound (c j) (hR j) hradius)
  exact tendsto_const_nhds.div_atTop hRt

/-- A fixed sub-equilibrium level bounds the pointwise indicator error by the potential
plus its distance to the equilibrium. -/
theorem RigidityHypotheses.phaseIndicatorError_le_potential_add
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (x : Space (m + 1)) :
    phaseIndicatorError (zeroExtension g u) x ≤
      phasePotentialDensity f (zeroExtension g u) x / normalizedPotential f a + (1 - a) := by
  have hw := hr.normalizedPotential_pos h ha.1 ha.2
  have h0 := h.zeroExtension_nonneg x
  have h1 := hr.zeroExtension_lt_one x
  by_cases hp : 0 < zeroExtension g u x
  · have heq : phaseIndicatorError (zeroExtension g u) x = 1 - zeroExtension g u x := by
      simp [phaseIndicatorError, positivePhaseIndicator, hp, abs_of_pos (sub_pos.mpr h1)]
    rw [heq]
    by_cases hle : zeroExtension g u x ≤ a
    · have hWa := hr.normalizedPotential_antitoneOn h ⟨h0, h1.le⟩ ⟨ha.1, ha.2.le⟩ hle
      have hpot : normalizedPotential f a ≤ phasePotentialDensity f (zeroExtension g u) x := by
        simpa [phasePotentialDensity, hp] using hWa
      have hd : 1 ≤ phasePotentialDensity f (zeroExtension g u) x / normalizedPotential f a :=
        (le_div_iff₀ hw).2 (by simpa only [one_mul] using hpot)
      linarith [ha.2]
    · have hd : 0 ≤ phasePotentialDensity f (zeroExtension g u) x / normalizedPotential f a :=
        div_nonneg (hr.phasePotential_bounds h x).1 hw.le
      linarith
  · have hz := le_antisymm (le_of_not_gt hp) h0
    have hd : 0 ≤ phasePotentialDensity f (zeroExtension g u) x / normalizedPotential f a :=
      div_nonneg (hr.phasePotential_bounds h x).1 hw.le
    simp only [phaseIndicatorError, positivePhaseIndicator, indicator_apply, mem_ofPred_eq,
      hz, lt_self_iff_false, ite_false, sub_zero, abs_zero]
    linarith [ha.2]

/-- The phase approximation is uniform in the choice of center along diverging scales. -/
theorem RigidityHypotheses.translated_phaseIndicatorError_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hRt : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      phaseIndicatorError (zeroExtension g u) (c j + R j • x)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun j ↦ hb.trans_le (integral_nonneg (fun x ↦ abs_nonneg _)))
  · intro ε hε
    let V := volume.real (closedBall (0 : Space (m + 1)) r)
    have hV : 0 ≤ V := measureReal_nonneg
    let δ := min (1 / 2 : ℝ) (ε / (2 * (V + 1)))
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
    have hδsmall : δ * (2 * (V + 1)) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have ha : 1 - δ ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have ht := (hr.translated_potential_tendsto_zero h hbound c hR hRt hradius).div_const
      (normalizedPotential f (1 - δ))
    simp only [zero_div] at ht
    filter_upwards [ht.eventually_lt_const (half_pos hε)] with j hj
    have hi := hr.integrableOn_translated_phasePotential h (c j) (R j) (isCompact_closedBall 0 r)
    have hc : IntegrableOn (fun _ : Space (m + 1) ↦ 1 - (1 - δ)) (closedBall 0 r) :=
      continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)
    have hh := integral_mono
      (h.integrableOn_translated_phaseIndicatorError (c j) (R j) (isCompact_closedBall 0 r))
      ((hi.div_const (normalizedPotential f (1 - δ))).add hc)
      (fun x ↦ hr.phaseIndicatorError_le_potential_add h ha (c j + R j • x))
    simp only [Pi.add_apply] at hh
    rw [integral_add (hi.div_const _) hc, integral_div, setIntegral_const, smul_eq_mul] at hh
    change _ ≤ _ + V * (1 - (1 - δ)) at hh
    nlinarith

/-- The translated primitive approaches the corresponding weighted phase indicator. -/
theorem RigidityHypotheses.translated_primitiveIndicatorError_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hRt : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      primitiveIndicatorError f (zeroExtension g u) (c j + R j • x)) atTop (𝓝 0) := by
  have ht := (hr.translated_phaseIndicatorError_tendsto_zero h hbound c hR hRt hradius).const_mul
    (Real.sqrt (2 * normalizedPotential f 0))
  simp only [mul_zero] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ abs_nonneg _)) _ ht
  intro j
  rw [← integral_const_mul]
  exact integral_mono
    (hr.integrableOn_translated_primitiveIndicatorError h (c j) (R j) (isCompact_closedBall 0 r))
    ((h.integrableOn_translated_phaseIndicatorError (c j) (R j) (isCompact_closedBall 0 r)).const_mul _)
    (fun x ↦ hr.primitiveIndicatorError_le h (c j + R j • x))

end SerrinEpigraph
