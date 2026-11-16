module

public import SerrinEpigraph.HarmonicProjectedBadSet
public import SerrinEpigraph.PlaneTiltTranslatedClearing

/-!
# The two bad-set estimates for the actual rescaled solution

The projected volume and the diffuse kinetic mass are controlled by the same
actual tilt integral. Surface growth of the kinetic density is derived from the
proved all-center phase-energy bound.
-/

public section
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The full kinetic density is bounded by twice the phase energy, including
the zero phase where the totalized gradient vanishes. -/
theorem RigidityHypotheses.translated_kinetic_density_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : Space (m + 1)) {T : ℝ} (hT : 0 < T) (x : Space (m + 1)) :
    ‖gradient (fun y ↦ zeroExtension g u (c + T • y)) x‖ ^ 2 / T ≤
      2 * rescaledPhaseEnergyDensity f T
        (fun y ↦ zeroExtension g u (c + T • y)) x := by
  by_cases hx : c + T • x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff _).mpr hx
    have hW := hr.normalizedPotential_nonneg h
      ⟨h.zeroExtension_nonneg (c + T • x), (hr.zeroExtension_lt_one _).le⟩
    simp only [rescaledPhaseEnergyDensity, indicator_apply, mem_ofPred_eq, hp, ite_true]
    have he : ‖gradient (fun y ↦ zeroExtension g u (c + T • y)) x‖ ^ 2 / T =
        2 * (‖gradient (fun y ↦ zeroExtension g u (c + T • y)) x‖ ^ 2 / (2 * T)) := by
      ring
    rw [he]
    nlinarith [mul_nonneg hT.le hW]
  · have hp : ¬0 < zeroExtension g u (c + T • x) := by
      simpa only [zeroExtension_of_notMem hx] using (lt_irrefl (0 : ℝ))
    simp [rescaledPhaseEnergyDensity, hp, gradient_comp_translate_dilation,
      h.gradient_zeroExtension_of_notMem hx]

/-- The sharp physical surface bound controls kinetic energy on every rescaled
ball, with arbitrary translation and dilation. -/
theorem RigidityHypotheses.translated_kinetic_ball_le_surface_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : Space (m + 1)) {T : ℝ} (hT : 0 < T) (x : Space (m + 1))
    {r : ℝ} (hradius : 0 < r) :
    (∫ y in ball x r, ‖gradient (fun z ↦ zeroExtension g u (c + T • z)) y‖ ^ 2 / T) ≤
      (2 * L) * r ^ m := by
  let v := fun z ↦ zeroExtension g u (c + T • z)
  have hv : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c T
  have hval (y : Space (m + 1)) : v y ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hi := (integrableOn_gradient_sq_of_locallyLipschitz hv
    (isCompact_closedBall x r)).div_const T
  have hE := h.integrableOn_rescaledPhaseEnergy hv hval T (isCompact_closedBall x r)
  have henergy :
      (∫ y in closedBall x r, rescaledPhaseEnergyDensity f T v y) ≤ L * r ^ m := by
    rw [integral_rescaledPhaseEnergyDensity_translate_center f _ c x hT]
    have hh := mul_le_mul_of_nonneg_left (hbound (c + T • x) (T * r)
      (mul_pos hT hradius)) (inv_nonneg.mpr (pow_nonneg hT.le m))
    convert hh using 1
    rw [mul_pow]
    field_simp
  calc
    _ ≤ ∫ y in closedBall x r, ‖gradient v y‖ ^ 2 / T :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall
        (fun y ↦ div_nonneg (sq_nonneg _) hT.le))
        (Filter.Eventually.of_forall ball_subset_closedBall)
    _ ≤ ∫ y in closedBall x r, 2 * rescaledPhaseEnergyDensity f T v y :=
      integral_mono hi (hE.const_mul 2) (hr.translated_kinetic_density_le_energy h c hT)
    _ = 2 * ∫ y in closedBall x r, rescaledPhaseEnergyDensity f T v y :=
      integral_const_mul _ _
    _ ≤ (2 * L) * r ^ m := by linarith

/-- The projected HA bad-set estimate for any translated rescaling of the
original solution, with no regularity premise on its free boundary. -/
theorem Hypotheses.translated_projected_tilt_bad_set_le
    (h : Hypotheses g u f κ) {π : Space (m + 1) → Space m}
    (hπ : LipschitzWith 1 π) (c : Space (m + 1))
    {e : Space (m + 1)} (he : ‖e‖ = 1) {T : ℝ} (hT : 0 < T)
    {A : Set (Space (m + 1))} (hA : IsCompact A) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    volume (π '' {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      η * r ^ m ≤ ∫ y in ball x r,
        diffuseTiltDensity T (fun z ↦ zeroExtension g u (c + T • z)) e y}) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ m) * volume (ball (0 : Space m) 1) /
        ENNReal.ofReal η) *
          ENNReal.ofReal (∫ x in A,
            diffuseTiltDensity T (fun z ↦ zeroExtension g u (c + T • z)) e x) :=
  measure_projected_tilt_bad_set_le hπ
    (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c T)
    he hT hA R hη

/-- The diffuse kinetic mass of the HA bad set is bounded by total tilt divided
by the threshold, for the actual solution at every center and positive scale. -/
theorem RigidityHypotheses.translated_kinetic_bad_set_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : Space (m + 1)) {e : Space (m + 1)} (he : ‖e‖ = 1)
    {T : ℝ} (hT : 0 < T) {A : Set (Space (m + 1))} (hA : IsCompact A)
    (R : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫⁻ x in {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      η * r ^ m ≤ ∫ y in ball x r,
        diffuseTiltDensity T (fun z ↦ zeroExtension g u (c + T • z)) e y},
      ENNReal.ofReal (‖gradient (fun z ↦ zeroExtension g u (c + T • z)) x‖ ^ 2 / T)) ≤
      (ENNReal.ofReal ((2 * L) * (5 : ℝ) ^ m) / ENNReal.ofReal η) *
        ENNReal.ofReal (∫ x in A,
          diffuseTiltDensity T (fun z ↦ zeroExtension g u (c + T • z)) e x) := by
  let v := fun z ↦ zeroExtension g u (c + T • z)
  have hv : LocallyLipschitz v :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz c T
  have hw : LocallyIntegrable (fun x ↦ ‖gradient v x‖ ^ 2 / T) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact (integrableOn_gradient_sq_of_locallyLipschitz hv hK).div_const T
  exact lintegral_weighted_bad_set_le hA.measurableSet
    (integrableOn_diffuseTiltDensity hv hA T he) (diffuseTiltDensity_nonneg hT v he)
    hw (fun x ↦ div_nonneg (sq_nonneg _) hT.le) R m (by positivity) hη
    (fun x r hradius ↦ hr.translated_kinetic_ball_le_surface_bound h hbound c hT x hradius)

end SerrinEpigraph
