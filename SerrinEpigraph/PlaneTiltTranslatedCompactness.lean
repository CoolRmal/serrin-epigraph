module

public import SerrinEpigraph.PlaneTiltBVCompactness
public import SerrinEpigraph.PlaneTiltTranslatedPhaseError

/-!
# Measurable phase compactness for arbitrary moving centers
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Under an all-center surface bound, every sequence of diverging scales and arbitrary
centers has one subsequence on which both the actual solution and its primitive converge
locally to the corresponding measurable phase indicators. -/
theorem RigidityHypotheses.translated_measurable_phase_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ c : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall c r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      ∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖phasePrimitive f (zeroExtension g u (c (φ j) + R (φ j) • x)) -
            E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0) ∧
        Tendsto (fun j ↦ ∫ x in K,
          ‖zeroExtension g u (c (φ j) + R (φ j) • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  obtain ⟨φ, v, hφ, hv⟩ := hr.translated_primitive_global_integral_limit h hbound c hR
  let U : ℕ → Space (m + 1) → ℝ := fun j x ↦ zeroExtension g u (c (φ j) + R (φ j) • x)
  let F : ℕ → Space (m + 1) → ℝ := fun j x ↦ phasePrimitive f (U j x)
  let P : ℕ → Space (m + 1) → ℝ := fun j x ↦
    phasePrimitive f 1 * positivePhaseIndicator (U j) x
  have hUc (j : ℕ) : Continuous (U j) :=
    (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz
      (c (φ j)) (R (φ j))).continuous
  have hFc (j : ℕ) : Continuous (F j) :=
    (locallyLipschitz_comp_translate_dilation (hr.phasePrimitive_zeroExtension_locallyLipschitz h)
      (c (φ j)) (R (φ j))).continuous
  have hPi (j : ℕ) {K : Set (Space (m + 1))} (hK : IsCompact K) : IntegrableOn (P j) K := by
    have hi : IntegrableOn (positivePhaseIndicator (U j)) K :=
      (continuousOn_const.integrableOn_compact hK).indicator
        (isOpen_lt continuous_const (hUc j)).measurableSet
    exact hi.const_mul _
  have herr (r : ℝ) (hr0 : 0 < r) : Tendsto
      (fun j ↦ ∫ x in closedBall 0 r, ‖P j x - F j x‖) atTop (𝓝 0) := by
    simpa only [P, F, U, positivePhaseIndicator, Real.norm_eq_abs, primitiveIndicatorError,
      Function.comp_def, indicator_apply, mem_ofPred_eq] using
      hr.translated_primitiveIndicatorError_tendsto_zero h hbound (c ∘ φ)
        (fun j ↦ hR (φ j)) (hRt.comp hφ.tendsto_atTop) hr0
  have hvm : AEStronglyMeasurable v volume := by
    have hm := AEStronglyMeasurable.iUnion (fun k : ℕ ↦
      (hv (closedBall 0 (k + 1 : ℝ)) (isCompact_closedBall 0 _)).1.aestronglyMeasurable)
    simpa only [iUnion_integer_closedBall, Measure.restrict_univ] using hm
  have hvalues : ∀ᵐ x ∂volume, v x = 0 ∨ v x = phasePrimitive f 1 := by
    have hloc (k : ℕ) : ∀ᵐ x ∂volume.restrict (closedBall 0 (k + 1 : ℝ)),
        v x = 0 ∨ v x = phasePrimitive f 1 := by
      apply ae_two_values_of_approximate_integral_limit F P v (phasePrimitive f 1)
        (fun j ↦ (hFc j).continuousOn.integrableOn_compact (isCompact_closedBall 0 _))
        (fun j ↦ hPi j (isCompact_closedBall 0 _))
        (hv _ (isCompact_closedBall 0 _)).1 _ (herr _ (by positivity))
        (hv _ (isCompact_closedBall 0 _)).2
      intro j x
      by_cases hx : 0 < U j x
      · exact Or.inr (by simp [P, positivePhaseIndicator, hx])
      · exact Or.inl (by simp [P, positivePhaseIndicator, hx])
    have hall := (ae_restrict_iUnion_iff
      (fun k : ℕ ↦ closedBall (0 : Space (m + 1)) (k + 1 : ℝ))
      (fun x ↦ v x = 0 ∨ v x = phasePrimitive f 1)).mpr hloc
    simpa only [iUnion_integer_closedBall, Measure.restrict_univ] using hall
  obtain ⟨E, hE, heq⟩ := exists_measurable_indicator_of_two_values hvm _ hvalues
  have hprim (K : Set (Space (m + 1))) (hK : IsCompact K) : Tendsto
      (fun j ↦ ∫ x in K, ‖F j x - E.indicator (fun _ ↦ phasePrimitive f 1) x‖)
        atTop (𝓝 0) := by
    apply (hv K hK).2.congr'
    apply Eventually.of_forall
    intro j
    apply integral_congr_ae
    filter_upwards [heq.restrict] with x hx
    rw [hx]
  have hσ := hr.phasePrimitive_one_pos h
  have hsolution (k : ℕ) : Tendsto
      (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖U j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    let K : Set (Space (m + 1)) := closedBall 0 (k + 1 : ℝ)
    have hK : IsCompact K := isCompact_closedBall 0 _
    have hI : IntegrableOn (E.indicator (fun _ ↦ (1 : ℝ))) K :=
      (continuousOn_const.integrableOn_compact hK).indicator hE
    have hIσ : IntegrableOn (E.indicator (fun _ ↦ phasePrimitive f 1)) K :=
      (continuousOn_const.integrableOn_compact hK).indicator hE
    have hP0 (j : ℕ) : IntegrableOn (positivePhaseIndicator (U j)) K :=
      (continuousOn_const.integrableOn_compact hK).indicator
        (isOpen_lt continuous_const (hUc j)).measurableSet
    have hw : Tendsto (fun j ↦ ∫ x in K,
        ‖P j x - E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0) := by
      have ht := (herr _ (by positivity : 0 < (k + 1 : ℝ))).add (hprim K hK)
      simp only [zero_add] at ht
      apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
      intro j
      exact integral_norm_sub_triangle (hPi j hK)
        ((hFc j).continuousOn.integrableOn_compact hK) hIσ
    have hfactor (j : ℕ) :
        (∫ x in K, ‖P j x - E.indicator (fun _ ↦ phasePrimitive f 1) x‖) =
          phasePrimitive f 1 * ∫ x in K,
            ‖positivePhaseIndicator (U j) x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      have hIeq : E.indicator (fun _ ↦ phasePrimitive f 1) x =
          phasePrimitive f 1 * E.indicator (fun _ ↦ (1 : ℝ)) x := by
        by_cases hx : x ∈ E <;> simp [hx]
      dsimp only [P]
      rw [hIeq, ← mul_sub, norm_mul, Real.norm_of_nonneg hσ.le]
    have hphase := hw.div_const (phasePrimitive f 1)
    simp only [zero_div, hfactor, mul_div_cancel_left₀ _ hσ.ne'] at hphase
    have herror : Tendsto (fun j ↦ ∫ x in K, ‖U j x - positivePhaseIndicator (U j) x‖)
        atTop (𝓝 0) := by
      simpa only [K, U, positivePhaseIndicator, phaseIndicatorError, Real.norm_eq_abs,
        abs_sub_comm, Function.comp_def, indicator_apply, mem_ofPred_eq] using
        hr.translated_phaseIndicatorError_tendsto_zero h hbound (c ∘ φ)
          (fun j ↦ hR (φ j)) (hRt.comp hφ.tendsto_atTop) (show 0 < (k + 1 : ℝ) by positivity)
    have ht := herror.add hphase
    simp only [zero_add] at ht
    apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
    intro j
    exact integral_norm_sub_triangle ((hUc j).continuousOn.integrableOn_compact hK) (hP0 j) hI
  refine ⟨φ, hφ, E, hE, fun K hK ↦ ⟨hprim K hK, ?_⟩⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have hs : K ⊆ closedBall 0 (k + 1 : ℝ) :=
    hr.trans ((ball_subset_ball (by linarith)).trans ball_subset_closedBall)
  apply integral_limit_mono_set hs U (E.indicator (fun _ ↦ (1 : ℝ)))
    (fun j ↦ (hUc j).continuousOn.integrableOn_compact (isCompact_closedBall 0 _))
    ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 _)).indicator hE)
    (hsolution k)

end SerrinEpigraph
