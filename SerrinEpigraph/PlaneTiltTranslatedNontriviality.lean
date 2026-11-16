module

public import SerrinEpigraph.PlaneTiltTranslatedMinimality
public import SerrinEpigraph.PlaneTiltTranslatedCompactness
public import SerrinEpigraph.AnnularGluingSequence
public import SerrinEpigraph.RecoveryEnergyLocalization

/-!
# Boundary-centered translated limits cannot be a constant phase
-/

public section
noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- A free-boundary anchor excludes local integral convergence to either constant well.
The proof uses the actual minimizer, an annular constant competitor, and the uniform
free-boundary energy lower density. -/
theorem RigidityHypotheses.translated_not_constant_phase_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) (hc : ∀ j, c j ∈ frontier (epigraph g))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {a : ℝ} (ha : a = 0 ∨ a = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) - a‖)
        atTop (𝓝 0)) : False := by
  let U : ℕ → Space (m + 1) → ℝ := fun j x ↦ zeroExtension g u (c j + R j • x)
  have hRp : ∀ j, 0 < R j := fun j ↦ zero_lt_one.trans_le (hR j)
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz (c j) (R j)
  have hUv (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hav : a ∈ Icc (0 : ℝ) 1 := by rcases ha with rfl | rfl <;> norm_num
  have hEc (j : ℕ) (x : Space (m + 1)) :
      rescaledPhaseEnergyDensity f (R j) (fun _ : Space (m + 1) ↦ a) x = 0 := by
    exact rescaledPhaseEnergyDensity_eq_zero_of_endpoint f (R j) (fun _ ↦ hav) ha
  let A : Set (Space (m + 1)) := closedBall 0 (1 + 1 : ℝ) \ ball 0 1
  have hA : IsCompact A := (isCompact_closedBall 0 _).diff isOpen_ball
  have hEB (j : ℕ) :
      (∫ x in A, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in A, rescaledPhaseEnergyDensity f (R j) (fun _ ↦ a) x) ≤ L * (1 + 1) ^ m := by
    simp only [hEc, integral_zero, add_zero]
    apply (setIntegral_mono_set
      (h.integrableOn_rescaledPhaseEnergy (hU j) (hUv j) (R j) (isCompact_closedBall 0 _))
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRp j).le (hUv j)))
      (Eventually.of_forall sdiff_subset)).trans
    exact hr.translated_rescaled_energy_le_surface_bound h hbound (c j) (hRp j)
      (by norm_num)
  obtain ⟨η, ε, hε, hglue⟩ := hr.exists_annular_gluing_sequence h hU
    (fun _ ↦ (LipschitzWith.const a).locallyLipschitz) hUv (fun _ _ ↦ hav)
    (r := 1) (t := 1) (by norm_num) (by norm_num)
    (continuousOn_const.integrableOn_compact hA) hR hRt hEB (hlocal A hA)
    (by simpa only [sub_self, norm_zero, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))
  have hupper (j : ℕ) :
      (∫ x in ball 0 1, rescaledPhaseEnergyDensity f (R j) (U j) x) ≤ ε j := by
    obtain ⟨hη, _, hs, hone, hηv, hcomp⟩ := hglue j
    have hh := hr.translated_inner_energy_le_of_glued_comparison h (c j) (hRp j)
      (by norm_num : (0 : ℝ) ≤ 1) (LipschitzWith.const a).locallyLipschitz hη.locallyLipschitz
      (fun _ ↦ hav) hηv (hs.trans ball_subset_closedBall) hone hcomp
    simpa only [hEc, integral_zero, zero_add] using hh
  obtain ⟨ρ, C, _, hC, hlo⟩ := hr.exists_translated_freeBoundary_energy_lower_bound h
  have hlarge : ∀ᶠ j in atTop, ρ ≤ R j * (1 / 2 : ℝ) := by
    filter_upwards [hRt.eventually (eventually_ge_atTop (2 * ρ))] with j hj
    linarith
  have hpositive : 0 < C * (1 / 2 : ℝ) ^ m := mul_pos hC (pow_pos (by norm_num) _)
  have hevent := hε.eventually (gt_mem_nhds hpositive)
  obtain ⟨j, hj, hjlarge⟩ := (hevent.and hlarge).exists
  have hdensity := hlo (c j) (R j) (hRp j) 0 (by simpa using hc j) (1 / 2) hjlarge
  have hmono : (∫ x in closedBall 0 (1 / 2 : ℝ),
      rescaledPhaseEnergyDensity f (R j) (U j) x) ≤
      ∫ x in ball 0 1, rescaledPhaseEnergyDensity f (R j) (U j) x := by
    apply setIntegral_mono_set
      ((h.integrableOn_rescaledPhaseEnergy (hU j) (hUv j) (R j)
        (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall)
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRp j).le (hUv j)))
    exact Eventually.of_forall (closedBall_subset_ball (by norm_num))
  exact (not_lt_of_ge ((hdensity.trans hmono).trans (hupper j))) hj

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Every local phase limit of diverging dilations has both phases of positive measure. -/
theorem RigidityHypotheses.translated_phase_limit_nontrivial (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) (hc : ∀ j, c j ∈ frontier (epigraph g)) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j)
    (hRt : Tendsto R atTop atTop) {E : Set (Space (m + 1))}
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    volume E ≠ 0 ∧ volume Eᶜ ≠ 0 := by
  have hnot {a : ℝ} (ha : a = 0 ∨ a = 1)
      (he : ∀ᵐ x ∂volume, E.indicator (fun _ ↦ (1 : ℝ)) x = a) : False := by
    apply hr.translated_not_constant_phase_limit h hbound c hc hR hRt ha
    intro K hK
    convert hlim K hK using 1
    funext j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae he] with x hx
    rw [hx]
  constructor
  · intro hz
    apply hnot (a := 0) (Or.inl rfl)
    have he : ∀ᵐ x ∂volume, x ∉ E := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hz
    filter_upwards [he] with x hx
    exact indicator_of_notMem hx _
  · intro hz
    apply hnot (a := 1) (Or.inr rfl)
    have he : ∀ᵐ x ∂volume, x ∈ E := mem_ae_iff.mpr hz
    filter_upwards [he] with x hx
    exact indicator_of_mem hx _

/-- Every boundary-centered family satisfying the all-center surface bound has a
single subsequence converging to a measurable phase of positive measure and positive
complementary measure. Both the solution and its primitive converge on every compact set. -/
theorem RigidityHypotheses.translated_nontrivial_measurable_phase_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    (c : ℕ → Space (m + 1)) (hc : ∀ j, c j ∈ frontier (epigraph g))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)),
      MeasurableSet E ∧ volume E ≠ 0 ∧ volume Eᶜ ≠ 0 ∧
      ∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖phasePrimitive f (zeroExtension g u (c (φ j) + R (φ j) • x)) -
            E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0) ∧
        Tendsto (fun j ↦ ∫ x in K,
          ‖zeroExtension g u (c (φ j) + R (φ j) • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, E, hE, hlim⟩ := hr.translated_measurable_phase_limit h hbound c
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt
  have hn := hr.translated_phase_limit_nontrivial h hbound (c ∘ φ) (fun j ↦ hc (φ j))
    (fun j ↦ hR (φ j)) (hRt.comp hφ.tendsto_atTop) (fun K hK ↦ (hlim K hK).2)
  exact ⟨φ, hφ, E, hE, hn.1, hn.2, hlim⟩

end SerrinEpigraph
