module

public import SerrinEpigraph.PhasePrimitiveGradient
public import SerrinEpigraph.RadialSlopeBound

/-!
# Lipschitz regularity of the phase primitive
-/

public section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

noncomputable section

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The phase primitive is Lipschitz on the entire normalized range, including its endpoints. -/
theorem RigidityHypotheses.phasePrimitive_lipschitzOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    LipschitzOnWith ⟨Real.sqrt (2 * normalizedPotential f 0), Real.sqrt_nonneg _⟩
      (phasePrimitive f) (Set.Icc 0 1) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro s hs t ht
  have hc : ContinuousOn (fun z ↦ Real.sqrt (2 * normalizedPotential f z)) (Set.Icc 0 1) :=
    (continuousOn_const.mul h.normalizedPotential_continuousOn).sqrt
  have hi (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun z ↦ Real.sqrt (2 * normalizedPotential f z)) volume 0 z :=
    (hc.mono (Set.Icc_subset_Icc_right hz.2)).intervalIntegrable_of_Icc hz.1
  rw [dist_eq_norm, phasePrimitive, phasePrimitive,
    intervalIntegral.integral_interval_sub_left (hi s hs) (hi t ht)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := Real.sqrt (2 * normalizedPotential f 0))
    (f := fun z ↦ Real.sqrt (2 * normalizedPotential f z)) (fun z hz ↦ ?_)
  · convert hb using 1
    rw [Real.dist_eq]
    rfl
  · have hz' : z ∈ Set.Icc (0 : ℝ) 1 := by
      rcases le_total t s with hts | hst
      · rw [Set.uIoc_of_le hts] at hz
        exact ⟨ht.1.trans hz.1.le, hz.2.trans hs.2⟩
      · rw [Set.uIoc_of_ge hst] at hz
        exact ⟨hs.1.trans hz.1.le, hz.2.trans ht.2⟩
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left
      (hr.normalizedPotential_antitoneOn h (by norm_num) hz' hz'.1) (by norm_num)

/-- The phase primitive of the zero extension is locally Lipschitz across the free boundary. -/
theorem RigidityHypotheses.phasePrimitive_zeroExtension_locallyLipschitz
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    LocallyLipschitz (fun x ↦ phasePrimitive f (zeroExtension g u x)) := by
  intro x
  obtain ⟨K, S, hS, hK⟩ := h.zeroExtension_locallyLipschitz x
  exact ⟨_, S, hS, (hr.phasePrimitive_lipschitzOn h).comp hK
    (fun y _ ↦ ⟨h.zeroExtension_nonneg y, (hr.zeroExtension_lt_one y).le⟩)⟩

end

end SerrinEpigraph
