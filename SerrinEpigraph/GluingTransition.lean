module

public import SerrinEpigraph.GluingTotalEnergy

/-!
# Localization of gluing costs to the transition region
-/

public section

open Set

namespace SerrinEpigraph

/-- Normalized inputs have nonnegative rescaled phase energy. -/
theorem RigidityHypotheses.rescaledPhaseEnergyDensity_nonneg
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℝ} (hR : 0 ≤ R) {v : Space d → ℝ} (hv : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (x : Space d) : 0 ≤ rescaledPhaseEnergyDensity f R v x := by
  by_cases hp : 0 < v x
  · simp only [rescaledPhaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq,
      hp, ite_true]
    exact add_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hR))
      (mul_nonneg hR (hr.normalizedPotential_nonneg h (hv x)))
  · simp [rescaledPhaseEnergyDensity, hp]

/-- A normalized cutoff has zero totalized gradient at either endpoint. -/
theorem gradient_cutoff_eq_zero_of_endpoint {d : ℕ} {η : Space d → ℝ}
    (hη : ∀ x, η x ∈ Icc (0 : ℝ) 1) {x : Space d} (hx : η x = 0 ∨ η x = 1) :
    gradient η x = 0 := by
  rcases hx with hx | hx
  · have hm : IsLocalMin η x := by
      filter_upwards with y
      rw [hx]
      exact (hη y).1
    simp only [gradient, hm.fderiv_eq_zero, map_zero]
  · have hm : IsLocalMax η x := by
      filter_upwards with y
      rw [hx]
      exact (hη y).2
    simp only [gradient, hm.fderiv_eq_zero, map_zero]

/-- At a cutoff endpoint the glued energy equals the selected input energy, including
points on the boundary of the transition region. -/
theorem rescaledEnergy_glued_eq_of_endpoint {d : ℕ} {U v η : Space d → ℝ}
    (f : ℝ → ℝ) (R : ℝ) {x : Space d}
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x)
    (hη : DifferentiableAt ℝ η x) (hval : ∀ y, η y ∈ Icc (0 : ℝ) 1)
    (hx : η x = 0 ∨ η x = 1) :
    rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x =
      (1 - η x) * rescaledPhaseEnergyDensity f R U x +
        η x * rescaledPhaseEnergyDensity f R v x := by
  have hg := gradient_cutoff_eq_zero_of_endpoint hval hx
  have he := gradient_gluedCompetitor hU hv hη
  rcases hx with hx | hx
  · simp only [hx, zero_smul, hg, smul_zero, add_zero] at he
    simp [rescaledPhaseEnergyDensity, Set.indicator_apply, gluedCompetitor_eq_reference U v η hx, he, hx]
  · simp only [hx, one_smul, hg, smul_zero, add_zero, add_sub_cancel] at he
    simp [rescaledPhaseEnergyDensity, Set.indicator_apply, gluedCompetitor_eq_candidate U v η hx, he, hx]

/-- Any bound on transition energy yields a global bound with the excess confined
to the strict transition set. Outside it the exact convex input energy suffices. -/
theorem rescaledEnergy_glued_le_transition_bound_ae {d : ℕ} {U v η : Space d → ℝ}
    (f : ℝ → ℝ) (R : ℝ)
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hEU : ∀ x, 0 ≤ rescaledPhaseEnergyDensity f R U x)
    (hEv : ∀ x, 0 ≤ rescaledPhaseEnergyDensity f R v x)
    {B : Space d → ℝ}
    (hB : ∀ᵐ x ∂MeasureTheory.volume, 0 < η x ∧ η x < 1 →
      rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x ≤ B x) :
    ∀ᵐ x ∂MeasureTheory.volume,
      rescaledPhaseEnergyDensity f R (gluedCompetitor U v η) x ≤
        (1 - η x) * rescaledPhaseEnergyDensity f R U x +
          η x * rescaledPhaseEnergyDensity f R v x +
          {y | 0 < η y ∧ η y < 1}.indicator B x := by
  filter_upwards [ae_differentiableAt_of_locallyLipschitz hU,
    ae_differentiableAt_of_locallyLipschitz hv,
    ae_differentiableAt_of_locallyLipschitz hη, hB] with x hxU hxv hxη hxB
  by_cases ht : 0 < η x ∧ η x < 1
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ht, and_self, ite_true]
    have hn := add_nonneg
      (mul_nonneg (sub_nonneg.mpr (hval x).2) (hEU x))
      (mul_nonneg (hval x).1 (hEv x))
    linarith [hxB ht]
  · have he : η x = 0 ∨ η x = 1 := by
      have hh := hval x
      rcases le_or_gt (η x) 0 with hz | hz
      · exact Or.inl (le_antisymm hz hh.1)
      · exact Or.inr (le_antisymm hh.2 (not_lt.mp (fun hlt ↦ ht ⟨hz, hlt⟩)))
    rw [rescaledEnergy_glued_eq_of_endpoint f R hxU hxv hxη hval he]
    simp [ht]

end SerrinEpigraph
