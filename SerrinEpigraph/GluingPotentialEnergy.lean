module

public import SerrinEpigraph.GluedCompetitor
public import SerrinEpigraph.RescaledPotential
public import SerrinEpigraph.RadialSlopeBound

/-!
# Potential-energy control across cutoff gluing
-/

public section

open Set

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The zero-level potential is controlled by the positive-level potential and a quadratic gap. -/
theorem RigidityHypotheses.potential_zero_le_quadratic_control
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    normalizedPotential f 0 ≤
      (normalizedPotential f 0 / normalizedPotential f (1 / 2)) * normalizedPotential f s +
        4 * normalizedPotential f 0 * s ^ 2 := by
  have h0 := hr.normalizedPotential_pos h (s := 0) (by norm_num) (by norm_num)
  have hh := hr.normalizedPotential_pos h (s := 1 / 2) (by norm_num) (by norm_num)
  have hs0 := hr.normalizedPotential_nonneg h ⟨hs.1.le, hs.2⟩
  have hratio : 0 ≤ normalizedPotential f 0 / normalizedPotential f (1 / 2) :=
    div_nonneg h0.le hh.le
  by_cases hsmall : s ≤ 1 / 2
  · have hmono := hr.normalizedPotential_antitoneOn h ⟨hs.1.le, hs.2⟩
      (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num) hsmall
    have he := mul_le_mul_of_nonneg_left hmono hratio
    rw [div_mul_cancel₀ _ hh.ne'] at he
    nlinarith [mul_nonneg (show 0 ≤ 4 * normalizedPotential f 0 by positivity) (sq_nonneg s)]
  · have hsq : (1 : ℝ) ≤ 4 * s ^ 2 := by nlinarith [sq_nonneg (s - 1 / 2)]
    have he := mul_le_mul_of_nonneg_left hsq h0.le
    nlinarith [mul_nonneg hratio hs0]

/-- Convex cutoff gluing controls phase potential by the two input potentials and mismatch. -/
theorem RigidityHypotheses.gluedCompetitor_potential_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {d : ℕ} {U v η : Space d → ℝ}
    (hU : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hv : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hη : ∀ x, η x ∈ Icc (0 : ℝ) 1) (x : Space d) :
    phasePotentialDensity f (gluedCompetitor U v η) x ≤
      (normalizedPotential f 0 / normalizedPotential f (1 / 2)) *
        (phasePotentialDensity f U x + phasePotentialDensity f v x) +
        4 * normalizedPotential f 0 * (v x - U x) ^ 2 := by
  have h0 := hr.normalizedPotential_pos h (s := 0) (by norm_num) (by norm_num)
  have hh := hr.normalizedPotential_pos h (s := 1 / 2) (by norm_num) (by norm_num)
  have hhalf := hr.normalizedPotential_antitoneOn h
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num)
  have hratio : 1 ≤ normalizedPotential f 0 / normalizedPotential f (1 / 2) :=
    (le_div_iff₀ hh).mpr (by simpa using hhalf)
  have hz := gluedCompetitor_mem_Icc hU hv hη x
  have hWz := hr.normalizedPotential_antitoneOn h
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hz hz.1
  have hWU := hr.normalizedPotential_nonneg h (hU x)
  have hWv := hr.normalizedPotential_nonneg h (hv x)
  have hgap : 0 ≤ 4 * normalizedPotential f 0 * (v x - U x) ^ 2 := by positivity
  by_cases hp : 0 < gluedCompetitor U v η x
  · simp only [phasePotentialDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_true]
    by_cases hUp : 0 < U x
    · by_cases hvp : 0 < v x
      · simp only [hUp, hvp, ite_true]
        have hmin : min (U x) (v x) ≤ gluedCompetitor U v η x := by
          dsimp only [gluedCompetitor]
          rcases le_total (U x) (v x) with hle | hle
          · rw [min_eq_left hle]
            nlinarith [mul_nonneg (hη x).1 (sub_nonneg.mpr hle)]
          · rw [min_eq_right hle]
            nlinarith [mul_nonneg (sub_nonneg.mpr (hη x).2) (sub_nonneg.mpr hle)]
        have hminrange : min (U x) (v x) ∈ Icc (0 : ℝ) 1 :=
          ⟨le_min (hU x).1 (hv x).1, (min_le_left _ _).trans (hU x).2⟩
        have hmono := hr.normalizedPotential_antitoneOn h hminrange hz hmin
        have hsum : normalizedPotential f (min (U x) (v x)) ≤
            normalizedPotential f (U x) + normalizedPotential f (v x) := by
          rcases le_total (U x) (v x) with hle | hle
          · rw [min_eq_left hle]; linarith
          · rw [min_eq_right hle]; linarith
        have he := mul_le_mul_of_nonneg_right hratio (add_nonneg hWU hWv)
        nlinarith
      · have hvz : v x = 0 := le_antisymm (le_of_not_gt hvp) (hv x).1
        have he := hr.potential_zero_le_quadratic_control h ⟨hUp, (hU x).2⟩
        simpa [hUp, hvz] using hWz.trans he
    · have hUz : U x = 0 := le_antisymm (le_of_not_gt hUp) (hU x).1
      by_cases hvp : 0 < v x
      · have he := hr.potential_zero_le_quadratic_control h ⟨hvp, (hv x).2⟩
        simpa [hvp, hUz] using hWz.trans he
      · have hvz : v x = 0 := le_antisymm (le_of_not_gt hvp) (hv x).1
        simp [gluedCompetitor, hUz, hvz] at hp
  · have hPU : 0 ≤ phasePotentialDensity f U x := by
      by_cases ht : 0 < U x <;> simp [phasePotentialDensity, ht, hWU]
    have hPv : 0 ≤ phasePotentialDensity f v x := by
      by_cases ht : 0 < v x <;> simp [phasePotentialDensity, ht, hWv]
    simp only [phasePotentialDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_false]
    exact add_nonneg (mul_nonneg (by linarith : 0 ≤ normalizedPotential f 0 /
      normalizedPotential f (1 / 2)) (add_nonneg hPU hPv)) hgap

end SerrinEpigraph
