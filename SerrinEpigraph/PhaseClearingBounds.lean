module

public import SerrinEpigraph.ClosedLipschitzMinimality
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Low-phase potential bounds and energy absorption

These estimates are the scalar part of the clearing argument. The energy comparison
with an annular competitor is proved separately; it is not assumed in the original
PDE hypotheses.
-/

public section
noncomputable section

open Set MeasureTheory InnerProductSpace

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A fixed low-value interval has a strictly positive potential floor and a finite
nonnegative upper bound for the reaction. -/
theorem RigidityHypotheses.exists_low_phase_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c F : ℝ, 0 < c ∧ 0 ≤ F ∧
      (∀ s ∈ Icc (0 : ℝ) (1 / 2), c ≤ normalizedPotential f s) ∧
      (∀ s ∈ Icc (0 : ℝ) (1 / 2), f s ≤ F) := by
  have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) 1 := by
    intro s hs
    exact ⟨hs.1, hs.2.trans (by norm_num)⟩
  obtain ⟨c, hc, hcW⟩ := isCompact_Icc.exists_forall_le'
    (h.normalizedPotential_continuousOn.mono hsub)
    (fun s hs ↦ hr.normalizedPotential_pos h hs.1 (hs.2.trans_lt (by norm_num)))
  have hfc : ContinuousOn f (Icc (0 : ℝ) (1 / 2)) :=
    h.reaction_contDiffOn.continuousOn.mono (fun _ hs ↦ hs.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  refine ⟨c, |M|, hc, abs_nonneg _, hcW, ?_⟩
  intro s hs
  exact (le_abs_self _).trans ((hM s hs).trans (le_abs_self M))

/-- A reaction upper bound controls the loss of potential under downward truncation. -/
theorem Hypotheses.low_phase_potential_sub_lower_bound
    (h : Hypotheses g u f κ) {δ F a b : ℝ} (hδ : δ ≤ 1)
    (hF : ∀ s ∈ Icc (0 : ℝ) δ, f s ≤ F)
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ δ) :
    -F * (a - b) ≤ normalizedPotential f a - normalizedPotential f b := by
  have hcont : ContinuousOn (normalizedPotential f) (Icc (0 : ℝ) δ) :=
    h.normalizedPotential_continuousOn.mono (fun _ hs ↦ ⟨hs.1, hs.2.trans hδ⟩)
  have hm : MonotoneOn (fun s ↦ normalizedPotential f s + F * s) (Icc (0 : ℝ) δ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hcont.add (continuous_const.mul continuous_id).continuousOn)
      (f' := fun s ↦ -f s + F)
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) δ := by simpa only [interior_Icc] using hs
      convert ((h.normalizedPotential_hasDerivAt hs'.1).add
        ((hasDerivAt_id s).const_mul F)).hasDerivWithinAt (s := interior (Icc 0 δ)) using 1
      simp
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) δ := by simpa only [interior_Icc] using hs
      linarith [hF s ⟨hs'.1.le, hs'.2.le⟩]
  have he := hm ⟨hb, hba.trans ha⟩ ⟨hb.trans hba, ha⟩ hba
  linarith

/-- Completing the square bounds gradient mass by low-phase energy. -/
theorem sqrt_mul_norm_le_low_phase_energy {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (p : Space d) :
    Real.sqrt (2 * c) * ‖p‖ ≤ ‖p‖ ^ 2 / 2 + c := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * c by positivity)
  nlinarith [sq_nonneg (‖p‖ - Real.sqrt (2 * c))]

/-- The divided form used to estimate the trace of the competitor. -/
theorem norm_le_low_phase_energy_div_sqrt {d : ℕ} {c : ℝ} (hc : 0 < c)
    (p : Space d) :
    ‖p‖ ≤ (‖p‖ ^ 2 / 2 + c) / Real.sqrt (2 * c) := by
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).mpr
  simpa only [mul_comm] using sqrt_mul_norm_le_low_phase_energy hc.le p

/-- Strict absorption of a nonnegative finite energy forces that energy to vanish. -/
theorem low_phase_energy_eq_zero_of_absorption {I θ : ℝ}
    (hI : 0 ≤ I) (hθ : θ < 1) (habsorb : I ≤ θ * I) : I = 0 := by
  have hprod : 0 ≤ (1 - θ) * I := mul_nonneg (sub_pos.mpr hθ).le hI
  have he : (1 - θ) * I = 0 := by nlinarith
  exact (mul_eq_zero.mp he).resolve_left (sub_pos.mpr hθ).ne'

end SerrinEpigraph
