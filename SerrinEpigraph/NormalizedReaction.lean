module

public import SerrinEpigraph.ReactionTail

/-!
# Quantitative positivity of the normalized reaction

The restored rigidity assumptions exclude the zero reaction and give a positive
linear lower bound near zero, as required in constructing the normalized potential.
-/

public section

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A fixed positive reaction value gives a linear lower bound to its left. -/
theorem RigidityHypotheses.reaction_linear_lower_bound (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → c * s ≤ f s := by
  refine ⟨f (1 / 2) / (1 / 2), div_pos (hr.reaction_pos _ (by norm_num))
    (by norm_num), ?_⟩
  intro s hs hsle
  have hratio := antitoneOn_reaction_div h.reaction_contDiffOn h.reaction_structure
    hs (show (0 : ℝ) < 1 / 2 by norm_num) hsle
  exact (le_div_iff₀ hs).mp hratio

/-- The normalized equilibrium is the only positive zero up to one. -/
theorem RigidityHypotheses.reaction_eq_zero_iff (hr : RigidityHypotheses g u f)
    {s : ℝ} (hs : 0 < s) (hsle : s ≤ 1) : f s = 0 ↔ s = 1 := by
  constructor
  · intro hz
    by_contra hne
    exact (hr.reaction_pos s ⟨hs, lt_of_le_of_ne hsle hne⟩).ne' hz
  · rintro rfl
    exact hr.reaction_one

/-- Beyond the normalized equilibrium the structural condition forces a nonpositive reaction. -/
theorem RigidityHypotheses.reaction_nonpos_after_one (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : 1 ≤ s) : f s ≤ 0 := by
  have hb := reaction_le_slope_mul h.reaction_contDiffOn h.reaction_structure
    (show (0 : ℝ) < 1 by norm_num) hs
  simpa only [hr.reaction_one, zero_div, zero_mul] using hb

end SerrinEpigraph
