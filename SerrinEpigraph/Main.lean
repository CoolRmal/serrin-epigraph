module

public import SerrinEpigraph.Basic

/-!
# The three source targets

These are unproved targets, not completed formalizations. No extra reaction assumptions
have been added to resolve the citation gap documented in `docs/statement-audit.md`.
-/

public section

namespace SerrinEpigraph

/-- Image 1: strict vertical monotonicity from zero lower exponential squared-mass growth. -/
theorem verticalDerivative_pos {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ) :
    ∀ x ∈ epigraph g, 0 < verticalDerivative u x := by
  sorry

/-- Image 2: affine and one-dimensional rigidity in ambient dimensions two through eight. -/
theorem rigidity_of_dimension_le_eight {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hdim : m + 1 ≤ 8) : IsAffineOneDimensional g u := by
  sorry

/-- Image 3: rigidity in ambient dimension at least nine under either one-sided linear bound. -/
theorem rigidity_of_oneSidedLinearBound {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hdim : 9 ≤ m + 1) (hg : HasOneSidedLinearBound g) :
    IsAffineOneDimensional g u := by
  sorry

end SerrinEpigraph
