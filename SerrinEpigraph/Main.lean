module

public import SerrinEpigraph.Nonnegative
public import SerrinEpigraph.StrongMaximum
public import SerrinEpigraph.RigidityReduction

/-!
# The three source targets

All three targets are proved. The two rigidity theorems are derived in
`SerrinEpigraph.RigidityReduction`, whose named obligations are all proved; the three theorems
below depend only on the standard axioms. The dimension bound of the one-sided theorem only
delimits the case: its proof does not need it.
Their reaction and boundedness assumptions include the source conversation and notes;
see `docs/scope-correction.md`.
-/

public section

namespace SerrinEpigraph

/-- Image 1: strict vertical monotonicity from zero lower exponential squared-mass growth. -/
theorem verticalDerivative_pos {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ) :
    ∀ x ∈ epigraph g, 0 < verticalDerivative u x :=
  h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg

/-- Image 2: affine and one-dimensional rigidity in ambient dimensions two through eight. -/
theorem rigidity_of_dimension_le_eight {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hr : RigidityHypotheses g u f) (hdim : m + 1 ≤ 8) :
    IsAffineOneDimensional g u :=
  hr.isAffineOneDimensional_of_le_eight h hdim

/-- Image 3: rigidity in ambient dimension at least nine under either one-sided linear bound. -/
theorem rigidity_of_oneSidedLinearBound {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hr : RigidityHypotheses g u f)
    (hdim : 9 ≤ m + 1) (hg : HasOneSidedLinearBound g) :
    IsAffineOneDimensional g u :=
  hr.isAffineOneDimensional_of_oneSidedLinearBound h hg

end SerrinEpigraph
