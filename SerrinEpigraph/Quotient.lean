module

public import SerrinEpigraph.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The negative directional quotient
-/

@[expose] public section

noncomputable section

namespace SerrinEpigraph

/-- The negative part of the vertical derivative divided by the positive solution. -/
def negativeQuotient {m : ℕ} (u : Space (m + 1) → ℝ) (x : Space (m + 1)) : ℝ :=
  max (-(verticalDerivative u x) / u x) 0

theorem negativeQuotient_nonneg {m : ℕ} (u : Space (m + 1) → ℝ) (x : Space (m + 1)) :
    0 ≤ negativeQuotient u x := le_max_right _ _

/-- The negative quotient vanishes exactly when the vertical derivative is nonnegative. -/
theorem negativeQuotient_eq_zero_iff {m : ℕ} {u : Space (m + 1) → ℝ}
    {x : Space (m + 1)} (hu : 0 < u x) :
    negativeQuotient u x = 0 ↔ 0 ≤ verticalDerivative u x := by
  rw [negativeQuotient, max_eq_right_iff, div_le_iff₀ hu, zero_mul, neg_nonpos]

/-- The directional-derivative origin of the quotient supplies one extra power. -/
theorem verticalDerivative_mul_negativeQuotient_pow {m k : ℕ}
    {u : Space (m + 1) → ℝ} {x : Space (m + 1)} (hu : 0 < u x) (hk : k ≠ 0) :
    verticalDerivative u x * negativeQuotient u x ^ k =
      -u x * negativeQuotient u x ^ (k + 1) := by
  by_cases hv : 0 ≤ verticalDerivative u x
  · rw [(negativeQuotient_eq_zero_iff hu).2 hv]
    simp [hk]
  · have hquot : negativeQuotient u x = -verticalDerivative u x / u x := by
      exact max_eq_left (div_nonneg (neg_nonneg.mpr (le_of_not_ge hv)) hu.le)
    rw [pow_succ]
    have hid : -u x * negativeQuotient u x = verticalDerivative u x := by
      rw [hquot]
      field_simp
    calc
      _ = (-u x * negativeQuotient u x) * negativeQuotient u x ^ k := by rw [hid]
      _ = _ := by ring

end SerrinEpigraph
