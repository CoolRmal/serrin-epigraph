module

public import SerrinEpigraph.NormalizedReaction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The normalized potential on the solution range

The potential is the reaction primitive measured from its equilibrium at one.
Its positivity and derivative are derived from the restored source assumptions.
-/

public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The potential normalized to vanish at the positive equilibrium. -/
def normalizedPotential (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in s..1, f t

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The reaction is integrable between any nonnegative point and its equilibrium. -/
theorem Hypotheses.reaction_intervalIntegrable (h : Hypotheses g u f κ)
    {s : ℝ} (hs : 0 ≤ s) : IntervalIntegrable f volume s 1 := by
  apply ContinuousOn.intervalIntegrable
  exact h.reaction_contDiffOn.continuousOn.mono (by
    intro t ht
    exact le_trans (le_min hs zero_le_one) ht.1)

@[simp]
theorem normalizedPotential_one (f : ℝ → ℝ) : normalizedPotential f 1 = 0 := by
  simp [normalizedPotential]

/-- The potential is strictly positive below the equilibrium, including at zero. -/
theorem RigidityHypotheses.normalizedPotential_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : 0 ≤ s) (hsone : s < 1) :
    0 < normalizedPotential f s := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (h.reaction_intervalIntegrable hs)
    (fun t ht ↦ hr.reaction_pos t ⟨lt_of_le_of_lt hs ht.1, ht.2⟩) hsone

/-- The potential is nonnegative throughout the closed normalized solution range. -/
theorem RigidityHypotheses.normalizedPotential_nonneg (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ normalizedPotential f s := by
  rcases lt_or_eq_of_le hs.2 with hlt | rfl
  · exact (hr.normalizedPotential_pos h hs.1 hlt).le
  · simp

/-- There are no other zeros of the potential in the closed normalized solution range. -/
theorem RigidityHypotheses.normalizedPotential_eq_zero_iff
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : normalizedPotential f s = 0 ↔ s = 1 := by
  constructor
  · intro hz
    by_contra hne
    exact (hr.normalizedPotential_pos h hs.1 (lt_of_le_of_ne hs.2 hne)).ne' hz
  · rintro rfl
    simp

/-- On the positive half-line, the potential derivative is minus the reaction. -/
theorem Hypotheses.normalizedPotential_hasDerivAt (h : Hypotheses g u f κ)
    {s : ℝ} (hs : 0 < s) : HasDerivAt (normalizedPotential f) (-f s) s := by
  have hc : ContinuousOn f (Set.Ioi (0 : ℝ)) :=
    h.reaction_contDiffOn.continuousOn.mono Set.Ioi_subset_Ici_self
  exact intervalIntegral.integral_hasDerivAt_left (h.reaction_intervalIntegrable hs.le)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hs))

/-- The first derivative formula on the positive half-line. -/
theorem Hypotheses.normalizedPotential_deriv (h : Hypotheses g u f κ)
    {s : ℝ} (hs : 0 < s) : deriv (normalizedPotential f) s = -f s :=
  (h.normalizedPotential_hasDerivAt hs).deriv

/-- The second derivative formula on the positive half-line. -/
theorem Hypotheses.normalizedPotential_deriv_hasDerivAt (h : Hypotheses g u f κ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (deriv (normalizedPotential f)) (-deriv f s) s := by
  have hd : DifferentiableAt ℝ f s :=
    (h.reaction_contDiffOn.differentiableOn_one s hs.le).differentiableAt
      (Ici_mem_nhds hs)
  apply hd.hasDerivAt.neg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact h.normalizedPotential_deriv ht

/-- The stable equilibrium is a nondegenerate local minimum of the potential. -/
theorem RigidityHypotheses.normalizedPotential_second_deriv_pos
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    0 < deriv (deriv (normalizedPotential f)) 1 := by
  rw [(h.normalizedPotential_deriv_hasDerivAt (show (0 : ℝ) < 1 by norm_num)).deriv]
  exact neg_pos.mpr hr.reaction_deriv_one_neg

end SerrinEpigraph
