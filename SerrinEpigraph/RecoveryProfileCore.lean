module

public import SerrinEpigraph.RecoveryTravelTime
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The inverse regularized transition profile
-/

public section

open Set

namespace SerrinEpigraph

/-- Inverse travel-time profile on the finite transition interval. Its behavior outside
that interval is intentionally unspecified until the constant-phase extension. -/
@[expose] noncomputable def recoveryProfileCore (f : ℝ → ℝ) (δ : ℝ) : ℝ → ℝ :=
  Function.invFunOn (recoveryTravelTime f δ) (Icc (0 : ℝ) 1)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- The travel-time coordinate covers exactly the finite transition interval. -/
theorem RigidityHypotheses.recoveryTravelTime_image
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    recoveryTravelTime f δ '' Icc (0 : ℝ) 1 = Icc 0 (recoveryTravelTime f δ 1) := by
  simpa only [recoveryTravelTime_zero] using
    (hr.recoveryTravelTime_continuousOn h hδ).image_Icc_of_monotoneOn zero_le_one
      (hr.recoveryTravelTime_strictMonoOn h hδ).monotoneOn

/-- The inverse stays normalized and recovers the prescribed travel time. -/
theorem RigidityHypotheses.recoveryProfileCore_spec
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 (recoveryTravelTime f δ 1)) :
    recoveryProfileCore f δ t ∈ Icc (0 : ℝ) 1 ∧
      recoveryTravelTime f δ (recoveryProfileCore f δ t) = t := by
  have hi : t ∈ recoveryTravelTime f δ '' Icc (0 : ℝ) 1 := by
    rw [hr.recoveryTravelTime_image h hδ]
    exact ht
  exact Function.invFunOn_pos hi

/-- Travelling to any normalized value and then inverting recovers that value. -/
theorem RigidityHypotheses.recoveryProfileCore_travelTime
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    recoveryProfileCore f δ (recoveryTravelTime f δ s) = s :=
  (hr.recoveryTravelTime_strictMonoOn h hδ).injOn.leftInvOn_invFunOn hs

/-- The profile begins at zero. -/
theorem RigidityHypotheses.recoveryProfileCore_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    recoveryProfileCore f δ 0 = 0 := by
  simpa only [recoveryTravelTime_zero] using
    hr.recoveryProfileCore_travelTime h hδ (show (0 : ℝ) ∈ Icc 0 1 by norm_num)

/-- The profile reaches one at the full transition time. -/
theorem RigidityHypotheses.recoveryProfileCore_end
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    recoveryProfileCore f δ (recoveryTravelTime f δ 1) = 1 :=
  hr.recoveryProfileCore_travelTime h hδ (by norm_num)

/-- The inverse profile is strictly increasing throughout its transition interval. -/
theorem RigidityHypotheses.recoveryProfileCore_strictMonoOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    StrictMonoOn (recoveryProfileCore f δ) (Icc 0 (recoveryTravelTime f δ 1)) := by
  intro a ha b hb hab
  obtain ⟨hqa, hea⟩ := hr.recoveryProfileCore_spec h hδ ha
  obtain ⟨hqb, heb⟩ := hr.recoveryProfileCore_spec h hδ hb
  by_contra hn
  have he := (hr.recoveryTravelTime_strictMonoOn h hδ).monotoneOn hqb hqa
    (le_of_not_gt hn)
  rw [hea, heb] at he
  exact (not_le_of_gt hab) he

end SerrinEpigraph
