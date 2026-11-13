module

public import SerrinEpigraph.RadialFlux
public import Mathlib.Analysis.Real.Sqrt

/-!
# Uniform slope bounds for radial ball profiles
-/

public section
noncomputable section
open Set

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The normalized potential decreases on the full solution range. -/
theorem RigidityHypotheses.normalizedPotential_antitoneOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    AntitoneOn (normalizedPotential f) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
    h.normalizedPotential_continuousOn (f' := fun s ↦ -f s)
  · intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hs
    exact (h.normalizedPotential_hasDerivAt hs'.1).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hs
    exact neg_nonpos.mpr (hr.reaction_pos s hs').le

/-- The one-dimensional energy scale bounds the slope at every radius. -/
theorem RadialBallProfile.slope_sq_le {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {r : ℝ} (ht : r ∈ Icc 0 R) :
    v.slope r ^ 2 ≤ 2 * normalizedPotential f 0 := by
  have he := v.energy_le_center h ht
  have hc := hr.normalizedPotential_nonneg h
    (v.value_range 0 ⟨le_rfl, v.radius_pos.le⟩)
  have hv := v.value_range r ht
  have hw := hr.normalizedPotential_antitoneOn h (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    hv hv.1
  dsimp only [radialEnergy] at he
  linarith

/-- An absolute slope bound independent of the central value and ball radius. -/
theorem RadialBallProfile.abs_slope_le {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {r : ℝ} (ht : r ∈ Icc 0 R) :
    |v.slope r| ≤ Real.sqrt (2 * normalizedPotential f 0) :=
  Real.abs_le_sqrt (v.slope_sq_le hr h ht)

/-- Outside a positive inner radius, curvature energy loss is controlled by the value drop. -/
theorem RadialBallProfile.energy_loss_le_value_drop {R : ℝ}
    (v : RadialBallProfile f m R) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) :
    radialEnergy f v.value v.slope a - radialEnergy f v.value v.slope b ≤
      (m : ℝ) / a * Real.sqrt (2 * normalizedPotential f 0) *
        (v.value a - v.value b) := by
  let B := Real.sqrt (2 * normalizedPotential f 0)
  let C := (m : ℝ) / a * B
  have hsub : Icc a b ⊆ Icc (0 : ℝ) R :=
    fun t ht ↦ ⟨ha.le.trans ht.1, ht.2.trans hb⟩
  have hEc : ContinuousOn (radialEnergy f v.value v.slope) (Icc a b) :=
    (((v.slope_continuous.pow 2).div_const 2).sub
      (h.normalizedPotential_continuousOn.comp v.value_continuous v.value_range)).mono hsub
  have hmono : MonotoneOn
      (fun t ↦ radialEnergy f v.value v.slope t - C * v.value t) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (hEc.sub ((v.value_continuous.mono hsub).const_mul C))
      (f' := fun t ↦ -(m : ℝ) / t * v.slope t ^ 2 - C * v.slope t)
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      have htR : t ∈ Ioo (0 : ℝ) R := ⟨ha.trans ht'.1, ht'.2.trans_le hb⟩
      exact ((h.radialEnergy_hasDerivAt (v.value_derivative t htR)
        (v.slope_derivative t htR) (v.value_pos t htR)).sub
        ((v.value_derivative t htR).const_mul C)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      have htR := hsub (show t ∈ Icc a b from ⟨ht'.1.le, ht'.2.le⟩)
      have hp := v.slope_nonpos hr h htR
      have hB : -v.slope t ≤ B := by
        simpa only [abs_of_nonpos hp] using v.abs_slope_le hr h htR
      have hs : v.slope t ^ 2 ≤ B * (-v.slope t) := by nlinarith
      have hk : (m : ℝ) / t ≤ (m : ℝ) / a :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) ha ht'.1.le
      have he := mul_le_mul hk hs (sq_nonneg (v.slope t))
        (div_nonneg (Nat.cast_nonneg m) ha.le)
      dsimp only [C]
      rw [neg_div]
      nlinarith
  have he := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  dsimp only [C, B] at he
  linarith

/-- The outer-region energy loss tends uniformly to zero with the inner radius. -/
theorem RadialBallProfile.energy_loss_le {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) :
    radialEnergy f v.value v.slope a - radialEnergy f v.value v.slope b ≤
      (m : ℝ) / a * Real.sqrt (2 * normalizedPotential f 0) := by
  have hva := v.value_range a ⟨ha.le, hab.trans hb⟩
  have hvb := v.value_range b ⟨ha.le.trans hab, hb⟩
  have hd : v.value a - v.value b ≤ 1 := by linarith [hva.2, hvb.1]
  exact (v.energy_loss_le_value_drop hr h ha hab hb).trans
    (mul_le_of_le_one_right (by positivity) hd)

end SerrinEpigraph
