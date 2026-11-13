module

public import SerrinEpigraph.PhaseEnergyShellBound
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Surface-order bounds for unit shells
-/

public section

open MeasureTheory Metric

namespace SerrinEpigraph

/-- Real ball volume scales as the ambient-dimensional power of the radius. -/
theorem real_volume_closedBall_scale (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall (0 : Space (m + 1)) R) =
      R ^ (m + 1) * volume.real (closedBall (0 : Space (m + 1)) 1) := by
  simp only [Measure.real, EuclideanSpace.volume_closedBall, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.ofReal_one,
    one_pow, one_mul, Fintype.card_fin]

/-- The increment of the dimension-th power across a unit interval has surface order. -/
theorem unit_power_increment_le (m : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (R + 1) ^ (m + 1) - R ^ (m + 1) ≤ (m + 1 : ℝ) * 2 ^ m * R ^ m := by
  have h0 : 0 ≤ R := le_trans zero_le_one hR
  have hh := abs_pow_sub_pow_le (a := R + 1) (b := R) (n := m + 1)
  have ha : |R + 1| = R + 1 := abs_of_nonneg (by linarith)
  have hb : |R| = R := abs_of_nonneg h0
  have hmax : max (R + 1) R = R + 1 := max_eq_left (by linarith)
  simp only [ha, hb, hmax, Nat.add_sub_cancel, add_sub_cancel_left, abs_one, one_mul,
    Nat.cast_add, Nat.cast_one] at hh
  have hp : (R + 1) ^ m ≤ (2 * R) ^ m :=
    pow_le_pow_left₀ (by linarith) (by linarith) m
  rw [mul_pow] at hp
  have hm : 0 ≤ (m + 1 : ℝ) := by positivity
  exact (le_abs_self _).trans (hh.trans (by nlinarith))

/-- Unit-shell volume is bounded by a constant times the radius to dimension minus one. -/
theorem real_volume_unitShell_le (m : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    volume.real (closedBall (0 : Space (m + 1)) (R + 1) \ closedBall 0 R) ≤
      (volume.real (closedBall (0 : Space (m + 1)) 1) * (m + 1 : ℝ) * 2 ^ m) * R ^ m := by
  have hsub : closedBall (0 : Space (m + 1)) R ⊆ closedBall 0 (R + 1) :=
    closedBall_subset_closedBall (by linarith)
  rw [measureReal_sdiff hsub isClosed_closedBall.measurableSet
    (isCompact_closedBall (0 : Space (m + 1)) (R + 1)).measure_ne_top]
  rw [real_volume_closedBall_scale m (R := R + 1) (by linarith),
    real_volume_closedBall_scale m (R := R) (by linarith), ← sub_mul]
  have he := mul_le_mul_of_nonneg_right (unit_power_increment_le m hR)
    (measureReal_nonneg : 0 ≤ volume.real (closedBall (0 : Space (m + 1)) 1))
  convert he using 1
  ring

/-- The phase energy of the zero extension grows at most like surface area. -/
theorem RigidityHypotheses.phaseEnergy_surface_growth
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫ x in closedBall 0 R, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ C * R ^ m := by
  obtain ⟨C, hC, hE⟩ := hr.exists_phaseEnergy_unitShell_bound h
  let D := volume.real (closedBall (0 : Space (m + 1)) 1) * (m + 1 : ℝ) * 2 ^ m
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg measureReal_nonneg (by positivity)) (by positivity)
  refine ⟨C * (D + 1), mul_pos hC (by linarith), fun R hR ↦ ?_⟩
  have hs := mul_le_mul_of_nonneg_left (real_volume_unitShell_le m hR) hC.le
  have hp : 0 ≤ R ^ m := pow_nonneg (by linarith) _
  calc
    _ ≤ C * volume.real (closedBall (0 : Space (m + 1)) (R + 1) \ closedBall 0 R) := hE R
    _ ≤ C * (D * R ^ m) := hs
    _ ≤ (C * (D + 1)) * R ^ m := by nlinarith

end SerrinEpigraph
