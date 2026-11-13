module

public import SerrinEpigraph.ConicalPhaseLimit

/-!
# A positive lower bound for rescaled energy
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The phase energy is strictly positive at every point of the original epigraph. -/
theorem RigidityHypotheses.phaseEnergy_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    0 < phaseEnergyDensity f 0 (zeroExtension g u) x := by
  have hp := (h.zeroExtension_pos_iff x).mpr hx
  simp only [phaseEnergyDensity, indicator_apply, mem_ofPred_eq, hp, ite_true, add_zero]
  exact add_pos_of_nonneg_of_pos (by positivity)
    (hr.normalizedPotential_pos h hp.le (hr.zeroExtension_lt_one x))

/-- Some ball centered at the origin has strictly positive phase energy. -/
theorem RigidityHypotheses.exists_positive_ball_energy (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ r : ℝ, 0 < r ∧ 0 < ∫ x in closedBall 0 r, phaseEnergyDensity f 0 (zeroExtension g u) x := by
  let p := point (0 : Space m) (g 0 + 1)
  have hp : p ∈ epigraph g := by simp [p, epigraph]
  let r := ‖p‖ + 1
  have hr0 : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr0, ?_⟩
  apply (integral_pos_iff_support_of_nonneg
    (hr.phaseEnergy_zeroExtension_nonneg h (by norm_num))
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall _ _))).mpr
  have hsupport : Function.support (phaseEnergyDensity f 0 (zeroExtension g u)) = epigraph g := by
    ext x
    constructor
    · intro hx
      by_contra hn
      have hp : ¬0 < zeroExtension g u x := fun hp ↦ hn ((h.zeroExtension_pos_iff x).mp hp)
      exact hx (by simp [phaseEnergyDensity, hp])
    · intro hx
      exact (hr.phaseEnergy_pos h hx).ne'
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  rw [hsupport, Measure.restrict_apply hΩ.measurableSet]
  have hpos : 0 < volume (epigraph g ∩ ball 0 r) :=
    (hΩ.inter isOpen_ball).measure_pos volume ⟨p, hp, by
      simp only [mem_ball, dist_zero_right]
      dsimp [r]
      linarith⟩
  exact hpos.trans_le (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))

/-- Surface-energy monotonicity forces a uniform positive lower bound on the rescaled unit-ball
energy at all sufficiently large scales. -/
theorem RigidityHypotheses.rescaledEnergy_eventually_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℝ in atTop,
      c ≤ ∫ x in closedBall 0 1,
        rescaledPhaseEnergyDensity f R (fun y ↦ zeroExtension g u (R • y)) x := by
  obtain ⟨r, hr0, hEr⟩ := hr.exists_positive_ball_energy h
  refine ⟨r ^ (-(m : ℤ)) * ∫ x in closedBall 0 r,
    phaseEnergyDensity f 0 (zeroExtension g u) x, mul_pos (zpow_pos hr0 _) hEr, ?_⟩
  filter_upwards [eventually_ge_atTop r] with R hR
  have hR0 : 0 < R := hr0.trans_le hR
  have hm := hr.surface_scaled_energy_monotone h 0 hr0 hR0 hR
  rw [integral_rescaledPhaseEnergyDensity f _ hR0 1, mul_one]
  simpa only [zpow_neg, zpow_natCast] using hm

end SerrinEpigraph
