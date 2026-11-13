module

public import SerrinEpigraph.RadialSlopeBound
public import SerrinEpigraph.PotentialComparison
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Radial profiles near equilibrium
-/

public section
noncomputable section
open Set

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A quadratic potential bound gives a slope bound proportional to distance from equilibrium. -/
theorem RadialBallProfile.neg_slope_le_equilibrium {R C : ℝ}
    (v : RadialBallProfile f m R) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (hC : 0 < C)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ C * (1 - s) ^ 2)
    {r : ℝ} (ht : r ∈ Icc 0 R) :
    -v.slope r ≤ (2 * C + 1) * (1 - v.value r) := by
  have he := v.energy_le_center h ht
  have hc := hr.normalizedPotential_nonneg h
    (v.value_range 0 ⟨le_rfl, v.radius_pos.le⟩)
  have hv := v.value_range r ht
  have hw := hW (v.value r) hv
  dsimp only [radialEnergy] at he
  have hs : v.slope r ^ 2 ≤ 2 * C * (1 - v.value r) ^ 2 := by linarith
  have hk : 2 * C ≤ (2 * C + 1) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hk (sq_nonneg (1 - v.value r))
  have hn : 0 ≤ (2 * C + 1) * (1 - v.value r) := by
    apply mul_nonneg (by positivity) (sub_nonneg.mpr hv.2)
  nlinarith [sq_nonneg (v.slope r + (2 * C + 1) * (1 - v.value r))]

/-- Distance from equilibrium grows at most exponentially in the radius. -/
theorem RadialBallProfile.equilibrium_growth_bound {R K : ℝ}
    (v : RadialBallProfile f m R)
    (hs : ∀ t ∈ Icc (0 : ℝ) R, -v.slope t ≤ K * (1 - v.value t))
    {r : ℝ} (ht : r ∈ Icc 0 R) :
    1 - v.value r ≤ (1 - v.value 0) * Real.exp (K * r) := by
  let F := fun t ↦ Real.exp (-K * t) * (1 - v.value t)
  have hmono : AntitoneOn F (Icc (0 : ℝ) R) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) R)
      ((by fun_prop : Continuous (fun t : ℝ ↦ Real.exp (-K * t))).continuousOn.mul
        (continuousOn_const.sub v.value_continuous))
      (f' := fun t ↦ Real.exp (-K * t) * (-K) * (1 - v.value t) +
        Real.exp (-K * t) * (-v.slope t))
    · intro t hti
      have hti' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hti
      convert
        (((hasDerivAt_id t).const_mul (-K)).exp.mul
          ((v.value_derivative t hti').const_sub 1)).hasDerivWithinAt using 1 <;>
        simp [id_eq, mul_one]
      funext x
      rfl
    · intro t hti
      have hti' : t ∈ Icc (0 : ℝ) R := interior_subset hti
      have he := mul_le_mul_of_nonneg_left (hs t hti') (Real.exp_pos (-K * t)).le
      nlinarith
  have he := hmono ⟨le_rfl, v.radius_pos.le⟩ ht ht.1
  dsimp only [F] at he
  simp only [mul_zero, Real.exp_zero, one_mul] at he
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (K * r)).le
  have hexp : Real.exp (-K * r) * Real.exp (K * r) = 1 := by
    rw [← Real.exp_add]
    rw [show -K * r + K * r = 0 by ring, Real.exp_zero]
  rw [mul_right_comm, hexp, one_mul] at hm
  exact hm

/-- The zero boundary forces a quantitative lower bound on the central deficit. -/
theorem RadialBallProfile.center_deficit_ge_exp {R K : ℝ}
    (v : RadialBallProfile f m R)
    (hs : ∀ t ∈ Icc (0 : ℝ) R, -v.slope t ≤ K * (1 - v.value t)) :
    Real.exp (-K * R) ≤ 1 - v.value 0 := by
  have he := v.equilibrium_growth_bound hs ⟨v.radius_pos.le, le_rfl⟩
  rw [v.boundary_zero, sub_zero] at he
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-K * R)).le
  have hexp : Real.exp (K * R) * Real.exp (-K * R) = 1 := by
    rw [← Real.exp_add, show K * R + -K * R = 0 by ring, Real.exp_zero]
  simpa only [one_mul, mul_assoc, hexp, mul_one] using hm

/-- One reaction-dependent constant controls all normalized ball profiles near equilibrium. -/
theorem RigidityHypotheses.radial_equilibrium_bounds
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (v : RadialBallProfile f m R),
      (∀ r ∈ Icc (0 : ℝ) R,
        1 - v.value r ≤ (1 - v.value 0) * Real.exp (K * r)) ∧
      Real.exp (-K * R) ≤ 1 - v.value 0 := by
  obtain ⟨C, hC, hW⟩ := hr.potential_quadratic_upper_bound h
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro R v
  have hs := fun t ht ↦ v.neg_slope_le_equilibrium hr h hC hW (r := t) ht
  exact ⟨fun _ ht ↦ v.equilibrium_growth_bound hs ht, v.center_deficit_ge_exp hs⟩

/-- A central deficit below the exponential threshold forces a larger radius. -/
theorem RadialBallProfile.radius_gt_of_center_deficit {R K T : ℝ}
    (v : RadialBallProfile f m R) (hK : 0 < K)
    (hb : Real.exp (-K * R) ≤ 1 - v.value 0)
    (ha : 1 - v.value 0 < Real.exp (-K * T)) : T < R := by
  have he : Real.exp (-K * R) < Real.exp (-K * T) := hb.trans_lt ha
  have harg := Real.exp_lt_exp.mp he
  nlinarith

end SerrinEpigraph
