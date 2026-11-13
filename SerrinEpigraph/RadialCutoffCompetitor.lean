module

public import SerrinEpigraph.ClosedLipschitzMinimality

/-!
# Competitors extinguishing the positive phase inside a ball
-/

public section
noncomputable section

open Set Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- A one-Lipschitz radial ramp, zero in the radius-R ball and at least one outside R+1. -/
@[expose] def radialRamp {d : ℕ} (R : ℝ) (x : Space d) : ℝ := max 0 (‖x‖ - R)

/-- The radial ramp has Lipschitz constant one. -/
theorem radialRamp_lipschitz (d : ℕ) (R : ℝ) : LipschitzWith 1 (@radialRamp d R) := by
  have hh : LipschitzWith 1 (fun x : Space d ↦ ‖x‖ - R) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using lipschitzWith_one_norm.dist_le_mul x y
  exact hh.const_max 0

/-- Cut the original function down to zero in a ball, preserving it outside a unit shell. -/
@[expose] def radialCutoffCompetitor {d : ℕ} (U : Space d → ℝ) (R : ℝ) (x : Space d) : ℝ :=
  min (U x) (radialRamp R x)

theorem radialCutoffCompetitor_locallyLipschitz {d : ℕ} {U : Space d → ℝ}
    (hU : LocallyLipschitz U) (R : ℝ) : LocallyLipschitz (radialCutoffCompetitor U R) :=
  hU.min (radialRamp_lipschitz d R).locallyLipschitz

/-- The cutoff is a normalized competitor whenever the original function is normalized. -/
theorem radialCutoffCompetitor_mem_Icc {d : ℕ} {U : Space d → ℝ}
    (hU : ∀ x, U x ∈ Icc (0 : ℝ) 1) (R : ℝ) (x : Space d) :
    radialCutoffCompetitor U R x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (hU x).1 (le_max_left _ _), (min_le_left _ _).trans (hU x).2⟩

/-- The cutoff competitor vanishes on the inner closed ball. -/
theorem radialCutoffCompetitor_zero {d : ℕ} {U : Space d → ℝ}
    (hU : ∀ x, 0 ≤ U x) {R : ℝ} {x : Space d} (hx : x ∈ closedBall 0 R) :
    radialCutoffCompetitor U R x = 0 := by
  have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  simp only [radialCutoffCompetitor, radialRamp, max_eq_left (sub_nonpos.mpr hn),
    min_eq_right (hU x)]

/-- Outside the outer ball the cutoff competitor equals the original function. -/
theorem radialCutoffCompetitor_eq {d : ℕ} {U : Space d → ℝ}
    (hU : ∀ x, U x ≤ 1) {R : ℝ} {x : Space d} (hx : R + 1 ≤ ‖x‖) :
    radialCutoffCompetitor U R x = U x := by
  apply min_eq_left
  have hh : 1 ≤ ‖x‖ - R := by linarith
  exact (hU x).trans (hh.trans (le_max_right _ _))

/-- The cutoff perturbation has support inside the outer closed ball. -/
theorem radialCutoffCompetitor_tsupport_subset {d : ℕ} {U : Space d → ℝ}
    (hU : ∀ x, U x ≤ 1) (R : ℝ) :
    tsupport (fun x ↦ radialCutoffCompetitor U R x - U x) ⊆ closedBall 0 (R + 1) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  by_contra hn
  have hnorm : R + 1 < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  exact hx (sub_eq_zero.mpr (radialCutoffCompetitor_eq hU hnorm.le))

/-- Taking a minimum selects one of the two gradients, or the totalized derivative is zero,
provided the first function is differentiable. -/
theorem gradient_min_eq_or {d : ℕ} {U V : Space d → ℝ} {x : Space d}
    (hU : Continuous U) (hV : Continuous V) (hd : DifferentiableAt ℝ U x) :
    gradient (fun z ↦ min (U z) (V z)) x = gradient U x ∨
      gradient (fun z ↦ min (U z) (V z)) x = gradient V x ∨
      gradient (fun z ↦ min (U z) (V z)) x = 0 := by
  rcases lt_trichotomy (U x) (V x) with hx | hx | hx
  · left
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [(isOpen_lt hU hV).mem_nhds hx] with z hz
    exact min_eq_left hz.le
  · by_cases hm : DifferentiableAt ℝ (fun z ↦ min (U z) (V z)) x
    · left
      have hmax : IsLocalMax (fun z ↦ min (U z) (V z) - U z) x := by
        filter_upwards with z
        simp only [min_eq_left hx.le, sub_self]
        exact sub_nonpos.mpr (min_le_left _ _)
      have he := hmax.fderiv_eq_zero
      rw [fderiv_fun_sub hm hd] at he
      simp only [gradient, sub_eq_zero.mp he]
    · right; right
      simp only [gradient, fderiv_zero_of_not_differentiableAt hm, map_zero]
  · right; left
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [(isOpen_lt hV hU).mem_nhds hx] with z hz
    exact min_eq_right hz.le

/-- The cutoff does not add more than one to the squared gradient at differentiability
points of the original function. -/
theorem radialCutoffCompetitor_gradient_sq_le {d : ℕ} {U : Space d → ℝ}
    (hU : Continuous U) {x : Space d} (hd : DifferentiableAt ℝ U x) (R : ℝ) :
    ‖gradient (radialCutoffCompetitor U R) x‖ ^ 2 ≤ ‖gradient U x‖ ^ 2 + 1 := by
  have hr := radialRamp_lipschitz d R
  have hn : ‖gradient (radialRamp R) x‖ ≤ 1 := by
    have he := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hr
    simpa only [gradient, LinearIsometryEquiv.norm_map, NNReal.coe_one] using he
  rcases gradient_min_eq_or hU hr.continuous hd with he | he | he
  · change ‖gradient (fun z ↦ min (U z) (radialRamp R z)) x‖ ^ 2 ≤ _
    rw [he]
    linarith
  · change ‖gradient (fun z ↦ min (U z) (radialRamp R z)) x‖ ^ 2 ≤ _
    rw [he]
    nlinarith [norm_nonneg (gradient (radialRamp R) x), sq_nonneg ‖gradient U x‖]
  · change ‖gradient (fun z ↦ min (U z) (radialRamp R z)) x‖ ^ 2 ≤ _
    rw [he, norm_zero]
    nlinarith [sq_nonneg ‖gradient U x‖]

/-- The radial cutoff costs at most a fixed energy density at differentiability points,
independently of the radius and of the original gradient size. -/
theorem RigidityHypotheses.radialCutoff_phaseEnergy_le
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ M : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hM : 0 ≤ M) (hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ M)
    {U : Space (m + 1) → ℝ} (hU : Continuous U) (hval : ∀ x, U x ∈ Icc (0 : ℝ) 1)
    {x : Space (m + 1)} (hd : DifferentiableAt ℝ U x) (R : ℝ) :
    phaseEnergyDensity f 0 (radialCutoffCompetitor U R) x ≤
      phaseEnergyDensity f 0 U x + (1 / 2 + M) := by
  have hv := radialCutoffCompetitor_mem_Icc hval R x
  have hsq := radialCutoffCompetitor_gradient_sq_le hU hd R
  have hpot := hW _ hv
  have hUpos := hr.normalizedPotential_nonneg h (hval x)
  by_cases hp : 0 < radialCutoffCompetitor U R x
  · have hx : 0 < U x := hp.trans_le (min_le_left _ _)
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, hx, ite_true,
      add_zero]
    linarith
  · simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_false]
    by_cases hx : 0 < U x
    · simp only [hx, ite_true, add_zero]
      nlinarith [sq_nonneg ‖gradient U x‖]
    · simp only [hx, ite_false, zero_add]
      linarith

end SerrinEpigraph
