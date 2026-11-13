module

public import SerrinEpigraph.RadialEquilibrium
public import SerrinEpigraph.RadialRiccati

/-!
# Boundary energy of radial ball profiles
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The boundary energy deficit is bounded by inner potential plus outer curvature loss. -/
theorem RadialBallProfile.boundary_energy_deficit_le {R a : ℝ}
    (v : RadialBallProfile f m R) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (ha : 0 < a) (haR : a ≤ R) :
    normalizedPotential f 0 - v.slope R ^ 2 / 2 ≤
      normalizedPotential f (v.value a) +
        (m : ℝ) / a * Real.sqrt (2 * normalizedPotential f 0) := by
  have he := v.energy_loss_le hr h ha haR le_rfl
  simp only [radialEnergy, v.boundary_zero] at he
  nlinarith [sq_nonneg (v.slope a)]

/-- Explicit control of boundary energy by the central deficit and an inner radius. -/
theorem RadialBallProfile.boundary_energy_deficit_le_exp {R a C : ℝ}
    (v : RadialBallProfile f m R) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (hC : 0 < C)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, normalizedPotential f s ≤ C * (1 - s) ^ 2)
    (ha : 0 < a) (haR : a ≤ R) :
    normalizedPotential f 0 - v.slope R ^ 2 / 2 ≤
      C * ((1 - v.value 0) * Real.exp ((2 * C + 1) * a)) ^ 2 +
        (m : ℝ) / a * Real.sqrt (2 * normalizedPotential f 0) := by
  have hva := v.value_range a ⟨ha.le, haR⟩
  have hg := v.equilibrium_growth_bound
    (fun t ht ↦ v.neg_slope_le_equilibrium hr h hC hW (r := t) ht) ⟨ha.le, haR⟩
  have hsq := sq_le_sq₀ (sub_nonneg.mpr hva.2) ((sub_nonneg.mpr hva.2).trans hg)
  have hpot := (hW (v.value a) hva).trans
    (mul_le_mul_of_nonneg_left (hsq.mpr hg) hC.le)
  have he := v.boundary_energy_deficit_le hr h ha haR
  linarith

/-- Boundary energies approach the one-dimensional value uniformly as central values approach one. -/
theorem RigidityHypotheses.radial_boundary_energy_approximation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ) (v : RadialBallProfile f m R),
      1 - v.value 0 < δ →
      0 ≤ normalizedPotential f 0 - v.slope R ^ 2 / 2 ∧
      normalizedPotential f 0 - v.slope R ^ 2 / 2 < ε := by
  obtain ⟨C, hC, hW⟩ := hr.potential_quadratic_upper_bound h
  let B := Real.sqrt (2 * normalizedPotential f 0)
  let a := 2 * ((m : ℝ) * B) / ε + 1
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have ha : 0 < a := by dsimp [a]; positivity
  have htail : (m : ℝ) / a * B < ε / 2 := by
    have he : 2 * ((m : ℝ) * B) / ε < a := by dsimp [a]; linarith
    have hm := (div_lt_iff₀ hε).mp he
    rw [div_mul_eq_mul_div, div_lt_iff₀ ha]
    nlinarith
  let K := 2 * C + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : ContinuousAt (fun d : ℝ ↦ C * (d * Real.exp (K * a)) ^ 2) 0 := by fun_prop
  have hev : ∀ᶠ d in 𝓝 (0 : ℝ), C * (d * Real.exp (K * a)) ^ 2 < ε / 2 :=
    hc.eventually (gt_mem_nhds (by simpa using half_pos hε))
  obtain ⟨η, hη, hsmall⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min η (Real.exp (-K * a)), lt_min hη (Real.exp_pos _), ?_⟩
  intro R v hv
  have hs := fun t ht ↦ v.neg_slope_le_equilibrium hr h hC hW (r := t) ht
  have haR : a < R := v.radius_gt_of_center_deficit hK (v.center_deficit_ge_exp hs)
    (hv.trans_le (min_le_right _ _))
  have hdnonneg : 0 ≤ 1 - v.value 0 :=
    sub_nonneg.mpr (v.value_range 0 ⟨le_rfl, v.radius_pos.le⟩).2
  have hsmall' := hsmall (show dist (1 - v.value 0) 0 < η by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hdnonneg]
    exact hv.trans_le (min_le_left _ _))
  have he := v.boundary_energy_deficit_le_exp hr h hC hW ha haR.le
  have hlo := v.boundary_slope_sq_le hr h
  refine ⟨by linarith, ?_⟩
  change C * ((1 - v.value 0) * Real.exp ((2 * C + 1) * a)) ^ 2 < ε / 2 at hsmall'
  change (m : ℝ) / a * Real.sqrt (2 * normalizedPotential f 0) < ε / 2 at htail
  linarith

/-- Arbitrarily large comparison balls exist with boundary energy arbitrarily near the limit. -/
theorem RigidityHypotheses.exists_large_radialBallProfile
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ R : ℝ, ∃ v : RadialBallProfile f m R, T < R ∧
      0 ≤ normalizedPotential f 0 - v.slope R ^ 2 / 2 ∧
      normalizedPotential f 0 - v.slope R ^ 2 / 2 < ε := by
  obtain ⟨δ, hδ, henergy⟩ := hr.radial_boundary_energy_approximation h hε
  obtain ⟨K, hK, hbounds⟩ := hr.radial_equilibrium_bounds h
  let d := min 1 (min δ (Real.exp (-K * T)))
  have hd : 0 < d := lt_min zero_lt_one (lt_min hδ (Real.exp_pos _))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdδ : d ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hdexp : d ≤ Real.exp (-K * T) := (min_le_right _ _).trans (min_le_right _ _)
  have ha : 1 - d / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  obtain ⟨R, v, hv⟩ := hr.exists_radialBallProfile h ha
  have hdef : 1 - v.value 0 = d / 2 := by rw [hv]; ring
  have hsmall : 1 - v.value 0 < δ := by rw [hdef]; linarith
  refine ⟨R, v, ?_, henergy R v hsmall⟩
  apply v.radius_gt_of_center_deficit hK (hbounds R v).2
  rw [hdef]
  linarith

end SerrinEpigraph
