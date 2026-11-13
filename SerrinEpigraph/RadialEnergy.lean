module

public import SerrinEpigraph.QuadraticPotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Dissipation of radial profile energy

The profile data include the radial equation explicitly. No existence of
radial comparison solutions is assumed or asserted by this module.
-/

public section
noncomputable section

namespace SerrinEpigraph

/-- The mechanical energy of a scalar profile and its radial derivative. -/
@[expose] def radialEnergy (f q p : ℝ → ℝ) (r : ℝ) : ℝ :=
  (p r) ^ 2 / 2 - normalizedPotential f (q r)

/-- Data of a normalized radial solution in a ball of ambient dimension `m + 1`. -/
structure RadialBallProfile (f : ℝ → ℝ) (m : ℕ) (R : ℝ) where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  radius_pos : 0 < R
  value_continuous : ContinuousOn value (Set.Icc 0 R)
  slope_continuous : ContinuousOn slope (Set.Icc 0 R)
  value_range : ∀ r ∈ Set.Icc 0 R, value r ∈ Set.Icc 0 1
  value_pos : ∀ r ∈ Set.Ioo 0 R, 0 < value r
  value_derivative : ∀ r ∈ Set.Ioo 0 R, HasDerivAt value (slope r) r
  slope_derivative : ∀ r ∈ Set.Ioo 0 R,
    HasDerivAt slope (-f (value r) - (m : ℝ) / r * slope r) r
  slope_zero : slope 0 = 0
  boundary_zero : value R = 0

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The radial curvature term is exactly the energy dissipation rate. -/
theorem Hypotheses.radialEnergy_hasDerivAt (h : Hypotheses g u f κ)
    {q p : ℝ → ℝ} {r : ℝ} (hq : HasDerivAt q (p r) r)
    (hp : HasDerivAt p (-f (q r) - (m : ℝ) / r * p r) r) (hpos : 0 < q r) :
    HasDerivAt (radialEnergy f q p) (-(m : ℝ) / r * (p r) ^ 2) r := by
  have he := ((hp.pow 2).div_const 2).sub
    ((h.normalizedPotential_hasDerivAt hpos).comp r hq)
  convert he using 1
  · rfl
  · ring

/-- The radial energy is nonincreasing from the center to the boundary. -/
theorem RadialBallProfile.energy_antitoneOn {R : ℝ} (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) :
    AntitoneOn (radialEnergy f v.value v.slope) (Set.Icc 0 R) := by
  have hc : ContinuousOn (radialEnergy f v.value v.slope) (Set.Icc 0 R) :=
    ((v.slope_continuous.pow 2).div_const 2).sub
      (h.normalizedPotential_continuousOn.comp v.value_continuous v.value_range)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) R) hc
    (f' := fun r ↦ -(m : ℝ) / r * (v.slope r) ^ 2)
  · intro r hr
    have hr' : r ∈ Set.Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hr
    exact (h.radialEnergy_hasDerivAt (v.value_derivative r hr') (v.slope_derivative r hr')
      (v.value_pos r hr')).hasDerivWithinAt
  · intro r hr
    have hr' : r ∈ Set.Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hr
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) hr'.1.le)
      (sq_nonneg _)

/-- Every radius has energy at most the negative central potential. -/
theorem RadialBallProfile.energy_le_center {R : ℝ} (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) {r : ℝ} (hr : r ∈ Set.Icc 0 R) :
    radialEnergy f v.value v.slope r ≤ -normalizedPotential f (v.value 0) := by
  have he := v.energy_antitoneOn h ⟨le_rfl, v.radius_pos.le⟩ hr hr.1
  simpa only [radialEnergy, v.slope_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, zero_sub] using he

/-- The boundary slope of a radial ball solution is bounded by the one-dimensional energy scale. -/
theorem RadialBallProfile.boundary_slope_sq_le {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    (v.slope R) ^ 2 ≤ 2 * normalizedPotential f 0 := by
  have he := v.energy_le_center h ⟨v.radius_pos.le, le_rfl⟩
  have hW := hr.normalizedPotential_nonneg h (v.value_range 0 ⟨le_rfl, v.radius_pos.le⟩)
  simp only [radialEnergy, v.boundary_zero] at he
  linarith

/-- A central value strictly below equilibrium gives a strict boundary-slope bound. -/
theorem RadialBallProfile.boundary_slope_sq_lt {R : ℝ} (v : RadialBallProfile f m R)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hv : v.value 0 < 1) :
    (v.slope R) ^ 2 < 2 * normalizedPotential f 0 := by
  have he := v.energy_le_center h ⟨v.radius_pos.le, le_rfl⟩
  have hW := hr.normalizedPotential_pos h
    (v.value_range 0 ⟨le_rfl, v.radius_pos.le⟩).1 hv
  simp only [radialEnergy, v.boundary_zero] at he
  linarith

/-- Away from the radial origin, the energy loss equals the integrated curvature dissipation. -/
theorem RadialBallProfile.energy_loss_eq_integral {R : ℝ} (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) :
    radialEnergy f v.value v.slope a - radialEnergy f v.value v.slope b =
      ∫ r in a..b, (m : ℝ) / r * (v.slope r) ^ 2 := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) R :=
    fun r hr ↦ ⟨ha.le.trans hr.1, hr.2.trans hb⟩
  have hc : ContinuousOn (radialEnergy f v.value v.slope) (Set.Icc a b) :=
    (((v.slope_continuous.pow 2).div_const 2).sub
      (h.normalizedPotential_continuousOn.comp v.value_continuous v.value_range)).mono hsub
  have hd : ∀ r ∈ Set.Ioo a b,
      HasDerivAt (radialEnergy f v.value v.slope) (-(m : ℝ) / r * (v.slope r) ^ 2) r := by
    intro r hr
    have hr' : r ∈ Set.Ioo (0 : ℝ) R := ⟨ha.trans hr.1, hr.2.trans_le hb⟩
    exact h.radialEnergy_hasDerivAt (v.value_derivative r hr') (v.slope_derivative r hr')
      (v.value_pos r hr')
  have hdiv : ContinuousOn (fun r : ℝ ↦ -(m : ℝ) / r) (Set.Icc a b) :=
    continuousOn_const.div continuousOn_id (fun r hr ↦ (ha.trans_le hr.1).ne')
  have hi := (hdiv.mul ((v.slope_continuous.mono hsub).pow 2)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd hi
  have hneg : (fun r ↦ -(m : ℝ) / r * (v.slope r) ^ 2) =
      (fun r ↦ -((m : ℝ) / r * (v.slope r) ^ 2)) := by
    funext r
    ring
  rw [hneg, intervalIntegral.integral_neg] at he
  linarith

end SerrinEpigraph
