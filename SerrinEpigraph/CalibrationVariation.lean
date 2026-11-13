module

public import SerrinEpigraph.FoliationPullback

/-!
# First variation of the calibrated energy density
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The affine energy density supplied by the foliation. -/
@[expose] def RigidityHypotheses.calibratedDensity (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : ℝ) (z : Space (m + 1)) : ℝ :=
  inner ℝ (hr.levelGradient h (y, s)) z - ‖hr.levelGradient h (y, s)‖ ^ 2 / 2 +
    normalizedPotential f s

/-- The calibrated density differentiates along any differentiable level and gradient paths. -/
theorem RigidityHypotheses.calibratedDensity_hasDerivAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) {s : ℝ → ℝ} {z : ℝ → Space (m + 1)}
    {t a : ℝ} {w : Space (m + 1)} (hs : HasDerivAt s a t) (hz : HasDerivAt z w t)
    (hval : s t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r ↦ hr.calibratedDensity h y (s r) (z r))
      (inner ℝ (hr.levelGradient h (y, s t)) w +
        (inner ℝ (fderiv ℝ (hr.levelGradient h) (y, s t) (0, 1))
          (z t - hr.levelGradient h (y, s t)) - f (s t)) * a) t := by
  have hp : HasDerivAt (fun r ↦ (y, s r)) (0, a) t := (hasDerivAt_const t y).prodMk hs
  have hB := ((hr.levelGradient_contDiffAt h (p := (y, s t)) hval).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hp
  have hW := (h.normalizedPotential_hasDerivAt hval.1).comp t hs
  have he := ((hB.inner ℝ hz).sub (hB.norm_sq.div_const 2)).add hW
  have ha : (0, a) = a • ((0 : Space m), (1 : ℝ)) := by simp
  rw [ha, map_smul] at he
  convert he using 1
  · rfl
  · simp only [Function.comp_apply, inner_sub_right,
      real_inner_smul_right, real_inner_comm]
    ring

/-- The calibrated density is bounded above by the ordinary energy density. -/
theorem RigidityHypotheses.calibratedDensity_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : ℝ) (z : Space (m + 1)) :
    hr.calibratedDensity h y s z ≤ ‖z‖ ^ 2 / 2 + normalizedPotential f s :=
  hr.levelGradient_energy_bound h (y, s) z

/-- The original solution attains equality in the calibrated energy bound. -/
theorem RigidityHypotheses.calibratedDensity_solution (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    hr.calibratedDensity h (horizontal x) (u x) (gradient u x) =
      ‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x) :=
  hr.levelGradient_energy_eq h hx

/-- The integrated first variation of the calibrated density vanishes for compact variations. -/
theorem RigidityHypotheses.calibratedDensity_firstVariation (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {v φ : Space (m + 1) → ℝ} {Ω : Set (Space (m + 1))}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hval : ∀ x ∈ Ω, v x ∈ Set.Ioo (0 : ℝ) 1)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    (∫ x, inner ℝ (hr.comparisonField h v x) (gradient φ x) +
      (inner ℝ (fderiv ℝ (hr.levelGradient h) (horizontal x, v x) (0, 1))
        (gradient v x - hr.comparisonField h v x) - f (v x)) * φ x) = 0 := by
  let b := stdOrthonormalBasis ℝ (Space (m + 1))
  have he := integral_field_variation_eq_zero (μ := volume) hΩ
    (hr.comparisonField_contDiffOn h hΩ hv hval) hφ hφc hsub b
  rw [← he]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · rw [hr.comparisonField_trace h
      ((hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)) (hval x hx) b]
    ring
  · have hz : φ x = 0 := Function.notMem_support.mp
      (fun hx' ↦ hx (hsub (subset_tsupport φ hx')))
    simp [hz]

end SerrinEpigraph
