module

public import SerrinEpigraph.SharpRadialLimit

/-!
# Energy scale monotonicity and the remaining Modica condition
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A nonnegative bulk coefficient in the scale formula gives monotonicity of
every nonnegative decreasing smooth radial energy weight. -/
theorem RigidityHypotheses.weighted_energy_monotone_of_coefficient_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (a : ℤ) (hA : ∀ x ∈ epigraph g,
      0 ≤ ((a : ℝ) + m - 1) / 2 * ‖gradient u x‖ ^ 2 +
        ((a : ℝ) + m + 1) * normalizedPotential f (u x))
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hq0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ q s) (hqanti : Antitone q)
    (c : Space (m + 1)) :
    MonotoneOn (fun r ↦ r ^ a * ∫ x in epigraph g,
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * radialWeight q c r x) (Ioi 0) := by
  have hd (r : ℝ) (hr0 : 0 < r) := hr.radial_energy_hasDerivAt h basis hq hzero c a hr0
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · exact fun r hr0 ↦ (hd r hr0).continuousAt.continuousWithinAt
  · exact fun r hr0 ↦ (hd r (interior_subset hr0)).differentiableAt.differentiableWithinAt
  · intro r hr0
    have hrpos : 0 < r := interior_subset hr0
    rw [(hd r hrpos).deriv]
    apply mul_nonneg (zpow_nonneg hrpos.le _)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
      with x hx
    have hfirst := mul_nonneg (hA x hx) (hq0 (‖x - c‖ ^ 2 / r ^ 2) (by positivity))
    have hsecond : 2 / r ^ 2 * radialWeight (deriv q) c r x *
        (inner ℝ (gradient u x) (x - c)) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hqanti.deriv_nonpos) (sq_nonneg _)
    exact sub_nonneg.mpr (hsecond.trans hfirst)

/-- Removing smooth cutoffs transfers scale monotonicity to the exact ball energy. -/
theorem RigidityHypotheses.ball_energy_monotone_of_coefficient_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (a : ℤ) (hA : ∀ x ∈ epigraph g,
      0 ≤ ((a : ℝ) + m - 1) / 2 * ‖gradient u x‖ ^ 2 +
        ((a : ℝ) + m + 1) * normalizedPotential f (u x))
    (c : Space (m + 1)) :
    MonotoneOn (fun r ↦ r ^ a * ∫ x in closedBall c r,
      phaseEnergyDensity f 0 (zeroExtension g u) x) (Ioi 0) := by
  have hmono (j : ℕ) := hr.weighted_energy_monotone_of_coefficient_nonneg h basis a hA
    (sharpRadialProfile_contDiff j) (fun s hs ↦ sharpRadialProfile_zero j hs)
    (fun s _ ↦ (sharpRadialProfile_mem_Icc j s).1) (sharpRadialProfile_antitone j) c
  have hlim (r : ℝ) (hr0 : 0 < r) :=
    (integral_sharpRadialProfile_tendsto c hr0
      (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall c (2 * r))))
        |>.const_mul (r ^ a)
  intro r hr0 s hs0 hrs
  have hlimr := hlim r hr0
  have hlims := hlim s hs0
  simp only [h.integral_phaseEnergy_mul] at hlimr hlims
  apply le_of_tendsto_of_tendsto hlimr hlims
  exact Eventually.of_forall (fun j ↦ hmono j hr0 hs0 hrs)

/-- The Dirichlet-normalized ball energy is monotone under the original hypotheses.
In ambient dimension n = m + 1 this is the exponent 2 - n. -/
theorem RigidityHypotheses.dirichlet_scaled_energy_monotone
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (c : Space (m + 1)) :
    MonotoneOn (fun r ↦ r ^ (1 - (m : ℤ)) * ∫ x in closedBall c r,
      phaseEnergyDensity f 0 (zeroExtension g u) x) (Ioi 0) := by
  apply hr.ball_energy_monotone_of_coefficient_nonneg h basis (1 - (m : ℤ)) _ c
  intro x hx
  have hW := hr.normalizedPotential_nonneg h ⟨(h.positive x hx).le,
    (hr.solution_lt_one x hx).le⟩
  simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast]
  nlinarith

/-- Surface-normalized ball energy is monotone once the Modica bound is available.
The bound remains an explicit additional premise here; it has not been proved from Hypotheses. -/
theorem RigidityHypotheses.surface_scaled_energy_monotone_of_modica
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (hmodica : ∀ x ∈ epigraph g, ‖gradient u x‖ ^ 2 / 2 ≤ normalizedPotential f (u x))
    (c : Space (m + 1)) :
    MonotoneOn (fun r ↦ r ^ (-(m : ℤ)) * ∫ x in closedBall c r,
      phaseEnergyDensity f 0 (zeroExtension g u) x) (Ioi 0) := by
  apply hr.ball_energy_monotone_of_coefficient_nonneg h basis (-(m : ℤ)) _ c
  intro x hx
  have hM := hmodica x hx
  simp only [Int.cast_neg, Int.cast_natCast]
  nlinarith

end SerrinEpigraph
