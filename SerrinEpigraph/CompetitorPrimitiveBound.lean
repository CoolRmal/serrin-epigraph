module

public import SerrinEpigraph.GraphRecoverySequence
public import SerrinEpigraph.PrimitiveEnergyLowerBound

/-!
# Exact primitive-energy bounds for normalized competitors
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The phase primitive preserves local Lipschitz regularity of any normalized competitor. -/
theorem RigidityHypotheses.phasePrimitive_comp_locallyLipschitz
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space d → ℝ} (hv : LocallyLipschitz v) (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1) :
    LocallyLipschitz (fun x ↦ phasePrimitive f (v x)) := by
  intro x
  obtain ⟨C, S, hS, hC⟩ := hv x
  exact ⟨_, S, hS, (hr.phasePrimitive_lipschitzOn h).comp hC (fun y _ ↦ hval y)⟩

/-- At differentiability points the primitive gradient is controlled by the
rescaled energy, including both endpoints of the normalized range. -/
theorem RigidityHypotheses.competitorPrimitive_gradient_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space d → ℝ} (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 < R) {x : Space d} (hv : DifferentiableAt ℝ v x) :
    ‖gradient (fun y ↦ phasePrimitive f (v y)) x‖ ≤
      rescaledPhaseEnergyDensity f R v x := by
  by_cases hzero : v x = 0
  · have hmin : IsLocalMin (fun y ↦ phasePrimitive f (v y)) x := by
      filter_upwards with y
      simpa only [hzero, phasePrimitive_zero] using (h.phasePrimitive_mem_Icc (hval y)).1
    simp only [gradient, hmin.fderiv_eq_zero, map_zero, norm_zero]
    exact hr.rescaledPhaseEnergyDensity_nonneg h hR.le hval x
  by_cases hone : v x = 1
  · have hmax : IsLocalMax (fun y ↦ phasePrimitive f (v y)) x := by
      filter_upwards with y
      simpa only [hone] using (h.phasePrimitive_mem_Icc (hval y)).2
    simp only [gradient, hmax.fderiv_eq_zero, map_zero, norm_zero]
    exact hr.rescaledPhaseEnergyDensity_nonneg h hR.le hval x
  have hx : v x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (hval x).1 (Ne.symm hzero), lt_of_le_of_ne (hval x).2 hone⟩
  have hd := (h.phasePrimitive_hasDerivAt hx).comp_hasFDerivAt x hv.hasFDerivAt
  simp only [Function.comp_def] at hd
  have hg : gradient (fun y ↦ phasePrimitive f (v y)) x =
      Real.sqrt (2 * normalizedPotential f (v x)) • gradient v x := by
    simp only [gradient, hd.fderiv, map_smul]
  rw [hg, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [rescaledPhaseEnergyDensity, indicator_of_mem (s := {y | 0 < v y}) hx.1]
  have hw := hr.normalizedPotential_nonneg h (hval x)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * normalizedPotential f (v x) by positivity)
  have hsq := sq_nonneg
    (‖gradient v x‖ - R * Real.sqrt (2 * normalizedPotential f (v x)))
  apply (mul_le_mul_iff_of_pos_right (show 0 < 2 * R by positivity)).mp
  have he : (‖gradient v x‖ ^ 2 / (2 * R) + R * normalizedPotential f (v x)) *
      (2 * R) = ‖gradient v x‖ ^ 2 + 2 * R ^ 2 * normalizedPotential f (v x) := by
    field_simp
  rw [he]
  have hsR : (R * Real.sqrt (2 * normalizedPotential f (v x))) ^ 2 =
      2 * R ^ 2 * normalizedPotential f (v x) := by rw [mul_pow, hs]; ring
  nlinarith

/-- Every normalized locally Lipschitz competitor controls its primitive gradient
mass by its diffuse energy on compact sets, with coefficient one. -/
theorem RigidityHypotheses.competitorPrimitive_gradient_integral_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space d → ℝ} (hv : LocallyLipschitz v) (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 < R) {K : Set (Space d)} (hK : IsCompact K) :
    (∫ x in K, ‖gradient (fun y ↦ phasePrimitive f (v y)) x‖) ≤
      ∫ x in K, rescaledPhaseEnergyDensity f R v x := by
  have hi := h.integrableOn_rescaledPhaseEnergy hv hval R hK
  have hbound : ∀ᵐ x ∂volume.restrict K,
      ‖gradient (fun y ↦ phasePrimitive f (v y)) x‖ ≤
        rescaledPhaseEnergyDensity f R v x := by
    filter_upwards [ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hv)] with x hx
    exact hr.competitorPrimitive_gradient_le_energy h hval hR hx
  have hg : IntegrableOn (fun x ↦ ‖gradient (fun y ↦ phasePrimitive f (v y)) x‖) K := by
    apply hi.mono' (measurable_gradient (fun y ↦ phasePrimitive f (v y))).norm.aestronglyMeasurable
    simpa only [norm_norm] using hbound
  exact integral_mono_ae hg hi hbound

/-- Unit vector divergence tests of arbitrary normalized competitors are bounded
by the diffuse energy of those competitors. -/
theorem RigidityHypotheses.competitorPrimitive_divergence_test_le_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {v : Space d → ℝ} (hv : LocallyLipschitz v) (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    {R : ℝ} (hR : 0 < R) {K : Set (Space d)} (hK : IsCompact K)
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ K) (hb : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x in K, phasePrimitive f (v x) * fieldDivergence b F x‖ ≤
      ∫ x in K, rescaledPhaseEnergyDensity f R v x := by
  exact (norm_setIntegral_mul_divergence_le_gradient_of_locallyLipschitz b
    (hr.phasePrimitive_comp_locallyLipschitz h hv hval)
    (fun x ↦ h.phasePrimitive_mem_Icc (hval x)) hF hc hK hs hb).trans
    (hr.competitorPrimitive_gradient_integral_le_energy h hv hval hR hK)

end SerrinEpigraph
