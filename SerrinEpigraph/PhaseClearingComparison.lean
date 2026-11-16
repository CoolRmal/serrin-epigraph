module

public import SerrinEpigraph.PhaseClearingCompetitor
public import SerrinEpigraph.PlaneTiltIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Energy comparison and strict absorption for phase clearing
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A bounded vector field and divergence cost only a small fraction of low-phase energy. -/
theorem Hypotheses.phaseClearing_inner_flux_le_energy
    (h : Hypotheses g u f κ) {c δ M D : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hW : ∀ s ∈ Icc (0 : ℝ) δ, c ≤ normalizedPotential f s)
    {x : Space (m + 1)} (hval : zeroExtension g u x ≤ δ)
    {q : Space (m + 1)} {a : ℝ} (hq : ‖q‖ ≤ M) (ha : a ≤ D) :
    inner ℝ (gradient (zeroExtension g u) x) q + zeroExtension g u x * a ≤
      (M / Real.sqrt (2 * c) + δ * D / c) *
        phaseEnergyDensity f 0 (zeroExtension g u) x := by
  by_cases hp : 0 < zeroExtension g u x
  · have hpot := hW _ ⟨hp.le, hval⟩
    let E := ‖gradient (zeroExtension g u) x‖ ^ 2 / 2 +
      normalizedPotential f (zeroExtension g u x)
    have hcE : c ≤ E := by dsimp [E]; nlinarith [sq_nonneg ‖gradient (zeroExtension g u) x‖]
    have hg : ‖gradient (zeroExtension g u) x‖ ≤ E / Real.sqrt (2 * c) := by
      apply (norm_le_low_phase_energy_div_sqrt hc _).trans
      exact div_le_div_of_nonneg_right (by dsimp [E]; linarith) (Real.sqrt_nonneg _)
    have hi : inner ℝ (gradient (zeroExtension g u) x) q ≤
        M / Real.sqrt (2 * c) * E := by
      calc
        _ ≤ ‖gradient (zeroExtension g u) x‖ * ‖q‖ := real_inner_le_norm _ _
        _ ≤ ‖gradient (zeroExtension g u) x‖ * M :=
          mul_le_mul_of_nonneg_left hq (norm_nonneg _)
        _ ≤ (E / Real.sqrt (2 * c)) * M := mul_le_mul_of_nonneg_right hg hM
        _ = _ := by ring
    have hv : zeroExtension g u x * a ≤ δ * D / c * E := by
      calc
        _ ≤ zeroExtension g u x * D := mul_le_mul_of_nonneg_left ha hp.le
        _ ≤ δ * D := mul_le_mul_of_nonneg_right hval hD
        _ ≤ δ * D / c * E := by
          have hd : 0 ≤ δ * D := mul_nonneg (hp.le.trans hval) hD
          have hh := mul_le_mul_of_nonneg_left hcE (div_nonneg hd hc.le)
          have he : δ * D / c * c = δ * D := div_mul_cancel₀ _ hc.ne'
          linarith
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_true,
      add_zero]
    change _ ≤ (M / Real.sqrt (2 * c) + δ * D / c) * E
    nlinarith
  · have hz : zeroExtension g u x = 0 := le_antisymm (le_of_not_gt hp) (h.zeroExtension_nonneg x)
    have hx : x ∉ epigraph g := fun hx ↦ hp ((h.zeroExtension_pos_iff x).mpr hx)
    simp [phaseEnergyDensity, hz, h.gradient_zeroExtension_of_notMem hx]

/-- Zero low-phase energy on an open set forces pointwise vanishing there. -/
theorem Hypotheses.zeroExtension_eq_zero_of_low_phase_energy_zero
    (h : Hypotheses g u f κ) {S : Set (Space (m + 1))} (hS : IsOpen S)
    {c δ : ℝ} (hc : 0 < c)
    (hW : ∀ s ∈ Icc (0 : ℝ) δ, c ≤ normalizedPotential f s)
    (hval : ∀ x ∈ S, zeroExtension g u x ≤ δ)
    (he : phaseEnergyDensity f 0 (zeroExtension g u) =ᵐ[volume.restrict S] 0) :
    EqOn (zeroExtension g u) 0 S := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hS
    h.zeroExtension_continuous.continuousOn continuousOn_const
  filter_upwards [he, ae_restrict_mem hS.measurableSet] with x hx hxS
  change zeroExtension g u x = 0
  by_contra hn
  have hp : 0 < zeroExtension g u x := lt_of_le_of_ne (h.zeroExtension_nonneg x) (Ne.symm hn)
  have hpot := hW _ ⟨hp.le, hval x hxS⟩
  simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_true,
    add_zero, Pi.zero_apply] at hx
  nlinarith [sq_nonneg ‖gradient (zeroExtension g u) x‖]

/-- Integrating the actual competitor decrease and its compact flux produces strict
energy absorption. The lower bound is a pointwise barrier estimate, not a new
minimality or clearing assumption. -/
theorem RigidityHypotheses.phaseClearing_integral_absorption
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v z : Space (m + 1) → ℝ} (hv : LocallyLipschitz v) (hz : LocallyLipschitz z)
    (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (hzval : ∀ x, z x ∈ Icc (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (hs : tsupport (fun x ↦ v x - zeroExtension g u x) ⊆ K)
    {F : Space (m + 1) → Space (m + 1)} (hF : ContDiff ℝ 1 F)
    (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ K)
    {S : Set (Space (m + 1))} (hS : MeasurableSet S) (hSK : S ⊆ K)
    {θ : ℝ} (hθ : θ < 1)
    (hpoint : ∀ᵐ x ∂volume.restrict K,
      (1 - θ) * S.indicator (phaseEnergyDensity f 0 (zeroExtension g u)) x ≤
        phaseEnergyDensity f 0 (zeroExtension g u) x - phaseEnergyDensity f 0 v x -
          inner ℝ (gradient z x) (F x) -
          z x * fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) F x) :
    phaseEnergyDensity f 0 (zeroExtension g u) =ᵐ[volume.restrict S] 0 := by
  let E := phaseEnergyDensity f 0 (zeroExtension g u)
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hiE := hr.integrableOn_phaseEnergy_zeroExtension h 0 hK
  have hiv := h.integrableOn_lipschitz_phaseEnergy hv hval 0 hK
  obtain ⟨C, hC⟩ := hcF.exists_bound_of_continuous hF.continuous
  have hig : IntegrableOn (fun x ↦ inner ℝ (gradient z x) (F x)) K := by
    apply ((integrableOn_gradient_of_locallyLipschitz hz hK).norm.mul_const C).mono'
      (((measurable_gradient z).inner (𝕜 := ℝ) hF.continuous.measurable).aestronglyMeasurable)
    exact Eventually.of_forall (fun x ↦ (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)))
  have hid := (hz.continuous.mul (fieldDivergence_continuous b hF)).continuousOn
    |>.integrableOn_compact (μ := volume) hK
  have hiS : IntegrableOn (S.indicator E) K := hiE.indicator hS
  have hcmp := integral_mono_ae (hiS.const_mul (1 - θ))
    (((hiE.sub hiv).sub hig).sub hid) hpoint
  simp only [Pi.sub_apply, Pi.mul_apply] at hcmp
  have hsplit₁ := integral_sub ((hiE.sub hiv).sub hig) hid
  have hsplit₂ := integral_sub (hiE.sub hiv) hig
  have hsplit₃ := integral_sub hiE hiv
  simp only [Pi.sub_apply, Pi.mul_apply] at hsplit₁ hsplit₂ hsplit₃
  rw [integral_const_mul, hsplit₁, hsplit₂, hsplit₃] at hcmp
  have hibp := setIntegral_mul_divergence_eq_neg_inner_of_locallyLipschitz
    b hz hzval hF hcF hK hsF
  have hmin := hr.phaseEnergy_minimal_lipschitz_closedRange h hv hK hs hval
  have hzero : ∫ x in K, S.indicator E x = 0 := by
    have hn : 0 ≤ ∫ x in K, S.indicator E x := integral_nonneg (fun x ↦ by
      apply Set.indicator_nonneg
      exact fun _ _ ↦ hr.phaseEnergy_zeroExtension_nonneg h le_rfl _)
    have hh : (1 - θ) * (∫ x in K, S.indicator E x) ≤ 0 := by
      dsimp [b] at hibp
      linarith
    nlinarith
  have hEq : ∫ x in K, S.indicator E x = ∫ x in S, E x := by
    rw [integral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSK]
  rw [hEq] at hzero
  exact (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x ↦ hr.phaseEnergy_zeroExtension_nonneg h le_rfl x))
    (hiE.mono_set hSK)).mp hzero

end SerrinEpigraph
