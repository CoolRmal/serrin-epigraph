module

public import SerrinEpigraph.PhaseClearingNondegeneracy
public import SerrinEpigraph.SharpGlobalLipschitz
public import SerrinEpigraph.SurfaceEnergyMonotonicity

/-!
# Uniform surface-energy density at interior levels
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A value in a fixed compact subinterval of (0,1) carries a uniform positive
surface-energy density at every radius above a fixed physical radius. -/
theorem RigidityHypotheses.exists_level_surface_energy_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ x : Space (m + 1), zeroExtension g u x ∈ Icc a b →
        ∀ R : ℝ, ρ ≤ R →
          c₀ * R ^ m ≤ ∫ y in closedBall x R,
            phaseEnergyDensity f 0 (zeroExtension g u) y := by
  have hsub : Icc (a / 2) ((b + 1) / 2) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨w₀, hw₀, hW⟩ := isCompact_Icc.exists_forall_le'
    (h.normalizedPotential_continuousOn.mono hsub)
    (fun t ht ↦ hr.normalizedPotential_pos h (by linarith [ht.1]) (by linarith [ht.2]))
  let ρ := min a (1 - b) / (2 * κ)
  have hρ : 0 < ρ := div_pos (lt_min ha (by linarith)) (by nlinarith [h.kappa_pos])
  have hκρ : κ * ρ = min a (1 - b) / 2 := by dsimp [ρ]; field_simp [h.kappa_pos.ne']
  have hvol : 0 < (volume (closedBall (0 : Space (m + 1)) ρ)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 hρ).ne' measure_closedBall_lt_top.ne
  let c₀ := w₀ * (volume (closedBall (0 : Space (m + 1)) ρ)).toReal / ρ ^ m
  have hc₀ : 0 < c₀ := div_pos (mul_pos hw₀ hvol) (pow_pos hρ _)
  refine ⟨ρ, c₀, hρ, hc₀, ?_⟩
  intro x hx R hρR
  have hR : 0 < R := hρ.trans_le hρR
  have hlocal (y : Space (m + 1)) (hy : y ∈ closedBall x ρ) :
      w₀ ≤ phaseEnergyDensity f 0 (zeroExtension g u) y := by
    have hd := (hr.zeroExtension_lipschitzWith h).dist_le_mul y x
    change dist (zeroExtension g u y) (zeroExtension g u x) ≤ κ * dist y x at hd
    have hdist : dist (zeroExtension g u y) (zeroExtension g u x) ≤ min a (1 - b) / 2 :=
      hd.trans ((mul_le_mul_of_nonneg_left hy h.kappa_pos.le).trans_eq hκρ)
    rw [Real.dist_eq] at hdist
    have hlow := (abs_le.mp hdist).1
    have hupp := (abs_le.mp hdist).2
    have hyval : zeroExtension g u y ∈ Icc (a / 2) ((b + 1) / 2) := by
      constructor
      · linarith [hx.1, min_le_left a (1 - b)]
      · linarith [hx.2, min_le_right a (1 - b)]
    have hyp : 0 < zeroExtension g u y := by linarith [hyval.1]
    have hpot := hW _ hyval
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hyp, ite_true, add_zero]
    nlinarith [sq_nonneg ‖gradient (zeroExtension g u) y‖]
  have hmass : w₀ * (volume (closedBall (0 : Space (m + 1)) ρ)).toReal ≤
      ∫ y in closedBall x ρ, phaseEnergyDensity f 0 (zeroExtension g u) y := by
    have hh := integral_mono_ae (continuousOn_const.integrableOn_compact
      (μ := volume) (isCompact_closedBall x ρ) (f := fun _ : Space (m + 1) ↦ w₀))
      (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall x ρ))
      (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy; exact hlocal y hy)
    simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at hh
    have hv : volume (closedBall x ρ) = volume (closedBall (0 : Space (m + 1)) ρ) := by
      rw [Measure.addHaar_closedBall volume x hρ.le,
        Measure.addHaar_closedBall volume (0 : Space (m + 1)) hρ.le]
    rw [hv] at hh
    simpa only [mul_comm] using hh
  have hmono := hr.surface_scaled_energy_monotone h x hρ hR hρR
  have hlo : c₀ ≤ ρ ^ (-(m : ℤ)) *
      ∫ y in closedBall x ρ, phaseEnergyDensity f 0 (zeroExtension g u) y := by
    rw [zpow_neg, zpow_natCast]
    dsimp [c₀]
    exact (div_le_div_of_nonneg_right hmass (pow_nonneg hρ.le _)).trans_eq (by ring)
  have hmain := hlo.trans hmono
  change c₀ ≤ R ^ (-(m : ℤ)) * ∫ y in closedBall x R,
    phaseEnergyDensity f 0 (zeroExtension g u) y at hmain
  rw [zpow_neg, zpow_natCast] at hmain
  have hdiv : c₀ ≤ (∫ y in closedBall x R,
      phaseEnergyDensity f 0 (zeroExtension g u) y) / R ^ m := by
    simpa only [div_eq_mul_inv, mul_comm] using hmain
  exact (le_div_iff₀ (pow_pos hR _)).mp hdiv

/-- The fixed level near each free boundary point transfers the same positive
surface-density bound to balls centered on the free boundary. -/
theorem RigidityHypotheses.exists_freeBoundary_surface_energy_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ R₀ c₀ : ℝ, 0 < R₀ ∧ 0 < c₀ ∧
      ∀ x ∈ frontier (epigraph g), ∀ R : ℝ, R₀ ≤ R →
        c₀ * R ^ m ≤ ∫ y in closedBall x R,
          phaseEnergyDensity f 0 (zeroExtension g u) y := by
  obtain ⟨α, L, hα, hL, hlevel⟩ := hr.exists_fixed_level_near_freeBoundary h
  obtain ⟨ρ, C, hρ, hC, hlower⟩ :=
    hr.exists_level_surface_energy_lower_bound h (a := α) (b := α) hα.1 hα.2
  refine ⟨2 * (L + ρ), C / (2 : ℝ) ^ m, by positivity, by positivity, ?_⟩
  intro x hx R hR
  obtain ⟨y, hy, hyval⟩ := hlevel x hx
  have hhalf : ρ ≤ R / 2 := by linarith
  have hLhalf : L ≤ R / 2 := by linarith
  have hE := hlower y (by rw [hyval]; exact ⟨le_rfl, le_rfl⟩) (R / 2) hhalf
  have hsub : closedBall y (R / 2) ⊆ closedBall x R := by
    intro z hz
    change dist z x ≤ R
    have hzy : dist z y ≤ R / 2 := hz
    have hyx : dist y x < L := hy
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ ≤ R := by linarith
  have hmono := setIntegral_mono_set
    (hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall x R))
    (Eventually.of_forall (fun z ↦ hr.phaseEnergy_zeroExtension_nonneg h le_rfl z))
    (Eventually.of_forall hsub)
  calc
    C / (2 : ℝ) ^ m * R ^ m = C * (R / 2) ^ m := by rw [div_pow]; ring
    _ ≤ _ := hE.trans hmono

end SerrinEpigraph
