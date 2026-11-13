module

public import SerrinEpigraph.SurfaceEnergyMonotonicity
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Finite limits of surface-scaled energies
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- A nonnegative function, monotone on positive arguments and bounded after one,
has a finite limit at infinity. -/
theorem exists_limit_of_monotoneOn_bounded {F : ℝ → ℝ}
    (hmono : MonotoneOn F (Ioi 0)) (hF0 : ∀ r : ℝ, 1 ≤ r → 0 ≤ F r)
    {C : ℝ} (hC : ∀ r : ℝ, 1 ≤ r → F r ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ C ∧ Tendsto F atTop (𝓝 L) := by
  let H := fun r : ℝ ↦ F (max 1 r)
  have hHmono : Monotone H := by
    intro r s hrs
    exact hmono (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le_max_left 1 hrs)
  have hHb : BddAbove (range H) := ⟨C, by rintro _ ⟨r, rfl⟩; exact hC _ (le_max_left _ _)⟩
  have hlim := tendsto_atTop_ciSup hHmono hHb
  refine ⟨⨆ r, H r, ge_of_tendsto hlim (Eventually.of_forall (fun r ↦ hF0 _ (le_max_left _ _))),
    le_of_tendsto hlim (Eventually.of_forall (fun r ↦ hC _ (le_max_left _ _))), ?_⟩
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  simp only [H, max_eq_right hr]

/-- Surface-normalized interior energy with a radial profile. -/
@[expose] def weightedSurfaceEnergy {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (f q : ℝ → ℝ) (c : Space (m + 1)) (r : ℝ) : ℝ :=
  r ^ (-(m : ℤ)) * ∫ x in epigraph g,
    (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * radialWeight q c r x

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Nonnegative radial profiles give nonnegative weighted surface energy. -/
theorem RigidityHypotheses.weightedSurfaceEnergy_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ q s)
    (c : Space (m + 1)) {r : ℝ} (hr0 : 0 < r) :
    0 ≤ weightedSurfaceEnergy g u f q c r := by
  apply mul_nonneg (zpow_nonneg hr0.le _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
    with x hx
  have hW := hr.normalizedPotential_nonneg h ⟨(h.positive x hx).le,
    (hr.solution_lt_one x hx).le⟩
  exact mul_nonneg (add_nonneg (by positivity) hW) (hq0 _ (by positivity))

/-- Surface growth bounds every radial weighted energy whose profile lies between zero and one. -/
theorem RigidityHypotheses.weightedSurfaceEnergy_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hqrange : ∀ s : ℝ, 0 ≤ s → q s ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → weightedSurfaceEnergy g u f q 0 r ≤ C := by
  obtain ⟨C, hC, hb⟩ := hr.phaseEnergy_surface_growth h
  refine ⟨C * 2 ^ m, by positivity, fun r hr1 ↦ ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  let E := phaseEnergyDensity f 0 (zeroExtension g u)
  let χ := radialWeight q (0 : Space (m + 1)) r
  have hiE : IntegrableOn E (closedBall 0 (2 * r)) :=
    hr.integrableOn_phaseEnergy_zeroExtension h 0 (isCompact_closedBall _ _)
  have hχ : Continuous χ := (contDiff_radialWeight hq 0 r).continuous
  have he : (∫ x, E x * χ x) = ∫ x in closedBall 0 (2 * r), E x * χ x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh ↦ hx (tsupport_radialWeight_subset hzero 0 hr0 hh))
    simp [hz]
  have hle : (∫ x, E x * χ x) ≤ ∫ x in closedBall 0 (2 * r), E x := by
    rw [he]
    apply setIntegral_mono_on (hiE.mul_continuousOn hχ.continuousOn (isCompact_closedBall _ _))
      hiE isClosed_closedBall.measurableSet
    intro x _
    exact (mul_le_mul_of_nonneg_left (hqrange _ (by positivity)).2
      (hr.phaseEnergy_zeroExtension_nonneg h le_rfl x)).trans_eq (mul_one _)
  have hscale : r ^ (-(m : ℤ)) * (C * (2 * r) ^ m) = C * 2 ^ m := by
    rw [zpow_neg, zpow_natCast, mul_pow]
    field_simp
  unfold weightedSurfaceEnergy
  rw [← h.integral_phaseEnergy_mul]
  exact (mul_le_mul_of_nonneg_left (hle.trans (hb (2 * r) (by linarith)))
    (zpow_nonneg hr0.le _)).trans_eq hscale

/-- Every admissible decreasing radial profile has a finite nonnegative limiting energy. -/
theorem RigidityHypotheses.weightedSurfaceEnergy_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hzero : ∀ s : ℝ, 2 ≤ s → q s = 0)
    (hqrange : ∀ s : ℝ, 0 ≤ s → q s ∈ Icc (0 : ℝ) 1) (hqanti : Antitone q) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (weightedSurfaceEnergy g u f q 0) atTop (𝓝 L) := by
  obtain ⟨C, _, hC⟩ := hr.weightedSurfaceEnergy_bound h hq hzero hqrange
  obtain ⟨L, hL, _, ht⟩ := exists_limit_of_monotoneOn_bounded
    (hr.weighted_surface_energy_monotone h hq hzero (fun s hs ↦ (hqrange s hs).1) hqanti 0)
    (fun r hr1 ↦ hr.weightedSurfaceEnergy_nonneg h (fun s hs ↦ (hqrange s hs).1) 0
      (zero_lt_one.trans_le hr1)) hC
  exact ⟨L, hL, ht⟩

/-- Exact surface-scaled ball energies have a finite nonnegative limit at infinity. -/
theorem RigidityHypotheses.surface_scaled_energy_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun r ↦ r ^ (-(m : ℤ)) * ∫ x in closedBall 0 r,
      phaseEnergyDensity f 0 (zeroExtension g u) x) atTop (𝓝 L) := by
  obtain ⟨C, _, hC⟩ := hr.phaseEnergy_surface_growth h
  have h0 (r : ℝ) (hr1 : 1 ≤ r) : 0 ≤ r ^ (-(m : ℤ)) * ∫ x in closedBall 0 r,
      phaseEnergyDensity f 0 (zeroExtension g u) x := by
    exact mul_nonneg (zpow_nonneg (by linarith) _)
      (integral_nonneg (hr.phaseEnergy_zeroExtension_nonneg h le_rfl))
  have hb (r : ℝ) (hr1 : 1 ≤ r) : r ^ (-(m : ℤ)) * (∫ x in closedBall 0 r,
      phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ C := by
    have hr0 : 0 < r := by linarith
    have hh := mul_le_mul_of_nonneg_left (hC r hr1) (zpow_nonneg hr0.le (-(m : ℤ)))
    have he : r ^ (-(m : ℤ)) * (C * r ^ m) = C := by
      rw [zpow_neg, zpow_natCast]
      field_simp
    exact hh.trans_eq he
  obtain ⟨L, hL, _, ht⟩ := exists_limit_of_monotoneOn_bounded
    (hr.surface_scaled_energy_monotone h 0) h0 hb
  exact ⟨L, hL, ht⟩

end SerrinEpigraph
