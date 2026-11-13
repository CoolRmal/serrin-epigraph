module

public import SerrinEpigraph.RadialEnergyIdentity
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Removing the radial cutoff from energy integrals
-/

public section

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- Smooth decreasing profiles whose transition intervals shrink to the unit radius squared. -/
@[expose] def sharpRadialProfile (j : ℕ) (s : ℝ) : ℝ :=
  1 - Real.smoothTransition ((j + 1 : ℝ) * (s - 1))

theorem sharpRadialProfile_contDiff (j : ℕ) : ContDiff ℝ 1 (sharpRadialProfile j) := by
  unfold sharpRadialProfile
  fun_prop

theorem sharpRadialProfile_mem_Icc (j : ℕ) (s : ℝ) : sharpRadialProfile j s ∈ Icc (0 : ℝ) 1 := by
  have h0 := Real.smoothTransition.nonneg (x := (j + 1 : ℝ) * (s - 1))
  have h1 := Real.smoothTransition.le_one (x := (j + 1 : ℝ) * (s - 1))
  constructor <;> dsimp [sharpRadialProfile] <;> linarith

theorem sharpRadialProfile_zero (j : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    sharpRadialProfile j s = 0 := by
  have ht : 1 ≤ (j + 1 : ℝ) * (s - 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  simp [sharpRadialProfile, Real.smoothTransition.one_of_one_le ht]

theorem sharpRadialProfile_antitone (j : ℕ) : Antitone (sharpRadialProfile j) := by
  intro s t hst
  apply sub_le_sub_left
  apply Real.smoothTransition.monotone
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hst 1) (by positivity)

/-- The radial weights converge pointwise to the closed-ball indicator, including on its sphere. -/
theorem radialWeight_sharpProfile_tendsto {d : ℕ} (c : Space d) {R : ℝ} (hR : 0 < R)
    (x : Space d) :
    Tendsto (fun j ↦ radialWeight (sharpRadialProfile j) c R x) atTop
      (𝓝 ((closedBall c R).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ closedBall c R
  · have hd : ‖x - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hs : ‖x - c‖ ^ 2 / R ^ 2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos hR)).mpr
      nlinarith [norm_nonneg (x - c)]
    have he (j : ℕ) : radialWeight (sharpRadialProfile j) c R x = 1 := by
      have ht : (j + 1 : ℝ) * (‖x - c‖ ^ 2 / R ^ 2 - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hs)
      simp [radialWeight, sharpRadialProfile, Real.smoothTransition.zero_of_nonpos ht]
    simp only [he, indicator_of_mem hx]
    exact tendsto_const_nhds
  · have hd : R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
    have hs : 0 < ‖x - c‖ ^ 2 / R ^ 2 - 1 := by
      apply sub_pos.mpr
      apply (one_lt_div (sq_pos_of_pos hR)).mpr
      nlinarith [norm_nonneg (x - c)]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (‖x - c‖ ^ 2 / R ^ 2 - 1))
    have hN' := (div_lt_iff₀ hs).mp hN
    rw [indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with j hj
    have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
    have ht : 1 ≤ (j + 1 : ℝ) * (‖x - c‖ ^ 2 / R ^ 2 - 1) := by nlinarith
    simp [radialWeight, sharpRadialProfile, Real.smoothTransition.one_of_one_le ht]

/-- Smooth radial weighted integrals converge to the exact closed-ball integral. -/
theorem integral_sharpRadialProfile_tendsto {d : ℕ} (c : Space d) {R : ℝ} (hR : 0 < R)
    {w : Space d → ℝ} (hw : IntegrableOn w (closedBall c (2 * R))) :
    Tendsto (fun j ↦ ∫ x, w x * radialWeight (sharpRadialProfile j) c R x) atTop
      (𝓝 (∫ x in closedBall c R, w x)) := by
  let K := closedBall c (2 * R)
  have hK : MeasurableSet K := isClosed_closedBall.measurableSet
  have he (j : ℕ) : (∫ x in K, w x * radialWeight (sharpRadialProfile j) c R x) =
      ∫ x, w x * radialWeight (sharpRadialProfile j) c R x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx
      (tsupport_radialWeight_subset (fun s hs ↦ sharpRadialProfile_zero j hs) c hR hh)), mul_zero]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (F := fun j x ↦ w x * radialWeight (sharpRadialProfile j) c R x)
    (f := fun x ↦ (closedBall c R).indicator w x) (fun x ↦ ‖w x‖)
    (fun j ↦ hw.aestronglyMeasurable.mul
      (contDiff_radialWeight (sharpRadialProfile_contDiff j) c R).continuous.aestronglyMeasurable)
    hw.norm
    (fun j ↦ Eventually.of_forall (fun x ↦ by
      rw [norm_mul]
      have hval := sharpRadialProfile_mem_Icc j (‖x - c‖ ^ 2 / R ^ 2)
      have hn : ‖radialWeight (sharpRadialProfile j) c R x‖ ≤ 1 := by
        change ‖sharpRadialProfile j (‖x - c‖ ^ 2 / R ^ 2)‖ ≤ 1
        rw [Real.norm_of_nonneg hval.1]
        exact hval.2
      exact mul_le_of_le_one_right (norm_nonneg _) hn))
    (Eventually.of_forall (fun x ↦ by
      have hlim := (radialWeight_sharpProfile_tendsto c hR x).const_mul (w x)
      by_cases hx : x ∈ closedBall c R
      · simpa only [indicator_of_mem hx, mul_one] using hlim
      · simpa only [indicator_of_notMem hx, mul_zero] using hlim))
  simp only [he] at ht
  have hsub : closedBall c R ⊆ K := closedBall_subset_closedBall (by linarith)
  rw [integral_indicator isClosed_closedBall.measurableSet,
    Measure.restrict_restrict isClosed_closedBall.measurableSet, inter_eq_left.mpr hsub] at ht
  exact ht

end SerrinEpigraph
