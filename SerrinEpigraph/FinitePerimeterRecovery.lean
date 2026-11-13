module

public import SerrinEpigraph.PerimeterSmoothApproximation

/-!
# Local energy recovery for measurable sets with finite perimeter
-/

public section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- A perimeter bound in a larger ball gives local energy recovery on a smaller
closed ball along a subsequence of any prescribed diverging positive scales.
The same competitors converge in integral norm to the measurable target phase. -/
theorem RigidityHypotheses.exists_finitePerimeter_recovery
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    {r s B : ℝ} (hrs : r < s) (hB : 0 ≤ B)
    (hP : variationalPerimeter b E (ball 0 s) ≤ ENNReal.ofReal B)
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop) :
    ∃ (n : ℕ → ℕ) (v : ℕ → Space d → ℝ) (D : ℕ → ℝ),
      (∀ j, j ≤ n j) ∧ Tendsto n atTop atTop ∧
      (∀ j, LocallyLipschitz (v j)) ∧ (∀ j x, v j x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in closedBall 0 r,
        ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) ∧
      (∀ j, (∫ x in closedBall 0 r, rescaledPhaseEnergyDensity f (R (n j)) (v j) x) ≤ D j) ∧
      Tendsto D atTop (𝓝 (phasePrimitive f 1 * B)) := by
  let τ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 3)
  have hτ (j : ℕ) : 0 < τ j := by dsimp [τ]; positivity
  have hτhalf (j : ℕ) : τ j < 1 / 2 := by
    dsimp [τ]
    apply (div_lt_div_iff₀ (by positivity : 0 < (j : ℝ) + 3) (by norm_num : (0 : ℝ) < 2)).mpr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hτt : Tendsto τ atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 2)
    simpa only [τ, Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_assoc,
      show (2 : ℝ) + 1 = 3 by norm_num] using ht
  obtain ⟨φ, hφ, _, hφG, hφE⟩ := exists_smoothPhase_approx_of_perimeter_bound b hE hrs hB hP
    (ε := fun j ↦ τ j ^ 2) (fun j ↦ sq_pos_of_pos (hτ j))
  have hφ2 (j : ℕ) : ContDiff ℝ 2 (φ j) := (hφ j).of_le (by simp)
  have hrec (j : ℕ) := hr.exists_smoothPhaseRecovery h (hφ2 j) hE (isCompact_closedBall 0 r)
    (hτ j) (hτ j) (hτ j) (hτhalf j)
  choose A C hA hC hrec using hrec
  have hselect (j : ℕ) : ∃ k : ℕ, j ≤ k ∧
      recoveryTravelTime f (τ j) 1 * C j / R k < τ j ∧
      recoveryTravelTime f (τ j) 1 * A j / R k < τ j / 2 := by
    have hi := tendsto_inv_atTop_zero.comp hRt
    have hct : Tendsto (fun k ↦ recoveryTravelTime f (τ j) 1 * C j / R k) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        hi.const_mul (recoveryTravelTime f (τ j) 1 * C j)
    have hat : Tendsto (fun k ↦ recoveryTravelTime f (τ j) 1 * A j / R k) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        hi.const_mul (recoveryTravelTime f (τ j) 1 * A j)
    exact ((eventually_ge_atTop j).and ((hct.eventually (gt_mem_nhds (hτ j))).and
      (hat.eventually (gt_mem_nhds (half_pos (hτ j)))))).exists
  choose n hn he hw using hselect
  have hv (j : ℕ) := hrec j (R (n j)) (hR (n j)) (hw j).le
  choose v hv hval herror henergy using hv
  let e := fun j ↦ recoveryTravelTime f (τ j) 1 * C j / R (n j)
  let D := fun j ↦ (1 + e j) ^ 2 *
    ((recoveryActionPrimitive f (τ j) 1 *
      (B + τ j * (volume (closedBall (0 : Space d) r)).toReal)) / (1 - 2 * τ j))
  have hact (j : ℕ) : 0 ≤ recoveryActionPrimitive f (τ j) 1 :=
    (hr.phasePrimitive_one_pos h).le.trans (hr.recoveryActionPrimitive_bounds h (hτ j)).1
  have hent (j : ℕ) : 0 ≤ e j := div_nonneg
    (mul_nonneg (hr.recoveryTravelTime_one_pos h (hτ j)).le (hC j)) (hR _).le
  have het : Tendsto e atTop (𝓝 0) := squeeze_zero hent (fun j ↦ (he j).le) hτt
  refine ⟨n, v, D, hn, tendsto_atTop_mono hn tendsto_id, hv, hval, ?_, ?_, ?_⟩
  · apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _))
      (fun j ↦ (herror j).trans ?_)
      (show Tendsto (fun j ↦ 2 * τ j) atTop (𝓝 0) by simpa using hτt.const_mul 2)
    calc
      _ ≤ (2 / τ j) * τ j ^ 2 := mul_le_mul_of_nonneg_left (hφE j) (by positivity)
      _ = 2 * τ j := by field_simp
  · intro j
    apply (henergy j).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ (by linarith [hτhalf j])
    exact mul_le_mul_of_nonneg_left (add_le_add (hφG j) le_rfl) (hact j)
  · have haction := hr.recoveryActionPrimitive_tendsto h hτ hτt
    have hnum := haction.mul
      ((hτt.mul_const (volume (closedBall (0 : Space d) r)).toReal).const_add B)
    have hden := (hτt.const_mul 2).const_sub 1
    have ht := ((het.const_add 1).pow 2).mul (hnum.div hden (by norm_num))
    simpa only [D, mul_zero, zero_mul, add_zero, sub_zero, one_pow, one_mul, div_one,
      Pi.div_apply] using ht

end SerrinEpigraph
