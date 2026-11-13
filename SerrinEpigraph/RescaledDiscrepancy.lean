module

public import SerrinEpigraph.BulkEnergyDiscrepancy

/-!
# Potential-minus-kinetic discrepancy on fixed rescaled balls
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- Potential minus kinetic energy inside the positive phase. -/
@[expose] def phaseDiscrepancyDensity {d : ℕ} (f : ℝ → ℝ) (v : Space d → ℝ) :
    Space d → ℝ :=
  {x | 0 < v x}.indicator (fun x ↦ normalizedPotential f (v x) - ‖gradient v x‖ ^ 2 / 2)

/-- The discrepancy with interface thickness equal to the inverse spatial scale. -/
@[expose] def rescaledDiscrepancyDensity {d : ℕ} (f : ℝ → ℝ) (R : ℝ)
    (v : Space d → ℝ) : Space d → ℝ :=
  {x | 0 < v x}.indicator
    (fun x ↦ R * normalizedPotential f (v x) - ‖gradient v x‖ ^ 2 / (2 * R))

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- For the zero extension the indicator may be removed from the kinetic term. -/
theorem Hypotheses.phaseDiscrepancy_eq_sub (h : Hypotheses g u f κ) :
    phaseDiscrepancyDensity f (zeroExtension g u) = fun x ↦
      phasePotentialDensity f (zeroExtension g u) x - ‖gradient (zeroExtension g u) x‖ ^ 2 / 2 := by
  funext x
  by_cases hx : x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff x).mpr hx
    simp [phaseDiscrepancyDensity, phasePotentialDensity, hp]
  · have hp : ¬0 < zeroExtension g u x := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
    simp [phaseDiscrepancyDensity, phasePotentialDensity, hp, h.gradient_zeroExtension_of_notMem hx]

/-- Modica's estimate gives a nonnegative whole-space discrepancy. -/
theorem RigidityHypotheses.phaseDiscrepancy_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    0 ≤ phaseDiscrepancyDensity f (zeroExtension g u) x := by
  by_cases hx : x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff x).mpr hx
    rw [phaseDiscrepancyDensity, indicator_of_mem (s := {y | 0 < zeroExtension g u y}) hp,
      zeroExtension_of_mem hx, h.gradient_zeroExtension hx]
    exact sub_nonneg.mpr (hr.modica_bound h hx)
  · have hp : ¬0 < zeroExtension g u x := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
    simp [phaseDiscrepancyDensity, hp]

/-- The unscaled discrepancy is locally integrable. -/
theorem RigidityHypotheses.integrableOn_phaseDiscrepancy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (phaseDiscrepancyDensity f (zeroExtension g u)) K := by
  rw [h.phaseDiscrepancy_eq_sub]
  exact (hr.integrableOn_phasePotential h hK).sub
    ((h.integrableOn_norm_gradient_zeroExtension_sq hK).div_const 2)

/-- A weighted whole-space discrepancy integral is the corresponding interior integral. -/
theorem Hypotheses.integral_phaseDiscrepancy_mul (h : Hypotheses g u f κ)
    (χ : Space (m + 1) → ℝ) :
    (∫ x, phaseDiscrepancyDensity f (zeroExtension g u) x * χ x) =
      ∫ x in epigraph g, (normalizedPotential f (u x) - ‖gradient u x‖ ^ 2 / 2) * χ x := by
  have he : (fun x ↦ phaseDiscrepancyDensity f (zeroExtension g u) x * χ x) =
      (epigraph g).indicator (fun x ↦
        (normalizedPotential f (u x) - ‖gradient u x‖ ^ 2 / 2) * χ x) := by
    funext x
    by_cases hx : x ∈ epigraph g
    · have hp := (h.zeroExtension_pos_iff x).mpr hx
      rw [phaseDiscrepancyDensity, indicator_of_mem (s := {y | 0 < zeroExtension g u y}) hp,
        indicator_of_mem hx,
        zeroExtension_of_mem hx, h.gradient_zeroExtension hx]
    · have hp : ¬0 < zeroExtension g u x := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
      simp [phaseDiscrepancyDensity, hp, hx]
  rw [he, integral_indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]

/-- Compact continuous weights give integrable discrepancy densities. -/
theorem RigidityHypotheses.integrable_phaseDiscrepancy_mul
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Integrable (fun x ↦ phaseDiscrepancyDensity f (zeroExtension g u) x * χ x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport χ))).mp
  exact (hr.integrableOn_phaseDiscrepancy h hc).mul_continuousOn hχ.continuousOn hc

/-- The fixed radial weight controls discrepancy on its inner half-ball. -/
theorem RigidityHypotheses.phaseDiscrepancy_halfBall_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {r : ℝ} (hr0 : 0 < r) :
    r ^ (-(m : ℤ)) * ((1 / 2) * ∫ x in closedBall 0 (r / 2),
      phaseDiscrepancyDensity f (zeroExtension g u) x) ≤
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 r := by
  let χ := radialWeight radialDefectProfile (0 : Space (m + 1)) r
  have hχ : Continuous χ := (contDiff_radialWeight radialDefectProfile_contDiff 0 r).continuous
  have hc : HasCompactSupport χ :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_radialWeight_subset (fun _ hs ↦ radialDefectProfile_zero (by linarith)) 0 hr0)
  have hχ0 (x : Space (m + 1)) : 0 ≤ χ x := (radialDefectProfile_mem_Icc (by positivity)).1
  have hχlow {x : Space (m + 1)} (hx : x ∈ closedBall 0 (r / 2)) : 1 / 2 ≤ χ x := by
    have hn : ‖x - 0‖ ≤ r / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hratio : ‖x - 0‖ ^ 2 / r ^ 2 ≤ 1 / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
      nlinarith [norm_nonneg (x - 0)]
    dsimp only [χ, radialWeight, radialDefectProfile]
    rw [max_eq_left (by linarith)]
    nlinarith
  have hi := hr.integrable_phaseDiscrepancy_mul h hχ hc
  have hle : (1 / 2) * (∫ x in closedBall 0 (r / 2),
      phaseDiscrepancyDensity f (zeroExtension g u) x) ≤
      ∫ x, phaseDiscrepancyDensity f (zeroExtension g u) x * χ x := by
    rw [← integral_const_mul]
    apply (setIntegral_mono_on
      ((hr.integrableOn_phaseDiscrepancy h (isCompact_closedBall _ _)).const_mul _) hi.integrableOn
      isClosed_closedBall.measurableSet (fun x hx ↦ ?_)).trans
      (setIntegral_le_integral hi (Eventually.of_forall (fun x ↦
        mul_nonneg (hr.phaseDiscrepancy_nonneg h x) (hχ0 x))))
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hχlow hx) (hr.phaseDiscrepancy_nonneg h x)
  unfold bulkEnergyDiscrepancy
  rw [← h.integral_phaseDiscrepancy_mul]
  exact mul_le_mul_of_nonneg_left hle (zpow_nonneg hr0.le _)

/-- Dilation multiplies the unscaled discrepancy by its scale. -/
theorem rescaledDiscrepancyDensity_dilation {d : ℕ} (f : ℝ → ℝ) (U : Space d → ℝ)
    {R : ℝ} (hR : 0 < R) (x : Space d) :
    rescaledDiscrepancyDensity f R (fun y ↦ U (R • y)) x =
      R * phaseDiscrepancyDensity f U (R • x) := by
  by_cases hx : 0 < U (R • x)
  · simp only [rescaledDiscrepancyDensity, phaseDiscrepancyDensity, indicator_apply,
      mem_ofPred_eq, hx, ite_true, gradient_comp_dilation, norm_smul,
      Real.norm_of_nonneg hR.le]
    field_simp
  · simp [rescaledDiscrepancyDensity, phaseDiscrepancyDensity, hx]

/-- Change of variables for the discrepancy on rescaled balls. -/
theorem integral_rescaledDiscrepancyDensity {m : ℕ} (f : ℝ → ℝ) (U : Space (m + 1) → ℝ)
    {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (∫ x in closedBall 0 r, rescaledDiscrepancyDensity f R (fun y ↦ U (R • y)) x) =
      (R ^ m)⁻¹ * ∫ x in closedBall 0 (R * r), phaseDiscrepancyDensity f U x := by
  simp_rw [rescaledDiscrepancyDensity_dilation f U hR]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume _ _ hR]
  simp only [smul_closedBall' hR.ne', smul_zero, Real.norm_of_nonneg hR.le,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, pow_succ]
  field_simp

/-- Fixed-ball rescaled discrepancy is controlled by the bulk discrepancy at a larger scale. -/
theorem RigidityHypotheses.rescaledDiscrepancy_le_bulk
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R r : ℝ} (hR : 0 < R) (hr0 : 0 < r) :
    (∫ x in closedBall 0 r,
      rescaledDiscrepancyDensity f R (fun y ↦ zeroExtension g u (R • y)) x) ≤
      2 * (2 * r) ^ m * bulkEnergyDiscrepancy g u f radialDefectProfile 0 (2 * r * R) := by
  have hb := hr.phaseDiscrepancy_halfBall_le h (show 0 < 2 * r * R by positivity)
  rw [show 2 * r * R / 2 = R * r by ring] at hb
  rw [integral_rescaledDiscrepancyDensity f _ hR r]
  have he (I : ℝ) : 2 * (2 * r) ^ m * ((2 * r * R) ^ (-(m : ℤ)) * ((1 / 2) * I)) =
      (R ^ m)⁻¹ * I := by
    rw [zpow_neg, zpow_natCast]
    simp only [mul_pow]
    field_simp
  rw [← he]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Bulk defect decay at integer multiples gives local equipartition on each fixed integer ball. -/
theorem RigidityHypotheses.rescaledDiscrepancy_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hB : ∀ k : ℕ, Tendsto (fun j ↦
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    (k : ℕ) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
      rescaledDiscrepancyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)
        atTop (𝓝 0) := by
  have ht := (hB (2 * k + 1)).const_mul (2 * (2 * (k + 1 : ℝ)) ^ m)
  have he : (fun j ↦ 2 * (2 * (k + 1 : ℝ)) ^ m *
      bulkEnergyDiscrepancy g u f radialDefectProfile 0 (((2 * k + 1 : ℕ) + 1 : ℝ) * R j)) =
      fun j ↦ 2 * (2 * (k + 1 : ℝ)) ^ m *
        bulkEnergyDiscrepancy g u f radialDefectProfile 0 (2 * (k + 1 : ℝ) * R j) := by
    funext j
    congr 2
    push_cast
    ring
  rw [he, mul_zero] at ht
  have h0 (j : ℕ) : 0 ≤ ∫ x in closedBall 0 (k + 1 : ℝ),
      rescaledDiscrepancyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x := by
    apply integral_nonneg
    intro x
    rw [rescaledDiscrepancyDensity_dilation f _ (hR j)]
    exact mul_nonneg (hR j).le (hr.phaseDiscrepancy_nonneg h _)
  exact squeeze_zero h0 (fun j ↦ hr.rescaledDiscrepancy_le_bulk h (hR j) (by positivity)) ht

end SerrinEpigraph
