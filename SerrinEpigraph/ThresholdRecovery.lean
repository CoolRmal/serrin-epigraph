module

public import SerrinEpigraph.MollifiedGradientMass

/-!
# Recovery profiles along thresholds of smooth phases
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- A threshold coordinate with a spatially varying positive length scale. -/
@[expose] def thresholdCoordinate {d : ℕ} (φ a : Space d → ℝ) (t : ℝ) (x : Space d) : ℝ :=
  (φ x - t) / a x

/-- The existing one-dimensional transition pulled back along a threshold coordinate. -/
@[expose] def thresholdRecovery {d : ℕ} (f : ℝ → ℝ) (δ R : ℝ)
    (φ a : Space d → ℝ) (t : ℝ) : Space d → ℝ :=
  geometricRecoveryProfile f δ R (thresholdCoordinate φ a t)

/-- Positive smooth length scales give smooth threshold coordinates. -/
theorem thresholdCoordinate_contDiff {d : ℕ} {φ a : Space d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (hpos : ∀ x, 0 < a x) (t : ℝ) :
    ContDiff ℝ 1 (thresholdCoordinate φ a t) :=
  (hφ.sub contDiff_const).div ha (fun x ↦ (hpos x).ne')

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- Threshold recovery competitors are locally Lipschitz and normalized. -/
theorem RigidityHypotheses.thresholdRecovery_regular
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {φ a : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a)
    (hpos : ∀ x, 0 < a x) (t : ℝ) :
    LocallyLipschitz (thresholdRecovery f δ R φ a t) ∧
      ∀ x, thresholdRecovery f δ R φ a t x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨(hr.recoveryProfile_lipschitz h hδ).locallyLipschitz.comp
    (contDiff_const.mul (thresholdCoordinate_contDiff hφ ha hpos t)).locallyLipschitz, ?_⟩
  exact fun x ↦ hr.recoveryProfile_mem_Icc h hδ _

/-- Thresholds away from the endpoints preserve phase approximation uniformly
once the transition layer is shorter than half the endpoint margin. -/
theorem RigidityHypotheses.thresholdRecovery_phase_error_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {φ a : Space d → ℝ} {E : Set (Space d)}
    {t τ : ℝ} (hτ : 0 < τ) (ht : t ∈ Icc τ (1 - τ)) {x : Space d}
    (ha : 0 < a x) (hwidth : recoveryTravelTime f δ 1 * a x / R ≤ τ / 2) :
    ‖thresholdRecovery f δ R φ a t x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ ≤
      (2 / τ) * ‖φ x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
  have hval := hr.recoveryProfile_mem_Icc h hδ (R * thresholdCoordinate φ a t x)
  change thresholdRecovery f δ R φ a t x ∈ Icc (0 : ℝ) 1 at hval
  have hcoef : 0 ≤ 2 / τ := by positivity
  have hone : 1 ≤ (2 / τ) * (τ / 2) := by field_simp; norm_num
  by_cases hx : x ∈ E
  · rw [indicator_of_mem hx]
    by_cases hv : thresholdRecovery f δ R φ a t x = 1
    · rw [hv, sub_self, norm_zero]
      exact mul_nonneg hcoef (norm_nonneg _)
    · have htime : R * thresholdCoordinate φ a t x < recoveryTravelTime f δ 1 := by
        by_contra hn
        exact hv (hr.recoveryProfile_eq_one h hδ (le_of_not_gt hn))
      have hsmall : φ x - t < recoveryTravelTime f δ 1 * a x / R := by
        dsimp [thresholdCoordinate] at htime
        apply (lt_div_iff₀ hR).mpr
        rw [← mul_div_assoc] at htime
        have he := (div_lt_iff₀ ha).mp htime
        nlinarith
      have hgap : τ / 2 ≤ ‖φ x - 1‖ := by
        have he := neg_le_abs (φ x - 1)
        rw [← Real.norm_eq_abs] at he
        linarith [ht.2]
      calc
        ‖thresholdRecovery f δ R φ a t x - 1‖ ≤ 1 := by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hval.1], by linarith [hval.2]⟩
        _ ≤ (2 / τ) * ‖φ x - 1‖ := hone.trans (mul_le_mul_of_nonneg_left hgap hcoef)
  · rw [indicator_of_notMem hx, sub_zero, sub_zero]
    by_cases hp : φ x ≤ t
    · have hv : thresholdRecovery f δ R φ a t x = 0 := by
        apply hr.recoveryProfile_eq_zero h hδ
        exact mul_nonpos_of_nonneg_of_nonpos hR.le
          (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) ha.le)
      rw [hv, norm_zero]
      exact mul_nonneg hcoef (norm_nonneg _)
    · have hgap : τ / 2 ≤ ‖φ x‖ := by
        have he := Real.le_norm_self (φ x)
        linarith [ht.1, lt_of_not_ge hp]
      calc
        ‖thresholdRecovery f δ R φ a t x‖ ≤ 1 := by
          rw [Real.norm_of_nonneg hval.1]
          exact hval.2
        _ ≤ (2 / τ) * ‖φ x‖ := hone.trans (mul_le_mul_of_nonneg_left hgap hcoef)

/-- The uniform threshold estimate passes directly to local integral error. -/
theorem RigidityHypotheses.integral_thresholdRecovery_phase_error_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {φ a : Space d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (hpos : ∀ x, 0 < a x)
    {E K : Set (Space d)} (hE : MeasurableSet E) (hK : IsCompact K)
    {t τ : ℝ} (hτ : 0 < τ) (ht : t ∈ Icc τ (1 - τ))
    (hwidth : ∀ x ∈ K, recoveryTravelTime f δ 1 * a x / R ≤ τ / 2) :
    (∫ x in K, ‖thresholdRecovery f δ R φ a t x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) ≤
      (2 / τ) * ∫ x in K, ‖φ x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
  have hv := (hr.thresholdRecovery_regular h hδ (R := R) hφ ha hpos t).1.continuous
  have hz : IntegrableOn (E.indicator (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hi := ((hv.continuousOn.integrableOn_compact hK).sub hz).norm
  have hj := (((hφ.continuous.continuousOn.integrableOn_compact hK).sub hz).norm).const_mul
    (2 / τ)
  have he := integral_mono_ae hi hj (ae_restrict_of_forall_mem hK.measurableSet
    (fun x hx ↦ hr.thresholdRecovery_phase_error_le h hδ hR hτ ht (hpos x) (hwidth x hx)))
  simpa only [integral_const_mul, Pi.sub_apply] using he

end SerrinEpigraph
