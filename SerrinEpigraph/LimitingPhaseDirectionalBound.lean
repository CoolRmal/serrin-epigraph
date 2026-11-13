module

public import SerrinEpigraph.LipschitzDirectionalTest

/-!
# Directional derivative bounds for the limiting phase
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- A common measurable phase limit inherits all directional derivative test bounds. -/
theorem RigidityHypotheses.limiting_phase_directional_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ → ℝ, (∀ j, 1 ≤ R j) → Tendsto R atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
            E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0)) ∧
        ∀ (k : ℕ) (ψ : Space (m + 1) → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ closedBall 0 (k + 1 : ℝ) → (∀ x, ‖ψ x‖ ≤ 1) →
          ∀ a : Space (m + 1),
          ‖∫ x in closedBall 0 (k + 1 : ℝ),
            E.indicator (fun _ ↦ phasePrimitive f 1) x * fderiv ℝ ψ x a‖ ≤
              ‖a‖ * (C * (k + 1 : ℝ) ^ m) := by
  obtain ⟨C, hC, hbound⟩ := hr.rescaledPhasePrimitive_directional_test_bound h
  refine ⟨C, hC, fun R hR hRtop ↦ ?_⟩
  obtain ⟨φ, hφ, E, hE, ht⟩ := hr.phasePrimitive_measurable_phase_limit h R hR hRtop
  refine ⟨φ, hφ, E, hE, ht, fun k ψ hψ hc hs hb a ↦ ?_⟩
  have hd : HasCompactSupport (fun x ↦ fderiv ℝ ψ x a) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ a)
  obtain ⟨D, hD⟩ := hd.exists_bound_of_continuous
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  apply integral_mul_bound_of_integral_limit
    (volume.restrict (closedBall 0 (k + 1 : ℝ)))
    (fun j x ↦ phasePrimitive f (zeroExtension g u (R (φ j) • x)))
    (E.indicator (fun _ ↦ phasePrimitive f 1)) (fun x ↦ fderiv ℝ ψ x a) D
    (‖a‖ * (C * (k + 1 : ℝ) ^ m))
  · intro j
    exact ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R (φ j)))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 (k + 1 : ℝ))
  · exact (continuousOn_const.integrableOn_compact
      (isCompact_closedBall 0 (k + 1 : ℝ))).indicator hE
  · exact ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  · exact hD
  · exact ht k
  · intro j
    apply hbound (R (φ j)) (k + 1 : ℝ) (lt_of_lt_of_le zero_lt_one (hR _))
      _ ψ hψ hc hs hb a
    have hk : (1 : ℝ) ≤ k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    nlinarith [hR (φ j)]

/-- A positive constant weight can be removed from an indicator integral bound. -/
theorem norm_integral_indicator_mul_le_of_weighted
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (E : Set X) (ψ : X → ℝ)
    {c B : ℝ} (hc : 0 < c)
    (hb : ‖∫ x, E.indicator (fun _ ↦ c) x * ψ x ∂μ‖ ≤ B) :
    ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * ψ x ∂μ‖ ≤ B / c := by
  have he : (∫ x, E.indicator (fun _ ↦ c) x * ψ x ∂μ) =
      c * ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * ψ x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by
      by_cases hx : x ∈ E <;> simp [hx])
  rw [he, norm_mul, Real.norm_of_nonneg hc.le] at hb
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

/-- The limiting phase has surface-order bounds on unweighted directional tests. -/
theorem RigidityHypotheses.limiting_phase_indicator_directional_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ → ℝ, (∀ j, 1 ≤ R j) → Tendsto R atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
            E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0)) ∧
        ∀ (k : ℕ) (ψ : Space (m + 1) → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ closedBall 0 (k + 1 : ℝ) → (∀ x, ‖ψ x‖ ≤ 1) →
          ∀ a : Space (m + 1),
          ‖∫ x in closedBall 0 (k + 1 : ℝ),
            E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ ψ x a‖ ≤
              ‖a‖ * (C * (k + 1 : ℝ) ^ m) := by
  obtain ⟨C, hC, hlim⟩ := hr.limiting_phase_directional_bound h
  have hc := hr.phasePrimitive_one_pos h
  refine ⟨C / phasePrimitive f 1, div_pos hC hc, fun R hR hRtop ↦ ?_⟩
  obtain ⟨φ, hφ, E, hE, ht, hb⟩ := hlim R hR hRtop
  refine ⟨φ, hφ, E, hE, ht, fun k ψ hψ hψc hs hψb a ↦ ?_⟩
  have he := norm_integral_indicator_mul_le_of_weighted
    (volume.restrict (closedBall 0 (k + 1 : ℝ))) E (fun x ↦ fderiv ℝ ψ x a) hc
    (hb k ψ hψ hψc hs hψb a)
  convert he using 1
  ring

end SerrinEpigraph
