module

public import SerrinEpigraph.PrimitiveEnergyLowerBound

/-!
# The exact surface-energy lower bound
-/

public section

open MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Weighting an indicator by a nonnegative scalar weights the absolute integral pairing. -/
theorem ofReal_norm_integral_weighted_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (ψ : X → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ c) x * ψ x ∂μ‖ =
      ENNReal.ofReal c * ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * ψ x ∂μ‖ := by
  have he : (∫ x, E.indicator (fun _ ↦ c) x * ψ x ∂μ) =
      c * ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * ψ x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by
      by_cases hx : x ∈ E <;> simp [hx])
  rw [he, norm_mul, Real.norm_of_nonneg hc, ENNReal.ofReal_mul hc]

/-- The primitive value at one times phase perimeter is bounded by the diffuse-energy liminf. -/
theorem RigidityHypotheses.perimeter_le_energy_liminf
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (r : ℝ)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖phasePrimitive f (zeroExtension g u (R j • x)) -
        E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0)) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter b E (ball 0 r) ≤
      liminf (fun j ↦ ENNReal.ofReal (∫ x in closedBall 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)) atTop := by
  unfold variationalPerimeter
  simp_rw [ENNReal.mul_iSup]
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hs ↦ iSup_le (fun hb ↦ ?_)))))
  have hsub := hs.trans ball_subset_closedBall
  have he := hr.primitive_limit_test_le_energy_liminf h b R hR r
    (E.indicator (fun _ ↦ phasePrimitive f 1))
    ((continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator hE)
    ht hF hc hsub hb
  have hrestrict : (∫ x in closedBall 0 r,
      E.indicator (fun _ ↦ phasePrimitive f 1) x * fieldDivergence b F x) =
      ∫ x, E.indicator (fun _ ↦ phasePrimitive f 1) x * fieldDivergence b F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fieldDivergence_zero_of_notMem_tsupport b F (fun hh ↦ hx (hsub hh)), mul_zero]
  rw [hrestrict, ofReal_norm_integral_weighted_indicator volume E (fieldDivergence b F)
    (hr.phasePrimitive_one_pos h).le] at he
  exact he

/-- A common phase subsequence satisfies the exact surface-energy lower bound on every ball. -/
theorem RigidityHypotheses.exists_phase_with_energy_liminf_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      (∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
          E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0)) ∧
      ∀ (k : ℕ) (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))),
        ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter b E (ball 0 (k + 1 : ℝ)) ≤
          liminf (fun j ↦ ENNReal.ofReal (∫ x in closedBall 0 (k + 1 : ℝ),
            rescaledPhaseEnergyDensity f (R (φ j))
              (fun y ↦ zeroExtension g u (R (φ j) • y)) x)) atTop := by
  obtain ⟨φ, hφ, E, hE, ht⟩ := hr.phasePrimitive_measurable_phase_limit h R hR hRtop
  refine ⟨φ, hφ, E, hE, ht, fun k b ↦ ?_⟩
  exact hr.perimeter_le_energy_liminf h b (fun j ↦ R (φ j))
    (fun j ↦ lt_of_lt_of_le zero_lt_one (hR (φ j))) (k + 1 : ℝ) hE (ht k)

end SerrinEpigraph
