module

public import SerrinEpigraph.TwoPhaseLimit

/-!
# A measurable global limiting phase
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- An almost-everywhere two-valued measurable function is a weighted measurable indicator. -/
theorem exists_measurable_indicator_of_two_values {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {v : X → ℝ} (hv : AEStronglyMeasurable v μ) (c : ℝ)
    (hvalues : ∀ᵐ x ∂μ, v x = 0 ∨ v x = c) :
    ∃ E : Set X, MeasurableSet E ∧ v =ᵐ[μ] E.indicator (fun _ ↦ c) := by
  classical
  refine ⟨{x | hv.mk v x = c}, measurableSet_eq_fun hv.measurable_mk measurable_const, ?_⟩
  filter_upwards [hv.ae_eq_mk, hvalues] with x hx hval
  by_cases hc : v x = c
  · simp [Set.indicator, ← hx, hc]
  · have hz : v x = 0 := hval.resolve_right hc
    simp [Set.indicator, ← hx, hz]

/-- Positive integer-radius balls cover the Euclidean space. -/
theorem iUnion_integer_closedBall (d : ℕ) :
    (⋃ k : ℕ, closedBall (0 : Space d) (k + 1 : ℝ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  simp only [mem_closedBall, dist_zero_right]
  linarith

/-- Diverging dilations have a subsequence converging locally to a measurable weighted phase. -/
theorem RigidityHypotheses.phasePrimitive_measurable_phase_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
          E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, v, hv, ht⟩ := hr.phasePrimitive_global_integral_limit h R hR
  have hvm : AEStronglyMeasurable v volume := by
    have hm := AEStronglyMeasurable.iUnion (fun k ↦ (hv k).aestronglyMeasurable)
    simpa only [iUnion_integer_closedBall, Measure.restrict_univ] using hm
  have hvalues : ∀ᵐ x ∂volume, v x = 0 ∨ v x = phasePrimitive f 1 := by
    have hlocal (k : ℕ) := hr.phasePrimitive_limit_two_values h (fun j ↦ R (φ j))
      (hRtop.comp hφ.tendsto_atTop) (show 0 < (k + 1 : ℝ) by positivity) v (hv k) (ht k)
    have hall := (ae_restrict_iUnion_iff
      (fun k : ℕ ↦ closedBall (0 : Space (m + 1)) (k + 1 : ℝ))
      (fun x ↦ v x = 0 ∨ v x = phasePrimitive f 1)).mpr hlocal
    simpa only [iUnion_integer_closedBall, Measure.restrict_univ] using hall
  obtain ⟨E, hE, heq⟩ := exists_measurable_indicator_of_two_values hvm _ hvalues
  refine ⟨φ, hφ, E, hE, fun k ↦ ?_⟩
  have he (j : ℕ) :
      (∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
          E.indicator (fun _ ↦ phasePrimitive f 1) x‖) =
      ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) - v x‖ := by
    apply integral_congr_ae
    filter_upwards [heq.restrict] with x hx
    rw [hx]
  simpa only [he] using ht k

end SerrinEpigraph
