module

public import SerrinEpigraph.LimitingPhaseDirectionalBound

/-!
# Assembling directional bounds into vector divergence test bounds
-/

public section

open MeasureTheory Metric
open scoped Topology

namespace SerrinEpigraph

/-- Scalar directional estimates imply a trace-derivative estimate for unit vector fields. -/
theorem norm_setIntegral_indicator_trace_le {d : ℕ} {E K : Set (Space d)}
    (hE : MeasurableSet E) (hK : IsCompact K) {B : ℝ}
    (hbound : ∀ ψ : Space d → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ K → (∀ x, ‖ψ x‖ ≤ 1) → ∀ a : Space d,
      ‖∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ ψ x a‖ ≤ ‖a‖ * B)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F : Space d → Space d}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ K)
    (hb : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x *
      (∑ i, inner ℝ (b i) (fderiv ℝ F x (b i)))‖ ≤ (d : ℝ) * B := by
  let ψ : Fin d → Space d → ℝ := fun i x ↦ inner ℝ (b i) (F x)
  have hψ (i : Fin d) : ContDiff ℝ 1 (ψ i) := (innerSL ℝ (b i)).contDiff.comp hF
  have hsupport (i : Fin d) : tsupport (ψ i) ⊆ tsupport F :=
    tsupport_comp_subset (by simp : inner ℝ (b i) (0 : Space d) = 0) F
  have hcompact (i : Fin d) : HasCompactSupport (ψ i) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (hsupport i)
  have hunit (i : Fin d) (x : Space d) : ‖ψ i x‖ ≤ 1 := by
    have hn := norm_inner_le_norm (𝕜 := ℝ) (b i) (F x)
    simp only [b.norm_eq_one, one_mul] at hn
    exact hn.trans (hb x)
  have hd (i : Fin d) (x : Space d) :
      fderiv ℝ (ψ i) x (b i) = inner ℝ (b i) (fderiv ℝ F x (b i)) := by
    have he := (innerSL ℝ (b i)).hasFDerivAt.comp x (hF.differentiable_one x).hasFDerivAt
    exact congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (b i)) he.fderiv
  have hi (i : Fin d) : IntegrableOn
      (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ (ψ i) x (b i)) K := by
    have hconst : IntegrableOn (E.indicator (fun _ ↦ (1 : ℝ))) K :=
      (continuousOn_const.integrableOn_compact hK).indicator hE
    have hderiv := ((hψ i).continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := b i))
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hderiv.continuousOn
    exact hconst.mul_bdd hderiv.aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with x hx; exact hD x hx)
  have hsum : (∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x *
      (∑ i, inner ℝ (b i) (fderiv ℝ F x (b i)))) =
      ∑ i, ∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ (ψ i) x (b i) := by
    simp_rw [← hd, Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ ↦ hi i)
  rw [hsum]
  calc
    _ ≤ ∑ i : Fin d, ‖∫ x in K,
        E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ (ψ i) x (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, B := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [b.norm_eq_one, one_mul] using
        hbound (ψ i) (hψ i) (hcompact i) ((hsupport i).trans hs) (hunit i) (b i)
    _ = (d : ℝ) * B := by simp

/-- The measurable limiting phase satisfies a uniform surface-order vector divergence test bound. -/
theorem RigidityHypotheses.limiting_phase_vector_test_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ → ℝ, (∀ j, 1 ≤ R j) →
      Filter.Tendsto R Filter.atTop Filter.atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ k : ℕ, Filter.Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
          ‖phasePrimitive f (zeroExtension g u (R (φ j) • x)) -
            E.indicator (fun _ ↦ phasePrimitive f 1) x‖) Filter.atTop (𝓝 0)) ∧
        ∀ (k : ℕ) (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
          (F : Space (m + 1) → Space (m + 1)), ContDiff ℝ 1 F → HasCompactSupport F →
          tsupport F ⊆ closedBall 0 (k + 1 : ℝ) → (∀ x, ‖F x‖ ≤ 1) →
          ‖∫ x in closedBall 0 (k + 1 : ℝ), E.indicator (fun _ ↦ (1 : ℝ)) x *
            (∑ i, inner ℝ (b i) (fderiv ℝ F x (b i)))‖ ≤ C * (k + 1 : ℝ) ^ m := by
  obtain ⟨C, hC, hlim⟩ := hr.limiting_phase_indicator_directional_bound h
  refine ⟨(m + 1 : ℝ) * C, mul_pos (by positivity) hC, fun R hR hRtop ↦ ?_⟩
  obtain ⟨φ, hφ, E, hE, ht, hb⟩ := hlim R hR hRtop
  refine ⟨φ, hφ, E, hE, ht, fun k b F hF hc hs hunit ↦ ?_⟩
  have he := norm_setIntegral_indicator_trace_le hE (isCompact_closedBall 0 (k + 1 : ℝ))
    (hb k) b hF hc hs hunit
  convert he using 1
  push_cast
  ring

end SerrinEpigraph
