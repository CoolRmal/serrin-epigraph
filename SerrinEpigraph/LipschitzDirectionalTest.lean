module

public import SerrinEpigraph.DirectionalTestBound
public import SerrinEpigraph.LipschitzTranslationIntegral
public import SerrinEpigraph.MollificationFamilyBounds

/-!
# Directional test bounds for bounded nonnegative locally Lipschitz functions
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Normalized averaging preserves a nonnegative constant upper bound. -/
theorem normalizedMollify_mem_Icc_of_bounds {d : ℕ} {v : Space d → ℝ}
    (hv : Continuous v) {B : ℝ} (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) B)
    (n : ℕ) (x : Space d) : normalizedMollify v n x ∈ Set.Icc (0 : ℝ) B := by
  have hc := mollify_contraction_mem_Ioo n
  have h0 := mollify_nonneg (fun x ↦ (hval x).1) n x
  have hB := mollify_le hv (fun x ↦ (hval x).2) n x
  change (1 - 1 / ((n : ℝ) + 2)) * mollify v n x ∈ Set.Icc (0 : ℝ) B
  exact ⟨mul_nonneg hc.1.le h0, (mul_le_of_le_one_left h0 hc.2.le).trans hB⟩

/-- Bounded nonnegative continuous functions are recovered in local integral norm by averaging. -/
theorem normalizedMollify_integral_error_tendsto {d : ℕ} {v : Space d → ℝ}
    (hv : Continuous v) {B : ℝ} (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) B)
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, ‖normalizedMollify v n x - v x‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun n ↦ ∫ x in K, ‖normalizedMollify v n x - v x‖) atTop
      (𝓝 (∫ _x in K, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * B)
    · intro n
      exact (((normalizedMollify_contDiff hv n).continuous.sub hv).norm.aestronglyMeasurable)
    · exact continuousOn_const.integrableOn_compact hK
    · intro n
      exact Eventually.of_forall (fun x ↦ by
        have hm := normalizedMollify_mem_Icc_of_bounds hv hval n x
        rw [norm_norm, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [(hval x).1, (hval x).2, hm.1, hm.2],
          by linarith [(hval x).1, (hval x).2, hm.1, hm.2]⟩)
    · exact Eventually.of_forall (fun x ↦ by
        simpa only [sub_self, norm_zero] using
          ((normalizedMollify_tendsto hv x).sub (tendsto_const_nhds (x := v x))).norm)
  simpa only [integral_zero] using ht

/-- Directional derivative tests of bounded nonnegative locally Lipschitz functions are
controlled by their actual gradient mass, including across nonsmooth interfaces. -/
theorem norm_setIntegral_mul_fderiv_le_gradient_of_locallyLipschitz
    {d : ℕ} {v ψ : Space d → ℝ} (hv : LocallyLipschitz v)
    {B : ℝ} (hval : ∀ x, v x ∈ Set.Icc (0 : ℝ) B)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {K : Set (Space d)} (hK : IsCompact K) (hs : tsupport ψ ⊆ K)
    (hb : ∀ x, ‖ψ x‖ ≤ 1) (a : Space d) :
    ‖∫ x in K, v x * fderiv ℝ ψ x a‖ ≤ ‖a‖ * ∫ x in K, ‖gradient v x‖ := by
  have hd : HasCompactSupport (fun x ↦ fderiv ℝ ψ x a) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ a)
  obtain ⟨C, hC⟩ := hd.exists_bound_of_continuous
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  exact norm_setIntegral_mul_fderiv_le_of_smooth_limit
    (fun n ↦ (normalizedMollify_contDiff hv.continuous n).of_le (by simp))
    hψ hc hK hs hb a (hv.continuous.continuousOn.integrableOn_compact hK) C _ hC
    (normalizedMollify_integral_error_tendsto hv.continuous hval hK)
    (normalizedMollify_integral_gradient_norm_tendsto hv hK)

/-- The actual rescaled phase primitives obey uniform directional derivative test bounds. -/
theorem RigidityHypotheses.rescaledPhasePrimitive_directional_test_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → 1 ≤ R * r →
      ∀ ψ : Space (m + 1) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ closedBall 0 r → (∀ x, ‖ψ x‖ ≤ 1) → ∀ a : Space (m + 1),
      ‖∫ x in closedBall 0 r,
        phasePrimitive f (zeroExtension g u (R • x)) * fderiv ℝ ψ x a‖ ≤
          ‖a‖ * (C * r ^ m) := by
  obtain ⟨C, hC, hgrad⟩ := hr.rescaledPhasePrimitive_gradient_bound h
  refine ⟨C, hC, fun R r hR hRr ψ hψ hc hs hb a ↦ ?_⟩
  have hlip : LocallyLipschitz
      (fun x ↦ phasePrimitive f (zeroExtension g u (R • x))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul R).locallyLipschitz
  have hval (x : Space (m + 1)) :
      phasePrimitive f (zeroExtension g u (R • x)) ∈ Set.Icc 0 (phasePrimitive f 1) :=
    h.phasePrimitive_mem_Icc ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  exact (norm_setIntegral_mul_fderiv_le_gradient_of_locallyLipschitz hlip hval hψ hc
    (isCompact_closedBall 0 r) hs hb a).trans
    (mul_le_mul_of_nonneg_left (hgrad R r hR hRr) (norm_nonneg a))

end SerrinEpigraph
