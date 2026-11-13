module

public import SerrinEpigraph.TranslationIntegral
public import SerrinEpigraph.LipschitzMollificationDerivative

/-!
# Translation control for locally Lipschitz functions
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

noncomputable section

/-- The compact-set integrals of mollified gradient norms recover the original gradient mass. -/
theorem normalizedMollify_integral_gradient_norm_tendsto
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, ‖gradient (normalizedMollify v n) x‖) atTop
      (𝓝 (∫ x in K, ‖gradient v x‖)) := by
  obtain ⟨C, hC⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hv hK
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (C : ℝ))
  · intro n
    exact ((measurable_gradient _).norm.aestronglyMeasurable).restrict
  · exact continuousOn_const.integrableOn_compact hK
  · intro n
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [norm_norm]
    exact hC n x hx
  · filter_upwards [ae_restrict_of_ae
      (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hv)] with x hx
    exact hx.norm

/-- Mollification recovers the local integral error of a fixed translation. -/
theorem normalizedMollify_integral_translate_tendsto
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v) (r : ℝ) (z : Space d) :
    Tendsto (fun n ↦ ∫ x in closedBall 0 r,
      ‖normalizedMollify v n (x + z) - normalizedMollify v n x‖) atTop
      (𝓝 (∫ x in closedBall 0 r, ‖v (x + z) - v x‖)) := by
  obtain ⟨C, hC⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space d) (r + ‖z‖ + 1))
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (C : ℝ) * ‖z‖)
  · intro n
    have hc := (normalizedMollify_contDiff hv.continuous n).continuous
    exact (((hc.comp (continuous_id.add continuous_const)).sub hc).norm.aestronglyMeasurable).restrict
  · exact continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)
  · intro n
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
    have hx' : ‖x‖ ≤ r := by simpa using hx
    have hxx : x ∈ closedBall 0 (r + ‖z‖) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith [norm_nonneg z]
    have hxz : x + z ∈ closedBall 0 (r + ‖z‖) := by
      simpa only [mem_closedBall, dist_zero_right] using
        (norm_add_le x z).trans (add_le_add hx' le_rfl)
    have hb := (normalizedMollify_lipschitzOn_closedBall hv.continuous hC n).dist_le_mul
      (x + z) hxz x hxx
    simpa only [norm_norm, dist_eq_norm, add_sub_cancel_left] using hb
  · exact Eventually.of_forall (fun x ↦
      ((normalizedMollify_tendsto hv.continuous (x + z)).sub
        (normalizedMollify_tendsto hv.continuous x)).norm)

/-- Locally Lipschitz functions satisfy the local integral translation estimate. -/
theorem integral_norm_translate_sub_le_of_locallyLipschitz
    {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v) (r : ℝ) (z : Space d) :
    (∫ x in closedBall 0 r, ‖v (x + z) - v x‖) ≤
      ‖z‖ * ∫ x in closedBall 0 (r + ‖z‖), ‖gradient v x‖ := by
  apply le_of_tendsto_of_tendsto
    (normalizedMollify_integral_translate_tendsto hv r z)
    ((normalizedMollify_integral_gradient_norm_tendsto hv
      (isCompact_closedBall 0 (r + ‖z‖))).const_mul ‖z‖)
  exact Eventually.of_forall (fun n ↦ integral_norm_translate_sub_le
    ((normalizedMollify_contDiff hv.continuous n).of_le (by simp)) r z)

/-- The primitive family has a translation bound uniform in spatial dilation. -/
theorem RigidityHypotheses.rescaledPhasePrimitive_translation_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r : ℝ) (z : Space (m + 1)),
      0 < R → 1 ≤ R * (r + ‖z‖) →
      (∫ x in closedBall 0 r,
        ‖phasePrimitive f (zeroExtension g u (R • (x + z))) -
          phasePrimitive f (zeroExtension g u (R • x))‖) ≤
        ‖z‖ * (C * (r + ‖z‖) ^ m) := by
  obtain ⟨C, hC, hb⟩ := hr.rescaledPhasePrimitive_gradient_bound h
  refine ⟨C, hC, fun R r z hR hRr ↦ ?_⟩
  have hv : LocallyLipschitz (fun x : Space (m + 1) ↦
      phasePrimitive f (zeroExtension g u (R • x))) :=
    (hr.phasePrimitive_zeroExtension_locallyLipschitz h).comp
      (lipschitzWith_smul R).locallyLipschitz
  exact (integral_norm_translate_sub_le_of_locallyLipschitz hv r z).trans
    (mul_le_mul_of_nonneg_left (hb R (r + ‖z‖) hR hRr) (norm_nonneg z))

end

end SerrinEpigraph
