module

public import SerrinEpigraph.GlobalPrimitiveLimit
public import SerrinEpigraph.PrimitiveIndicatorApproximation

/-!
# Two-valued integral limits
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- Integral limits of functions taking two fixed values take the same values almost everywhere. -/
theorem ae_two_values_of_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (v : X → ℝ) (c : ℝ)
    (hF : ∀ j, Integrable (F j) μ) (hv : Integrable v μ)
    (hvalues : ∀ j x, F j x = 0 ∨ F j x = c)
    (ht : Tendsto (fun j ↦ ∫ x, ‖F j x - v x‖ ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, v x = 0 ∨ v x = c := by
  let D : X → ℝ := fun x ↦ min ‖v x‖ ‖v x - c‖
  have hcont : Continuous (fun t : ℝ ↦ min ‖t‖ ‖t - c‖) :=
    continuous_id.norm.min (continuous_id.sub continuous_const).norm
  have hD : Integrable D μ := hv.norm.mono'
    (hcont.comp_aestronglyMeasurable hv.aestronglyMeasurable)
    (Eventually.of_forall (fun x ↦ by
      dsimp only [D]
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (norm_nonneg _))]
      exact min_le_left _ _))
  have hnonneg (x : X) : 0 ≤ D x := le_min (norm_nonneg _) (norm_nonneg _)
  have hle : (∫ x, D x ∂μ) ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    exact Eventually.of_forall (fun j ↦ integral_mono hD ((hF j).sub hv).norm (fun x ↦ by
      rcases hvalues j x with hx | hx
      · simp [D, hx]
      · simpa only [hx, norm_sub_rev (c) (v x)] using min_le_right ‖v x‖ ‖v x - c‖))
  have hz := le_antisymm hle (integral_nonneg hnonneg)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall hnonneg) hD).mp hz
  filter_upwards [hae] with x hx
  simp only [D, Pi.zero_apply] at hx
  rcases le_total ‖v x‖ ‖v x - c‖ with hle | hle
  · left
    exact norm_eq_zero.mp (by simpa only [min_eq_left hle] using hx)
  · right
    exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa only [min_eq_right hle] using hx))

/-- Vanishing integral error transfers a two-valued constraint to an integral limit. -/
theorem ae_two_values_of_approximate_integral_limit {d : ℕ} {S : Set (Space d)}
    (F P : ℕ → Space d → ℝ) (v : Space d → ℝ) (c : ℝ)
    (hF : ∀ j, IntegrableOn (F j) S) (hP : ∀ j, IntegrableOn (P j) S)
    (hv : IntegrableOn v S) (hvalues : ∀ j x, P j x = 0 ∨ P j x = c)
    (herr : Tendsto (fun j ↦ ∫ x in S, ‖P j x - F j x‖) atTop (𝓝 0))
    (ht : Tendsto (fun j ↦ ∫ x in S, ‖F j x - v x‖) atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict S, v x = 0 ∨ v x = c := by
  apply ae_two_values_of_integral_limit (volume.restrict S) P v c hP hv hvalues
  have hsum := herr.add ht
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro j
    exact integral_nonneg (fun x ↦ norm_nonneg _)
  · intro j
    exact integral_norm_sub_triangle (hP j) (hF j) hv

/-- Every local primitive limit along diverging dilations takes only its two phase values. -/
theorem RigidityHypotheses.phasePrimitive_limit_two_values
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r)
    (v : Space (m + 1) → ℝ) (hv : IntegrableOn v (closedBall 0 r))
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖phasePrimitive f (zeroExtension g u (R j • x)) - v x‖) atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict (closedBall 0 r), v x = 0 ∨ v x = phasePrimitive f 1 := by
  let F := fun j x ↦ phasePrimitive f (zeroExtension g u (R j • x))
  let P := fun j x ↦ phasePrimitive f 1 * positivePhaseIndicator (zeroExtension g u) (R j • x)
  have hF (j : ℕ) : IntegrableOn (F j) (closedBall 0 r) :=
    ((hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul (R j))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 r)
  have hP (j : ℕ) : IntegrableOn (P j) (closedBall 0 r) := by
    have hc : Continuous (fun x : Space (m + 1) ↦ zeroExtension g u (R j • x)) :=
      h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
    have hi : IntegrableOn
        ({x | 0 < zeroExtension g u (R j • x)}.indicator (fun _ ↦ (1 : ℝ)))
        (closedBall 0 r) :=
      (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator
        (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
    exact hi.const_mul (phasePrimitive f 1)
  apply ae_two_values_of_approximate_integral_limit F P v (phasePrimitive f 1) hF hP hv
  · intro j x
    by_cases hx : 0 < zeroExtension g u (R j • x)
    · right
      simp [P, positivePhaseIndicator, hx]
    · left
      simp [P, positivePhaseIndicator, hx]
  · simpa only [P, F, Real.norm_eq_abs, primitiveIndicatorError, Function.comp_def] using
      (hr.primitiveIndicatorError_tendsto_zero h hradius).comp hR
  · exact ht

end SerrinEpigraph
