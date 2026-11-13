module

public import SerrinEpigraph.RegularizedGradientWidth
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Averaging transition cost over threshold parameters
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Translating and reversing a threshold, then scaling its coordinate,
multiplies the total one-dimensional mass by the positive width. -/
theorem integral_scaled_threshold {q : ℝ → ℝ} (hq : Integrable q) {a : ℝ}
    (ha : 0 < a) (s : ℝ) : Integrable (fun t ↦ q ((s - t) / a)) ∧
      (∫ t, q ((s - t) / a)) = a * ∫ t, q t := by
  refine ⟨(hq.comp_div ha.ne').comp_sub_left s, ?_⟩
  rw [integral_sub_left_eq_self (fun t ↦ q (t / a)) volume s,
    Measure.integral_comp_div, abs_of_pos ha, smul_eq_mul]

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ R : ℝ}

/-- The transition-density majorant is Borel measurable, including the two
endpoints of its support. -/
theorem RigidityHypotheses.measurable_recoveryLayerDensity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    Measurable (recoveryLayerDensity f δ R) := by
  have hv : Continuous (fun t ↦ recoveryProfile f δ (R * t)) :=
    (hr.recoveryProfile_lipschitz h hδ).continuous.comp (continuous_const.mul continuous_id)
  have hW := h.normalizedPotential_continuousOn.comp_continuous hv
    (fun t ↦ hr.recoveryProfile_mem_Icc h hδ (R * t))
  exact (continuous_const.mul ((continuous_const.mul hW).add continuous_const)).measurable.indicator
    measurableSet_Ioo

/-- A continuous coordinate makes the localized layer density integrable on
each compact region. -/
theorem RigidityHypotheses.integrableOn_recoveryLayerDensity_comp
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {ρ : Space d → ℝ} (hρ : Continuous ρ) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ recoveryLayerDensity f δ R (ρ x)) K := by
  have hv : Continuous (fun x ↦ recoveryProfile f δ (R * ρ x)) :=
    (hr.recoveryProfile_lipschitz h hδ).continuous.comp (continuous_const.mul hρ)
  have hW := h.normalizedPotential_continuousOn.comp_continuous hv
    (fun x ↦ hr.recoveryProfile_mem_Icc h hδ (R * ρ x))
  have hc : Continuous (fun x ↦ R * (2 *
      normalizedPotential f (recoveryProfile f δ (R * ρ x)) + δ)) :=
    continuous_const.mul ((continuous_const.mul hW).add continuous_const)
  have hi := hc.continuousOn.integrableOn_compact (μ := volume) hK
  convert hi.indicator ((measurableSet_Ioo (a := 0)
    (b := recoveryTravelTime f δ 1 / R)).preimage hρ.measurable) using 1
  funext x
  by_cases hx : ρ x ∈ Ioo 0 (recoveryTravelTime f δ 1 / R) <;>
    simp [recoveryLayerDensity, hx]

/-- The full threshold average is exactly the regularized transition action
times the integral of the variable width. -/
theorem RigidityHypotheses.threshold_layer_average
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) (hR : 0 < R) {φ a : Space d → ℝ}
    (hφ : Continuous φ) (ha : Continuous a) (hpos : ∀ x, 0 < a x)
    {K : Set (Space d)} (hK : IsCompact K) :
    Integrable (fun t ↦ ∫ x in K, recoveryLayerDensity f δ R (thresholdCoordinate φ a t x)) ∧
      (∫ t, ∫ x in K, recoveryLayerDensity f δ R (thresholdCoordinate φ a t x)) =
        recoveryActionPrimitive f δ 1 * ∫ x in K, a x := by
  let F : Space d → ℝ → ℝ := fun x t ↦
    recoveryLayerDensity f δ R (thresholdCoordinate φ a t x)
  have hfm : Measurable F.uncurry :=
    (hr.measurable_recoveryLayerDensity h hδ).comp
      (((hφ.comp continuous_fst).sub continuous_snd).div (ha.comp continuous_fst)
        (fun p ↦ (hpos p.1).ne')).measurable
  have hf (x : Space d) : Integrable (F x) ∧
      (∫ t, F x t) = a x * recoveryActionPrimitive f δ 1 := by
    simpa only [F, thresholdCoordinate, hr.integral_recoveryLayerDensity h hδ hR] using
      integral_scaled_threshold (hr.integrable_recoveryLayerDensity h hδ (R := R))
        (hpos x) (φ x)
  have hnonneg (x : Space d) (t : ℝ) : 0 ≤ F x t :=
    hr.recoveryLayerDensity_nonneg h hδ hR.le _
  have hi : Integrable F.uncurry ((volume.restrict K).prod volume) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun x ↦ (hf x).1), ?_⟩
    have he : (fun x ↦ ∫ t, ‖F x t‖) = fun x ↦ a x * recoveryActionPrimitive f δ 1 := by
      funext x
      simp only [Real.norm_of_nonneg (hnonneg x _), (hf x).2]
    simpa only [Function.uncurry, he] using
      (ha.continuousOn.integrableOn_compact (μ := volume) hK).mul_const
        (recoveryActionPrimitive f δ 1)
  refine ⟨hi.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hi]
  simp only [(hf _).2, integral_mul_const, mul_comm]

end SerrinEpigraph
