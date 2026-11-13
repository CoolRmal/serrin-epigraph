module

public import SerrinEpigraph.PrimitiveIndicatorApproximation

/-!
# Uniform bounds for families of mollifications
-/

public section

open MeasureTheory Metric ContinuousLinearMap

namespace SerrinEpigraph

noncomputable section

/-- A fixed averaging kernel gives a common local Lipschitz bound for all bounded inputs. -/
theorem mollify_family_lipschitzOn {d : ℕ} (n : ℕ) (r M : ℝ) (hM : 0 ≤ M) :
    ∃ C : NNReal, ∀ v : Space d → ℝ, Continuous v → (∀ x, ‖v x‖ ≤ M) →
      LipschitzOnWith C (mollify v n) (closedBall 0 r) := by
  let k := (averagingBump d n).normed volume
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    ((averagingBump d n).hasCompactSupport_normed (μ := volume))
    ((averagingBump d n).contDiff_normed (n := (1 : ℕ∞))) (by simp)
  let V := volume.real (closedBall (0 : Space d) (r + 1))
  refine ⟨⟨(L : ℝ) * M * V, mul_nonneg (mul_nonneg L.coe_nonneg hM) measureReal_nonneg⟩,
    fun v hv hvM ↦ lipschitzOnWith_iff_dist_le_mul.mpr (fun x hx y hy ↦ ?_)⟩
  have hi (z : Space d) : Integrable (fun t ↦ k (z - t) * v t) := by
    have hh := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_right
      (μ := volume)
      (lsmul ℝ ℝ).flip hv.locallyIntegrable ((averagingBump d n).continuous_normed (μ := volume)) z
    exact hh.integrable
  have he (z : Space d) : mollify v n z = ∫ t, k (z - t) * v t := by
    exact convolution_eq_swap (lsmul ℝ ℝ)
  rw [dist_eq_norm, he x, he y, ← integral_sub (hi x) (hi y)]
  have hz (z : Space d) (hz : z ∈ closedBall 0 r) (t : Space d)
      (ht : t ∉ closedBall 0 (r + 1)) : k (z - t) = 0 := by
    apply Function.notMem_support.mp
    rw [(averagingBump d n).support_normed_eq]
    intro hb
    have hzt : ‖z - t‖ < (averagingBump d n).rOut := by simpa using hb
    have hz' : ‖z‖ ≤ r := by simpa using hz
    have ht' : r + 1 < ‖t‖ := by simpa using ht
    have hn := norm_sub_le z (z - t)
    rw [sub_sub_cancel] at hn
    linarith [averagingBump_rOut_le_one d n]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := closedBall (0 : Space d) (r + 1)) (fun t ht ↦ by
      rw [hz x hx t ht, hz y hy t ht]; simp)]
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := closedBall (0 : Space d) (r + 1))
    (C := (L : ℝ) * dist x y * M)
    (f := fun t ↦ k (x - t) * v t - k (y - t) * v t)
    (isCompact_closedBall (0 : Space d) (r + 1)).measure_lt_top
    (fun t _ ↦ ?_)
  · calc
      _ ≤ ((L : ℝ) * dist x y * M) * V := hb
      _ = _ := by change _ = ((L : ℝ) * M * V) * dist x y; ring
  · rw [← sub_mul, norm_mul]
    have hxy : ‖k (x - t) - k (y - t)‖ ≤ (L : ℝ) * dist x y := by
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hL.dist_le_mul (x - t) (y - t)
    exact mul_le_mul hxy (hvM t) (norm_nonneg _) (mul_nonneg L.coe_nonneg (dist_nonneg))

/-- The primitive stays between its two phase values on the normalized range. -/
theorem Hypotheses.phasePrimitive_mem_Icc
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    phasePrimitive f s ∈ Set.Icc 0 (phasePrimitive f 1) := by
  refine ⟨phasePrimitive_nonneg f hs.1, ?_⟩
  have hc : ContinuousOn (fun t ↦ Real.sqrt (2 * normalizedPotential f t)) (Set.Icc 0 1) :=
    (continuousOn_const.mul h.normalizedPotential_continuousOn).sqrt
  exact intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
    (Filter.Eventually.of_forall (fun _ ↦ Real.sqrt_nonneg _))
    (hc.intervalIntegrable_of_Icc zero_le_one)

/-- Fixed mollification gives a Lipschitz constant independent of the spatial dilation. -/
theorem RigidityHypotheses.mollifiedPrimitive_uniform_lipschitzOn
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (n : ℕ) (r : ℝ) :
    ∃ C : NNReal, ∀ R : ℝ,
      LipschitzOnWith C
        (mollify (fun x ↦ phasePrimitive f (zeroExtension g u (R • x))) n)
        (closedBall 0 r) := by
  obtain ⟨C, hC⟩ := mollify_family_lipschitzOn (d := m + 1) n r
    (phasePrimitive f 1) (hr.phasePrimitive_one_pos h).le
  refine ⟨C, fun R ↦ hC _ ?_ ?_⟩
  · exact (hr.phasePrimitive_zeroExtension_locallyLipschitz h).continuous.comp
      (continuous_id.const_smul R)
  · intro x
    have hb := h.phasePrimitive_mem_Icc
      ⟨h.zeroExtension_nonneg (R • x), (hr.zeroExtension_lt_one (R • x)).le⟩
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2

end

end SerrinEpigraph
