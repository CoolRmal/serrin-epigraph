module

public import SerrinEpigraph.MollificationBounds
public import SerrinEpigraph.WeakQuotient
public import SerrinEpigraph.CalibrationConvergence

/-!
# Derivatives of localized mollifications
-/

public section
noncomputable section

open MeasureTheory Filter ContinuousLinearMap Metric InnerProductSpace
open scoped Topology Convolution

namespace SerrinEpigraph

/-- The derivative of a compactly supported smooth function commutes with averaging. -/
theorem mollify_fderiv {d : ℕ} {v : Space d → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (n : ℕ) (x : Space d) :
    fderiv ℝ (mollify v n) x =
      ((averagingBump d n).normed volume ⋆[lsmul ℝ ℝ, volume] fderiv ℝ v) x := by
  have he := (hc.hasFDerivAt_convolution_right (μ := volume) (lsmul ℝ ℝ)
    ((averagingBump d n).continuous_normed (μ := volume)).locallyIntegrable hv x).fderiv
  have hL : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompR (Space d) =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (Space d →L[ℝ] ℝ) →L[ℝ] (Space d →L[ℝ] ℝ)) := by
    ext a L
    rfl
  rw [hL] at he
  exact he

/-- For a compactly supported C¹ function, the averaged derivatives converge pointwise. -/
theorem mollify_fderiv_tendsto {d : ℕ} {v : Space d → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (x : Space d) :
    Tendsto (fun n ↦ fderiv ℝ (mollify v n) x) atTop (𝓝 (fderiv ℝ v x)) := by
  simp_rw [mollify_fderiv hv hc]
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (φ := averagingBump d) tendsto_one_div_add_atTop_nhds_zero_nat
    (hv.continuous_fderiv one_ne_zero) x

/-- The normalization coefficients converge to one. -/
theorem mollify_contraction_tendsto :
    Tendsto (fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have hs := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht

/-- Normalization multiplies the gradient of an average by its scalar coefficient. -/
theorem normalizedMollify_gradient {d : ℕ} {v : Space d → ℝ} (hv : Continuous v)
    (n : ℕ) (x : Space d) :
    gradient (normalizedMollify v n) x =
      (1 - 1 / ((n : ℝ) + 2)) • gradient (mollify v n) x := by
  change gradient (fun y ↦ (1 - 1 / ((n : ℝ) + 2)) * mollify v n y) x = _
  simp only [gradient,
    fderiv_const_mul ((mollify_contDiff hv n).differentiable (by simp) x), map_smul]

/-- Normalized averaging recovers gradients of compactly supported C¹ functions. -/
theorem normalizedMollify_gradient_tendsto_of_compact {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) (x : Space d) :
    Tendsto (fun n ↦ gradient (normalizedMollify v n) x) atTop (𝓝 (gradient v x)) := by
  have ht := ((toDual ℝ (Space d)).symm.continuous.tendsto (fderiv ℝ v x)).comp
    (mollify_fderiv_tendsto hv hc x)
  have hs := mollify_contraction_tendsto.smul ht
  simp_rw [normalizedMollify_gradient hv.continuous]
  simpa only [gradient, one_smul, Function.comp_def] using hs

/-- Locally equal functions have locally equal averages once the kernel is sufficiently small. -/
theorem mollify_eventuallyEq {d : ℕ} {v w : Space d → ℝ} {x : Space d}
    (hvw : v =ᶠ[𝓝 x] w) :
    ∀ᶠ n in atTop, mollify v n =ᶠ[𝓝 x] mollify w n := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hvw
  have hsmall : ∀ᶠ n : ℕ in atTop, (averagingBump d n).rOut < r / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (half_pos hr))
  filter_upwards [hsmall] with n hn
  filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
  apply integral_congr_ae
  filter_upwards with t
  change (averagingBump d n).normed volume t * v (y - t) =
    (averagingBump d n).normed volume t * w (y - t)
  by_cases hk : (averagingBump d n).normed volume t = 0
  · simp only [hk, zero_mul]
  · have ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut := by
      rw [← (averagingBump d n).support_normed_eq (μ := volume)]
      exact hk
    have ht' : ‖t‖ < r / 2 :=
      (by simpa only [mem_ball, dist_zero_right] using ht : ‖t‖ < (averagingBump d n).rOut).trans hn
    have hyt : y - t ∈ ball x r := by
      rw [mem_ball, dist_eq_norm]
      have he : y - t - x = (y - x) - t := by abel
      rw [he]
      have hy' : ‖y - x‖ < r / 2 := by simpa only [mem_ball, dist_eq_norm] using hy
      exact (norm_sub_le _ _).trans_lt (by linarith)
    rw [hball hyt]

/-- Local equality also transfers to the gradients of normalized averages eventually. -/
theorem normalizedMollify_gradient_eventuallyEq {d : ℕ} {v w : Space d → ℝ} {x : Space d}
    (hvw : v =ᶠ[𝓝 x] w) :
    (fun n ↦ gradient (normalizedMollify v n) x) =ᶠ[atTop]
      (fun n ↦ gradient (normalizedMollify w n) x) := by
  filter_upwards [mollify_eventuallyEq hvw] with n hn
  have he : normalizedMollify v n =ᶠ[𝓝 x] normalizedMollify w n := by
    filter_upwards [hn] with y hy
    simp only [normalizedMollify, hy]
  exact he.gradient_eq

/-- At every point of an open C¹ region, normalized averaging recovers the original gradient. -/
theorem normalizedMollify_gradient_tendsto_on_open {d : ℕ} {v : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω)
    {x : Space d} (hx : x ∈ Ω) :
    Tendsto (fun n ↦ gradient (normalizedMollify v n) x) atTop (𝓝 (gradient v x)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  let ψ : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hsub : tsupport (ψ : Space d → ℝ) ⊆ Ω := by
    rw [ψ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [ψ]; linarith : ψ.rOut < r)).trans hball
  have hw := contDiff_mul_of_tsupport_subset hΩ hv ψ.contDiff hsub
  have hc : HasCompactSupport (fun y ↦ v y * ψ y) := ψ.hasCompactSupport.mul_left
  have he : (fun y ↦ v y * ψ y) =ᶠ[𝓝 x] v := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simp only [Pi.one_apply] at hy
    simp only [hy, mul_one]
  have ht := normalizedMollify_gradient_tendsto_of_compact hw hc x
  rw [he.gradient_eq] at ht
  exact ht.congr' (normalizedMollify_gradient_eventuallyEq he)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Gradients of the normalized approximations converge away from the original boundary. -/
theorem Hypotheses.normalizedMollify_gradient_tendsto_off_frontier
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∉ frontier (epigraph g)) :
    Tendsto (fun n ↦ gradient (normalizedMollify (zeroExtension g u) n) x) atTop
      (𝓝 (gradient (zeroExtension g u) x)) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  by_cases hxi : x ∈ epigraph g
  · have he := zeroExtension_eventuallyEq (u := u) h.graph_contDiff.continuous hxi
    have ht := normalizedMollify_gradient_tendsto_on_open hΩ
      (h.solution_contDiffOn.of_le (by norm_num)) hxi
    rw [he.gradient_eq]
    exact ht.congr' (normalizedMollify_gradient_eventuallyEq he).symm
  · have hxc : x ∉ closure (epigraph g) := by
      intro hc
      apply hx
      exact ⟨hc, by simpa only [hΩ.interior_eq] using hxi⟩
    have he := zeroExtension_eventuallyEq_zero (u := u) hxc
    have ht := normalizedMollify_gradient_tendsto_on_open
      (v := (0 : Space (m + 1) → ℝ)) isOpen_univ contDiffOn_const (Set.mem_univ x)
    rw [he.gradient_eq]
    exact ht.congr' (normalizedMollify_gradient_eventuallyEq he).symm

/-- The explicit smooth approximations recover the zero-extension gradient almost everywhere. -/
theorem Hypotheses.normalizedMollify_gradient_tendsto_ae (h : Hypotheses g u f κ) :
    ∀ᵐ x, Tendsto (fun n ↦ gradient (normalizedMollify (zeroExtension g u) n) x) atTop
      (𝓝 (gradient (zeroExtension g u) x)) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h.frontier_epigraph_null] with x hx
  exact h.normalizedMollify_gradient_tendsto_off_frontier hx

/-- The explicit approximation sequence recovers the zero-extension phase energy through
calibration integrals, with no approximation assumptions left to supply. -/
theorem RigidityHypotheses.normalizedMollify_calibration_tendsto_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x)
      (normalizedMollify (zeroExtension g u) n x)
      (gradient (normalizedMollify (zeroExtension g u) n) x)) atTop
      (𝓝 (∫ x in K,
        phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) (zeroExtension g u) x)) := by
  obtain ⟨b, hb, hval⟩ := hr.normalizedMollify_level_bound h hK
  obtain ⟨C, hC⟩ := h.normalizedMollify_gradient_bound hK
  apply hr.tendsto_calibration_zeroExtension_energy h hK hb
    (fun n ↦ (normalizedMollify_contDiff h.zeroExtension_continuous n).of_le (by simp))
    hval hC
  · exact Eventually.of_forall (normalizedMollify_tendsto h.zeroExtension_continuous)
  · exact ae_restrict_of_ae h.normalizedMollify_gradient_tendsto_ae

end SerrinEpigraph
