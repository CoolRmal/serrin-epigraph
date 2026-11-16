module

public import SerrinEpigraph.PhaseClearingGaussianBounds
public import SerrinEpigraph.PhaseClearingBarrierCriterion

/-!
# Half-ball clearing by an explicit smooth Gaussian competitor
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A quantitative half-ball clearing theorem, with the absorption inequality
displayed explicitly in terms of the amplitude and radius. -/
theorem RigidityHypotheses.zeroExtension_eq_zero_halfBall_of_absorption
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {c : Space (m + 1)} {δ F R c₀ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hF : 0 ≤ F) (hR : 0 < R) (hc₀ : 0 < c₀)
    (hW : ∀ t ∈ Icc (0 : ℝ) δ, c₀ ≤ normalizedPotential f t)
    (hf : ∀ t ∈ Icc (0 : ℝ) δ, f t ≤ F)
    (hsmall : ∀ x ∈ ball c R, zeroExtension g u x ≤ δ)
    (habs : phaseClearingGaussianGradientConstant m * (δ / R + F * R) /
        Real.sqrt (2 * c₀) +
      δ * (phaseClearingGaussianLaplacianConstant m * (δ / R ^ 2 + F)) / c₀ < 1) :
    EqOn (zeroExtension g u) 0 (ball c (R / 2)) := by
  let A := phaseClearingGaussianAmplitude m δ F R
  let b := phaseClearingGaussianRate m R
  let w := phaseClearingGaussian A b (R / 2) c
  let η : ContDiffBump c := ⟨3 * R / 4, R, by positivity, by linarith⟩
  let Q : Space (m + 1) → Space (m + 1) := fun x ↦ η x • gradient w x
  let basis := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hw : ContDiff ℝ 2 w := (phaseClearingGaussian_contDiff A b (R / 2) c).of_le (by simp)
  have hgw : ContDiff ℝ 1 (gradient w) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp (hw.fderiv_right (by norm_num))
  have hQ : ContDiff ℝ 1 Q := η.contDiff.smul hgw
  have hQsupport : Function.support Q ⊆ closedBall c R := by
    intro x hx
    have hηx : η x ≠ 0 := fun he ↦ hx (by simp [Q, he])
    have hh : x ∈ Function.support η := hηx
    rw [η.support_eq] at hh
    exact ball_subset_closedBall hh
  have hQc : HasCompactSupport Q :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) hQsupport
  have hQs : tsupport Q ⊆ closedBall c R := closure_minimal hQsupport isClosed_closedBall
  have hQlocal (x : Space (m + 1)) (hx : x ∈ ball c (3 * R / 4)) :
      Q =ᶠ[𝓝 x] gradient w := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have he : η y = 1 := η.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp only [Q, he, one_smul]
  have hQdiv (x : Space (m + 1)) (hx : x ∈ ball c (3 * R / 4)) :
      fieldDivergence basis Q x = (Δ w) x := by
    have hd := (hQlocal x hx).fderiv_eq (𝕜 := ℝ)
    rw [laplacian_eq_sum_gradient_derivative_of_differentiable (hgw.differentiable_one x) basis]
    unfold fieldDivergence
    rw [hd]
    simp only [real_inner_comm]
  have hA : 0 < A := phaseClearingGaussianAmplitude_pos m hδ hF
  have hb : 0 < b := phaseClearingGaussianRate_pos m hR
  apply hr.zeroExtension_eq_zero_of_clearing_barrier h
    (s := R / 2) (r := 3 * R / 4) (R := R) (δ := δ) (c₀ := c₀)
    (F₀ := F) (M := phaseClearingGaussianGradientConstant m * (δ / R + F * R))
    (D := phaseClearingGaussianLaplacianConstant m * (δ / R ^ 2 + F))
    (w := w) (η := η) (Q := Q)
    (by positivity) (by linarith) (by linarith) hδone hc₀
    (by unfold phaseClearingGaussianGradientConstant; positivity)
    (by unfold phaseClearingGaussianLaplacianConstant; positivity) hW hf hsmall
    (hw.of_le (by norm_num)) η.contDiff (fun _ ↦ ⟨η.nonneg, η.le_one⟩)
    (fun _ hx ↦ η.one_of_mem_closedBall hx) (by rw [η.support_eq])
  · intro x hx
    apply phaseClearingGaussian_nonpos_inner hA.le hb.le
    have hh : ‖x - c‖ < R / 2 := by simpa only [mem_ball, dist_eq_norm] using hx
    nlinarith [norm_nonneg (x - c)]
  · intro x _ hx
    apply phaseClearingGaussian_pos_outer hA hb
    have hh : R / 2 < ‖x - c‖ := by simpa only [dist_eq_norm] using hx
    nlinarith [norm_nonneg (x - c)]
  · intro x hx hdist
    exact (hsmall x hx).trans (phaseClearingGaussian_buffer_ge m hδ hF hR
      (by simpa only [dist_eq_norm] using hdist))
  · exact hQ
  · exact hQc
  · exact hQs
  · intro x hx
    exact (hQlocal x hx).eq_of_nhds
  · intro x hx hsx
    rw [hQdiv x hx]
    have hh := phaseClearingGaussian_supersolution m hδ hF hR
      (c := c) (x := x) (show ‖x - c‖ ∈ Icc (R / 2) R from
        ⟨by simpa only [dist_eq_norm] using hsx.le,
          by have hd : ‖x - c‖ < 3 * R / 4 := by
               simpa only [mem_ball, dist_eq_norm] using hx
             linarith⟩)
    change F ≤ -(Δ w) x at hh
    linarith
  · intro x hx
    rw [(hQlocal x (ball_subset_ball (by linarith) hx)).eq_of_nhds]
    exact phaseClearingGaussian_scaled_gradient_bound m hδ hF hR
      (by simpa only [mem_ball, dist_eq_norm] using (show dist x c ≤ R / 2 from hx.le))
  · intro x hx
    rw [hQdiv x (ball_subset_ball (by linarith) hx)]
    exact phaseClearingGaussian_scaled_laplacian_bound m hδ hF hR c x
  · exact habs

/-- Uniform small-amplitude clearing at all sufficiently small physical radii.
The constants are obtained from the original reaction and dimension. -/
theorem RigidityHypotheses.exists_phase_clearing_constants
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ a R₀ : ℝ, 0 < a ∧ 0 < R₀ ∧
      ∀ (c : Space (m + 1)) (R : ℝ), 0 < R → R ≤ R₀ →
        (∀ x ∈ ball c R, zeroExtension g u x ≤ a * R) →
          EqOn (zeroExtension g u) 0 (ball c (R / 2)) := by
  obtain ⟨c₀, F, hc₀, hF, hW, hf⟩ := hr.exists_low_phase_bounds h
  let G := phaseClearingGaussianGradientConstant m
  let L := phaseClearingGaussianLaplacianConstant m
  have hG : 0 ≤ G := by dsimp [G, phaseClearingGaussianGradientConstant]; positivity
  have hL : 0 ≤ L := by dsimp [L, phaseClearingGaussianLaplacianConstant]; positivity
  let P : ℝ → ℝ := fun t ↦ G * (t + F * t) / Real.sqrt (2 * c₀) +
    L * (t ^ 2 + t * F * t) / c₀
  have hP : Continuous P := by unfold P; fun_prop
  have hPzero : P 0 < 1 := by simp [P]
  obtain ⟨ε, hε, hεP⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt hP continuous_const).mem_nhds hPzero)
  let a := min (ε / 2) (1 / 2 : ℝ)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have haε : a < ε := (min_le_left _ _).trans_lt (by linarith)
  have haHalf : a ≤ 1 / 2 := min_le_right _ _
  have haP : P a < 1 := hεP (by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha] using haε)
  refine ⟨a, a, ha, ha, ?_⟩
  intro c R hR hRa hsmall
  have hδ : 0 < a * R := mul_pos ha hR
  have hδhalf : a * R ≤ 1 / 2 := by nlinarith
  apply hr.zeroExtension_eq_zero_halfBall_of_absorption h hδ
    (hδhalf.trans (by norm_num)) hF hR hc₀
    (fun t ht ↦ hW t ⟨ht.1, ht.2.trans hδhalf⟩)
    (fun t ht ↦ hf t ⟨ht.1, ht.2.trans hδhalf⟩) hsmall
  have hFR : F * R ≤ F * a := mul_le_mul_of_nonneg_left hRa hF
  have hid :
      G * (a * R / R + F * R) / Real.sqrt (2 * c₀) +
        (a * R) * (L * (a * R / R ^ 2 + F)) / c₀ =
      G * (a + F * R) / Real.sqrt (2 * c₀) +
        L * (a ^ 2 + a * F * R) / c₀ := by
    field_simp
  change G * (a * R / R + F * R) / Real.sqrt (2 * c₀) +
    (a * R) * (L * (a * R / R ^ 2 + F)) / c₀ < 1
  rw [hid]
  apply lt_of_le_of_lt ?_ haP
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : a + F * R ≤ a + F * a) hG)
      (Real.sqrt_nonneg _)
  · apply div_le_div_of_nonneg_right ?_ hc₀.le
    apply mul_le_mul_of_nonneg_left ?_ hL
    nlinarith [mul_le_mul_of_nonneg_left hFR ha.le]

end SerrinEpigraph
