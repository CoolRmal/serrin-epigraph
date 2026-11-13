module

public import SerrinEpigraph.StrongMaximum
public import SerrinEpigraph.LimitEquation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# From a continuous weak Laplacian to second-order touching tests

A C1 function with continuous weak Laplacian satisfies the viscosity test inequality.
The proof uses the already established strong maximum principle, without differentiating
the function a second time.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian ContDiff

namespace SerrinEpigraph

/-- At an upper C2 touching test, the test Laplacian bounds the continuous weak Laplacian. -/
theorem weak_laplacian_le_at_upper_test {d : ℕ} {v F ψ : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hF : ContinuousOn F Ω)
    (heq : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ y, inner ℝ (gradient v y) (gradient φ y)) = -(∫ y, F y * φ y))
    (hψ : ContDiff ℝ 2 ψ) {x : Space d} (hx : x ∈ Ω)
    (hmax : IsLocalMax (fun y ↦ v y - ψ y) x) : F x ≤ (Δ ψ) x := by
  by_contra hn
  have hlt : (Δ ψ) x < F x := lt_of_not_ge hn
  let a := (F x - (Δ ψ) x) / 2
  have ha : 0 < a := by dsimp only [a]; linarith
  have hD : ContinuousAt (fun y ↦ F y - (Δ ψ) y) x :=
    (hF.continuousAt (hΩ.mem_nhds hx)).sub
      (continuous_laplacian_of_contDiff hψ).continuousAt
  have hDa : a < F x - (Δ ψ) x := by dsimp only [a]; linarith
  have hev : ∀ᶠ y in 𝓝 x,
      y ∈ Ω ∧ a < F y - (Δ ψ) y ∧ v y - ψ y ≤ v x - ψ x := by
    filter_upwards [hΩ.mem_nhds hx, hD (Ioi_mem_nhds hDa), hmax] with y hy hDy hmy
    exact ⟨hy, hDy, hmy⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hsub : ball x r ⊆ Ω := fun y hy ↦ (hball hy).1
  let w := fun y ↦ ψ y - v y + (v x - ψ x)
  have hw : ContDiffOn ℝ 1 w (ball x r) :=
    ((hψ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).contDiffOn.sub (hv.mono hsub)).add
      contDiffOn_const
  have hw0 (y : Space d) (hy : y ∈ ball x r) : 0 ≤ w y := by
    have hh := (hball hy).2.2
    dsimp only [w]
    linarith
  have hweakw (φ : Space d → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ ball x r) :
      (∫ y, inner ℝ (gradient w y) (gradient φ y)) =
        ∫ y, (F y - (Δ ψ) y) * φ y := by
    have hp : Integrable (fun y ↦ inner ℝ (gradient ψ y) (gradient φ y)) :=
      integrable_inner_gradient_of_hasCompactSupport isOpen_ball
        (hψ.of_le (by norm_num)).contDiffOn hφ hc hs
    have hvp : Integrable (fun y ↦ inner ℝ (gradient v y) (gradient φ y)) :=
      integrable_inner_gradient_of_hasCompactSupport isOpen_ball (hv.mono hsub) hφ hc hs
    have hiF : Integrable (fun y ↦ F y * φ y) :=
      integrable_mul_of_tsupport_subset (hF.mono hsub) hφ.continuous hc hs
    have hiL : Integrable (fun y ↦ (Δ ψ) y * φ y) :=
      integrable_mul_of_tsupport_subset (continuous_laplacian_of_contDiff hψ).continuousOn
        hφ.continuous hc hs
    have hpoint (y : Space d) : inner ℝ (gradient w y) (gradient φ y) =
        inner ℝ (gradient ψ y) (gradient φ y) - inner ℝ (gradient v y) (gradient φ y) := by
      by_cases hy : y ∈ ball x r
      · have hvd := (hv.differentiableOn_one y (hsub hy)).differentiableAt
          (hΩ.mem_nhds (hsub hy))
        simp only [w, gradient, fderiv_add_const,
          fderiv_fun_sub (hψ.differentiable (by norm_num) y) hvd, map_sub, inner_sub_left]
      · simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hy (hs hh))]
    simp_rw [hpoint]
    rw [integral_sub hp hvp,
      integral_inner_gradient_eq_neg_laplacian_mul isOpen_ball hψ.contDiffOn hφ hc hs,
      heq φ hφ hc (hs.trans hsub)]
    rw [neg_sub_neg, ← integral_sub hiF hiL]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y ↦ by dsimp only; ring)
  have hsuper : IsWeakSupersolution volume (ball x r) 1 w := by
    intro φ hφ hc hs hφ0
    have hp := integrable_inner_gradient_of_hasCompactSupport (μ := volume)
      isOpen_ball hw hφ hc hs
    have hwφ : Integrable (fun y ↦ 1 * w y * φ y) :=
      integrable_mul_of_tsupport_subset (continuousOn_const.mul hw.continuousOn)
        hφ.continuous hc hs
    rw [integral_add hp hwφ, hweakw φ hφ hc hs]
    apply add_nonneg
    · apply integral_nonneg
      intro y
      by_cases hy : y ∈ ball x r
      · exact mul_nonneg (ha.le.trans (hball hy).2.1.le) (hφ0 y)
      · simp [image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (hs hh))]
    · apply integral_nonneg
      intro y
      by_cases hy : y ∈ ball x r
      · exact mul_nonneg (by simpa using hw0 y hy) (hφ0 y)
      · simp [image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (hs hh))]
  have hwzero := hsuper.eq_zero_of_zero isOpen_ball (convex_ball x r).isPreconnected
    hw hw0 zero_lt_one (mem_ball_self hr) (show w x = 0 by dsimp only [w]; ring)
  let φ : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hφ : ContDiff ℝ 1 φ := φ.contDiff
  have hc : HasCompactSupport (φ : Space d → ℝ) := φ.hasCompactSupport
  have hs : tsupport (φ : Space d → ℝ) ⊆ ball x r := by
    rw [φ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [φ]; linarith)
  have hφx : φ x ≠ 0 := by
    rw [φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)]
    norm_num
  have hφpos : 0 < ∫ y, φ y := integral_pos_of_integrable_nonneg_nonzero
    φ.continuous (φ.continuous.integrable_of_hasCompactSupport hc) φ.nonneg' hφx
  have hpairzero : (∫ y, inner ℝ (gradient w y) (gradient φ y)) = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall (fun y ↦ by
      dsimp only [Pi.zero_apply]
      by_cases hy : y ∈ ball x r
      · have he : w =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
          filter_upwards [isOpen_ball.mem_nhds hy] with z hz
          exact hwzero z hz
        rw [he.gradient_eq]
        simp [gradient]
      · simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hh ↦ hy (hs hh))])
  have hiD : Integrable (fun y ↦ (F y - (Δ ψ) y) * φ y) :=
    integrable_mul_of_tsupport_subset
      ((hF.mono hsub).sub (continuous_laplacian_of_contDiff hψ).continuousOn)
      φ.continuous hc hs
  have hiA : Integrable (fun y ↦ a * φ y) :=
    (φ.continuous.integrable_of_hasCompactSupport hc).const_mul a
  have hbound : a * (∫ y, φ y) ≤ ∫ y, (F y - (Δ ψ) y) * φ y := by
    rw [← integral_const_mul]
    apply integral_mono hiA hiD
    intro y
    by_cases hy : y ∈ ball x r
    · exact mul_le_mul_of_nonneg_right (hball hy).2.1.le φ.nonneg
    · simp [image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (hs hh))]
  rw [← hweakw φ hφ hc hs, hpairzero] at hbound
  exact (not_lt_of_ge hbound) (mul_pos ha hφpos)

end SerrinEpigraph
