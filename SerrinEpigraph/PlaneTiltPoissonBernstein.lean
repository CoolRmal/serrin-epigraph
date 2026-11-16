module

public import SerrinEpigraph.PlaneTiltPoissonBochner

/-!
# An interior gradient estimate with a small forcing-gradient error
-/

public section
noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The weak Bernstein source for an inhomogeneous Poisson equation. -/
@[expose] def poissonBernsteinSource {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (v F η : Space d → ℝ) (A : ℝ)
    (x : Space d) : ℝ :=
  η x * (hessianSquare b v x + inner ℝ (gradient v x) (gradient F x)) +
    (‖gradient v x‖ ^ 2 / 2) * (Δ η) x +
    2 * inner ℝ (gradient η x) (gradient (fun y ↦ ‖gradient v y‖ ^ 2 / 2) x) +
    A * (‖gradient v x‖ ^ 2 + v x * F x)

/-- The generic Poisson Bernstein quantity has a continuous weak Laplacian. -/
theorem poisson_bernstein_weak_laplacian {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v F η : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hF : ContDiffOn ℝ 1 F Ω) (hη : ContDiff ℝ 2 η)
    (heq : ∀ x ∈ Ω, (Δ v) x = F x) (A : ℝ) :
    ContDiffOn ℝ 1 (bernsteinQuantity v η A) Ω ∧
      ContinuousOn (poissonBernsteinSource b v F η A) Ω ∧
      HasWeakLaplacian Ω (bernsteinQuantity v η A) (poissonBernsteinSource b v F η A) := by
  have hv1 : ContDiffOn ℝ 1 v Ω := hv.of_le (by norm_num)
  have hp := gradient_contDiffOn_of_two hΩ hv
  have hK : ContDiffOn ℝ 1 (fun x ↦ ‖gradient v x‖ ^ 2 / 2) Ω :=
    (hp.norm_sq (𝕜 := ℝ)).div_const 2
  have hKp := (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
    (hK.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hFp := (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
    (hF.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hη1 : ContDiffOn ℝ 1 η Ω := (hη.of_le (by norm_num)).contDiffOn
  have hηp := (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
    (hη1.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hKB := hasWeakLaplacian_half_gradient_norm_sq_of_poisson b hΩ hv hF heq
  have hKBc := (hessianSquare_continuousOn_of_two b hΩ hv).add (hp.continuousOn.inner hFp)
  have hV : HasWeakLaplacian Ω v F := by
    intro φ hφ hc hs
    have hh := integral_inner_gradient_eq_source_mul (μ := volume) hΩ hv hφ hc hs
      (F := fun x ↦ -F x) (fun x hx ↦ by rw [heq x hx])
    simpa only [neg_mul, integral_neg] using hh
  have hV2 := hV.half_sq hΩ hv1 hF.continuousOn
  have hV2c := (hp.continuousOn.norm.pow 2).add (hv.continuousOn.mul hF.continuousOn)
  have hηK := (hasWeakLaplacian_of_contDiffOn hΩ hη.contDiffOn).mul hKB hΩ hη1 hK
    (continuous_laplacian_of_contDiff hη).continuousOn hKBc
  have hA := hV2.const_mul hΩ ((hv1.pow 2).div_const 2) A
  have hsum := hηK.add hA hΩ (hη1.mul hK)
    (contDiffOn_const.mul ((hv1.pow 2).div_const 2))
    (((hK.continuousOn.mul (continuous_laplacian_of_contDiff hη).continuousOn).add
      (hη1.continuousOn.mul hKBc)).add (continuousOn_const.mul (hηp.inner hKp)))
    (continuousOn_const.mul hV2c)
  refine ⟨(hη1.mul hK).add (contDiffOn_const.mul ((hv1.pow 2).div_const 2)), ?_, ?_⟩
  · exact (((hη1.continuousOn.mul hKBc).add
      (hK.continuousOn.mul (continuous_laplacian_of_contDiff hη).continuousOn)).add
        (continuousOn_const.mul (hηp.inner hKp))).add (continuousOn_const.mul hV2c)
  · convert hsum using 1
    · rfl
    · funext x
      dsimp only [poissonBernsteinSource]
      ring

/-- The polynomial cutoff absorbs the mixed Hessian term for any C2 function. -/
theorem polynomial_poisson_kinetic_cross_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v : Space d → ℝ} {x : Space d}
    (hv : ContDiffAt ℝ 2 v x) (c : Space d) :
    -(16 * ‖x - c‖ ^ 2 * ‖gradient v x‖ ^ 2) ≤
      polynomialBallBarrier c 1 x * hessianSquare b v x +
        2 * inner ℝ (gradient (polynomialBallBarrier c 1) x)
          (gradient (fun y ↦ ‖gradient v y‖ ^ 2 / 2) x) := by
  have hh := hessian_completion_nonneg b hv (1 - ‖x - c‖ ^ 2) ((4 : ℝ) • (x - c))
  rw [norm_smul] at hh
  simp only [real_inner_smul_left, Real.norm_eq_abs] at hh
  norm_num at hh
  rw [gradient_polynomialBallBarrier, real_inner_smul_left]
  dsimp only [polynomialBallBarrier]
  norm_num
  nlinarith only [hh]

/-- A forcing-gradient lower bound gives a quantitative Bernstein-source lower bound. -/
theorem poissonBernsteinSource_lower_bound {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v F : Space d → ℝ} {x c : Space d}
    (hv : ContDiffAt ℝ 2 v x) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hx : x ∈ closedBall c 1)
    (hforce : -(B * ‖gradient v x‖ ^ 2) - D ≤ inner ℝ (gradient v x) (gradient F x)) :
    ‖gradient v x‖ ^ 2 - D + (B + 2 * (d : ℝ) + 13) * v x * F x ≤
      poissonBernsteinSource b v F (polynomialBallBarrier c 1) (B + 2 * (d : ℝ) + 13) x := by
  have hcross := polynomial_poisson_kinetic_cross_bound b hv c
  have hη := polynomialBallBarrier_unit_mem_Icc hx
  have hg := sq_nonneg ‖gradient v x‖
  have hforce' : -(B * ‖gradient v x‖ ^ 2) - D ≤
      polynomialBallBarrier c 1 x * inner ℝ (gradient v x) (gradient F x) := by
    have hh := mul_le_mul_of_nonneg_left hforce hη.1
    have hn : -(B * ‖gradient v x‖ ^ 2) - D ≤ 0 := by nlinarith [mul_nonneg hB hg]
    nlinarith [mul_le_mul_of_nonpos_right hη.2 hn]
  have hn : ‖x - c‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hn2 : ‖x - c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - c)]
  have hlap : 8 * ‖x - c‖ ^ 2 - 4 * (d : ℝ) ≤
      (Δ (polynomialBallBarrier c 1)) x := by
    rw [laplacian_polynomialBallBarrier]
    simp only [Space, finrank_euclideanSpace, Fintype.card_fin, one_pow]
    nlinarith [mul_nonneg (sq_nonneg ‖x - c‖) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h2 := mul_le_mul_of_nonneg_right hlap (div_nonneg hg (by norm_num : (0 : ℝ) ≤ 2))
  have h3 := mul_le_mul_of_nonneg_right hn2 hg
  dsimp only [poissonBernsteinSource]
  nlinarith only [hcross, hforce', h2, h3, hg]

/-- Interior gradient control from the solution size and a small forcing-gradient
error. It is valid for C2 solutions with a C1 Poisson source. -/
theorem poisson_gradient_sq_le_on_unit_ball {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v F : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hF : ContDiffOn ℝ 1 F Ω) (heq : ∀ x ∈ Ω, (Δ v) x = F x)
    {c : Space d} (hc : closedBall c 1 ⊆ Ω) {B D δ M : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hval : ∀ x ∈ closedBall c 1, |v x| ≤ δ)
    (hsrc : ∀ x ∈ closedBall c 1, |F x| ≤ M)
    (hforce : ∀ x ∈ closedBall c 1,
      -(B * ‖gradient v x‖ ^ 2) - D ≤ inner ℝ (gradient v x) (gradient F x)) :
    ‖gradient v c‖ ^ 2 ≤ D + (B + 2 * (d : ℝ) + 13) * δ * M +
      (B + 2 * (d : ℝ) + 13) * δ ^ 2 := by
  let A := B + 2 * (d : ℝ) + 13
  let η := polynomialBallBarrier c 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hη : ContDiff ℝ 2 η := contDiff_polynomialBallBarrier c 1
  obtain ⟨hQ, hS, hweak⟩ := poisson_bernstein_weak_laplacian b hΩ hv hF hη heq A
  have hcball : c ∈ closedBall c 1 := mem_closedBall_self (by norm_num)
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall c 1).exists_isMaxOn ⟨c, hcball⟩
    (hQ.continuousOn.mono hc)
  have hvy2 : v y ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hval y hy)
  have hvFy : -(δ * M) ≤ v y * F y := by
    have hh : |v y * F y| ≤ δ * M := by
      rw [abs_mul]
      exact mul_le_mul (hval y hy) (hsrc y hy) (abs_nonneg _) hδ
    exact (abs_le.mp hh).1
  have hηy := polynomialBallBarrier_unit_mem_Icc hy
  have hQbound : bernsteinQuantity v η A y ≤ (D + A * δ * M + A * δ ^ 2) / 2 := by
    by_cases hyball : y ∈ ball c 1
    · have hlocal : IsLocalMax (bernsteinQuantity v η A) y :=
        hmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hyball) ball_subset_closedBall)
      have hsource := hweak.nonpos_of_isLocalMax hΩ hQ hS (hc hy) hlocal
      have hlower := poissonBernsteinSource_lower_bound b
        (hv.contDiffAt (hΩ.mem_nhds (hc hy))) hB hD hy (hforce y hy)
      have hg : ‖gradient v y‖ ^ 2 ≤ D + A * δ * M := by
        have hh := mul_le_mul_of_nonneg_left hvFy hA
        change ‖gradient v y‖ ^ 2 - D + A * v y * F y ≤ _ at hlower
        nlinarith only [hlower, hsource, hh]
      have hηg := mul_le_mul_of_nonneg_right hηy.2 (sq_nonneg ‖gradient v y‖)
      have hAv := mul_le_mul_of_nonneg_left hvy2 hA
      dsimp only [bernsteinQuantity, η]
      nlinarith only [hg, hηg, hAv]
    · have hdist : dist y c = 1 := le_antisymm hy (not_lt.mp hyball)
      have hzero : η y = 0 := polynomialBallBarrier_sphere c y 1 hdist
      have hAv := mul_le_mul_of_nonneg_left hvy2 hA
      dsimp only [bernsteinQuantity]
      rw [hzero]
      nlinarith [mul_nonneg (mul_nonneg hA hδ) hM]
  have hcenter : ‖gradient v c‖ ^ 2 / 2 ≤ bernsteinQuantity v η A c := by
    dsimp only [bernsteinQuantity, η]
    rw [polynomialBallBarrier_center]
    norm_num
    positivity
  have hh : bernsteinQuantity v η A c ≤ bernsteinQuantity v η A y := hmax hcball
  change ‖gradient v c‖ ^ 2 ≤ D + A * δ * M + A * δ ^ 2
  linarith

end SerrinEpigraph
