module

public import SerrinEpigraph.WeakViscosity

/-!
# Quadratic penalization of bounded functions on closed domains
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The quadratic penalty about a chosen center. -/
@[expose] def quadraticPenalty {d : ℕ} (a : ℝ) (c x : Space d) : ℝ := a * ‖x - c‖ ^ 2

/-- Quadratic penalties are smooth. -/
theorem contDiff_quadraticPenalty {d : ℕ} (a : ℝ) (c : Space d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (quadraticPenalty a c) :=
  contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)

/-- First directional derivative of a quadratic penalty. -/
theorem fderiv_quadraticPenalty {d : ℕ} (a : ℝ) (c x v : Space d) :
    fderiv ℝ (quadraticPenalty a c) x v = 2 * a * inner ℝ (x - c) v := by
  have hd := (((hasFDerivAt_id x).sub_const c).norm_sq).const_mul a
  change HasFDerivAt (quadraticPenalty a c) _ x at hd
  rw [hd.fderiv]
  simp [inner_sub_left]
  ring

/-- Gradient of a quadratic penalty. -/
theorem gradient_quadraticPenalty {d : ℕ} (a : ℝ) (c x : Space d) :
    gradient (quadraticPenalty a c) x = (2 * a) • (x - c) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, fderiv_quadraticPenalty, real_inner_smul_left]

/-- Laplacian of a quadratic penalty. -/
theorem laplacian_quadraticPenalty {d : ℕ} (a : ℝ) (c x : Space d) :
    (Δ (quadraticPenalty a c)) x = 2 * a * d := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hd := ((contDiff_quadraticPenalty a c (n := 2)).fderiv_right
    (by norm_num)).differentiable_one x
  rw [laplacian_eq_sum_fderiv b hd]
  have hsecond (i : Fin d) :
      fderiv ℝ (fun y ↦ fderiv ℝ (quadraticPenalty a c) y (b i)) x (b i) = 2 * a := by
    have he : (fun y ↦ fderiv ℝ (quadraticPenalty a c) y (b i)) =
        fun y ↦ 2 * a * inner ℝ (y - c) (b i) := by
      funext y
      exact fderiv_quadraticPenalty a c y (b i)
    have ht : DifferentiableAt ℝ (fun y : Space d ↦ y - c) x := differentiableAt_id.sub_const c
    rw [he, fderiv_const_mul (ht.inner ℝ (differentiableAt_const (b i)))]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_inner_apply ℝ ht (differentiableAt_const (b i))]
    simp [fderiv_sub_const, fderiv_fun_id, b.orthonormal.norm_eq_one]
  simp_rw [hsecond]
  simp [mul_comm]

/-- A bounded continuous function, nonpositive on the boundary, has an interior penalized
maximum above any positive value. The distance estimate is uniform in the chosen maximizer. -/
theorem exists_quadratic_penalized_max {d : ℕ} {Ω : Set (Space d)} {Q : Space d → ℝ}
    (hΩ : IsOpen Ω) (hQ : ContinuousOn Q (closure Ω)) {M : ℝ}
    (hbound : ∀ y ∈ closure Ω, Q y ≤ M)
    (hboundary : ∀ y ∈ closure Ω, y ∉ Ω → Q y ≤ 0)
    {x : Space d} (hx : x ∈ Ω) (hxpos : 0 < Q x) {a : ℝ} (ha : 0 < a) :
    ∃ y ∈ Ω, Q x ≤ Q y ∧ a * ‖y - x‖ ^ 2 ≤ M ∧
      IsLocalMax (fun z ↦ Q z - quadraticPenalty a x z) y := by
  have hM : 0 < M := hxpos.trans_le (hbound x (subset_closure hx))
  let R := M / a + 1
  let P := fun z ↦ Q z - quadraticPenalty a x z
  let K := closure Ω ∩ closedBall x R
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith [div_nonneg hM.le ha.le]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRa : a * R = M + a := by dsimp only [R]; field_simp
  have hlarge : M < a * R ^ 2 := by
    have hsq : R ≤ R ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq ha.le
    linarith
  have hK : IsCompact K := (isCompact_closedBall x R).inter_left isClosed_closure
  have hxK : x ∈ K := ⟨subset_closure hx, mem_closedBall_self hR.le⟩
  have hP : ContinuousOn P K := (hQ.mono inter_subset_left).sub
    (contDiff_quadraticPenalty a x (n := 0)).continuous.continuousOn
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hP
  have hxy : Q x ≤ P y := by simpa [P, quadraticPenalty] using hmax hxK
  have hypos : 0 < P y := hxpos.trans_le hxy
  have hpen : 0 ≤ a * ‖y - x‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have hyΩ : y ∈ Ω := by
    by_contra hn
    have hh := hboundary y hy.1 hn
    change 0 < Q y - a * ‖y - x‖ ^ 2 at hypos
    linarith
  have hyball : y ∈ ball x R := by
    by_contra hn
    have hrnorm : R ≤ ‖y - x‖ := by simpa only [mem_ball, dist_eq_norm, not_lt] using hn
    have hsq : R ^ 2 ≤ ‖y - x‖ ^ 2 := by nlinarith [norm_nonneg (y - x)]
    have hp := mul_le_mul_of_nonneg_left hsq ha.le
    have hb := hbound y hy.1
    change 0 < Q y - a * ‖y - x‖ ^ 2 at hypos
    linarith
  refine ⟨y, hyΩ, ?_, ?_, ?_⟩
  · change Q x ≤ Q y - a * ‖y - x‖ ^ 2 at hxy
    linarith
  · have hb := hbound y hy.1
    change 0 < Q y - a * ‖y - x‖ ^ 2 at hypos
    linarith
  · exact hmax.isLocalMax (inter_mem
      (mem_of_superset (hΩ.mem_nhds hyΩ) subset_closure)
      (mem_of_superset (isOpen_ball.mem_nhds hyball) ball_subset_closedBall))

end SerrinEpigraph
