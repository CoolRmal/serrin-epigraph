module

public import SerrinEpigraph.BernsteinQuantity
public import SerrinEpigraph.PolynomialBarrier

/-!
# The interior Bernstein estimate with the polynomial ball cutoff
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology Laplacian ContDiff

namespace SerrinEpigraph

/-- Completing a square for each coordinate derivative controls the kinetic cross term. -/
theorem hessian_completion_nonneg {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {u : Space d → ℝ} {x : Space d}
    (hu : ContDiffAt ℝ 2 u x) (t : ℝ) (z : Space d) :
    0 ≤ t ^ 2 * hessianSquare b u x -
      2 * t * inner ℝ z (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) +
      ‖z‖ ^ 2 * ‖gradient u x‖ ^ 2 := by
  let v := fun i ↦ fderiv ℝ u x (b i)
  let p := fun i ↦ gradient (fun y ↦ fderiv ℝ u y (b i)) x
  have hs : 0 ≤ ∑ i, ‖t • p i - v i • z‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hnorm (i : Fin d) : ‖t • p i - v i • z‖ ^ 2 =
      t ^ 2 * ‖p i‖ ^ 2 - 2 * t * (v i * inner ℝ z (p i)) + ‖z‖ ^ 2 * v i ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm z (p i)]
    ring
  simp_rw [hnorm] at hs
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hp : (∑ i, v i * inner ℝ z (p i)) =
      inner ℝ z (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) := by
    rw [gradient_half_gradient_norm_sq_eq_sum b hu, inner_sum]
    simp only [real_inner_smul_right]
    rfl
  have hv := half_gradient_norm_sq_eq_sum b u x
  rw [← Finset.sum_div] at hv
  have hv' : (∑ i, v i ^ 2) = ‖gradient u x‖ ^ 2 := by dsimp only [v]; linarith
  rw [hp, hv'] at hs
  exact hs

/-- Explicit gradient of the squared quadratic ball cutoff. -/
theorem gradient_polynomialBallBarrier {d : ℕ} (c x : Space d) (R : ℝ) :
    gradient (polynomialBallBarrier c R) x = (-4 * (R ^ 2 - ‖x - c‖ ^ 2)) • (x - c) := by
  apply (toDual ℝ (Space d)).injective
  ext z
  change inner ℝ (gradient (polynomialBallBarrier c R) x) z = _
  rw [inner_gradient_left, fderiv_polynomialBallBarrier]
  change _ = inner ℝ ((-4 * (R ^ 2 - ‖x - c‖ ^ 2)) • (x - c)) z
  rw [real_inner_smul_left]

/-- On the unit ball the polynomial cutoff lies between zero and one. -/
theorem polynomialBallBarrier_unit_mem_Icc {d : ℕ} {c x : Space d}
    (hx : x ∈ closedBall c 1) : polynomialBallBarrier c 1 x ∈ Icc (0 : ℝ) 1 := by
  have hn : ‖x - c‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hn0 := norm_nonneg (x - c)
  constructor
  · exact sq_nonneg _
  · change (1 ^ 2 - ‖x - c‖ ^ 2) ^ 2 ≤ 1
    have hn2 : ‖x - c‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg ‖x - c‖) (sub_nonneg.mpr hn2)]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The polynomial cutoff's mixed kinetic term is absorbed by its Hessian term. -/
theorem Hypotheses.polynomial_kinetic_cross_bound (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (c : Space (m + 1))
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    -(16 * ‖x - c‖ ^ 2 * ‖gradient u x‖ ^ 2) ≤
      polynomialBallBarrier c 1 x * hessianSquare b u x +
        2 * inner ℝ (gradient (polynomialBallBarrier c 1) x)
          (gradient (fun y ↦ ‖gradient u y‖ ^ 2 / 2) x) := by
  have hh := hessian_completion_nonneg b
    (h.solution_contDiffOn.contDiffAt
      ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx))
    (1 - ‖x - c‖ ^ 2) ((4 : ℝ) • (x - c))
  rw [norm_smul] at hh
  simp only [real_inner_smul_left, Real.norm_eq_abs] at hh
  norm_num at hh
  rw [gradient_polynomialBallBarrier, real_inner_smul_left]
  dsimp only [polynomialBallBarrier]
  norm_num
  nlinarith only [hh]

/-- A fixed coefficient makes the weak Bernstein source dominate the gradient squared. -/
theorem Hypotheses.bernsteinSource_lower_bound (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (c : Space (m + 1))
    {B : ℝ} (hB : 0 ≤ B) {x : Space (m + 1)} (hx : x ∈ epigraph g)
    (hxball : x ∈ closedBall c 1) (hf : deriv f (u x) ≤ B) :
    ‖gradient u x‖ ^ 2 - (B + 2 * (m + 1 : ℝ) + 13) * u x * f (u x) ≤
      bernsteinSource b u f (polynomialBallBarrier c 1) (B + 2 * (m + 1 : ℝ) + 13) x := by
  have hcross := h.polynomial_kinetic_cross_bound b c hx
  have hη := polynomialBallBarrier_unit_mem_Icc hxball
  have hfη : polynomialBallBarrier c 1 x * deriv f (u x) ≤ B :=
    (mul_le_mul_of_nonneg_left hf hη.1).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hη.2 hB])
  have hn : ‖x - c‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hxball
  have hn2 : ‖x - c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - c)]
  have hdim : (0 : ℝ) ≤ m + 1 := by positivity
  have hlap : 8 * ‖x - c‖ ^ 2 - 4 * (m + 1 : ℝ) ≤
      (Δ (polynomialBallBarrier c 1)) x := by
    rw [laplacian_polynomialBallBarrier]
    simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one, one_pow]
    nlinarith [mul_nonneg (sq_nonneg ‖x - c‖) hdim]
  have hG := sq_nonneg ‖gradient u x‖
  have h1 := mul_le_mul_of_nonneg_right hfη hG
  have h2 := mul_le_mul_of_nonneg_right hlap (div_nonneg hG (by norm_num : (0 : ℝ) ≤ 2))
  have h3 := mul_le_mul_of_nonneg_right hn2 hG
  dsimp only [bernsteinSource]
  nlinarith only [hcross, h1, h2, h3, hG]

end SerrinEpigraph
