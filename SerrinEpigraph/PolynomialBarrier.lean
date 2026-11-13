module

public import SerrinEpigraph.WeakEquation
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A polynomial comparison function on balls

The squared quadratic vanishes on the sphere and has an explicit upper bound
for its negative Laplacian divided by itself.
-/

public section

noncomputable section

open InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared quadratic used on a ball of radius `R`. -/
@[expose] def polynomialBallBarrier (c : E) (R : ℝ) (x : E) : ℝ :=
  (R ^ 2 - ‖x - c‖ ^ 2) ^ 2

/-- The comparison polynomial is smooth on the whole ambient space. -/
theorem contDiff_polynomialBallBarrier (c : E) (R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (polynomialBallBarrier c R) :=
  (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).pow 2

private theorem fderiv_squared_distance (c x v : E) :
    fderiv ℝ (fun y ↦ ‖y - c‖ ^ 2) x v = 2 * inner ℝ (x - c) v := by
  have heq : (fun y : E ↦ ‖y - c‖ ^ 2) = fun y ↦ inner ℝ (y - c) (y - c) :=
    funext fun y ↦ (real_inner_self_eq_norm_sq (y - c)).symm
  have hd : DifferentiableAt ℝ (fun y : E ↦ y - c) x :=
    differentiableAt_id.sub_const c
  rw [heq, fderiv_inner_apply ℝ hd hd]
  simp only [fderiv_sub_const, fderiv_fun_id, ContinuousLinearMap.id_apply]
  rw [real_inner_comm v (x - c)]
  ring

/-- First directional derivative of the comparison polynomial. -/
theorem fderiv_polynomialBallBarrier (c x v : E) (R : ℝ) :
    fderiv ℝ (polynomialBallBarrier c R) x v =
      -4 * (R ^ 2 - ‖x - c‖ ^ 2) * inner ℝ (x - c) v := by
  have hn : DifferentiableAt ℝ (fun y : E ↦ ‖y - c‖ ^ 2) x :=
    ((contDiff_id.sub contDiff_const).norm_sq ℝ (n := 1)).differentiable_one x
  unfold polynomialBallBarrier
  rw [fderiv_fun_pow 2 (hn.const_sub _)]
  simp only [fderiv_const_sub, smul_apply, smul_eq_mul, neg_apply]
  rw [fderiv_squared_distance]
  norm_num
  ring

/-- Second directional derivative of the comparison polynomial. -/
theorem fderiv_fderiv_polynomialBallBarrier (c x v : E) (R : ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ (polynomialBallBarrier c R) y v) x v =
      8 * inner ℝ (x - c) v ^ 2 - 4 * (R ^ 2 - ‖x - c‖ ^ 2) * ‖v‖ ^ 2 := by
  have ht : DifferentiableAt ℝ (fun y : E ↦ y - c) x := differentiableAt_id.sub_const c
  have hi := ht.inner ℝ (differentiableAt_const v)
  have hn : DifferentiableAt ℝ (fun y : E ↦ ‖y - c‖ ^ 2) x :=
    ((contDiff_id.sub contDiff_const).norm_sq ℝ (n := 1)).differentiable_one x
  have heq : (fun y ↦ fderiv ℝ (polynomialBallBarrier c R) y v) =
      fun y ↦ -4 * (R ^ 2 - ‖y - c‖ ^ 2) * inner ℝ (y - c) v :=
    funext fun y ↦ fderiv_polynomialBallBarrier c y v R
  have hinner : fderiv ℝ (fun y : E ↦ inner ℝ (y - c) v) x v = ‖v‖ ^ 2 := by
    rw [fderiv_inner_apply ℝ ht (differentiableAt_const v)]
    simp [fderiv_sub_const, fderiv_fun_id]
  rw [heq, fderiv_fun_mul ((hn.const_sub _).const_mul _) hi,
    fderiv_const_mul (hn.const_sub _)]
  simp only [fderiv_const_sub, smul_apply, smul_eq_mul, neg_apply, add_apply]
  rw [fderiv_squared_distance, hinner]
  ring

variable [FiniteDimensional ℝ E]

/-- Exact Laplacian of the comparison polynomial. -/
theorem laplacian_polynomialBallBarrier (c x : E) (R : ℝ) :
    (Δ (polynomialBallBarrier c R)) x =
      8 * ‖x - c‖ ^ 2 - 4 * (R ^ 2 - ‖x - c‖ ^ 2) * Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hd := ((contDiff_polynomialBallBarrier c R (n := 2)).fderiv_right
    (by norm_num)).differentiable_one x
  rw [laplacian_eq_sum_fderiv b hd]
  simp_rw [fderiv_fderiv_polynomialBallBarrier, b.orthonormal.norm_eq_one, one_pow, mul_one]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, b.sum_sq_inner_left]
  simp [mul_comm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The barrier takes its maximum scale at the center. -/
theorem polynomialBallBarrier_center (c : E) (R : ℝ) :
    polynomialBallBarrier c R c = R ^ 4 := by
  simp [polynomialBallBarrier]
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The barrier vanishes on the sphere. -/
theorem polynomialBallBarrier_sphere (c x : E) (R : ℝ) (hx : dist x c = R) :
    polynomialBallBarrier c R x = 0 := by
  rw [dist_eq_norm] at hx
  simp [polynomialBallBarrier, hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The barrier is strictly positive inside every ball of positive radius. -/
theorem polynomialBallBarrier_pos (c x : E) {R : ℝ} (hR : 0 < R)
    (hx : dist x c < R) : 0 < polynomialBallBarrier c R x := by
  rw [dist_eq_norm] at hx
  have hs : 0 < R ^ 2 - ‖x - c‖ ^ 2 := by nlinarith [norm_nonneg (x - c)]
  exact sq_pos_of_pos hs

/-- An explicit bound for the negative Laplacian, valid everywhere for positive radius. -/
theorem neg_laplacian_polynomialBallBarrier_le (c x : E) {R : ℝ} (hR : 0 < R) :
    -(Δ (polynomialBallBarrier c R)) x ≤
      ((Module.finrank ℝ E : ℝ) + 2) ^ 2 / R ^ 2 * polynomialBallBarrier c R x := by
  rw [laplacian_polynomialBallBarrier]
  change -(8 * ‖x - c‖ ^ 2 - 4 * (R ^ 2 - ‖x - c‖ ^ 2) * (Module.finrank ℝ E : ℝ)) ≤
    ((Module.finrank ℝ E : ℝ) + 2) ^ 2 / R ^ 2 * (R ^ 2 - ‖x - c‖ ^ 2) ^ 2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hid : ((Module.finrank ℝ E : ℝ) + 2) ^ 2 * (R ^ 2 - ‖x - c‖ ^ 2) ^ 2 -
      (-(8 * ‖x - c‖ ^ 2 - 4 * (R ^ 2 - ‖x - c‖ ^ 2) * (Module.finrank ℝ E : ℝ))) * R ^ 2 =
      (((Module.finrank ℝ E : ℝ) + 2) * (R ^ 2 - ‖x - c‖ ^ 2) - 2 * R ^ 2) ^ 2 +
        4 * (R ^ 2) ^ 2 := by ring
  nlinarith [sq_nonneg (((Module.finrank ℝ E : ℝ) + 2) *
    (R ^ 2 - ‖x - c‖ ^ 2) - 2 * R ^ 2), sq_nonneg (R ^ 2)]

end SerrinEpigraph
