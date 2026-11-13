module

public import SerrinEpigraph.WeakEquation
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gaussian barriers on annuli

The explicit radial barrier used for propagation of positivity has a nonnegative
`Δb - M b` on an annulus when its exponential parameter is sufficiently large.
-/

public section

noncomputable section

open InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Gaussian centered at `c`. -/
@[expose]
def radialGaussian (c : E) (α : ℝ) (x : E) : ℝ := Real.exp (-α * ‖x - c‖ ^ 2)

/-- The Gaussian barrier vanishing on the sphere of radius `R`. -/
@[expose]
def annularBarrier (c : E) (α R : ℝ) (x : E) : ℝ :=
  radialGaussian c α x - Real.exp (-α * R ^ 2)

theorem contDiff_radialGaussian (c : E) (α : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (radialGaussian c α) := by
  have hn : ContDiff ℝ n (fun y : E ↦ ‖y - c‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  exact (contDiff_const.mul hn).exp

theorem contDiff_annularBarrier (c : E) (α R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (annularBarrier c α R) :=
  (contDiff_radialGaussian c α).sub contDiff_const

omit [InnerProductSpace ℝ E] in
theorem radialGaussian_pos (c x : E) (α : ℝ) : 0 < radialGaussian c α x :=
  Real.exp_pos _

omit [InnerProductSpace ℝ E] in
/-- The annular barrier is positive inside its outer sphere. -/
theorem annularBarrier_pos {c x : E} {α R : ℝ} (hα : 0 < α) (hR : 0 ≤ R)
    (hx : ‖x - c‖ < R) : 0 < annularBarrier c α R x := by
  apply sub_pos.2 (Real.exp_lt_exp.2 ?_)
  have hs := (sq_lt_sq₀ (norm_nonneg (x - c)) hR).2 hx
  nlinarith [mul_lt_mul_of_pos_left hs hα]

omit [InnerProductSpace ℝ E] in
/-- The annular barrier is nonpositive beyond its outer sphere. -/
theorem annularBarrier_nonpos {c x : E} {α R : ℝ} (hα : 0 ≤ α) (hR : 0 ≤ R)
    (hx : R ≤ ‖x - c‖) : annularBarrier c α R x ≤ 0 := by
  apply sub_nonpos.2 (Real.exp_le_exp.2 ?_)
  have hs := (sq_le_sq₀ hR (norm_nonneg (x - c))).2 hx
  nlinarith [mul_le_mul_of_nonneg_left hs hα]

omit [InnerProductSpace ℝ E] in
theorem annularBarrier_eq_zero {c x : E} {α R : ℝ} (hx : ‖x - c‖ = R) :
    annularBarrier c α R x = 0 := by
  simp [annularBarrier, radialGaussian, hx]

omit [InnerProductSpace ℝ E] in
theorem annularBarrier_lt_one (c x : E) {α : ℝ} (hα : 0 ≤ α) (R : ℝ) :
    annularBarrier c α R x < 1 := by
  have hg : radialGaussian c α x ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x - c‖])
  have he := Real.exp_pos (-α * R ^ 2)
  change radialGaussian c α x - Real.exp (-α * R ^ 2) < 1
  linarith

private theorem fderiv_norm_sq_sub_apply (c x v : E) :
    fderiv ℝ (fun y ↦ ‖y - c‖ ^ 2) x v = 2 * inner ℝ (x - c) v := by
  have hfun : (fun y : E ↦ ‖y - c‖ ^ 2) = fun y ↦ inner ℝ (y - c) (y - c) := by
    funext y
    exact (real_inner_self_eq_norm_sq (y - c)).symm
  have ht : DifferentiableAt ℝ (fun y : E ↦ y - c) x := differentiableAt_id.sub_const c
  rw [hfun, fderiv_inner_apply ℝ ht ht]
  simp only [fderiv_sub_const, fderiv_fun_id, ContinuousLinearMap.id_apply]
  rw [real_inner_comm v (x - c)]
  ring

/-- First directional derivative of the radial Gaussian. -/
theorem fderiv_radialGaussian_apply (c x v : E) (α : ℝ) :
    fderiv ℝ (radialGaussian c α) x v =
      -2 * α * inner ℝ (x - c) v * radialGaussian c α x := by
  have hn : DifferentiableAt ℝ (fun y : E ↦ ‖y - c‖ ^ 2) x :=
    ((show ContDiff ℝ 1 (fun y : E ↦ ‖y - c‖ ^ 2) from
      (contDiff_id.sub contDiff_const).norm_sq ℝ).differentiable_one x)
  change fderiv ℝ (fun y ↦ Real.exp (-α * ‖y - c‖ ^ 2)) x v =
    -2 * α * inner ℝ (x - c) v * Real.exp (-α * ‖x - c‖ ^ 2)
  rw [fderiv_exp (hn.const_mul (-α)), fderiv_const_mul hn]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_norm_sq_sub_apply]
  ring

/-- Second directional derivative of the radial Gaussian. -/
theorem fderiv_fderiv_radialGaussian_apply (c x v : E) (α : ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ (radialGaussian c α) y v) x v =
      (4 * α ^ 2 * inner ℝ (x - c) v ^ 2 - 2 * α * ‖v‖ ^ 2) *
        radialGaussian c α x := by
  have ht : DifferentiableAt ℝ (fun y : E ↦ y - c) x := differentiableAt_id.sub_const c
  have hi : DifferentiableAt ℝ (fun y : E ↦ inner ℝ (y - c) v) x :=
    ht.inner ℝ (differentiableAt_const v)
  have hg : DifferentiableAt ℝ (radialGaussian c α) x :=
    (contDiff_radialGaussian c α (n := 1)).differentiable_one x
  have hfirst : (fun y ↦ fderiv ℝ (radialGaussian c α) y v) =
      fun y ↦ -2 * α * inner ℝ (y - c) v * radialGaussian c α y :=
    funext fun y ↦ fderiv_radialGaussian_apply c y v α
  have hinner : fderiv ℝ (fun y : E ↦ inner ℝ (y - c) v) x v = ‖v‖ ^ 2 := by
    rw [fderiv_inner_apply ℝ ht (differentiableAt_const v)]
    simp [fderiv_sub_const, fderiv_fun_id]
  rw [hfirst, fderiv_fun_mul (hi.const_mul (-2 * α)) hg, fderiv_const_mul hi]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hinner, fderiv_radialGaussian_apply]
  ring

variable [FiniteDimensional ℝ E]

/-- The Gaussian Laplacian in any finite-dimensional real inner-product space. -/
theorem laplacian_radialGaussian (c x : E) (α : ℝ) :
    (Δ (radialGaussian c α)) x =
      (4 * α ^ 2 * ‖x - c‖ ^ 2 - 2 * α * Module.finrank ℝ E) *
        radialGaussian c α x := by
  let b := stdOrthonormalBasis ℝ E
  have hd : DifferentiableAt ℝ (fderiv ℝ (radialGaussian c α)) x :=
    ((contDiff_radialGaussian c α (n := 2)).fderiv_right (by norm_num)).differentiable_one x
  rw [laplacian_eq_sum_fderiv b hd]
  simp_rw [fderiv_fderiv_radialGaussian_apply, b.orthonormal.norm_eq_one, one_pow, mul_one]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, b.sum_sq_inner_left]
  simp [mul_comm]

theorem laplacian_annularBarrier (c x : E) (α R : ℝ) :
    (Δ (annularBarrier c α R)) x =
      (4 * α ^ 2 * ‖x - c‖ ^ 2 - 2 * α * Module.finrank ℝ E) *
        radialGaussian c α x := by
  change (Δ ((radialGaussian c α - fun _ : E ↦ Real.exp (-α * R ^ 2)) : E → ℝ)) x = _
  rw [((contDiff_radialGaussian c α (n := 2)).contDiffAt (x := x)).laplacian_sub
    (contDiffAt_const (c := Real.exp (-α * R ^ 2)))]
  simp only [laplacian_const, Pi.zero_apply, sub_zero, laplacian_radialGaussian]

/-- A sufficiently steep Gaussian is a subsolution on every annulus outside radius `r`. -/
theorem annularBarrier_subsolution {c x : E} {α r R M : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hx : r ≤ ‖x - c‖)
    (hα : 2 * α * Module.finrank ℝ E + M ≤ 4 * α ^ 2 * r ^ 2) :
    0 ≤ (Δ (annularBarrier c α R)) x - M * annularBarrier c α R x := by
  have hs := (sq_le_sq₀ hr (norm_nonneg (x - c))).2 hx
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * α ^ 2 by positivity)
  have hcoeff : 0 ≤ 4 * α ^ 2 * ‖x - c‖ ^ 2 - 2 * α * Module.finrank ℝ E - M := by
    linarith
  rw [laplacian_annularBarrier, annularBarrier]
  have hg := mul_nonneg hcoeff (radialGaussian_pos c x α).le
  have he := mul_nonneg hM (Real.exp_pos (-α * R ^ 2)).le
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- There is a positive Gaussian parameter satisfying the annular subsolution bound. -/
theorem exists_annularBarrier_parameter {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) :
    ∃ α : ℝ, 0 < α ∧
      2 * α * Module.finrank ℝ E + M ≤ 4 * α ^ 2 * r ^ 2 := by
  let d : ℝ := Module.finrank ℝ E
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  let α : ℝ := (d + M + 1) / r ^ 2 + 1
  have hα1 : 1 ≤ α := by
    dsimp [α]
    exact le_add_of_nonneg_left (div_nonneg (by linarith) hr2.le)
  have hαr : α * r ^ 2 = d + M + 1 + r ^ 2 := by
    dsimp [α]
    field_simp
  refine ⟨α, by linarith, ?_⟩
  have hc : 2 * d + M ≤ 4 * α * r ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ α by linarith)
  have hMα : M ≤ M * α := by nlinarith
  change 2 * α * d + M ≤ 4 * α ^ 2 * r ^ 2
  nlinarith

end SerrinEpigraph
