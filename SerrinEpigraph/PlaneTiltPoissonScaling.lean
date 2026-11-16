module

public import SerrinEpigraph.PlaneTiltPoissonBernstein
public import SerrinEpigraph.PlaneTiltTranslatedEnergy

/-!
# Interior Poisson estimates on arbitrary balls
-/

public section
noncomputable section

open Set Metric MeasureTheory InnerProductSpace
open scoped Topology Laplacian ContDiff

namespace SerrinEpigraph

/-- Dilation scales the classical Laplacian by the square of its factor. -/
theorem laplacian_comp_dilation_of_contDiffAt {d : ℕ} {v : Space d → ℝ}
    (R : ℝ) (x : Space d) (hv : ContDiffAt ℝ 2 v (R • x)) :
    (Δ (fun y ↦ v (R • y))) x = R ^ 2 * (Δ v) (R • x) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hw : ContDiffAt ℝ 2 (fun y ↦ v (R • y)) x :=
    hv.comp x (by fun_prop)
  have hd := (hv.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
    (by norm_num)
  have hwd := (hw.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
    (by norm_num)
  rw [laplacian_eq_sum_fderiv b hwd, laplacian_eq_sum_fderiv b hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fderiv_comp_smul, smul_apply, smul_eq_mul]
  have hdi : DifferentiableAt ℝ (fun y ↦ fderiv ℝ v (R • y) (b i)) x :=
    (hd.clm_apply (differentiableAt_const (b i))).comp x
      ((differentiableAt_id.const_smul R))
  rw [fderiv_const_mul hdi, fderiv_comp_smul (f := fun y ↦ fderiv ℝ v y (b i))]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Translation and dilation scale the Laplacian exactly. -/
theorem laplacian_comp_translate_dilation_of_contDiffAt {d : ℕ} {v : Space d → ℝ}
    (c : Space d) (R : ℝ) (x : Space d) (hv : ContDiffAt ℝ 2 v (c + R • x)) :
    (Δ (fun y ↦ v (c + R • y))) x = R ^ 2 * (Δ v) (c + R • x) := by
  have ht : ContDiffAt ℝ 2 (fun y ↦ v (c + y)) (R • x) :=
    hv.comp _ (contDiffAt_const.add contDiffAt_id)
  rw [laplacian_comp_dilation_of_contDiffAt R x ht]
  congr 1
  simpa only [add_comm] using laplacian_comp_add_right v c (R • x)

/-- The quantitative C2 Poisson gradient estimate is invariant under changing
the interior ball radius. The form with a factor r² avoids division by small radii. -/
theorem poisson_gradient_sq_le_on_closedBall {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {v F : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hF : ContDiffOn ℝ 1 F Ω) (heq : ∀ x ∈ Ω, (Δ v) x = F x)
    {c : Space d} {r B D δ M : ℝ} (hr : 0 < r) (hc : closedBall c r ⊆ Ω)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hval : ∀ x ∈ closedBall c r, |v x| ≤ δ)
    (hsrc : ∀ x ∈ closedBall c r, |F x| ≤ M)
    (hforce : ∀ x ∈ closedBall c r,
      -(B * ‖gradient v x‖ ^ 2) - D ≤ inner ℝ (gradient v x) (gradient F x)) :
    r ^ 2 * ‖gradient v c‖ ^ 2 ≤ r ^ 4 * D +
      (r ^ 2 * B + 2 * (d : ℝ) + 13) * δ * (r ^ 2 * M) +
      (r ^ 2 * B + 2 * (d : ℝ) + 13) * δ ^ 2 := by
  let Ω' := (fun x : Space d ↦ c + r • x) ⁻¹' Ω
  let v' := fun x : Space d ↦ v (c + r • x)
  let F' := fun x : Space d ↦ r ^ 2 * F (c + r • x)
  have hΩ' : IsOpen Ω' := hΩ.preimage (by fun_prop)
  have hv' : ContDiffOn ℝ 2 v' Ω' := hv.comp (by fun_prop) (fun _ hx ↦ hx)
  have hF' : ContDiffOn ℝ 1 F' Ω' :=
    contDiffOn_const.mul (hF.comp (by fun_prop) (fun _ hx ↦ hx))
  have hmap {x : Space d} (hx : x ∈ closedBall 0 1) : c + r • x ∈ closedBall c r := by
    simp only [mem_closedBall, dist_zero_right] at hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hr.le
  have hgc (x : Space d) : gradient v' x = r • gradient v (c + r • x) :=
    gradient_comp_translate_dilation v c r x
  have hgf {x : Space d} (hx : x ∈ Ω') :
      gradient F' x = r ^ 3 • gradient F (c + r • x) := by
    have hd : DifferentiableAt ℝ (fun y ↦ F (c + r • y)) x :=
      ((hF.comp (by fun_prop) (fun _ hy ↦ hy) : ContDiffOn ℝ 1
        (fun y ↦ F (c + r • y)) Ω').differentiableOn_one x hx).differentiableAt
          (hΩ'.mem_nhds hx)
    change (toDual ℝ (Space d)).symm (fderiv ℝ F' x) = _
    rw [show F' = fun y ↦ r ^ 2 * F (c + r • y) from rfl,
      fderiv_const_mul hd, map_smul]
    change r ^ 2 • gradient (fun y ↦ F (c + r • y)) x = _
    rw [gradient_comp_translate_dilation, smul_smul, ← pow_succ]
  have hbound := poisson_gradient_sq_le_on_unit_ball b hΩ' hv' hF'
    (fun x hx ↦ by
      change (Δ v') x = r ^ 2 * F (c + r • x)
      rw [laplacian_comp_translate_dilation_of_contDiffAt c r x
        (hv.contDiffAt (hΩ.mem_nhds hx)), heq _ hx])
    (c := 0) (fun _ hx ↦ hc (hmap hx))
    (B := r ^ 2 * B) (D := r ^ 4 * D) (δ := δ) (M := r ^ 2 * M)
    (by positivity) (by positivity) hδ (by positivity)
    (fun _ hx ↦ hval _ (hmap hx))
    (fun x hx ↦ by
      dsimp only [F']
      rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left (hsrc _ (hmap hx)) (sq_nonneg r))
    (fun x hx ↦ by
      rw [hgc, hgf (hc (hmap hx)), norm_smul, Real.norm_of_nonneg hr.le,
        real_inner_smul_left, real_inner_smul_right]
      have hh := mul_le_mul_of_nonneg_left (hforce _ (hmap hx)) (pow_nonneg hr.le 4)
      nlinarith only [hh])
  simpa only [hgc, smul_zero, add_zero, norm_smul, Real.norm_of_nonneg hr.le, mul_pow]
    using hbound

end SerrinEpigraph
