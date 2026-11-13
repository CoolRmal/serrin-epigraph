module

public import SerrinEpigraph.LevelGradient
public import SerrinEpigraph.WeakEquation

/-!
# The equation satisfied by the foliation gradient
-/

public section

noncomputable section

open InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Differentiating the gradient along a solution leaf recovers the original Hessian. -/
theorem RigidityHypotheses.levelGradient_leaf_derivative (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (v : Space (m + 1)) :
    fderiv ℝ (hr.levelGradient h) p (horizontal v, fderiv ℝ u (hr.levelPoint h p) v) =
      fderiv ℝ (gradient u) (hr.levelPoint h p) v := by
  rw [hr.levelGradient_fderiv_apply h hs]
  have hp := h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg _
    (hr.levelPoint_mem h hs)
  have hv : point (horizontal v) 0 + v (Fin.last m) • verticalDirection m = v := by
    simpa only [zero_add, point_horizontal_last] using
      point_add_vertical (horizontal v) 0 (v (Fin.last m))
  have he := congrArg (fderiv ℝ u (hr.levelPoint h p)) hv
  rw [map_add, map_smul] at he
  have ht : (fderiv ℝ u (hr.levelPoint h p) v -
      fderiv ℝ u (hr.levelPoint h p) (point (horizontal v) 0)) /
        verticalDerivative u (hr.levelPoint h p) = v (Fin.last m) := by
    apply (div_eq_iff (ne_of_gt hp)).mpr
    change fderiv ℝ u (hr.levelPoint h p) (point (horizontal v) 0) +
      v (Fin.last m) * verticalDerivative u (hr.levelPoint h p) = _ at he
    linarith
  simp only [ht, point_horizontal_last]

/-- The Laplacian is the trace of the differential of the gradient. -/
theorem Hypotheses.laplacian_eq_sum_gradient_derivative (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space (m + 1))) :
    (Δ u) x = ∑ i, inner ℝ (fderiv ℝ (gradient u) x (b i)) (b i) := by
  have hc := (h.solution_contDiffOn.fderiv_of_isOpen
    (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num)).contDiffAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hd := hc.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space (m + 1))).symm.contDiff.contDiffAt.comp x hc).differentiableAt
      (by norm_num)
  rw [laplacian_eq_sum_fderiv b hd]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y ↦ fderiv ℝ u y (b i)) =
      (fun y ↦ inner ℝ (b i) (gradient u y)) := by
    funext y
    rw [real_inner_comm, inner_gradient_left]
  rw [he]
  have hder := (innerSL ℝ (b i)).hasFDerivAt.comp x hg.hasFDerivAt
  have hv := congrArg (fun L : Space (m + 1) →L[ℝ] ℝ ↦ L (b i)) hder.fderiv
  calc
    _ = inner ℝ (b i) (fderiv ℝ (gradient u) x (b i)) := by
      simpa [Function.comp_def] using hv
    _ = _ := real_inner_comm _ _

/-- The foliation field satisfies the PDE after the chain rule in the solution level. -/
theorem RigidityHypotheses.levelGradient_equation (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space (m + 1))) :
    (∑ i, inner ℝ (fderiv ℝ (hr.levelGradient h) p (horizontal (b i), 0)) (b i)) +
        inner ℝ (fderiv ℝ (hr.levelGradient h) p (0, 1)) (hr.levelGradient h p) =
      -f p.2 := by
  let D := fderiv ℝ (hr.levelGradient h) p
  let B := hr.levelGradient h p
  have he (i : ι) :
      inner ℝ (fderiv ℝ (gradient u) (hr.levelPoint h p) (b i)) (b i) =
        inner ℝ (D (horizontal (b i), 0)) (b i) +
          inner ℝ B (b i) * inner ℝ (D (0, 1)) (b i) := by
    rw [← hr.levelGradient_leaf_derivative h hs (b i)]
    have hp : (horizontal (b i), fderiv ℝ u (hr.levelPoint h p) (b i)) =
        (horizontal (b i), 0) +
          (fderiv ℝ u (hr.levelPoint h p) (b i)) • (0, 1) := by simp
    rw [hp, map_add, map_smul, inner_add_left, real_inner_smul_left]
    simp only [B, D, levelGradient, inner_gradient_left]
  have hsum := h.laplacian_eq_sum_gradient_derivative (hr.levelPoint_mem h hs) b
  simp_rw [he] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hparse : (∑ i, inner ℝ B (b i) * inner ℝ (D (0, 1)) (b i)) =
      inner ℝ (D (0, 1)) B := by
    simpa only [real_inner_comm, mul_comm] using b.sum_inner_mul_inner B (D (0, 1))
  rw [hparse] at hsum
  have hpde := h.equation _ (hr.levelPoint_mem h hs)
  rw [hr.solution_levelPoint h hs, hsum] at hpde
  linarith

/-- The level derivative of the calibration energy component. -/
theorem RigidityHypotheses.levelGradient_energy_deriv (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun s ↦ ‖hr.levelGradient h (p.1, s)‖ ^ 2 / 2 - normalizedPotential f s) p.2 =
      inner ℝ (fderiv ℝ (hr.levelGradient h) p (0, 1)) (hr.levelGradient h p) + f p.2 := by
  have hp : HasFDerivAt (fun s : ℝ ↦ (p.1, s))
      (ContinuousLinearMap.inr ℝ (Space m) ℝ) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hd := ((hr.levelGradient_contDiffAt h hs).differentiableAt
    (by norm_num)).hasFDerivAt.comp p.2 hp
  have hv : HasDerivAt (fun s ↦ hr.levelGradient h (p.1, s))
      (fderiv ℝ (hr.levelGradient h) p (0, 1)) p.2 := by
    simpa [Function.comp_def] using hd.hasDerivAt
  have he := ((hv.norm_sq).div_const 2).sub (h.normalizedPotential_hasDerivAt hs.1)
  change HasDerivAt
    (fun s ↦ ‖hr.levelGradient h (p.1, s)‖ ^ 2 / 2 - normalizedPotential f s)
    _ p.2 at he
  rw [he.deriv]
  rw [real_inner_comm (hr.levelGradient h p)]
  ring

/-- The horizontal divergence and level derivative of the calibration field cancel. -/
theorem RigidityHypotheses.levelGradient_calibration_identity (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space (m + 1))) :
    (∑ i, inner ℝ (fderiv ℝ (hr.levelGradient h) p (horizontal (b i), 0)) (b i)) +
      deriv (fun s ↦ ‖hr.levelGradient h (p.1, s)‖ ^ 2 / 2 - normalizedPotential f s) p.2 =
        0 := by
  rw [hr.levelGradient_energy_deriv h hs]
  have he := hr.levelGradient_equation h hs b
  linarith

end SerrinEpigraph
