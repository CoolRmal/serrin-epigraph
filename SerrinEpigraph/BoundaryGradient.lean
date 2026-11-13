module

public import SerrinEpigraph.LevelBoundary
public import SerrinEpigraph.QuadraticPotential

/-!
# Full gradient and gradient norm at the zero boundary
-/

public section

noncomputable section

open InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ}

/-- Horizontal and vertical components are orthogonal in the point coordinates. -/
theorem inner_point_point (a b : Space m) (s t : ℝ) :
    inner ℝ (point a s) (point b t) = inner ℝ a b + s * t := by
  simp [PiLp.inner_apply, point, Fin.sum_univ_castSucc, mul_comm]

/-- The specified outward normal is a unit vector. -/
theorem norm_outwardNormal (g : Space m → ℝ) (y : Space m) : ‖outwardNormal g y‖ = 1 := by
  have hp : 0 < 1 + ‖gradient g y‖ ^ 2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn : Real.sqrt (1 + ‖gradient g y‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have he : ‖outwardNormal g y‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ
      ((Real.sqrt (1 + ‖gradient g y‖ ^ 2))⁻¹ • point (gradient g y) (-1))
      ((Real.sqrt (1 + ‖gradient g y‖ ^ 2))⁻¹ • point (gradient g y) (-1)) = 1
    rw [real_inner_smul_left, real_inner_smul_right, inner_point_point,
      real_inner_self_eq_norm_sq]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (outwardNormal g y)]

variable {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Every boundary directional derivative is determined by its vertical component. -/
theorem Hypotheses.boundary_fderiv_apply (h : Hypotheses g u f κ)
    (y : Space m) (w : Space (m + 1)) :
    fderivWithin ℝ u (closure (epigraph g)) (point y (g y)) w =
      (w (Fin.last m) - fderiv ℝ g y (horizontal w)) *
        (κ / Real.sqrt (1 + ‖gradient g y‖ ^ 2)) := by
  let L := fderivWithin ℝ u (closure (epigraph g)) (point y (g y))
  have hu := h.solution_contDiffOn_closure.differentiableOn_one _
    (point_mem_closure_epigraph (le_refl (g y)))
  have ht := fderivWithin_point_tangent_eq_zero (h.graph_contDiff.differentiable_one y)
    hu h.dirichlet (horizontal w)
  have hv := boundary_vertical_derivative_eq (h.graph_contDiff.differentiable_one y)
    hu h.dirichlet (h.neumann y)
  have hp : point (horizontal w) (fderiv ℝ g y (horizontal w)) +
      (w (Fin.last m) - fderiv ℝ g y (horizontal w)) • verticalDirection m = w := by
    simpa only [add_sub_cancel, point_horizontal_last] using
      point_add_vertical (horizontal w) (fderiv ℝ g y (horizontal w))
        (w (Fin.last m) - fderiv ℝ g y (horizontal w))
  have he := congrArg L hp
  change L _ = L w at he
  simpa only [map_add, map_smul, L, ht, hv, zero_add, smul_eq_mul] using he.symm

/-- The full boundary gradient is minus the prescribed normal derivative times the outward normal. -/
theorem Hypotheses.boundary_gradient_eq (h : Hypotheses g u f κ) (y : Space m) :
    gradientWithin u (closure (epigraph g)) (point y (g y)) = -κ • outwardNormal g y := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradientWithin_left, h.boundary_fderiv_apply y w]
  conv_rhs => rw [← point_horizontal_last w]
  simp only [outwardNormal, real_inner_smul_left, inner_point_point, neg_mul, one_mul,
    inner_gradient_left]
  ring

/-- The boundary gradient has the constant norm prescribed by the Neumann condition. -/
theorem Hypotheses.norm_boundary_gradient (h : Hypotheses g u f κ) (y : Space m) :
    ‖gradientWithin u (closure (epigraph g)) (point y (g y))‖ = κ := by
  rw [h.boundary_gradient_eq y, norm_smul, norm_outwardNormal]
  simp [Real.norm_eq_abs, abs_of_pos h.kappa_pos]

/-- The closed foliation gradient has norm κ at level zero. -/
theorem RigidityHypotheses.norm_closedLevelGradient_zero (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) : ‖hr.closedLevelGradient h (y, 0)‖ = κ := by
  simp only [closedLevelGradient, hr.levelPoint_zero h y, h.norm_boundary_gradient y]

/-- The energy component of the closed foliation field is constant at level zero. -/
theorem RigidityHypotheses.closedLevelGradient_energy_zero (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) :
    ‖hr.closedLevelGradient h (y, 0)‖ ^ 2 / 2 - normalizedPotential f 0 =
      κ ^ 2 / 2 - normalizedPotential f 0 := by
  rw [hr.norm_closedLevelGradient_zero h y]

/-- The interior calibration energy component converges to its constant boundary value. -/
theorem RigidityHypotheses.levelGradient_energy_tendsto_boundary
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (y : Space m) :
    Tendsto (fun p : Space m × ℝ ↦ ‖hr.levelGradient h p‖ ^ 2 / 2 - normalizedPotential f p.2)
      (𝓝[{p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1}] (y, 0))
      (𝓝 (κ ^ 2 / 2 - normalizedPotential f 0)) := by
  have hs : Tendsto (fun p : Space m × ℝ ↦ p.2)
      (𝓝[{p : Space m × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) 1}] (y, 0))
      (𝓝[Set.Icc (0 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_snd.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact ⟨hp.1.le, hp.2.le⟩
  have hW := (h.normalizedPotential_continuousOn 0 (by simp)).tendsto.comp hs
  have hB := (hr.levelGradient_tendsto_boundary h y).norm
  rw [h.norm_boundary_gradient y] at hB
  exact ((hB.pow 2).div_const 2).sub hW

end SerrinEpigraph
