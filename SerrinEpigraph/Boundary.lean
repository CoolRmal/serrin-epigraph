module

public import SerrinEpigraph.Geometry

/-!
# Differential traces on the graph boundary
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ}

/-- Assemble horizontal and vertical components as a continuous linear map. -/
def pointContinuousLinearMap : Space m × ℝ →L[ℝ] Space (m + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ point p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]
      map_smul' := by
        intro c p
        ext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point] }

@[simp]
theorem pointContinuousLinearMap_apply (p : Space m × ℝ) :
    pointContinuousLinearMap p = point p.1 p.2 := rfl

theorem point_add_vertical (y : Space m) (s t : ℝ) :
    point y s + t • verticalDirection m = point y (s + t) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point, verticalDirection]

private theorem hasFDerivAt_graph {g : Space m → ℝ} {y : Space m}
    (hg : DifferentiableAt ℝ g y) :
    HasFDerivAt (fun z ↦ point z (g z))
      (pointContinuousLinearMap.comp ((ContinuousLinearMap.id ℝ (Space m)).prod (fderiv ℝ g y)))
      y := by
  exact pointContinuousLinearMap.hasFDerivAt.comp y
    ((hasFDerivAt_id y).prodMk hg.hasFDerivAt)

/-- The differential of a zero Dirichlet trace annihilates every graph tangent vector. -/
theorem fderivWithin_point_tangent_eq_zero {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {y : Space m} (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableWithinAt ℝ u (closure (epigraph g)) (point y (g y)))
    (hdir : ∀ z, u (point z (g z)) = 0) (v : Space m) :
    fderivWithin ℝ u (closure (epigraph g)) (point y (g y))
      (point v (fderiv ℝ g y v)) = 0 := by
  have hd := hu.hasFDerivWithinAt.comp_hasFDerivAt y (hasFDerivAt_graph hg)
    (Filter.Eventually.of_forall (fun z ↦ point_mem_closure_epigraph (le_refl (g z))))
  have heq : u ∘ (fun z ↦ point z (g z)) = fun _ ↦ 0 := funext hdir
  rw [heq] at hd
  have hzero := hd.unique (hasFDerivAt_const (0 : ℝ) y)
  simpa using congrArg (fun L : Space m →L[ℝ] ℝ ↦ L v) hzero

private theorem normal_derivative_eq {g : Space m → ℝ} {y : Space m}
    (L : Space (m + 1) →L[ℝ] ℝ)
    (htan : L (point (gradient g y) (fderiv ℝ g y (gradient g y))) = 0) :
    L (outwardNormal g y) =
      -Real.sqrt (1 + ‖gradient g y‖ ^ 2) * L (verticalDirection m) := by
  have hsq : 0 < 1 + ‖gradient g y‖ ^ 2 := by positivity
  have hgrad : fderiv ℝ g y (gradient g y) = ‖gradient g y‖ ^ 2 := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
  have hp := point_add_vertical (gradient g y) (fderiv ℝ g y (gradient g y))
    (-1 - fderiv ℝ g y (gradient g y))
  have hval := congrArg L hp
  simp only [map_add, map_smul, smul_eq_mul, htan, zero_add] at hval
  have hcancel : fderiv ℝ g y (gradient g y) + (-1 - fderiv ℝ g y (gradient g y)) = -1 := by
    ring
  rw [hcancel] at hval
  rw [outwardNormal, map_smul, smul_eq_mul, ← hval, hgrad]
  have hsqrt := Real.sq_sqrt hsq.le
  have hne := ne_of_gt (Real.sqrt_pos.2 hsq)
  field_simp
  rw [hsqrt]
  ring

/-- The positive vertical trace forced by the constant negative outward normal derivative. -/
theorem boundary_vertical_derivative_eq {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {κ : ℝ} {y : Space m} (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableWithinAt ℝ u (closure (epigraph g)) (point y (g y)))
    (hdir : ∀ z, u (point z (g z)) = 0)
    (hneu : fderivWithin ℝ u (closure (epigraph g)) (point y (g y))
      (outwardNormal g y) = -κ) :
    fderivWithin ℝ u (closure (epigraph g)) (point y (g y)) (verticalDirection m) =
      κ / Real.sqrt (1 + ‖gradient g y‖ ^ 2) := by
  have hn := normal_derivative_eq
    (fderivWithin ℝ u (closure (epigraph g)) (point y (g y)))
    (fderivWithin_point_tangent_eq_zero hg hu hdir (gradient g y))
  have hpos : 0 < Real.sqrt (1 + ‖gradient g y‖ ^ 2) := by positivity
  apply (eq_div_iff hpos.ne').2
  rw [hneu] at hn
  nlinarith

/-- Positive Neumann data give a strictly positive vertical differential on the boundary. -/
theorem boundary_vertical_derivative_pos {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {κ : ℝ} {y : Space m} (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableWithinAt ℝ u (closure (epigraph g)) (point y (g y)))
    (hdir : ∀ z, u (point z (g z)) = 0)
    (hneu : fderivWithin ℝ u (closure (epigraph g)) (point y (g y))
      (outwardNormal g y) = -κ) (hκ : 0 < κ) :
    0 < fderivWithin ℝ u (closure (epigraph g)) (point y (g y)) (verticalDirection m) := by
  rw [boundary_vertical_derivative_eq hg hu hdir hneu]
  exact div_pos hκ (by positivity)

/-- The vertical differential within the closed epigraph is continuous up to the boundary. -/
theorem continuousOn_verticalDifferential_closure {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} (hg : Differentiable ℝ g)
    (hu : ContDiffOn ℝ 1 u (closure (epigraph g))) :
    ContinuousOn
      (fun x ↦ fderivWithin ℝ u (closure (epigraph g)) x (verticalDirection m))
      (closure (epigraph g)) := by
  exact (hu.continuousOn_fderivWithin (uniqueDiffOn_closure_epigraph hg) le_rfl).clm_apply
    continuousOn_const

/-- Within-closure and ambient differentials agree at interior points. -/
theorem fderivWithin_closure_eq_fderiv {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    (hg : Continuous g) {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    fderivWithin ℝ u (closure (epigraph g)) x = fderiv ℝ u x := by
  exact fderivWithin_of_mem_nhds
    (Filter.mem_of_superset ((isOpen_epigraph hg).mem_nhds hx) subset_closure)

/-- Every graph point has a neighborhood where the interior vertical derivative is positive. -/
theorem exists_ball_verticalDerivative_pos {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ) (y : Space m) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ epigraph g ∩ Metric.ball (point y (g y)) ε,
      0 < verticalDerivative u x := by
  have hg := h.graph_contDiff.differentiable_one
  have hy := point_mem_closure_epigraph (le_refl (g y))
  have hpos := boundary_vertical_derivative_pos (hg y)
    (h.solution_contDiffOn_closure.differentiableOn_one _ hy) h.dirichlet (h.neumann y) h.kappa_pos
  have hc := continuousOn_verticalDifferential_closure hg h.solution_contDiffOn_closure _ hy
  have hev : ∀ᶠ x in 𝓝[closure (epigraph g)] (point y (g y)),
      0 < fderivWithin ℝ u (closure (epigraph g)) x (verticalDirection m) :=
    hc (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨ε, hε, fun x hx ↦ ?_⟩
  have hxpos := hball hx.2 (subset_closure hx.1)
  simpa only [fderivWithin_closure_eq_fderiv hg.continuous hx.1, verticalDerivative] using hxpos

end SerrinEpigraph
