module

public import SerrinEpigraph.TangentBallComparison
public import SerrinEpigraph.BoundaryGradient
public import SerrinEpigraph.TangentBalls
public import SerrinEpigraph.RadialBoundaryEnergy
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Boundary slope comparison for interior tangent balls
-/

public section

open Set Metric InnerProductSpace

namespace SerrinEpigraph

/-- Comparison with a radial ball solution bounds its boundary slope by the prescribed
Neumann magnitude at any common boundary point. -/
theorem RadialBallProfile.neg_boundary_slope_le_kappa
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R : ℝ}
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) {c : Space (m + 1)} {y : Space m}
    (hball : closedBall c R ⊆ closure (epigraph g))
    (hs : point y (g y) ∈ sphere c R) : -v.slope R ≤ κ := by
  let x := point y (g y)
  let L := fderivWithin ℝ u (closure (epigraph g)) x
  have hx : x ∈ closedBall c R := sphere_subset_closedBall hs
  have hu := (h.solution_contDiffOn_closure.differentiableOn_one x
    (hball hx)).hasFDerivWithinAt.mono hball
  have hv := v.spatial_hasFDerivWithinAt_boundary hs
  have hmin : IsMinOn (fun z ↦ u z - v.spatial c z) (closedBall c R) x := by
    intro z hz
    change u x - v.spatial c x ≤ u z - v.spatial c z
    rw [show u x = 0 from h.dirichlet y, v.spatial_boundary_zero hs]
    have hh := v.spatial_le_solution_of_closedBall_subset_closure h hr hball z hz
    linarith
  have hcone : c - x ∈ posTangentConeAt (closedBall c R) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall c R).segment_subset hx (mem_closedBall_self v.radius_pos.le))
  have hd := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg (hu.sub hv) hcone
  have hnorm : ‖x - c‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hs
  have hrad : inner ℝ (x - c) (c - x) = -R ^ 2 := by
    rw [show c - x = -(x - c) by abel, inner_neg_right, real_inner_self_eq_norm_sq, hnorm]
  have hd' : 0 ≤ L (c - x) + v.slope R * R := by
    change 0 ≤ L (c - x) - (v.slope R / R) * inner ℝ (x - c) (c - x) at hd
    rw [hrad] at hd
    have he : v.slope R / R * (-R ^ 2) = -v.slope R * R := by
      field_simp [v.radius_pos.ne']
    rw [he] at hd
    linarith
  have hupper : L (c - x) ≤ κ * R := by
    rw [show L (c - x) = inner ℝ (gradientWithin u (closure (epigraph g)) x) (c - x)
      from inner_gradientWithin_left.symm]
    have hb := real_inner_le_norm (gradientWithin u (closure (epigraph g)) x) (c - x)
    have hnorm' : ‖c - x‖ = R := by rw [norm_sub_rev]; exact hnorm
    simpa only [x, h.norm_boundary_gradient y, hnorm'] using hb
  nlinarith [v.radius_pos]

/-- Every radial ball profile has boundary slope bounded by the epigraph Neumann magnitude. -/
theorem RadialBallProfile.neg_boundary_slope_le_kappa_global
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R : ℝ}
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) : -v.slope R ≤ κ := by
  obtain ⟨t, z, hb, hz, hd⟩ :=
    epigraph_exists_interior_tangent_ball h.graph_contDiff.continuous v.radius_pos
  have hcb : closedBall (point (0 : Space m) t) R ⊆ closure (epigraph g) := by
    rw [← closure_ball _ v.radius_pos.ne']
    exact closure_mono hb
  have hzgraph : g (horizontal z) = z (Fin.last m) := by
    simpa only [frontier_epigraph h.graph_contDiff.continuous, mem_ofPred_eq] using hz
  have he : point (horizontal z) (g (horizontal z)) = z := by
    rw [hzgraph, point_horizontal_last]
  apply v.neg_boundary_slope_le_kappa h hr hcb (y := horizontal z)
  rw [he]
  exact hd

/-- The prescribed Neumann energy is at least the normalized potential drop. -/
theorem RigidityHypotheses.kappa_sq_ge_twice_potential
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    2 * normalizedPotential f 0 ≤ κ ^ 2 := by
  by_contra hn
  have hgap : 0 < normalizedPotential f 0 - κ ^ 2 / 2 := by linarith
  obtain ⟨R, v, _, _, hdef⟩ := hr.exists_large_radialBallProfile h hgap 0
  have hs := v.neg_boundary_slope_le_kappa_global h hr
  have hsneg := v.boundary_slope_neg hr h
  have hsq : v.slope R ^ 2 ≤ κ ^ 2 := by
    nlinarith [h.kappa_pos]
  linarith

end SerrinEpigraph
