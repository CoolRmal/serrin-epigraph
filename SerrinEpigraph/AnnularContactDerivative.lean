module

public import SerrinEpigraph.TangentAnnularComparison
public import SerrinEpigraph.BoundaryGradient
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Directional derivative comparison at exterior contact
-/

public section

open Set Metric InnerProductSpace
open scoped NNReal

namespace SerrinEpigraph

/-- At an exterior contact point, every inward tangent direction satisfies the
directional derivative inequality supplied by the annular upper solution. -/
theorem IncreasingRadialSegment.boundary_directional_derivative_le
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1)
    {c : Space (m + 1)} {y : Space m}
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ)
    (hs : point y (g y) ∈ sphere c a) {w : Space (m + 1)}
    (hw : w ∈ posTangentConeAt (closure (epigraph g)) (point y (g y))) :
    fderivWithin ℝ u (closure (epigraph g)) (point y (g y)) w ≤
      (v.slope a / a) * inner ℝ (point y (g y) - c) w := by
  let x := point y (g y)
  let D := closure (epigraph g) ∩ ball c b
  have hxΩ : x ∈ closure (epigraph g) := point_mem_closure_epigraph le_rfl
  have hxB : x ∈ ball c b := by
    change dist x c < b
    exact (show dist x c = a from hs) ▸ v.radii_lt
  have hDA : D ⊆ closedRadialAnnulus c a b := by
    intro z hz
    have hlow : a ≤ dist z c := le_of_not_gt (fun hlt ↦ hball hlt hz.1)
    exact ⟨by simpa only [dist_eq_norm] using hlow,
      by simpa only [mem_ball, dist_eq_norm] using hz.2.le⟩
  have hu := (h.solution_contDiffOn_closure.differentiableOn_one x hxΩ).hasFDerivWithinAt.mono
    (show D ⊆ closure (epigraph g) from inter_subset_left)
  have hv := (v.spatial_hasFDerivWithinAt_inner hs).mono hDA
  have hmin : IsMinOn (fun z ↦ v.spatial c z - u z) D x := by
    intro z hz
    change v.spatial c x - u x ≤ v.spatial c z - u z
    rw [v.spatial_inner_zero hs, show u x = 0 from h.dirichlet y]
    have hcomp := v.solution_le_spatial_of_exterior_ball h hr hb hball z
      (isOpen_ball.closure_inter hz)
    linarith
  have hcone : w ∈ posTangentConeAt D x := by
    change w ∈ tangentConeAt ℝ≥0 (closure (epigraph g) ∩ ball c b) x
    rw [tangentConeAt_inter_nhds (isOpen_ball.mem_nhds hxB)]
    exact hw
  have hd := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg (hv.sub hu) hcone
  change 0 ≤ (v.slope a / a) * inner ℝ (x - c) w -
    fderivWithin ℝ u (closure (epigraph g)) x w at hd
  exact sub_nonneg.mp hd

/-- The inward unit normal direction gives the Neumann upper bound once its
membership in the closed-domain positive tangent cone is supplied. -/
theorem IncreasingRadialSegment.kappa_le_inner_slope_of_normal_mem
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1)
    {c : Space (m + 1)} {y : Space m}
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ)
    (hs : point y (g y) ∈ sphere c a)
    (hn : -outwardNormal g y ∈
      posTangentConeAt (closure (epigraph g)) (point y (g y))) : κ ≤ v.slope a := by
  have hd := v.boundary_directional_derivative_le h hr hb hball hs hn
  rw [map_neg, h.neumann y, neg_neg] at hd
  have hnorm : ‖point y (g y) - c‖ = a := by
    simpa only [mem_sphere, dist_eq_norm] using hs
  have hi := real_inner_le_norm (point y (g y) - c) (-outwardNormal g y)
  rw [hnorm, norm_neg, norm_outwardNormal, mul_one] at hi
  have hp := v.slope_nonneg a ⟨le_rfl, v.radii_lt.le⟩
  have hh := mul_le_mul_of_nonneg_left hi (div_nonneg hp v.inner_pos.le)
  have he : v.slope a / a * a = v.slope a := div_mul_cancel₀ _ v.inner_pos.ne'
  rw [he] at hh
  exact hd.trans hh

end SerrinEpigraph
