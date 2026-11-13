module

public import SerrinEpigraph.AnnularContactDerivative
public import SerrinEpigraph.InwardTangent
public import SerrinEpigraph.BallSlopeComparison

/-!
# Neumann slope upper bounds from exterior annuli
-/

public section

open Set Metric

namespace SerrinEpigraph

/-- Exterior contact with an annular upper solution bounds the Neumann constant. -/
theorem IncreasingRadialSegment.kappa_le_inner_slope
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1)
    {c : Space (m + 1)} {y : Space m}
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ)
    (hs : point y (g y) ∈ sphere c a) : κ ≤ v.slope a :=
  v.kappa_le_inner_slope_of_normal_mem h hr hb hball hs
    (neg_outwardNormal_mem_posTangentConeAt (h.graph_contDiff.differentiable_one y))

/-- Every increasing annular profile reaching one gives a global Neumann upper bound. -/
theorem IncreasingRadialSegment.kappa_le_inner_slope_global
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) (hb : v.value b = 1) : κ ≤ v.slope a := by
  obtain ⟨t, z, hball, hz, hd⟩ :=
    epigraph_exists_exterior_tangent_ball h.graph_contDiff.continuous v.inner_pos
  have hzgraph : g (horizontal z) = z (Fin.last m) := by
    simpa only [frontier_epigraph h.graph_contDiff.continuous, mem_ofPred_eq] using hz
  have he : point (horizontal z) (g (horizontal z)) = z := by
    rw [hzgraph, point_horizontal_last]
  apply v.kappa_le_inner_slope h hr hb hball (y := horizontal z)
  rw [he]
  exact hd

/-- The exterior annular comparisons give the upper Neumann energy bound. -/
theorem RigidityHypotheses.kappa_sq_le_twice_potential
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    κ ^ 2 ≤ 2 * normalizedPotential f 0 := by
  by_contra hn
  have hW : 0 ≤ 2 * normalizedPotential f 0 :=
    mul_nonneg (by norm_num) (hr.normalizedPotential_nonneg h (by simp))
  have hs := Real.sq_sqrt hW
  have hs0 := Real.sqrt_nonneg (2 * normalizedPotential f 0)
  have hlt : Real.sqrt (2 * normalizedPotential f 0) < κ := by
    nlinarith [h.kappa_pos]
  obtain ⟨p, hsp, hpk⟩ := exists_between hlt
  have hp : 0 < p := hs0.trans_lt hsp
  have he : 2 * normalizedPotential f 0 < p ^ 2 := by nlinarith
  obtain ⟨A, _, hA⟩ := hr.exists_increasing_annular_profile h hp he
  obtain ⟨b, v, hv, hb, _⟩ := hA A le_rfl
  have hk := v.kappa_le_inner_slope_global h hr hb
  rw [hv] at hk
  exact (not_le_of_gt hpk) hk

/-- Interior balls and exterior annuli identify the boundary Neumann energy exactly. -/
theorem RigidityHypotheses.kappa_sq_eq_twice_potential
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    κ ^ 2 = 2 * normalizedPotential f 0 :=
  le_antisymm (hr.kappa_sq_le_twice_potential h) (hr.kappa_sq_ge_twice_potential h)

end SerrinEpigraph
