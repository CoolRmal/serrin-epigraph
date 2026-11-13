module

public import SerrinEpigraph.ScaledComparison
public import SerrinEpigraph.RadialBoundaryDerivative

/-!
# Nonlinear comparison on a relatively compact domain
-/

public section

open MeasureTheory InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

include μ in
/-- Boundary ordering propagates inside a compact connected domain when the upper solution
is strictly positive on its closure and the reaction quotient is nonincreasing. -/
theorem nonlinear_comparison_of_compact_closure {Ω : Set E} {u v : E → ℝ} {f : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hc : IsCompact (closure Ω))
    (hboundary : (closure Ω \ Ω).Nonempty)
    (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    (hueq : ∀ x ∈ Ω, -(Δ u) x = f (u x))
    (hveq : ∀ x ∈ Ω, -(Δ v) x = f (v x))
    (hu0 : ∀ x ∈ closure Ω, 0 < u x) (hv0 : ∀ x ∈ Ω, 0 ≤ v x)
    (hbd : ∀ x ∈ closure Ω \ Ω, v x ≤ u x) :
    ∀ x ∈ closure Ω, v x ≤ u x := by
  obtain ⟨z, hz⟩ := hboundary
  have hratio : ContinuousOn (fun x ↦ v x / u x) (closure Ω) :=
    hvc.div huc (fun x hx ↦ (hu0 x hx).ne')
  obtain ⟨a, ha, hmax⟩ := hc.exists_isMaxOn ⟨z, hz.1⟩ hratio
  let t := v a / u a
  have horder : ∀ x ∈ closure Ω, v x ≤ t * u x := by
    intro x hx
    exact (div_le_iff₀ (hu0 x hx)).mp (hmax hx)
  by_cases ht : t ≤ 1
  · intro x hx
    exact (horder x hx).trans (by nlinarith [hu0 x hx])
  have ht' : 1 < t := lt_of_not_ge ht
  have haΩ : a ∈ Ω := by
    by_contra hnot
    have hb := hbd a ⟨ha, hnot⟩
    have htone : t ≤ 1 := (div_le_one (hu0 a ha)).mpr hb
    exact ht htone
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (continuousOn_const.mul huc :
    ContinuousOn (fun x ↦ t * u x) (closure Ω))
  have heq : Set.EqOn v (fun x ↦ t * u x) Ω :=
    scaled_solution_eq_of_contact (μ := μ) hΩ hconn hu hv hf hstructure hueq hveq
      ht'.le (fun x hx ↦ hu0 x (subset_closure hx)) hv0
      (fun x hx ↦ horder x (subset_closure hx))
      (fun x hx ↦ (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, Pi.mul_apply] using hB x (subset_closure hx))) haΩ
      (by dsimp [t]; field_simp [(hu0 a ha).ne'])
  have heqc : Set.EqOn v (fun x ↦ t * u x) (closure Ω) :=
    heq.of_subset_closure hvc (continuousOn_const.mul huc) subset_closure Set.Subset.rfl
  have hzval := heqc hz.1
  have hzbd := hbd z hz
  have hzpos := hu0 z hz.1
  exfalso
  nlinarith

/-- A radial Dirichlet ball solution lies below the positive epigraph solution whenever
the entire closed ball is contained in the epigraph. -/
theorem RadialBallProfile.spatial_le_solution {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R : ℝ}
    (v : RadialBallProfile f m R) (h : Hypotheses g u f κ)
    (hr : RigidityHypotheses g u f) {c : Space (m + 1)}
    (hball : Metric.closedBall c R ⊆ epigraph g) :
    ∀ x ∈ Metric.closedBall c R, v.spatial c x ≤ u x := by
  have hcl := closure_ball c v.radius_pos.ne'
  have hsub : Metric.ball c R ⊆ epigraph g := Metric.ball_subset_closedBall.trans hball
  have hboundary : (closure (Metric.ball c R) \ Metric.ball c R).Nonempty := by
    rw [hcl, Metric.closedBall_sdiff_ball]
    exact NormedSpace.sphere_nonempty.mpr v.radius_pos.le
  have huc : ContinuousOn u (closure (Metric.ball c R)) := by
    rw [hcl]
    exact h.solution_contDiffOn.continuousOn.mono hball
  have hvc : ContinuousOn (v.spatial c) (closure (Metric.ball c R)) := by
    rw [hcl]
    exact v.spatial_continuousOn c
  have hcomp := nonlinear_comparison_of_compact_closure (μ := volume)
    Metric.isOpen_ball (convex_ball c R).isPreconnected
    (hcl ▸ isCompact_closedBall c R) hboundary
    (h.solution_contDiffOn.mono hsub) (v.spatial_contDiffOn_two h c) huc hvc
    h.reaction_contDiffOn h.reaction_structure
    (fun x hx ↦ h.equation x (hsub hx)) (fun x hx ↦ v.spatial_equation h hx)
    (fun x hx ↦ h.positive x (hball (hcl ▸ hx)))
    (fun x hx ↦ (v.spatial_pos hr h hx).le) ?_
  · simpa only [hcl] using hcomp
  · intro x hx
    have hs : x ∈ Metric.sphere c R := by
      rwa [hcl, Metric.closedBall_sdiff_ball] at hx
    rw [v.spatial_boundary_zero hs]
    exact (h.positive x (hball (Metric.sphere_subset_closedBall hs))).le

end SerrinEpigraph
