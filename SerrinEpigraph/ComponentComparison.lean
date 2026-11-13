module

public import SerrinEpigraph.CompactComparison
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Nonlinear comparison without a connectedness assumption
-/

public section

open Set MeasureTheory InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

/-- A boundary point of a component of an open set cannot lie in the open set. -/
theorem component_boundary_subset {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) :
    closure (connectedComponentIn Ω x) \ connectedComponentIn Ω x ⊆ closure Ω \ Ω := by
  intro z hz
  refine ⟨closure_mono (connectedComponentIn_subset Ω x) hz.1, ?_⟩
  intro hzΩ
  have hzC := mem_connectedComponentIn hzΩ
  obtain ⟨y, hyz, hyx⟩ := mem_closure_iff.mp hz.1 (connectedComponentIn Ω z)
    hΩ.connectedComponentIn hzC
  have he : connectedComponentIn Ω x = connectedComponentIn Ω z :=
    (connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hyz).symm
  exact hz.2 (he ▸ hzC)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

include μ in
/-- Compact-domain nonlinear comparison holds component by component on any proper open set. -/
theorem nonlinear_comparison_on_proper_open {Ω : Set E} {u v : E → ℝ} {f : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hproper : Ω ≠ univ) (hc : IsCompact (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hf : ContDiffOn ℝ 1 f (Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    (hueq : ∀ x ∈ Ω, -(Δ u) x = f (u x))
    (hveq : ∀ x ∈ Ω, -(Δ v) x = f (v x))
    (hu0 : ∀ x ∈ closure Ω, 0 < u x) (hv0 : ∀ x ∈ Ω, 0 ≤ v x)
    (hbd : ∀ x ∈ closure Ω \ Ω, v x ≤ u x) :
    ∀ x ∈ closure Ω, v x ≤ u x := by
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · let C := connectedComponentIn Ω x
    have hC : IsOpen C := hΩ.connectedComponentIn
    have hsub : C ⊆ Ω := connectedComponentIn_subset Ω x
    have hcl : closure C ⊆ closure Ω := closure_mono hsub
    have hxC : x ∈ C := mem_connectedComponentIn hxΩ
    have hCproper : C ≠ univ := by
      intro he
      apply hproper
      exact univ_subset_iff.mp (he ▸ hsub)
    have hfront : (closure C \ C).Nonempty := by
      have hh := nonempty_frontier_iff.mpr ⟨⟨x, hxC⟩, hCproper⟩
      simpa only [frontier, hC.interior_eq] using hh
    have hcomp := nonlinear_comparison_of_compact_closure (μ := μ) hC
      isPreconnected_connectedComponentIn (hc.of_isClosed_subset isClosed_closure hcl) hfront
      (hu.mono hsub) (hv.mono hsub) (huc.mono hcl) (hvc.mono hcl) hf hstructure
      (fun y hy ↦ hueq y (hsub hy)) (fun y hy ↦ hveq y (hsub hy))
      (fun y hy ↦ hu0 y (hcl hy)) (fun y hy ↦ hv0 y (hsub hy))
      (fun y hy ↦ hbd y (component_boundary_subset hΩ x hy))
    exact hcomp x (subset_closure hxC)
  · exact hbd x ⟨hx, hxΩ⟩

end SerrinEpigraph
