module

public import SerrinEpigraph.ZeroExtension
public import SerrinEpigraph.FoliationPullback
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Local Lipschitz regularity of the zero extension
-/

public section

noncomputable section

open InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Coordinates measuring height above the graph. -/
@[expose] def flattenedCoordinates (g : Space m → ℝ) (x : Space (m + 1)) : Space m × ℝ :=
  (horizontal x, x (Fin.last m) - g (horizontal x))

/-- Convert height above the graph back to an ambient point. -/
@[expose] def graphPoint (g : Space m → ℝ) (p : Space m × ℝ) : Space (m + 1) :=
  point p.1 (g p.1 + p.2)

/-- Graph coordinates are continuously differentiable for a C¹ graph. -/
theorem contDiff_flattenedCoordinates (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (flattenedCoordinates g) := by
  have hh : ContDiff ℝ 1 (horizontal : Space (m + 1) → Space m) :=
    horizontalContinuousLinearMap.contDiff
  have hl : ContDiff ℝ 1 (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (show Space (m + 1) →L[ℝ] ℝ from
      PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).contDiff
  exact hh.prodMk (hl.sub (hg.comp hh))

/-- The inverse graph coordinates are continuously differentiable. -/
theorem contDiff_graphPoint (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (graphPoint g) :=
  pointContinuousLinearMap.contDiff.comp
    (contDiff_fst.prodMk ((hg.comp contDiff_fst).add contDiff_snd))

/-- Flattening transfers the C¹ solution on the closed epigraph to a convex half-space. -/
theorem Hypotheses.contDiffOn_flattenedSolution (h : Hypotheses g u f κ) :
    ContDiffOn ℝ 1 (u ∘ graphPoint g) (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
  apply h.solution_contDiffOn_closure.comp (contDiff_graphPoint h.graph_contDiff).contDiffOn
  intro p hp
  exact point_mem_closure_epigraph (le_add_of_nonneg_right hp.2)

private def clampHalfSpace (p : Space m × ℝ) :
    (Set.univ ×ˢ Set.Ici (0 : ℝ) : Set (Space m × ℝ)) :=
  ⟨(p.1, max p.2 0), Set.mem_univ _, le_max_right _ _⟩

private theorem lipschitz_clampHalfSpace : LipschitzWith 1 (clampHalfSpace (m := m)) := by
  have hl : LipschitzWith (max 1 1) (fun p : Space m × ℝ ↦ (p.1, max p.2 0)) :=
    LipschitzWith.prod_fst.prodMk (LipschitzWith.prod_snd.max_const (0 : ℝ))
  change LipschitzWith 1 (fun p : Space m × ℝ ↦
    (⟨(p.1, max p.2 0), ⟨Set.mem_univ _, le_max_right _ _⟩⟩ :
      (Set.univ ×ˢ Set.Ici (0 : ℝ) : Set (Space m × ℝ))))
  simpa only [max_self] using hl.subtype_mk
    (p := fun z : Space m × ℝ ↦ z ∈ Set.univ ×ˢ Set.Ici (0 : ℝ))
    (fun p ↦ ⟨Set.mem_univ _, le_max_right p.2 0⟩)

/-- Clamping the flattened vertical coordinate gives precisely the zero extension. -/
theorem Hypotheses.zeroExtension_eq_clamped (h : Hypotheses g u f κ) (x : Space (m + 1)) :
    zeroExtension g u x =
      u (point (horizontal x) (g (horizontal x) + max (x (Fin.last m) - g (horizontal x)) 0)) := by
  by_cases hx : x ∈ epigraph g
  · have hp : 0 ≤ x (Fin.last m) - g (horizontal x) := sub_nonneg.mpr (le_of_lt hx)
    rw [max_eq_left hp, add_sub_cancel, point_horizontal_last, zeroExtension_of_mem hx]
  · have hp : x (Fin.last m) - g (horizontal x) ≤ 0 := sub_nonpos.mpr (le_of_not_gt hx)
    rw [max_eq_right hp, add_zero, h.dirichlet, zeroExtension_of_notMem hx]

/-- The whole-space zero extension is locally Lipschitz, including across the boundary. -/
theorem Hypotheses.zeroExtension_locallyLipschitz (h : Hypotheses g u f κ) :
    LocallyLipschitz (zeroExtension g u) := by
  have hf := h.contDiffOn_flattenedSolution.locallyLipschitzOn
    ((convex_univ : Convex ℝ (Set.univ : Set (Space m))).prod (convex_Ici (0 : ℝ)))
  have hc := hf.restrict.comp lipschitz_clampHalfSpace.locallyLipschitz
  have hg := hc.comp (contDiff_flattenedCoordinates h.graph_contDiff).locallyLipschitz
  have he : (((Set.univ ×ˢ Set.Ici (0 : ℝ)).domRestrict (u ∘ graphPoint g)) ∘
      clampHalfSpace) ∘ flattenedCoordinates g = zeroExtension g u := by
    funext x
    exact (h.zeroExtension_eq_clamped x).symm
  rwa [he] at hg

/-- On each compact set the zero extension has a finite Lipschitz constant. -/
theorem Hypotheses.zeroExtension_lipschitzOn_compact (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ C : NNReal, LipschitzOnWith C (zeroExtension g u) K :=
  h.zeroExtension_locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK

end SerrinEpigraph
