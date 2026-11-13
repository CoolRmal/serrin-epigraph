module

public import SerrinEpigraph.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Consequences of the reaction structure condition
-/

public section

namespace SerrinEpigraph

/-- The structural condition makes the reaction divided by its argument nonincreasing. -/
theorem antitoneOn_reaction_div {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s) :
    AntitoneOn (fun s ↦ f s / s) (Set.Ioi 0) := by
  have hd : ∀ s ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f s := by
    intro s hs
    exact (hf.differentiableOn_one s hs.le).differentiableAt (Ici_mem_nhds hs)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
  · exact fun s hs ↦ ((hd s hs).continuousAt.div continuousAt_id hs.ne').continuousWithinAt
  · intro s hs
    exact ((hd s (by simpa using hs)).div differentiableAt_id
      (by simpa using (show (0 : ℝ) < s from by simpa using hs).ne')).differentiableWithinAt
  · intro s hs
    have hs' : 0 < s := by simpa using hs
    have hderiv := (hd s hs').hasDerivAt.div (hasDerivAt_id s) hs'.ne'
    have heq : deriv (fun t ↦ f t / t) s = (deriv f s * s - f s) / s ^ 2 := by
      simpa only [Pi.div_def, id_eq, mul_one] using hderiv.deriv
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hstructure s hs']) (sq_nonneg s)

end SerrinEpigraph
