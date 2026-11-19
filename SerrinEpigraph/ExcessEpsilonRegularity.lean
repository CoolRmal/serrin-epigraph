module

public import SerrinEpigraph.TiltExcessDecay
public import SerrinEpigraph.RegularBoundary

/-!
# The excess form of ε-regularity

`ExcessEpsilonRegularityHyp` is the normalized De Giorgi ε-regularity statement: a flat
configuration (a local perimeter minimizer trapped in the unit slab over `B₂`, with the origin
on its boundary) whose cylindrical excess over `B₂` is small has only `C¹` regular boundary
points in the half cylinder. It is the interface between the excess-decay chain (GR9–GR13),
which proves it, and the blow-up arguments deriving `EpsilonRegularityHyp` and
`SingularSetUSCHyp` from it.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory

namespace SerrinEpigraph

/-- Normalized excess-form ε-regularity (blueprint GR13): small cylindrical excess of a flat
configuration forces every boundary point of the half cylinder to be `C¹` regular. -/
def ExcessEpsilonRegularityHyp : Prop :=
  ∀ m : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (E Ω : Set (Space (m + 1))) (μ : Measure (Space (m + 1)))
      (ν : Space (m + 1) → Space (m + 1)),
      IsFlatConfig (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω μ ν →
      (projectedExcessMeasure μ ν).real (ball 0 2) ≤ ε₀ →
      ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (1 / 2) →
        |x (Fin.last m)| < 1 / 2 → IsC1BoundaryPoint E x

end SerrinEpigraph
