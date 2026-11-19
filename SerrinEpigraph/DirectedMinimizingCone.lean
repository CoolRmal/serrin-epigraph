module

public import SerrinEpigraph.LocalPerimeterMinimizer

/-!
# Directed minimizing cones and half-spaces

Basic vocabulary shared by the cone classification modules and the final reduction:
the directed (vertically monotone) minimizing cones produced by the blow-down analysis,
and the open half-space with a prescribed inner normal.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory InnerProductSpace

namespace SerrinEpigraph

/-- A nontrivial, conical, vertically monotone local perimeter minimizer in `Space (m + 1)`. -/
structure IsDirectedMinimizingCone {m : ℕ} (E : Set (Space (m + 1))) : Prop where
  measurableSet : MeasurableSet E
  nontrivial : volume E ≠ 0 ∧ volume Eᶜ ≠ 0
  dilation : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E
  vertical : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E
  minimizer : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E univ

/-- The open half-space with inner normal `e`. -/
def positiveHalfspace {d : ℕ} (e : Space d) : Set (Space d) := {x | 0 < inner ℝ e x}

end SerrinEpigraph
