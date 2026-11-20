module

public import SerrinEpigraph.DiffuseStressEstimates

/-!
# Membership in the coordinate cubes of `DiffuseStressEstimates`

`SerrinEpigraph.DiffuseStressEstimates` states the stable-well exponential tail
(`RigidityHypotheses.rescaled_stable_well_exponential_tail`, FE3) on the coordinate cubes
`openCoordCube` and `closedCoordCube`. This module records their membership
characterizations for downstream applications of FE3.
-/

@[expose] public section

namespace SerrinEpigraph

theorem mem_closedCoordCube_iff {d : ℕ} {x₀ x : Space d} {L : ℝ} :
    x ∈ closedCoordCube x₀ L ↔ ∀ i : Fin d, |(x - x₀) i| ≤ L :=
  Iff.rfl

theorem mem_openCoordCube_iff {d : ℕ} {x₀ x : Space d} {L : ℝ} :
    x ∈ openCoordCube x₀ L ↔ ∀ i : Fin d, |(x - x₀) i| < L :=
  Iff.rfl

end SerrinEpigraph
