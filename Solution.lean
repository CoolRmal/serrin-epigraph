module

public import SerrinEpigraph

/-!
# Proof-development entry point

This module imports the complete development. All three Comparator targets,
`SerrinEpigraph.verticalDerivative_pos`, `SerrinEpigraph.rigidity_of_dimension_le_eight` and
`SerrinEpigraph.rigidity_of_oneSidedLinearBound`, are proved and depend only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
This module never imports the independent specification in `Challenge`.
-/
