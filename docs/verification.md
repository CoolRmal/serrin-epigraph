# Verification record

## Smooth weights for finite graph covers

The `SerrinEpigraph Challenge Solution` build passed (3909 jobs).
`GraphPartition.lean` constructs subordinate smooth nonnegative weights with
compact support and total weight one on the compact base. Diagnostics are clean;
the theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Weighted recovery energy estimates, perimeter identification, both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Finite buffered graph cover

The `SerrinEpigraph Challenge Solution` build passed (3908 jobs).
`FiniteGraphCover.lean` proves existence of a finite buffered cover retaining
the local area recovery bounds on every closed half-radius patch. Diagnostics
are clean and the cover theorem uses only the standard three axioms. Gluing
and overlap control, variational perimeter identification, both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Local graph-area recovery coefficient

The `SerrinEpigraph Challenge Solution` build passed (3907 jobs).
`GraphAreaDensity.lean` proves area-density continuity, local oscillation bounds,
and recovery energy bounded by the local area integral plus arbitrary small
base-volume error, times action. Diagnostics are clean and the local area-bound
theorem uses only the standard three axioms. Competitor patching and variational
perimeter identification, both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Local graph recovery bound

The `SerrinEpigraph Challenge Solution` build passed (3906 jobs).
`LocalRecoveryBound.lean` proves recovery energy estimates for C1 coordinates
whose gradient is controlled only on the integration region, and specializes
them to graph heights with local slope control. Diagnostics are clean and the
local graph theorem uses only the standard three axioms. Sharp perimeter
recovery, both Main rigidity proofs, full Comparator, and Palomar registration
remain incomplete.

## Assembled graph recovery bound

The `SerrinEpigraph Challenge Solution` build passed (3905 jobs).
`GraphRecoveryBound.lean` proves unit-Lipschitz normalized height for globally
controlled graph slopes, the Euclidean energy bound with projected-volume
coefficient, and compact-local L1 convergence to the epigraph indicator.
Diagnostics are clean and the energy theorem uses only the standard three
axioms. Sharp perimeter localization, both Main rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Euclidean coordinate-volume transfer

The `SerrinEpigraph Challenge Solution` build passed (3904 jobs).
`EuclideanProductVolume.lean` verifies the volume-preserving horizontal/vertical
split and the normalized graph-height measure bound for Euclidean subsets.
Diagnostics are clean and the measure-bound theorem uses only the standard
three axioms. Local recovery energy assembly and perimeter estimates, both
Main rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Euclidean graph-height gradient

The `SerrinEpigraph Challenge Solution` build passed (3903 jobs).
`GraphHeightGradient.lean` proves the graph-height differential, gradient,
exact squared norm, and unit-gradient bound after normalization. Diagnostics
are clean and the normalization theorem uses only the standard three axioms.
Chart measure transfer and sharp perimeter estimates, both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Normalized graph-height measure

The `SerrinEpigraph Challenge Solution` build passed (3902 jobs).
`NormalizedGraphMeasure.lean` proves the exact scaling of coordinate-measure
domination and the resulting normalized graph-layer integral bound. Diagnostics
are clean and the integral theorem uses only the standard three axioms.
Geometric gradient control and perimeter assembly, both Main rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## Vertical graph-layer measure

The `SerrinEpigraph Challenge Solution` build passed (3901 jobs).
`GraphLayerMeasure.lean` proves measure preservation under vertical graph
flattening, the exact height-distribution formula, and the vertical layer
integral bound. Diagnostics are clean and the integral theorem uses only the
standard three axioms. Gradient normalization and perimeter identification,
both Main rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Flat-cylinder layer measure

The `SerrinEpigraph Challenge Solution` build passed (3900 jobs).
`FlatLayerMeasure.lean` verifies the exact projected measure and layer mass
for flat cylinders, together with the upper bound on arbitrary subsets.
Diagnostics are clean and the subset integral theorem uses only the standard
three axioms. Curved-chart measure estimates and perimeter identification,
both Main rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Recovery bound from coordinate-measure domination

The `SerrinEpigraph Challenge Solution` build passed (3899 jobs).
`RecoveryMeasureBound.lean` proves the exact action upper bound under an
explicit domination hypothesis on the pushed-forward transition-layer volume.
Diagnostics are clean; the geometric energy theorem uses only the standard
three axioms. The domination hypothesis itself is not proved here. Geometric
recovery, both Main rigidity proofs, full Comparator, and Palomar registration
remain incomplete.

## Exact scaled layer mass

The `SerrinEpigraph Challenge Solution` build passed (3898 jobs).
`RecoveryLayerMass.lean` proves that the nonnegative, integrable supported
layer density has total mass exactly equal to the regularized action at
every positive scale. Diagnostics are clean and the mass theorem uses only
the standard three axioms. Geometric measure comparison, both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Distance recovery competitors

The `SerrinEpigraph Challenge Solution` build passed (3897 jobs).
`DistanceRecovery.lean` constructs competitors from distance to the complement,
proves global Lipschitz regularity and exterior zero values, identifies the
positive-distance set for proper open sets, and proves local L1 convergence
and the interior boundary-layer energy bound. Diagnostics are clean; the L1
theorem uses only the standard three axioms. Sharp geometric layer estimates,
both Main rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Localized recovery energy integral

The `SerrinEpigraph Challenge Solution` build passed (3896 jobs).
`RecoveryEnergyLocalization.lean` proves zero energy at both pure phases,
localization to the open transition layer, and the compact-set integral bound
for one-Lipschitz coordinates. Diagnostics are clean; the integral theorem's
transitive audit uses only the standard three axioms. The geometric perimeter
upper bound, both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Interior geometric recovery energy

The `SerrinEpigraph Challenge Solution` build passed (3895 jobs).
`GeometricRecoveryEnergy.lean` proves the interior derivative of the extended
profile, the spatial gradient formula, and the interior energy bound for
coordinates whose gradient norm is at most one. Diagnostics are clean and
the energy bound has only the standard three axioms. Exterior localization,
integrated geometric upper bounds, both Main rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Geometric recovery profile convergence

The `SerrinEpigraph Challenge Solution` build passed (3894 jobs).
`GeometricRecoveryProfile.lean` defines the pullback along a geometric
coordinate and proves range bounds, quantitative Lipschitz regularity,
and compact-local L1 convergence to the positive-coordinate indicator.
Diagnostics are clean; the L1 theorem has only the standard three axioms.
Geometric energy upper bounds, both Main rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Recovery thickness and phase convergence

The `SerrinEpigraph Challenge Solution` build passed (3893 jobs).
`RecoveryThickness.lean` proves the transition-time bound 1/√(2δ), vanishing
scaled thickness under the explicit scale condition, eventual equality to one
at positive distances, and pointwise convergence to the positive half-line
indicator. Diagnostics are clean and the convergence theorem uses only the
standard three axioms. Multidimensional recovery energy estimates, both Main
rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Recovery action limit

The `SerrinEpigraph Challenge Solution` build passed (3892 jobs).
`RecoveryActionBounds.lean` proves the pointwise action-density bounds, the
integrated error bound √(2δ), and convergence to `phasePrimitive f 1` for
positive regularizations tending to zero. Diagnostics are clean and the limit
theorem's transitive audit uses only the standard three axioms. Multidimensional
geometric recovery, both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Exact core transition action

The `SerrinEpigraph Challenge Solution` build passed (3891 jobs).
`RecoveryAction.lean` proves the exact phase-coordinate formula for the core
transition's kinetic-plus-potential integral. Diagnostics are clean and the
energy-integral theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
The regularization limit and geometric recovery upper bound remain unfinished;
both Main rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Global Lipschitz recovery profile

The `SerrinEpigraph Challenge Solution` build passed (3890 jobs).
`RecoveryProfileExtension.lean` proves a Lipschitz bound for the core through
the endpoints and for its constant-phase extension on the whole real line,
with normalized range and exact exterior values zero and one. Diagnostics are
clean and the global Lipschitz theorem has only the standard three axioms.
Total recovery action and the geometric upper bound remain unfinished. Both
Main rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Inverse profile regularity and energy identity

The `SerrinEpigraph Challenge Solution` build passed (3889 jobs).
`RecoveryProfileRegularity.lean` proves endpoint-inclusive continuity, strict
interior phase values, the inverse-profile derivative, and its regularized
energy density identity. Diagnostics are clean; the energy identity's
transitive audit uses only the standard three axioms. Constant extension and
total recovery action remain unfinished. Both Main rigidity proofs, full
Comparator, and Palomar registration remain incomplete.

## Inverse regularized recovery profile

The `SerrinEpigraph Challenge Solution` build passed (3888 jobs).
`RecoveryProfileCore.lean` defines the inverse travel-time profile and proves
its normalized range, inverse identities, endpoint values, and strict
monotonicity. Diagnostics are clean and the inverse monotonicity theorem uses
only the standard three axioms. Inverse regularity and recovery energy remain
unfinished, as do both Main rigidity proofs, full Comparator, and Palomar
registration.

## Regularized recovery travel time

The `SerrinEpigraph Challenge Solution` build passed (3887 jobs).
`RecoveryTravelTime.lean` defines the reciprocal-speed primitive for W+δ and
proves continuity, its interior derivative, strict monotonicity on [0,1], and
positive finite travel time to one. Diagnostics are clean; the monotonicity
theorem's transitive audit uses only the standard three axioms. The inverse
profile, recovery energy bound, and geometric use remain unfinished. Both Main
rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Perimeter bound from candidate-energy comparison

The `SerrinEpigraph Challenge Solution` build passed (3886 jobs).
`PerimeterComparison.lean` bounds the nonnegative energy liminf using a
convergent comparison sequence, then combines it with the exact perimeter
lower bound on smaller balls. Diagnostics are clean and the perimeter
comparison theorem has only the standard three axioms. This does not yet
prove perimeter minimality: a geometric recovery upper bound is still needed.
Both Main rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Reference inner-energy sequence comparison

The `SerrinEpigraph Challenge Solution` build passed (3885 jobs).
`InnerEnergyComparison.lean` proves a cutoff-free comparison of actual rescaled
reference inner energy with outer candidate energy plus a vanishing error,
under explicit annular input hypotheses. It also transfers candidate-energy
convergence to eventual reference-energy upper bounds. Diagnostics are clean;
the application theorem has only the standard three axioms. Recovery inputs,
perimeter minimality, and geometric classification remain unfinished. Both Main
rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Cancellation of reference annular energy

The `SerrinEpigraph Challenge Solution` build passed (3884 jobs).
`GluingEnergyCancellation.lean` proves the weighted integral bound, cancels
reference energy on the outer region, and applies rescaled minimality to give
an inner-ball/outer-ball energy comparison with the same gluing error.
Diagnostics are clean; the application theorem has only the standard three
axioms. Recovery construction and geometric classification remain open, as do
both Main rigidity proofs, full Comparator, and Palomar registration.

## Preservation of candidate limits

The `SerrinEpigraph Challenge Solution` build passed (3883 jobs).
`GluedLimit.lean` bounds the glued/candidate difference pointwise and in local
integral norm, then proves candidate-limit preservation from vanishing mismatch
outside the cutoff's inner region. Diagnostics are clean; the convergence
theorem's transitive audit contains only the standard three axioms. Recovery
construction and geometric classification remain unfinished, as do both Main
rigidity proofs, full Comparator, and Palomar registration.

## Annular gluing sequence with vanishing error

The `SerrinEpigraph Challenge Solution` build passed (3882 jobs).
`AnnularGluingSequence.lean` constructs a sequence of smooth cutoffs with an
integrated gluing comparison and an error tending to zero. Bounded energy and
common local L1 convergence are assumed only on the annulus. Diagnostics are
clean; the sequence theorem has only the standard three axioms. This remains
conditional on the input sequences, whose required recovery construction and
geometric use are unfinished. Both Main rigidity proofs, full Comparator, and
Palomar registration remain incomplete.

## Annular selection and integrated comparison

The `SerrinEpigraph Challenge Solution` build passed (3881 jobs).
`AnnularTransitionCost.lean` selects cutoffs from annular cost alone and applies
the result to the gluing majorant and integrated energy comparison. The proof
does not require common limits inside the inner ball. Diagnostics are clean
and the integrated annular comparison has only the standard three axioms.
Recovery competitors and geometric classification remain unfinished, as do
both Main rigidity proofs, full Comparator, and Palomar registration.

## Common-limit control of squared mismatch

The `SerrinEpigraph Challenge Solution` build passed (3880 jobs).
`GluingMismatchConvergence.lean` proves the normalized squared-difference
bound, its integral bound by errors to a common limit, convergence of squared
mismatch, and vanishing averaged gluing cost under common local L1 convergence
and bounded energy. Diagnostics and the final theorem's standard-axiom audit
are clean. Recovery construction and geometric classification remain open;
both Main rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Vanishing averaged gluing error

The `SerrinEpigraph Challenge Solution` build passed (3879 jobs).
`GluingScaleChoice.lean` proves the scale-comparable layer-count estimate,
chooses the natural ceiling of the scale, and proves vanishing of the averaged
integral majorant under explicit bounded-energy and vanishing squared-mismatch
hypotheses. Diagnostics are clean and the integral convergence theorem has
only the standard three axioms. Recovery inputs satisfying these hypotheses
must still be constructed for the geometric comparison. Both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Integrated selected gluing comparison

The `SerrinEpigraph Challenge Solution` build passed (3878 jobs).
`IntegratedGluing.lean` proves the integrated localized energy bound and selects
a smooth cutoff giving weighted input energies plus 1/N of the ambient gluing
majorant. All integral comparisons include explicit integrability proofs.
Diagnostics are clean; the selected comparison's transitive audit contains
only the standard three axioms. The error has not yet been shown to vanish.
Both Main rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Integrable majorant and its selected cutoff

The `SerrinEpigraph Challenge Solution` build passed (3877 jobs).
`GluingCostIntegral.lean` proves local integrability of normalized rescaled
energies and their gluing majorant, nonnegativity, the exact integral formula,
and existence of a smooth cutoff selected by this actual majorant. Diagnostics
are clean and the cutoff theorem's transitive audit uses only the standard
three axioms. The integrated energy comparison and vanishing-error argument
are not yet complete. Both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Explicit transition-energy majorant

The `SerrinEpigraph Challenge Solution` build passed (3876 jobs).
`GluingCostBound.lean` bounds glued energy by a fixed multiple of the input
energies plus squared mismatch with coefficient G²/R + 4 R W(0), assuming a
cutoff gradient bound G. The localized theorem confines this additional
majorant to the transition region and preserves exact endpoint energy outside.
Diagnostics and the localized theorem's standard-axiom audit are clean.
Integrating and proving vanishing errors remains necessary; both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Smooth cutoff with selected transition cost

The `SerrinEpigraph Challenge Solution` build passed (3875 jobs).
`SelectedTransitionCutoff.lean` constructs a smooth compactly supported cutoff
in a selected low-cost layer. Its fixed-annulus version gives transition cost
at most 1/N of the ambient cost and gradient bound C N/t for annulus width t.
Diagnostics are clean; the fixed-annulus theorem's transitive audit uses only
the standard three axioms. This supplies a cutoff, not yet a recovery sequence
with vanishing errors. Both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Radial transition-layer selection

The `SerrinEpigraph Challenge Solution` build passed (3874 jobs).
`TransitionLayerSelection.lean` proves cutoff transition containment in an
annulus, disjoint-layer integral averaging, disjointness of consecutive radial
layers, and selection of a radial layer with at most 1/N of the outer-ball
cost. All costs are explicitly assumed nonnegative and integrable. Diagnostics
are clean and the radial selection theorem has only the standard three axioms.
No vanishing transition-error conclusion is claimed yet. Both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Transition-localized gluing costs

The `SerrinEpigraph Challenge Solution` build passed (3873 jobs).
`GluingTransition.lean` proves nonnegativity of normalized rescaled energy,
vanishing cutoff gradient at endpoints, exact selection of input energy there,
and an almost-everywhere bound localizing excess energy to the strict transition
set. Diagnostics are clean; the localization theorem uses only the standard
three axioms. This does not establish that the transition cost vanishes.
Recovery construction, both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Rescaled local minimality

The `SerrinEpigraph Challenge Solution` build passed (3872 jobs).
`RescaledMinimality.lean` proves support transport under inverse dilation,
closed-range locally Lipschitz minimality for the rescaled energy, and its
application to cutoff-glued competitors. The change of variables uses the
positive surface-scale factor, preserving the energy inequality.
File diagnostics are clean; the final comparison theorem's transitive axiom
audit contains only the standard three axioms. Recovery and transition-error
estimates remain open, as do both Main rigidity proofs, full Comparator, and
Palomar registration.

## Total rescaled gluing energy

The `SerrinEpigraph Challenge Solution` build passed (3871 jobs).
`GluingTotalEnergy.lean` proves the exact kinetic/potential decomposition for
nonnegative functions, using vanishing totalized gradient at a zero minimum.
It combines the preceding estimates into an almost-everywhere total energy
bound for locally Lipschitz cutoff gluing. Diagnostics are clean and the
transitive axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The estimate retains both explicit mismatch errors; proving they vanish for
suitable recovery competitors remains necessary. The two Main rigidity proof
holes, full Comparator, and Palomar registration remain incomplete.

## Phase-restricted potential cost of gluing

The complete `SerrinEpigraph Challenge Solution` build passed (3870 jobs).

`GluingPotentialEnergy.lean` bounds the zero-level potential by a positive-level
potential and a quadratic gap. Using antitonicity and positivity at one half,
it then controls the phase-restricted potential of the glued competitor by
the two input potentials plus their squared mismatch, with explicit constants
involving the potential at zero and one half. The proof treats zero/positive
phase interfaces separately, respecting the indicator discontinuity at zero.

Diagnostics and the gluing theorem's transitive axiom audit are clean, using
only the standard three axioms. Combining total transition-energy control,
recovery profiles, and vanishing errors remains necessary for interface
minimality. Both Main rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Adjustable quadratic energy cost of gluing

The complete `SerrinEpigraph Challenge Solution` build passed (3869 jobs).

`GluingGradientEnergy.lean` proves parameterized Young and convex-square
inequalities, then bounds the glued gradient square by the convex combination
of the original gradient squares with factor one plus an arbitrary positive
parameter, together with an explicit mismatch-cutoff error. Division by twice
the scale gives the kinetic part of diffuse energy. The final theorem proves
this inequality almost everywhere for locally Lipschitz inputs.

Diagnostics and the final theorem's transitive axiom audit are clean, using
only the standard three axioms. Potential-energy control, recovery profiles,
and vanishing transition errors remain; interface minimality does not yet
follow. Both Main rigidity proofs, full Comparator, and Palomar registration
remain incomplete.

## Admissible cutoff gluing of competitors

The complete `SerrinEpigraph Challenge Solution` build passed (3868 jobs).

`GluedCompetitor.lean` constructs cutoff interpolation between a reference and
candidate. It proves local Lipschitz regularity, preservation of the closed
normalized range, agreement with the reference/candidate at cutoff values zero
and one, and confinement of the perturbation to the cutoff support. Its exact
gradient formula yields the convex gradient bound plus the value-difference
times cutoff-gradient error. The constructed function is applied directly to
the already proved phase-energy minimality theorem.

Diagnostics and the admissibility-application and gradient-bound axiom audits
are clean, using only the standard three axioms. Recovery profiles and
quantitative transition-energy control remain needed; this does not yet prove
interface minimality. Geometric classification, both Main rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## Exact weighted perimeter–energy liminf inequality

The complete `SerrinEpigraph Challenge Solution` build passed (3867 jobs).

`PerimeterEnergyLiminf.lean` proves the scalar-weight identity for absolute
indicator pairings and distributes the nonnegative primitive weight over the
variational supremum. The resulting theorem bounds the primitive value at one
times the phase perimeter in an open ball by the diffuse-energy liminf on the
closed ball. A common-subsequence theorem packages this exact coefficient on
all positive integer-radius balls for the same measurable phase limit.

Diagnostics and the common-subsequence theorem's transitive axiom audit are
clean, using only the standard three axioms. This is the lower-bound side;
recovery competitors and their matching boundary values still need construction
before interface minimality follows. Geometric classification, both Main
rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Exact primitive-to-energy comparison and tested liminf bound

The complete `SerrinEpigraph Challenge Solution` build passed (3866 jobs).

`PrimitiveEnergyLowerBound.lean` proves that the actual rescaled primitive's
gradient density is bounded pointwise by its rescaled diffuse-energy density,
and integrates the comparison with coefficient one. Combined with the exact
vector test estimate, this bounds every admissible divergence pairing by the
diffuse energy. Local integral convergence then passes each pairing to the
extended-nonnegative diffuse-energy liminf, without a dimension factor.

Diagnostics and the tested-liminf theorem's transitive axiom audit are clean,
using only the standard three axioms. Taking the weighted perimeter supremum
and constructing recovery competitors remain necessary for interface minimality.
Geometric classification, both Main rigidity proofs, full Comparator, and
Palomar registration remain incomplete.

## Exact gradient-mass control of divergence tests

The complete `SerrinEpigraph Challenge Solution` build passed (3865 jobs).

`SharpDivergenceBound.lean` proves exact compact vector integration by parts,
then controls a unit-field divergence pairing by the gradient mass with
coefficient one. Normalized mollification and convergence of both coefficients
and gradient masses extend the estimate to bounded nonnegative locally
Lipschitz functions. This removes the dimension loss in the earlier component
bounds, as required for the precise surface-energy lower bound.

Diagnostics and the locally Lipschitz theorem's transitive axiom audit are
clean, using only the standard three axioms. The sharp diffuse-energy liminf
bound, competitor recovery, interface minimality, geometric classification,
both Main rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Lower semicontinuity of variational perimeter

The complete `SerrinEpigraph Challenge Solution` build passed (3864 jobs).

`PerimeterLowerSemicontinuity.lean` proves continuity and support localization
of divergence, passes local integral convergence of measurable phase indicators
to each compact divergence pairing, and obtains the full variational-perimeter
liminf inequality. Perimeters are extended nonnegative values; no finite
perimeter assumption is imposed on the approximating sets.

Diagnostics and the liminf theorem's transitive axiom audit are clean, using
only the standard three axioms. This lower bound does not itself supply the
competitor recovery and energy comparison needed for interface minimality.
Interface minimality, geometric classification, both Main rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## Intrinsic perimeter and representative invariance

The complete `SerrinEpigraph Challenge Solution` build passed (3863 jobs).

`PerimeterInvariance.lean` identifies the basis formula for divergence with
Mathlib's intrinsic linear trace and proves that divergence and variational
perimeter are independent of the orthonormal basis. It also proves that
changing a phase on a null set inside the test domain leaves its perimeter
unchanged. The two definitions in `VariationalPerimeter.lean` are exposed for
use in downstream proofs; their mathematical definitions are unchanged.

Diagnostics and both invariance theorems' transitive axiom audits are clean,
using only the standard three axioms. Perimeter lower semicontinuity, interface
minimality, and geometric classification remain. Both Main rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## Variational perimeter bounds

The complete `SerrinEpigraph Challenge Solution` build passed (3834 jobs).

`VariationalPerimeter.lean` defines the divergence in an orthonormal basis and
an extended-nonnegative variational perimeter as the supremum of absolute
pairings against compactly supported C¹ unit vector fields. It proves domain
monotonicity, transfers containing-set test bounds to perimeter bounds, and
excludes infinite perimeter under a finite real bound. Applied to the common
phase limit, it gives surface-order perimeter bounds on every positive
integer-radius open ball, for each orthonormal basis.

Diagnostics are clean and the application theorem's transitive axiom audit
uses only the standard three axioms. Interface minimality and geometric
classification remain unproved. Both Main rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Vector divergence test bound for the phase limit

The complete `SerrinEpigraph Challenge Solution` build passed (3833 jobs).

`PhaseVectorTestBound.lean` decomposes a compactly supported unit-bounded C¹
vector field into scalar components in any orthonormal basis. Directional
bounds, integrability of the component pairings, and the finite-sum triangle
inequality yield a bound on the full derivative trace pairing. Applied to the
same measurable phase limit, this gives surface-order control for all vector
divergence tests, absorbing the dimension factor into the constant.

The final theorem's transitive axiom audit uses only the standard three axioms;
there are no new build warnings or holes. Packaging the variational perimeter,
interface minimality, and geometric classification remain. Both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Directional bounds inherited by the limiting phase

The complete `SerrinEpigraph Challenge Solution` build passed (3832 jobs).

`LimitingPhaseDirectionalBound.lean` passes the actual rescaled primitive's
uniform directional test estimates to the same measurable phase obtained by
local integral compactness. Dividing by the strictly positive primitive value
at one yields surface-order bounds for the unweighted phase indicator. The
result retains the common subsequence and its local integral convergence, and
holds simultaneously for every direction and admissible compact scalar test.

The final theorem's transitive axiom audit uses only the standard three axioms.
The build has no new warnings or proof holes. Full vector-test perimeter
control, interface minimality, geometric classification, both Main rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Locally Lipschitz directional tests and the actual rescaled primitive

The complete `SerrinEpigraph Challenge Solution` build passed (3831 jobs).

`LipschitzDirectionalTest.lean` proves normalized mollification preserves a
nonnegative constant upper bound and converges in integral norm on compact
sets. Together with convergence of gradient masses, this extends the directional
test estimate to bounded nonnegative locally Lipschitz functions. Its application
to the actual rescaled phase primitives gives a dilation-independent bound
proportional to the direction norm and the radius to the boundary dimension.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only the standard three axioms. Passing the bounds to the limiting phase,
assembling perimeter control, interface minimality, and classification remain.
Both Main rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Directional derivative test bounds

The complete `SerrinEpigraph Challenge Solution` build passed (3830 jobs).

`DirectionalTestBound.lean` restricts compactly supported directional integration
by parts to any containing compact set. For a smooth coefficient it bounds
the integral against a derivative of a unit-bounded test function by the
direction norm times the local gradient mass. A further theorem passes this
bound through integral convergence of smooth approximations when their gradient
masses converge.

Diagnostics and both bound theorems' transitive axiom audits are clean, using
only the standard three axioms. Applying the transfer theorem to locally
Lipschitz mollification and obtaining the limiting phase perimeter bound remain.
Interface minimality, geometric classification, both Main rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## Bounded testing of the primitive limit

The complete `SerrinEpigraph Challenge Solution` build passed (3829 jobs).

`IntegralLimitTesting.lean` proves convergence of integrals against bounded
measurable scalar tests from integral-norm convergence, and transfer of uniform
bounds on the tested integrals. The application theorem supplies one primitive
subsequence and one measurable phase set simultaneously valid for every bounded
measurable test on every integer-radius ball.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only the standard three axioms. This is a limit-passage result, not yet
a perimeter estimate: integration by parts and the actual derivative-test
bounds still need to be established. Interface minimality and classification,
both Main rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Common local limit of solutions and phase indicators

The complete `SerrinEpigraph Challenge Solution` build passed (3828 jobs).

`SolutionPhaseConvergence.lean` uses the vanishing solution-to-phase-indicator
error and the integral triangle inequality to transfer local indicator
convergence to the rescaled zero-extended solutions. It packages one common
subsequence and one measurable phase set for both local integral limits on
every positive integer-radius ball.

Diagnostics and the final theorem's transitive axiom audit are clean, using
only the standard three axioms. The proof roadmap now distinguishes established
integral compactness from the remaining interface minimality and flatness
arguments. Both Main rigidity proofs, full Comparator, and Palomar registration
remain incomplete.

## Local convergence of rescaled epigraph indicators

The complete `SerrinEpigraph Challenge Solution` build passed (3827 jobs).

`PhaseSetConvergence.lean` transfers primitive convergence to convergence of
positive-phase indicators using the vanishing primitive approximation error
and the strictly positive primitive value at one. It then identifies the
rescaled positive phase with the epigraph of the rescaled graph. The resulting
theorem provides a common subsequence and a measurable set such that the
rescaled epigraph indicators converge in integral norm on every positive
integer-radius ball.

Diagnostics and the final theorem's transitive axiom audit are clean; only
the standard three axioms occur. No interface minimality or flatness is
asserted. Both Main rigidity holes, full Comparator, and Palomar registration
remain incomplete.

## Measurable global limiting phase

The complete `SerrinEpigraph Challenge Solution` build passed (3826 jobs).

`GlobalPhaseSet.lean` combines local integrability and the local two-valued
constraint across the integer-ball cover. A measurable representative yields
a measurable phase set whose weighted indicator agrees almost everywhere
with the global primitive limit. The final theorem gives one strictly
increasing subsequence and one measurable phase set, with local integral
convergence on every positive integer-radius ball for any diverging sequence
of dilation factors at least one.

Diagnostics are clean and the final theorem's transitive axiom audit uses only
the standard three axioms. Interface minimality and geometric classification
remain unproved. The two Main rigidity holes, full Comparator, and Palomar
registration remain incomplete.

## Local two-phase identification

The complete `SerrinEpigraph Challenge Solution` build passed (3825 jobs).

`TwoPhaseLimit.lean` proves that integral limits of two-valued functions remain
two-valued almost everywhere. The proof integrates the minimum distance to
the two values and forces that nonnegative integral to vanish. A transfer
lemma handles vanishing integral approximation error. Applied to the actual
weighted phase indicators, this proves that every local primitive limit along
diverging dilations takes only zero and the primitive value at one almost
everywhere.

The application theorem's transitive axiom audit uses only the standard three
axioms, and diagnostics are clean. Global phase-set packaging, interface
minimality and geometric classification remain. Both rigidity proofs, full
Comparator, and Palomar registration remain incomplete.

## Global representative of the local primitive limits

The complete `SerrinEpigraph Challenge Solution` build passed (3824 jobs).

`GlobalPrimitiveLimit.lean` proves almost-everywhere gluing on a countable
measurable cover with ordered compatibility. Applied to the integer balls,
it constructs one global function representing every local primitive limit,
with integrability and integral convergence on each ball along the same
strictly increasing subsequence.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only `propext`, `Classical.choice`, and `Quot.sound`. Identifying the
two-phase limit and the geometric classification remain. Both rigidity proof
holes, full Comparator, and Palomar registration are still incomplete.

## Compatibility of local L¹ limits

The complete `SerrinEpigraph Challenge Solution` build passed (3823 jobs).

`LocalLimitCompatibility.lean` proves restriction of integral convergence to
smaller sets and almost-everywhere uniqueness of integrable limits. Applied
to the common phase-primitive subsequence, this shows all local limits agree
almost everywhere on nested integer-radius balls.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only `propext`, `Classical.choice`, and `Quot.sound`. A global
representative and identification of the limiting phase remain to be proved.
Both rigidity proofs, full Comparator, and Palomar registration remain
incomplete; the successful build does not discharge the two Main proof holes.

## Actual local L¹ limits of unsmoothed primitives

The complete `SerrinEpigraph Challenge Solution` build passed (3822 jobs).

`LocalPrimitiveLimits.lean` embeds an integrable Cauchy sequence in Mathlib's
complete L¹ space, identifies its metric with the integral of the absolute
difference, and obtains an integrable representative of its limit. It applies
this to the common primitive subsequence, producing an actual local integrable
limit on every positive integer-radius ball along the same subsequence.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only the standard three axioms. Compatibility of representatives on
nested balls and identification of the limiting phase are not yet proved.
Both rigidity proofs, full Comparator, and Palomar registration remain
incomplete.

## Integral Cauchy subsequence without mollification

The complete `SerrinEpigraph Challenge Solution` build passed (3821 jobs).

`IntegralCauchyApproximation.lean` proves the integral triangle inequality,
transfer of the integral Cauchy property from approximations with uniformly
vanishing errors, and the integral Cauchy criterion from uniform convergence
on compact sets. Applying these to the common mollified subsequence and the
uniform mollification error proves that a single subsequence of the actual,
unsmoothed phase primitives is Cauchy in integral norm on every positive
integer-radius ball, for any sequence of dilation factors at least one.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only the standard three axioms. Constructing the L¹ limits by completeness,
checking compatibility on nested balls, and identifying the limiting phase
remain necessary. Both rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Uniform local mollification error

The complete `SerrinEpigraph Challenge Solution` build passed (3820 jobs).

`MollificationIntegralError.lean` proves the pointwise averaging bound for
mollification error and integrates it using compact product integrability and
Fubini. The translation hypothesis is needed only on the actual kernel support.
Applied to the dilated phase primitive, it gives one C > 0 such that

$$
\int_{\overline B_r}|\rho_n*\Phi(U(R\cdot))-\Phi(U(R\cdot))|
\le\frac{C(r+1)^m}{n+1}\qquad(R\ge1,\ r\ge1).
$$

Thus the local error vanishes uniformly in dilation as the mollification index
grows. Diagnostics and the final theorem's transitive audit are clean, using
only the standard three axioms. Combining this estimate with the common
mollified subsequence to establish unsmoothed local integral convergence remains
necessary. Both rigidity proofs, full Comparator, and Palomar registration
remain incomplete.

## Locally Lipschitz translation estimates and uniform dilation control

The complete `SerrinEpigraph Challenge Solution` build passed (3819 jobs).

`LipschitzTranslationIntegral.lean` proves convergence of compact-set integrals
of normalized-mollification gradient norms by dominated convergence. It also
proves convergence of the fixed-translation integral error using a uniform
local Lipschitz bound. Passing the smooth translation inequality to the limit
gives its full locally Lipschitz version.

Applied to the actual dilated phase primitive, with the previously proved
gradient integral bound, it yields a single C > 0 such that

$$
\int_{\overline B_r}|\Phi(U(R(x+z)))-\Phi(U(Rx))|\,dx
\le |z| C(r+|z|)^m
$$

whenever R > 0 and R(r+|z|) ≥ 1. Diagnostics and the final theorem's transitive
axiom audit are clean, using only the standard three axioms. Averaging this
translation estimate to remove mollification remains necessary. Both rigidity
proofs, full Comparator, and Palomar registration remain incomplete.

## Local integral translation estimate

The complete `SerrinEpigraph Challenge Solution` build passed (3818 jobs).

`TranslationIntegral.lean` first controls the integral of a translated
nonnegative continuous function by its integral over an enlarged ball.
It then integrates the segment gradient inequality, proves product
integrability on compact sets, exchanges the two integrals, and obtains

$$
\int_{\overline B_r}|v(x+z)-v(x)|\,dx
\le |z|\int_{\overline B_{r+|z|}}|\nabla v|\,dx
$$

for every continuously differentiable real function on Euclidean space.
Diagnostics and the transitive axiom audit are clean, using only the standard
three axioms. The locally Lipschitz extension and uniform mollification error
bound remain necessary. Both rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Segment gradient estimate for translation control

The complete `SerrinEpigraph Challenge Solution` build passed (3817 jobs).

`SegmentGradientEstimate.lean` proves the exact line-segment fundamental theorem
for a continuously differentiable real function on Euclidean space, and derives

$$
|v(x+z)-v(x)|\le |z|\int_0^1|\nabla v(x+tz)|\,dt.
$$

The proof uses the spatial derivative composed with the affine segment, the
fundamental theorem of calculus, and the operator-norm bound identified with
the Euclidean gradient norm. Diagnostics and the transitive audit are clean,
using only the standard three axioms. This is the smooth pointwise estimate;
spatial integration, extension to locally Lipschitz functions, and uniform
mollification error control still need completion. Both rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## A common subsequence for all mollifications and integer balls

The complete `SerrinEpigraph Challenge Solution` build passed (3816 jobs).

`SimultaneousMollifiedCompactness.lean` proves a countable-family version of
uniform subsequence extraction. It takes the compact closure of each bounded
Lipschitz family and uses sequential compactness of their countable product.
Applied to the phase primitive, one strictly increasing subsequence gives
uniform convergence for every mollification index on every ball of positive
integer radius. This is a single shared subsequence, not independently chosen
subsequences for different indices or balls.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only the standard three axioms. Uniform control of the mollification
error and the resulting unsmoothed local integral convergence remain to be
proved. The two rigidity proofs, full Comparator, and Palomar registration
remain incomplete.

## Uniformly convergent subsequences of mollified primitives

The complete `SerrinEpigraph Challenge Solution` build passed (3815 jobs).

`MollifiedPrimitiveCompactness.lean` applies Arzelà–Ascoli to a uniformly
Lipschitz sequence of bounded continuous functions on a compact metric space,
then extracts a strictly increasing subsequence with uniform convergence.
It applies this result to any sequence of dilations of the phase primitive,
restricted to any fixed closed ball and mollified at any fixed index. The
limit is a bounded continuous function on that ball.

Diagnostics and the application theorem's transitive axiom audit are clean,
using only the standard three axioms. The subsequence may depend on the ball
and mollification index; a simultaneous diagonal choice and uniform removal
of mollification are still needed. Both rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Uniform Lipschitz bounds for fixed mollification

The complete `SerrinEpigraph Challenge Solution` build passed (3813 jobs).

`MollificationFamilyBounds.lean` proves that a fixed averaging kernel maps any
uniformly bounded family of continuous inputs to a family with a common
Lipschitz constant on each closed ball. The proof uses the swapped convolution,
a global Lipschitz bound for the smooth compactly supported kernel, and the
finite volume of the enlarged ball containing the difference integrand.

It also proves the phase primitive remains between its two equilibrium values
on the normalized range. Applied to the dilated primitive, this gives a local
Lipschitz constant independent of dilation at each fixed mollification index.
Diagnostics and the final theorem's transitive audit use only the standard
three axioms. Subsequence extraction and uniform removal of mollification
remain necessary; neither rigidity proof, full Comparator, nor Palomar
registration is complete.

## Primitive approximation by the two phase values

The complete `SerrinEpigraph Challenge Solution` build passed (3812 jobs).

`PrimitiveIndicatorApproximation.lean` transfers the local integral approximation
from the solution to its phase primitive using the proved Lipschitz constant:

$$
|\Phi(1)1_{\{U>0\}}-\Phi(U)|
\le\sqrt{2W(0)}\,|1_{\{U>0\}}-U|.
$$

It proves compact-set integrability after dilation and, for each fixed r > 0,

$$
\int_{\overline B_r}|\Phi(1)1_{\{U(Rx)>0\}}-\Phi(U(Rx))|\,dx\longrightarrow0.
$$

Diagnostics and the final theorem's transitive axiom audit are clean, using
only the standard three axioms. This comparison does not supply a convergent
subsequence. Compactness, geometric classification, both rigidity proofs,
full Comparator, and Palomar registration remain incomplete.

## Primitive regularity across the free boundary

The complete `SerrinEpigraph Challenge Solution` build passed (3811 jobs).

`PhasePrimitiveRegularity.lean` proves that the phase primitive is Lipschitz on
the whole closed normalized range, with constant

$$
\sqrt{2W(0)}.
$$

The proof bounds the integral of the square-root potential between any two
values in [0,1], so it includes both endpoints without assuming two-sided
differentiability there. Composing with the zero extension proves local
Lipschitz regularity of the phase primitive across the free boundary.
Diagnostics and the transitive axiom audit are clean and use only the standard
three axioms. Compactness and geometric classification remain unproved, as do
the two rigidity targets, full Comparator, and Palomar registration.

## Spatial chain rule and primitive gradient bound

The complete `SerrinEpigraph Challenge Solution` build passed (3810 jobs).

`PhasePrimitiveGradient.lean` proves the spatial gradient identity

$$
\nabla\Phi(U)=\sqrt{2W(U)}\,\nabla U,\qquad
\Phi(s)=\int_0^s\sqrt{2W(t)}\,dt.
$$

This identity holds everywhere for Mathlib's totalized gradient: the interior
uses the ordinary chain rule, while the zero phase (including the boundary)
uses the local-minimum derivative theorem and the nonnegativity of the primitive.
Taking norms and applying dilation yields

$$
\int_{\overline B_r}|\nabla(\Phi(U(R\cdot)))|\le C r^m
\qquad(R>0,\ Rr\ge1).
$$

Diagnostics and the transitive audit are clean, with only the standard three
axioms. Local Lipschitz regularity of the composite, compactness, and geometric
classification still need completion. The two rigidity targets, full Comparator,
and Palomar registration remain incomplete.

## Weighted gradient and phase primitive

The complete `SerrinEpigraph Challenge Solution` build passed (3809 jobs).

`WeightedGradient.lean` proves the pointwise Young inequality

$$
\sqrt{2W(U)}|\nabla U|\le e(U),
$$

including the zero phase, using the proved vanishing gradient of the zero
extension outside the epigraph. It establishes local integrability and the
uniform rescaled bound

$$
\int_{\overline B_r}\sqrt{2W(U(Rx))}|\nabla(U(R\cdot))(x)|\,dx\le C r^m
\quad(R>0,\ Rr\ge1).
$$

`PhasePrimitive.lean` defines the integral of the square-root potential, proves
its derivative at every value strictly between zero and one, and proves its
value at one is strictly positive while its value at zero vanishes. Diagnostics
and transitive audits are clean and use only the standard three axioms.
The spatial chain rule and compactness argument still need completion; neither
rigidity theorem, full Comparator, nor Palomar registration is complete.

## Local integral approximation by phase indicators

The complete `SerrinEpigraph Challenge Solution` build passed (3807 jobs).

`PhaseIndicatorApproximation.lean` proves local integrability of the absolute
error between the dilated zero extension and its positive-phase indicator.
Splitting at any fixed level a in [0,1) gives the bound

$$
\int_{\overline B_r}|1_{\{U(Rx)>0\}}-U(Rx)|\,dx
\le |\{0<U(Rx)\le a\}\cap\overline B_r|+(1-a)|\overline B_r|.
$$

Taking a sufficiently close to one and using vanishing transition volume proves
that the left side tends to zero for every fixed positive radius. Diagnostics
are clean and the transitive axiom audit uses only the three standard axioms.
This compares two scale-dependent functions; it does not assert existence of a
limiting region. Phase compactness, both rigidity proofs, full Comparator, and
Palomar registration remain incomplete.

## Vanishing intermediate-phase volume

The complete `SerrinEpigraph Challenge Solution` build passed (3806 jobs).

`TransitionVolume.lean` defines the measurable region where the dilated zero
extension lies strictly above zero and at or below a fixed level a < 1.
Monotonicity and strict positivity of the normalized potential give

$$
|\{0<U(Rx)\le a\}\cap\overline B_r|
\le \frac{1}{W(a)}\int_{\overline B_r}1_{\{U(Rx)>0\}}W(U(Rx))\,dx
\longrightarrow 0
$$

for every fixed positive radius and 0 ≤ a < 1. Local integrability of the
dilated potential is proved directly from continuity and the phase indicator.
Diagnostics and the transitive audit are clean, using only the three standard
axioms. Interface compactness and geometric classification are not inferred from
this volume convergence. Both rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Vanishing rescaled phase potential

The complete `SerrinEpigraph Challenge Solution` build passed (3805 jobs).

`RescaledPotential.lean` proves local integrability and nonnegativity of the
potential restricted to the positive phase, and compares it with the full energy.
The exact dilation formula then gives

$$
0\le\int_{\overline B_r}1_{\{U(Rx)>0\}}W(U(Rx))\,dx
\le \frac{C r^m}{R}\qquad(R>0,\ Rr\ge1).
$$

For each fixed positive radius this integral tends to zero as the scale tends
to infinity. The positive-phase indicator is retained throughout. Diagnostics
are clean, and the limit theorem's transitive audit uses only the three standard
axioms. This does not yet extract an interface limit or classify its geometry;
both rigidity proofs, full Comparator, and Palomar registration remain incomplete.

## Uniform rescaled phase energy

`RescaledPhaseEnergy.lean` defines the actual gradient-based density

$$
e_R(v)=1_{\{v>0\}}\left(\frac{|\nabla v|^2}{2R}+R W(v)\right).
$$

It proves the gradient dilation formula and the exact change of variables

$$
\int_{\overline B_r} e_R(U(R\cdot))
=R^{-m}\int_{\overline B_{Rr}} e(U)
\le C r^m\qquad(R>0,\ Rr\ge1).
$$

The complete `SerrinEpigraph Challenge Solution` build passed (3804 jobs).
Diagnostics are clean; the final bound's transitive axiom audit uses only
`propext`, `Classical.choice`, and `Quot.sound`. No compactness or interface
classification is assumed. Both rigidity proofs, full Comparator, and Palomar
registration remain incomplete.

## Surface-order phase-energy growth

`UnitShellVolume.lean` proves real Euclidean ball-volume scaling, bounds the
unit increment of a power, and obtains a surface-order unit-shell volume bound.
Combining this with the integrated cutoff comparison proves a single positive
constant C such that

$$
\int_{\overline B_R} e(U)\le C R^m\qquad(R\ge1)
$$

in ambient dimension m+1. Diagnostics and the final growth theorem's transitive
axiom audit are clean, using only `propext`, `Classical.choice`, and `Quot.sound`.
Rescaling compactness and geometric classification remain open; both rigidity
targets, full Comparator, and Palomar registration are still incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3803 jobs).

## Integrated unit-shell energy bound

`PhaseEnergyShellBound.lean` splits both original and competitor energies into
the inner ball and its unit shell. The cutoff energy vanishes in the inner ball;
integrating the pointwise cost and using closed-range minimality cancels the
original shell energy. The final theorem supplies one positive constant,
independent of radius, bounding every ball energy by the unit-shell volume.
Diagnostics and the final theorem's transitive axiom audit are clean, using
only `propext`, `Classical.choice`, and `Quot.sound`. The explicit polynomial
shell-volume bound and geometric classification remain to be proved. Both
rigidity targets, full Comparator, and Palomar registration are incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3777 jobs).

## Radial cutoff competitor and energy cost

`RadialCutoffCompetitor.lean` proves the radial ramp is one-Lipschitz, the
minimum competitor vanishes on the inner ball and equals the reference outside
the unit shell, and its perturbation support is compact. A gradient-selection
lemma for minima yields a radius-independent squared-gradient cost; the final
pointwise phase-energy bound adds at most 1/2+M under a potential bound M.
Diagnostics and the final theorem's transitive axiom audit are clean; only
`propext`, `Classical.choice`, and `Quot.sound` are used. The integrated growth
estimate, geometric classification, both rigidity targets, full Comparator,
and Palomar registration remain unfinished.
The complete `SerrinEpigraph Challenge Solution` build passed (3776 jobs).

## Epigraph rescaling and one-sided bounds

`EpigraphRescaling.lean` proves the exact domain identity for the rescaled graph,
both one-sided bound formulas with intercept C/R, and passage to homogeneous
cone bounds under an explicit pointwise-convergence hypothesis. Diagnostics
are clean and the final bound theorem's transitive audit uses only `propext`,
`Classical.choice`, and `Quot.sound`, with no source warnings. No existence or
flatness of a blow-down limit is claimed. Both rigidity proofs, full Comparator,
and Palomar registration remain unfinished.
The complete `SerrinEpigraph Challenge Solution` build passed (3775 jobs).

## Closed-range Lipschitz free-boundary minimality

`CappedEnergy.lean` proves uniform compact gradient bounds for the cap family,
pointwise phase-energy convergence including the zero phase, and dominated
energy-integral convergence. `ClosedLipschitzMinimality.lean` passes the existing
comparison to the limit. The resulting theorem covers every locally Lipschitz
competitor valued in [0,1] whose difference from the zero extension has support
inside the compact integration set. Both new files have clean diagnostics;
the final minimality theorem's transitive axiom audit uses only `propext`,
`Classical.choice`, and `Quot.sound`, with no source warnings.
The geometric classification, both rigidity targets, full Comparator, and
Palomar registration remain unfinished.
The complete `SerrinEpigraph Challenge Solution` build passed (3774 jobs).

## Endpoint competitor cap and gradient convergence

`CappedCompetitor.lean` constructs a ceiling between the reference solution and
one. Taking its minimum with a normalized competitor preserves local Lipschitz
regularity, positive phase, and support of the difference, while lowering all
values strictly below one. Values converge as the cap parameter goes to zero;
gradients converge at every differentiability point of the reference function,
including where the competitor attains one. Diagnostics are clean and the
gradient convergence theorem's transitive axiom audit uses only `propext`,
`Classical.choice`, and `Quot.sound`. Energy-integral convergence is still
needed before claiming closed-range minimality. Both rigidity targets, full
Comparator, and Palomar registration remain incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3772 jobs).

## Minimality for locally Lipschitz competitors below equilibrium

`LipschitzCalibration.lean` establishes the calibration integral limit,
integrability, and invariance for compact locally Lipschitz perturbations.
`LipschitzMinimality.lean` derives energy comparison on enclosing balls and
arbitrary compact sets containing the support. Its final theorem applies
directly to any locally Lipschitz competitor valued in [0,1), with compactly
supported difference from the zero extension, and uses the unshifted energy.
Both modules have clean diagnostics. The final theorem's transitive audit uses
only `propext`, `Classical.choice`, and `Quot.sound`, with no source warnings.
Endpoint value one is not yet covered. Both rigidity targets, full Comparator,
and Palomar registration remain incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3771 jobs).

## Gradient convergence for locally Lipschitz competitors

`LipschitzMollificationDerivative.lean` proves differentiation under the
averaging integral for globally Lipschitz functions, local integrability of
their derivatives, almost-everywhere convergence by Lebesgue differentiation,
and convergence for normalized gradients. Real-valued Lipschitz extensions on
a countable ball cover transfer the result to arbitrary locally Lipschitz
functions. Diagnostics are clean; the final local theorem's transitive audit
uses only `propext`, `Classical.choice`, and `Quot.sound`, with no source warnings.
Connecting this convergence to Lipschitz minimality remains to be done. Both
rigidity targets, full Comparator, and Palomar registration remain incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3769 jobs).

## General locally Lipschitz competitor bounds

`LipschitzCompetitorEnergy.lean` proves compact bounds for gradients and
normalized-mollification gradients, almost-everywhere differentiability by a
countable application of Rademacher, compact integrability of squared gradients,
and finite local phase energy for normalized locally Lipschitz competitors.
Diagnostics are clean. Axiom audits of phase-energy integrability,
almost-everywhere differentiability, and mollified-gradient bounds use only
`propext`, `Classical.choice`, and `Quot.sound`, with no source warnings.
Gradient convergence and the full Lipschitz minimality argument remain open;
both rigidity targets, full Comparator, and Palomar are also incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3768 jobs).

## Unshifted free-boundary minimality for smooth perturbations

`UnshiftedMinimality.lean` combines the exact Neumann energy identity with
`CrossBoundaryMinimality.lean`. It proves that the phase-energy shift vanishes
and gives unshifted energy comparison on every compact set containing the
support of a C¹ perturbation, and on an enclosing ball. Competitors may change
positive phase but must still take values in [0,1). This does not assert
minimality for arbitrary Lipschitz competitors or complete either rigidity
target. Lean diagnostics are clean; the compact-set theorem's transitive axiom
audit uses only `propext`, `Classical.choice`, and `Quot.sound`, with no source
warnings. Full Comparator and Palomar registration remain incomplete.
The complete `SerrinEpigraph Challenge Solution` build passed (3767 jobs).

## Exact Neumann energy identity

`InwardTangent.lean` proves that right-hand velocities of curves in a set belong
to its positive tangent cone, constructs such curves above the graph tangent
hyperplane, and establishes inward-normal cone membership. Consequently
`AnnularSlopeComparison.lean` removes the intermediate geometric hypothesis,
applies arbitrary-radius exterior tangent balls, and proves

$$
\kappa^2\le 2W(0),\qquad \kappa^2=2W(0).
$$

Both new modules have clean Lean diagnostics. The energy identity's transitive
axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`, with no
source warnings. Both rigidity targets, full Comparator, and Palomar registration
remain unfinished. Subsequent work must remove the energy shift in minimality
and prove the required geometric classification.
The complete `SerrinEpigraph Challenge Solution` build passed (3766 jobs).

## Exterior contact directional derivatives

`AnnularContactDerivative.lean` proves the directional derivative comparison
at an exterior tangent point for every vector in the positive tangent cone of
the closed epigraph. It also derives the Neumann upper bound by the inner
radial slope assuming inward-normal cone membership. That membership is an
explicit hypothesis of this intermediate result and remains to be proved;
it has not been added to either rigidity target. Diagnostics are clean, and
the final intermediate theorem's transitive axiom audit uses only `propext`,
`Classical.choice`, and `Quot.sound`. The unconditional upper Neumann energy
bound, both rigidity targets, full Comparator, and Palomar remain unfinished.
The complete `SerrinEpigraph Challenge Solution` build passed (3764 jobs).

## Exterior annular comparison without a shift

`TangentAnnularComparison.lean` proves the upper comparison for an unshifted
exterior ball, on the closure of the epigraph/outer-ball intersection. The proof
passes to zero positive downward shift within the radial interval and extends
the interior inequality by continuity. Lean diagnostics are clean; its
transitive axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
The complete `SerrinEpigraph Challenge Solution` build passed (3763 jobs).
Contact derivative comparison and the upper Neumann energy bound remain open,
as do both rigidity targets, full Comparator, and Palomar registration.

## Shifted exterior annular comparison

`AnnularComparison.lean` proves comparison on the closure of the intersection
of the epigraph and the outer ball. It checks compactness, strict positivity of
the annular profile, both equations, and boundary ordering on both boundary
pieces. The downward-shift specialization has clean Lean diagnostics and its
transitive axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
The complete `SerrinEpigraph Challenge Solution` build passed (3762 jobs).
Zero-shift comparison, the upper Neumann energy bound, both rigidity proofs,
full Comparator, and Palomar registration remain unfinished.

## Disconnected comparison domains and exterior separation

`ComponentComparison.lean` proves that component boundaries of an open set lie
on its boundary and applies nonlinear comparison component by component on any
proper open set with compact closure. `ExteriorBallGeometry.lean` proves that
every positive downward shift of an exterior ball places its entire closed ball
outside the closed epigraph, giving a strict distance lower bound at every
closed-epigraph point. The final comparison and distance theorems passed
transitive axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`.
After correcting a complement-membership simplification, the complete build
passed (3761 jobs); source diagnostics are clean. Annular comparison itself,
reverse Neumann energy, both rigidity targets, full Comparator, and Palomar
registration remain unfinished.

## Annular regularity and inner boundary differential

`AnnularRegularity.lean` derives C1 slope and C2 radial value regularity from the
radial equations, and composes with the smooth Euclidean norm away from the
center to prove C2 regularity on the open annulus. It also proves the right
derivative at the inner radius and the explicit spatial differential within the
closed annulus at the inner sphere. The spatial regularity and boundary
differential theorems passed individual transitive axiom audits with only
`propext`, `Classical.choice`, and `Quot.sound`, with no source warnings. The
complete build passed (3749 jobs). Exterior comparison, the reverse energy bound,
both rigidity classifications, full Comparator acceptance, and Palomar
registration remain unfinished.

## Spatial annular equation

`AnnularSpatial.lean` lifts the constructed radial profiles by Euclidean distance.
It proves continuity on the closed annulus, normalized range, interior positivity,
zero inner sphere value and one outer sphere value, explicit first and second
spatial derivatives, and `IncreasingRadialSegment.spatial_equation` for the
original reaction. The equation theorem's transitive axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, with clean source diagnostics.
The full build passed (3748 jobs). Continuous second differentiability and inner
boundary derivatives are still needed for the exterior comparison. The reverse
energy inequality, final rigidity proofs, full Comparator, and Palomar remain
unfinished.

## Annular solution existence completed

`AnnularMaximal.lean` completes the compatible union and proves that it is an
extension of the seed at the supremal radius, including agreement at the seed's
outer endpoint by continuity. The maximality criterion then forces outer value
one. `RigidityHypotheses.exists_increasing_annular_profile` assembles this with
local existence and the energy-margin choice: every positive initial slope with
squared value greater than twice the potential drop is realized by a radial
zero-to-one solution at every sufficiently large inner radius, with strictly
positive slope throughout its closed interval.
The final theorem's transitive axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`, with clean source diagnostics. The full
build passed (3747 jobs). Spatial annulus regularity, exterior comparison, the
reverse Neumann energy inequality, and both rigidity classifications remain
unfinished. Full Comparator and Palomar registration have not been achieved.

## Finite annular endpoint limits and completion

`AnnularLimits.lean` bounds the union's slope by the common initial slope and
uses the radial endpoint-limit theorem to obtain finite value and slope limits.
The value limit lies in the normalized closed interval and the slope limit is
nonnegative. It also proves a general continuity result for filling a finite
left limit and `increasingRadialSegment_of_endpoint_limits`, which packages a
completed half-open increasing radial system as a closed segment.
The union-limit theorem and segment-completion theorem passed individual
transitive axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`,
with clean source diagnostics. The complete build passed (3746 jobs).
Assembly of the completed supremal extension remains, followed by the exterior
comparison and rigidity work. Full Comparator and Palomar remain incomplete.

## Supremal annular system on the half-open interval

`AnnularUnion.lean` defines a union of compatible radial segments, proves local
agreement and continuity, passes both radial equations to the union, and
identifies its domain with the interval ending at the supremum of bounded radii.
`IncreasingRadialSegment.exists_supremal_system` applies this construction to all
extensions of the seed and preserves its half-open initial segment, normalized
values, positive interior values, and nonnegative slope.
The theorem's transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`, with no source warnings. The complete build passed (3745 jobs).
This constructs the solution before the supremal endpoint, not at that endpoint;
finite endpoint completion is still needed. Rigidity, full Comparator acceptance,
and Palomar registration remain unfinished.

## Compatibility and bounded annular extension radii

`AnnularBranches.lean` defines `AnnularExtension` of a fixed increasing seed.
`AnnularExtension.compatible` proves that any two extensions agree in both
components on their full closed overlap. The earlier width estimate gives a
uniform finite upper bound for every extension radius under a positive energy
margin. `value_eq_one_of_radius_eq_sup` proves that an extension attaining the
supremum of these radii has outer value one, since otherwise the extension
theorem contradicts the supremum.
Compatibility and the supremal endpoint theorem passed individual transitive
axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`, and no
source warnings. The complete build passed (3744 jobs). Existence of an extension
attaining that supremum is not yet proved. The remaining rigidity work, full
Comparator acceptance, and Palomar registration remain unfinished.

## Glued extension of annular segments

`AnnularContinuation.lean` proves `IncreasingRadialSegment.exists_extension`:
positive endpoint slope and value below one give a strictly longer increasing
segment agreeing with both old components on the entire original closed
interval. The splice satisfies both differential equations at the junction,
not merely on its two sides. `exists_extension_of_energy_margin` supplies the
endpoint slope from the earlier energy estimate. Its transitive axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`, with no source
warnings. The full build passed (3743 jobs). The maximal annular continuation,
reverse Neumann energy inequality, and rigidity classifications remain open;
full Comparator acceptance and Palomar registration are still outstanding.

## Annular endpoint derivatives and local restart

`AnnularEndpoint.lean` proves that increasing radial segments are nondecreasing,
have positive outer endpoint value, and satisfy both radial equations as left
derivatives at that endpoint. If the endpoint value is below one and its slope
is positive, `exists_local_restart` gives a matching local radial solution with
values strictly between zero and one and strictly positive slope.
The slope endpoint theorem and restart theorem passed individual transitive
axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`; source
diagnostics are clean. The complete build passed (3742 jobs). A glued extended
segment and continuation to value one are still required. Both rigidity targets,
full Comparator acceptance, and Palomar registration remain unfinished.

## Local increasing annular solution and parameter choice

`AnnularLocal.lean` proves `exists_increasingRadialSegment` from reaction
regularity, positive initial radius, and positive initial slope. The resulting
segment solves the original radial equation, starts at value zero, has strictly
positive slope throughout, and stays below value one. No existence assumption
for the segment is used.
`exists_annular_energy_margin` chooses a positive slope margin uniformly for
all sufficiently large inner radii when the initial slope energy exceeds the
potential drop. Both theorems passed individual transitive axiom audits with
only `propext`, `Classical.choice`, and `Quot.sound`, and no source warnings.
The full build passed (3741 jobs). Continuation to value one and the remaining
rigidity/comparison obligations are still unfinished; full Comparator and
Palomar registration have not been achieved.

## Smooth extension and zero-state local flow

`ReactionSmoothExtension.lean` extends the continuous right derivative constantly
across zero and integrates it. The resulting reaction is globally continuously
differentiable and agrees with the original on every nonnegative argument.
`exists_radial_system_from_zero` then gives a local radial solution with zero
initial value and arbitrary initial slope at every positive radius. The original
radial equation holds wherever the local solution is nonnegative.
The local-flow theorem's transitive axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; source diagnostics are clean. The complete
build passed (3740 jobs). Continuation to value one, exterior comparison, the
reverse energy bound, and both rigidity proofs remain open. Full Comparator and
Palomar registration are not complete.

## Increasing annular segment estimates

`AnnularEnergy.lean` introduces explicit increasing radial ODE segment data and
proves slope monotonicity and the estimate

$$
E(a)-E(r)\le \frac{m}{a}p(a)q(r).
$$

Consequently, if the initial energy after this curvature allowance is at least
half the square of a positive constant, the slope stays above that constant and
the segment length is at most its reciprocal. `IncreasingRadialSegment.width_le`
and its dependencies passed the transitive axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`; no source warnings were reported. The full
build passed (3739 jobs). No annular solution existence is assumed or claimed:
these estimates are conditional on the displayed ODE data. The reverse Neumann
energy inequality, rigidity proofs, full Comparator, and Palomar remain open.

## Neumann energy lower bound

`BallSlopeComparison.lean` proves the tangent-ball boundary slope inequality,
its application to every radial ball profile via arbitrary-radius tangent balls,
and `RigidityHypotheses.kappa_sq_ge_twice_potential`:

$$
\kappa^2\ge 2W(0),\qquad W(s)=\int_s^1 f(t)\,dt.
$$

The boundary argument applies Fermat's one-sided derivative inequality in the
positive tangent cone to the nonnegative difference of the two solutions. The
Neumann gradient norm bounds the resulting directional derivative. The final
lower bound follows from the already proved radial boundary-energy approximation.
Its transitive axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`, with no source warnings. The full build passed (3738 jobs).
The reverse energy inequality and the two rigidity proofs remain unfinished;
full Comparator acceptance and Palomar registration are still outstanding.

## Tangent-ball comparison

`TangentBallComparison.lean` proves that every positive upward translation of a
closed ball in the closed epigraph lies inside the open epigraph. Applying the
interior-ball comparison to the translated ball and passing to zero translation
gives `RadialBallProfile.spatial_le_solution_of_closedBall_subset_closure`.
The theorem covers boundary contact without requiring positivity on that
boundary. Its transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`, with no source warnings. The full build passed (3737 jobs).
Boundary slope comparison, Bernoulli normalization, and the final rigidity
classifications remain unfinished. Full Comparator acceptance and Palomar
registration are not yet achieved.

## Compact-domain and interior-ball comparison

`nonlinear_comparison_of_compact_closure` proves boundary-to-interior comparison
for two classical solutions on a connected open domain with compact closure and
nonempty boundary, assuming the upper solution is positive on the closure and
the reaction quotient condition holds. The proof maximizes the ratio, applies
strong scaled comparison, and extends equality to the boundary to contradict a
ratio greater than one.
`RadialBallProfile.spatial_le_solution` applies it to the constructed radial ball
solutions whenever the closed ball is contained in the epigraph. Its transitive
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
source warnings. The full build passed (3736 jobs). Tangent-ball comparison and
the final rigidity proofs remain unfinished; this is not full Comparator
acceptance or Palomar registration.

## Nonlinear scaled comparison

`ScaledComparison.lean` proves the reaction scaling inequality, a linear bound
for the reaction difference, the resulting weak supersolution inequality, and
`scaled_solution_eq_of_contact`. The latter says that an ordered nonnegative
solution touching a scaled positive solution at an interior point must equal it
throughout the connected open domain. Its hypotheses include the original
reaction quotient condition, a scaling factor at least one, and a bounded scaled
solution; the Lipschitz constant is derived from the reaction regularity.
The final theorem's transitive axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no source warnings. The full build
passed (3735 jobs). Compact-ball comparison still requires the maximum-ratio
argument and boundary contradiction. Neither rigidity target is complete.

## Strong comparison infrastructure

Added `isWeakSupersolution_of_classical`, `IsWeakSupersolution.positive`, and
`IsWeakSupersolution.eq_zero_of_zero`. These convert classical differential
inequalities into weak inequalities and rule out an interior zero for a
nonnegative supersolution having a positive value on a connected open domain.
The classical conversion and zero-propagation theorem were individually audited:
only `propext`, `Classical.choice`, and `Quot.sound` occur. The complete command
`lake build SerrinEpigraph Challenge Solution` passed (3734 jobs).
This supplies the strong maximum principle needed for the ball comparison;
the nonlinear ball comparison and the two rigidity targets remain unfinished.
No full Comparator acceptance or Palomar registration is claimed.

The strict monotonicity theorem is proved. The two rigidity theorems remain
unproved, so this is not a completed three-theorem formalization or a Palomar
registration.

## Source-context correction checked locally

After restoring `RigidityHypotheses` in both the independent Challenge and the
development, `lake build SerrinEpigraph Challenge Solution` passed (3555 jobs).
The three lemmas in `NormalizedReaction.lean` elaborate without proof holes;
explicit axiom inspection reports only `propext`, `Classical.choice`, and
`Quot.sound` for each. The full target audit still rejects the two unfinished
rigidity proofs. This local build is not a new full Comparator acceptance or
Palomar registration. The earlier successful Comparator snapshot below predates
the correction and verifies only monotonicity.

## Normalized potential development

The subsequent `NormalizedPotential.lean` addition builds in the complete project
(3556 jobs). Its positivity, nonnegativity, unique-zero, first derivative, second
derivative, and positive equilibrium curvature proofs were individually audited;
each uses only `propext`, `Classical.choice`, and `Quot.sound`. This verifies the
potential lemmas, not the two still unfinished rigidity classifications.

## Uniform equilibrium estimates

`EquilibriumEstimates.lean` adds a neighborhood bound on the negative reaction
derivative, the corresponding positive potential curvature bound, and a linear
reaction lower bound below equilibrium. The full build passed (3557 jobs).
Individual axiom inspection of all three new declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`. The two main rigidity proof holes
remain; this is not full Comparator acceptance.

## Quadratic potential bound

`QuadraticPotential.lean` proves the exact linear integral, a local quadratic
potential lower bound, continuity on the closed solution interval, and a uniform
quadratic lower bound on that whole interval. The complete build passed (3571
jobs); individual axiom inspection of all four declarations found only the three
standard permitted axioms. `normalizedPotential` is exposed for use in subsequent
modules; its mathematical definition is unchanged. Both main rigidity proofs
remain unfinished.

## Two-sided potential comparison

`PotentialComparison.lean` completes the upper quadratic bound and combines it
with the lower bound on the full closed solution range. Its four declarations
were individually checked for axiom dependencies: only `propext`,
`Classical.choice`, and `Quot.sound` occur. The full project build passed (3572
jobs). The two rigidity target holes remain and still prevent full acceptance.

## Vertical ray limits

`VerticalLimit.lean` derives the vertical section derivative and strict
monotonicity, proves existence of a positive limit at most one on each ray,
and proves strict separation of every finite interior value from that limit.
All four declarations use only the standard three axioms. The complete build
passed (3573 jobs). Neither equality of the ray limits nor their identification
with one is claimed; the two main rigidity proofs are still unfinished.

## Compact translated domains

`TranslatedDomain.lean` proves eventual inclusion of each compact set under
upward translation, monotonicity between interior translates, and a positive
lower bound uniform over all sufficiently high translates on that compact set.
All four declarations were individually audited and depend only on the three
standard permitted axioms. The full build passed (3574 jobs). This does not yet
establish regularity or the equation for a translation limit, or either rigidity
classification.

## Measurable horizontal profile

`LimitProfile.lean` constructs a horizontal profile from the proved ray limits,
proves it measurable using continuous graph sections, and proves pointwise
convergence of ambient vertical translates and their reactions. Each of its
seven theorems was individually audited: only the standard three permitted
axioms occur. The full build passed (3575 jobs). No limit equation or constancy
of the profile has been assumed; those steps and both main rigidity proofs remain.

## Compact weighted integral convergence

`TranslateIntegrals.lean` proves convergence under compact weighted integration
for continuous observables of the translated solution, with explicit solution
and reaction specializations. All three declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The full build passed (3576 jobs). The
translated distributional equation has not yet been established; the two main
rigidity proofs and full Comparator acceptance remain outstanding.

## Distributional and translated equations

`DistributionalEquation.lean` proves second integration by parts, the PDE with
both derivatives on the test, translation covariance of the Laplacian, and the
eventual translated identity for each fixed compact test. All five public
theorems were individually axiom-audited and use only the three permitted
standard axioms. The full build passed (3577 jobs). The limit equation and the
two main rigidity proofs remain unfinished.

## Limit distributional equation

`LimitEquation.lean` proves that the lifted ray-limit profile satisfies the
semilinear PDE against every compactly supported C² test. Its superharmonicity
is also proved. The six public declarations, including test-support and
continuity lemmas, were individually axiom-audited and use only the standard
three permitted axioms. The full build passed (3578 jobs). Constancy of the
profile, both main rigidity classifications, full Comparator acceptance, and
Palomar registration remain unfinished.

## Polynomial ball comparison function

`PolynomialBarrier.lean` constructs a smooth squared quadratic, computes its
first and second directional derivatives and Laplacian, and proves its center,
sphere, positivity, and negative-Laplacian bounds. All eight public theorems use
only the standard three axioms. The full build passed (3579 jobs). Comparison
with the solution and the resulting identification of its ray limits remain
to be formalized; no main rigidity target has been closed by this addition.

## Local minimum and contact contradiction

`LocalMinimum.lean` proves the scalar second-derivative condition, its
directional version, the nonnegative Laplacian condition at an interior local
minimum, and the positive-contact contradiction for strict reaction/barrier
coefficient separation. All four declarations use only the standard three
axioms. The complete build passed (3581 jobs). Constructing a contact point by
compact optimization and completing the main rigidity proofs remain outstanding.

## Compact contact and comparison

`CompactContact.lean` constructs an interior scaled contact by maximizing a
continuous quotient on a compact set, then combines the contact with the local
Laplacian contradiction to prove comparison under a strict coefficient gap.
Both public declarations use only the three standard permitted axioms. The
full build passed (3582 jobs). Applying this comparison to the polynomial ball
barrier, proving the ray limits equal one, and the rigidity classifications remain.

## Vertical limits equal one

`BallLowerBound.lean` applies compact comparison to the scaled polynomial on an
interior ball. `LimitOne.lean` chooses a sufficiently large radius and translates
the ball upward to prove every ray limit equals one. All five public declarations
in these two modules were individually audited and use only the three standard
permitted axioms. The full build passed (3584 jobs). This closes identification
of the vertical limit; variational minimization, the two main rigidity proofs,
full Comparator acceptance, and Palomar registration remain unfinished.

## Inverse level heights

`LevelHeight.lean` proves existence and uniqueness of each intermediate solution
level on every vertical ray, strict monotonicity and continuity of the inverse
height in the level variable, and recovery of every original point's height.
All five theorems were individually audited and use only the standard three
axioms. The full build passed (3585 jobs). Joint regularity and the variational
calibration, as well as the two rigidity classifications, remain unfinished.

## Joint continuity of inverse heights

`LevelHeightContinuity.lean` proves comparison equivalences for inverse heights,
continuity of horizontal solution sections at interior points, and joint
continuity of the inverse height in horizontal position and solution level.
All four declarations use only the standard three axioms. The full build passed
(3586 jobs). Differentiability, calibration, and both rigidity classifications
remain unfinished; this is not full Comparator acceptance.

## Public snapshot checked

Commit: [`7a91f2313ae92019716dbaf15616fd6981e11451`](https://github.com/CoolRmal/serrin-epigraph/commit/7a91f2313ae92019716dbaf15616fd6981e11451).

On 2026-11-13 the [independent monotonicity job](https://github.com/CoolRmal/serrin-epigraph/actions/runs/43381524241/job/131740132434)
passed using the Linux sandbox and `comparator-monotonicity.json`.
This configuration checks exactly `SerrinEpigraph.verticalDerivative_pos`
against the independent `Challenge.lean` statement, with only the standard
axioms permitted.

| Check | Result |
| --- | --- |
| Build all development and specification modules | Passed |
| Monotonicity axiom audit | Only `propext`, `Classical.choice`, `Quot.sound` |
| con-ron kernel | Accepted 45,592 declarations with `--verified` |
| NanoDa kernel | Accepted |
| Lean default kernel | Accepted |
| Monotonicity Comparator | `Your solution is okay!` |
| Full three-theorem axiom audit | Rejected the two remaining `sorryAx` dependencies |
| Full three-theorem Comparator | Rejected: `Illegal axiom detected: 'sorryAx'` |
| Full Palomar preflight and registration | Not performed |

The successful check uses the ordinary sandboxed command, without the local
`--preliminary` option:

```sh
./scripts/verify-comparator.sh --config comparator-monotonicity.json
```

The original acceptance configuration remains `comparator.json` and still
selects all three pictured theorems. The separate successful check does not
replace it. See [the proof plan](proof-plan.md) and
[the rigidity audit](rigidity-gap.md) for the remaining obligations.

## Inverse height derivative

`LevelHeightDerivative.lean` extends the inverse height to real levels and proves
interior continuity, the reciprocal vertical derivative formula, and positivity
of that derivative. All four theorem declarations were audited individually:
they use only `propext`, `Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3587 jobs).
The two main rigidity proofs remain unfinished; this is not full Comparator
acceptance or Palomar registration.

## Joint inverse height regularity

`LevelHeightSmooth.lean` proves joint C² regularity of the real inverse height
at every level strictly between zero and one. It uses the implicit function
theorem and the previously proved uniqueness of the level height. The second
new theorem gives its full differential, including horizontal variations.
Both declarations were audited individually and use only `propext`,
`Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3593 jobs).
The two main rigidity proofs remain unfinished; full Comparator acceptance and
Palomar registration have not been obtained.

## Foliation gradient and pointwise energy comparison

`LevelGradient.lean` defines the level point and gradient field, proves their
C²/C¹ regularity, their recovery of the original solution point and gradient,
strict positivity of the vertical gradient component, and explicit differential
formulas. The affine energy expression lies below the energy density and attains
it on the original solution. All eleven new theorem declarations were audited
individually: only `propext`, `Classical.choice`, and `Quot.sound` occur.
`lake build SerrinEpigraph Challenge Solution` passed (3594 jobs).
The divergence identity and integrated minimization argument are not yet proved.
The two main rigidity theorems, full Comparator acceptance, and Palomar
registration remain unfinished.

## Foliation equation and calibration cancellation

`FoliationEquation.lean` proves the differential along a solution leaf, the
Laplacian trace formula, and the chain-rule equation for the foliation gradient.
Combining it with the level derivative of the energy component gives the
calibration divergence cancellation identity. All five declarations were
audited individually and use only `propext`, `Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3595 jobs).
This does not yet prove integrated calibration or local energy minimization.
Both rigidity proofs, full Comparator acceptance, and Palomar registration
remain unfinished.

## Integrated identity along comparison functions

`VectorIntegrationByParts.lean` proves vector integration by parts near a compact
test support and its zero-divergence consequence. `FoliationPullback.lean` proves
regularity, the derivative and trace formula, and the resulting integral
identity for the foliation gradient evaluated along an arbitrary C¹ comparison
function with values in (0,1). All six public theorem declarations were audited:
only `propext`, `Classical.choice`, and `Quot.sound` occur.
`lake build SerrinEpigraph Challenge Solution` passed (3597 jobs).
Constancy of calibrated energy along comparison paths and local energy
minimization remain unproved. The two rigidity theorems, complete Comparator
acceptance, and Palomar registration remain unfinished.

## Vanishing integrated first variation

`CalibrationVariation.lean` defines the calibrated density, proves its chain
rule along differentiable level/gradient paths, and proves its integrated first
variation is zero for compact variations. Its pointwise upper bound by the
ordinary energy and equality on the solution are recorded as named lemmas.
`VectorIntegrationByParts.lean` also now proves the integrable sum form of the
vector first-variation identity. All five new public theorem declarations were
audited individually: only `propext`, `Classical.choice`, and `Quot.sound` occur.
`lake build SerrinEpigraph Challenge Solution` passed (3598 jobs).
Differentiation under the integral and constancy along comparison paths remain
to be established. Both rigidity proofs, full Comparator acceptance, and Palomar
registration remain unfinished.

## Differentiation of the calibrated energy integral

`CalibrationIntegral.lean` proves a uniform admissible variation interval on a
compact spatial set, establishes the continuity and uniform control needed for
differentiation under the integral, and proves that the calibrated energy
integral has derivative zero for compact variations. It reuses the existing
compact-cylinder differentiation theorem from `WeakLinearization.lean`.
All four new declarations were audited individually and use only `propext`,
`Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3599 jobs).
Constancy along full comparison paths and the resulting energy inequality
remain to be proved. Both rigidity theorems, full Comparator acceptance, and
Palomar registration remain unfinished.

## Interior energy minimality

`CalibrationPath.lean` proves zero derivative at each admissible path parameter,
constancy between the endpoints, and energy minimality against C¹ perturbations
compactly supported inside the epigraph whose perturbed solution stays in (0,1).
The comparison uses the actual gradient of the perturbed function. All four
new declarations were audited individually and use only `propext`,
`Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3600 jobs).
This is fixed-domain interior minimality; it does not yet establish the
free-boundary minimization permitting changes of positive phase. Both rigidity
proofs, full Comparator acceptance, and Palomar registration remain unfinished.

## Closed-range interior comparisons

`ClosedRangeMinimality.lean` proves continuity of compact spatial integrals on
compact parameter sets and uses it to extend interior energy minimality to C¹
compact perturbations whose resulting values lie in [0,1]. The proof approximates
such perturbations by strict-range ones and passes the energy inequality to
the endpoint. Both declarations use only `propext`, `Classical.choice`, and
`Quot.sound`, as checked individually.
`lake build SerrinEpigraph Challenge Solution` passed (3601 jobs).
Perturbations are still supported strictly inside the original epigraph;
free-boundary comparison, both rigidity proofs, full Comparator acceptance,
and Palomar registration remain unfinished.

## Zero-level boundary trace

`LevelBoundary.lean` proves joint continuity of the total inverse height and
level point at level zero. The gradient defined using the differential within
the closed epigraph is continuous there, agrees with the interior foliation
gradient at intermediate positive levels, and is its boundary trace. The
vertical component at level zero is identified using the Neumann condition.
All ten new theorem declarations were audited and use only `propext`,
`Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3602 jobs).
Cross-boundary energy comparison and the two rigidity proofs remain unfinished,
as do full Comparator acceptance and Palomar registration.

## Full boundary gradient and calibration energy trace

`BoundaryGradient.lean` proves that the outward normal is a unit vector and
that the complete boundary gradient is minus κ times that normal. Its norm is
therefore κ. The energy component of the foliation field converges to the
constant κ²/2 − W(0) at level zero; no identity making this constant vanish has
been assumed. All eight declarations were audited individually and use only
`propext`, `Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3603 jobs).
Cross-boundary comparison and both rigidity proofs remain unfinished, as do
full Comparator acceptance and Palomar registration.

## Whole-space zero extension

`ZeroExtension.lean` constructs the solution extended by zero outside the
epigraph. It proves global continuity, nonnegativity, the exact positive phase,
the upper bound by one, interior and exterior gradient identities, vertical
monotonicity and limit one, and the original PDE in the positive phase.
All fifteen new declarations were audited individually and use only `propext`,
`Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3604 jobs).
No boundary differentiability or cross-boundary energy minimality is claimed.
Both rigidity proofs, full Comparator acceptance, and Palomar registration
remain unfinished.

## Cross-boundary local Lipschitz regularity

`ZeroExtensionRegularity.lean` flattens the C¹ epigraph boundary, transfers the
solution to a convex closed half-space, and identifies the zero extension with
the solution composed with vertical clamping. This proves local Lipschitz
regularity across the original boundary and a finite Lipschitz constant on
every compact set. All six public theorem declarations were audited and use
only `propext`, `Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3605 jobs).
Cross-boundary energy minimality and both rigidity theorems remain unfinished;
full Comparator acceptance and Palomar registration have not been obtained.

## Almost-everywhere derivatives and null boundary

`ZeroExtensionDifferentiability.lean` applies Rademacher on a countable compact
cover to prove almost-everywhere differentiability of the zero extension. It
identifies its totalized gradient with the original gradient extended by zero.
The nonzero Neumann slope rules out differentiability at every graph point;
therefore the frontier is an ambient-volume null set. All six declarations were
audited individually and use only `propext`, `Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3683 jobs, including the
new Rademacher dependencies).
Cross-boundary energy minimality, both rigidity proofs, full Comparator
acceptance, and Palomar registration remain unfinished.

## Finite local phase energy

`PhaseEnergy.lean` proves that the squared gradient and positive-phase energy
of the zero extension are integrable on every compact ambient set. The
whole-space energy integral equals the original interior energy integral.
The additive energy constant remains explicit: no Bernoulli normalization is
assumed. All seven public theorem declarations were individually audited and
use only `propext`, `Classical.choice`, and `Quot.sound`.
`lake build SerrinEpigraph Challenge Solution` passed (3684 jobs).
Cross-boundary energy minimality, both rigidity proofs, full Comparator
acceptance, and Palomar registration remain unfinished.

## Calibration inequality across the zero phase

`BoundaryCalibration.lean` shifts the closed foliation calibration by the
actual boundary energy constant. It proves that this density vanishes at
zero level and zero gradient, that its deficit from the shifted energy is
half the squared gradient mismatch, and that it bounds the positive-phase
energy of every globally nonnegative competitor pointwise. The original
zero extension attains equality everywhere, including outside the epigraph.
No identity setting the energy offset to zero is assumed.
All four theorem declarations were audited and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The complete build passed (3685 jobs).
The integrated cross-boundary comparison, both rigidity proofs, full Comparator
acceptance, and Palomar registration remain unfinished.

## Integrable calibration for competitors touching zero

`BoundaryCalibrationIntegral.lean` proves continuity of the closed foliation
field on the level strip [0,1), continuity and compact-set integrability of
the calibration density for smooth competitors in that range, and compact-set
integrability of phase energy for smooth competitors in [0,1]. The pointwise
calibration inequality therefore integrates for smooth competitors that may
touch zero. All five new theorems were audited individually and use only
`propext`, `Classical.choice`, and `Quot.sound`. The complete build passed
(3686 jobs).
This does not yet prove invariance of the calibration integral when the
positive phase changes, or cross-boundary energy minimality. Both rigidity
proofs, full Comparator acceptance, and Palomar registration remain unfinished.

## Closed-level calibration invariance for smooth competitors

`ClosedCalibrationPath.lean` proves that compact smooth variations between
globally C¹ functions taking values in [0,1) preserve the closed calibration
integral. Both endpoints may vanish and their positive phases may differ.
The proof lifts each endpoint toward one half, applies the positive-level
path identity, and passes to zero regularization through continuity of the
compact-set integrals. All five new theorems were individually audited and
use only `propext`, `Classical.choice`, and `Quot.sound`. The full build passed
(3687 jobs).
The zero extension is locally Lipschitz, not globally C¹, so the new identity
does not yet apply to it. Extension to that regularity, free-boundary energy
minimality, both rigidity proofs, full Comparator acceptance, and Palomar
registration remain unfinished.

## Stability of calibration integrals under bounded approximation

`CalibrationConvergence.lean` proves convergence of compact-set calibration
integrals under almost-everywhere convergence of levels and vector fields,
assuming continuous approximating fields, a uniform level bound below one,
and a uniform vector bound on the compact set. Compactness supplies the
integrable domination, including at level zero. The limiting fields need not
be smooth. A specialization identifies the limiting calibration integral
with the phase energy of the zero extension, when a smooth approximation
with convergent gradients and these bounds is supplied.
Both new theorems were audited and use only `propext`, `Classical.choice`, and
`Quot.sound`. The complete build passed (3688 jobs).
The approximation sequence and its gradient convergence have not yet been
constructed. Free-boundary energy minimality, both rigidity proofs, full
Comparator acceptance, and Palomar registration remain unfinished.

## Explicit smooth approximation of the zero extension

`Mollification.lean` defines normalized smooth averaging kernels with outer
radius 1/(n+1), their convolution with a continuous function, and a contraction
by 1-1/(n+2). It proves smoothness, preservation of nonnegativity and constant
upper bounds, and pointwise convergence. Applied to the zero extension, the
contracted sequence consists of smooth functions valued in [0,1) and converges
to the extension at every point.
All nine new theorems were audited and use only `propext`, `Classical.choice`,
and `Quot.sound`. The complete build passed (3691 jobs).
Uniform compact gradient bounds, convergence of gradients, and support control
for comparison pairs remain to be proved before applying calibration stability.
Free-boundary energy minimality, both rigidity proofs, full Comparator acceptance,
and Palomar registration remain unfinished.

## Uniform compact bounds for the smooth approximations

`MollificationBounds.lean` proves a translated-difference estimate for averaging,
then shows that a Lipschitz bound on a larger closed ball controls all averages
on the smaller ball. The normalization contraction preserves this bound.
Applied to the locally Lipschitz zero extension, this gives a common gradient
bound for every approximation on each compact set. A separate local averaging
estimate and the extreme value theorem provide a common level bound strictly
below one on each compact set.
All seven new theorems were individually audited and use only `propext`,
`Classical.choice`, and `Quot.sound`. The full build passed (3692 jobs).
Almost-everywhere gradient convergence and support control for comparison pairs
remain. Free-boundary energy minimality, both rigidity proofs, full Comparator
acceptance, and Palomar registration remain unfinished.

## Uniform support control for mollified comparison pairs

`MollificationSupport.lean` proves that averaging enlarges a ball containing
the support of a perturbation by at most one, uniformly in the approximation
index. It establishes the corresponding topological support bound and
additivity of normalized convolution for continuous functions. Consequently,
for a continuous compact comparison pair valued in [0,1], all smoothed pairs
have equal closed calibration integrals on a single fixed ball.
All five new theorems were audited individually and use only `propext`,
`Classical.choice`, and `Quot.sound`. The full build passed (3693 jobs).
Almost-everywhere gradient convergence remains necessary to pass the integral
identity to the original pair. Free-boundary energy minimality, both rigidity
proofs, full Comparator acceptance, and Palomar registration remain unfinished.

## Gradient convergence and recovery of the original phase energy

`MollificationDerivative.lean` proves commutation of differentiation and
averaging for compactly supported C¹ functions, convergence of their averaged
derivatives, and locality of mollification. Compact localization extends
gradient convergence to every point of an open C¹ region. Applied to the
zero extension in the interior and exterior, with the already-null frontier
removed, this yields almost-everywhere convergence of the explicit normalized
mollification gradients. The established compact bounds now imply convergence
of its calibration integrals to the original phase energy, with no additional
approximation hypotheses.
All eleven new theorems were individually audited and use only `propext`,
`Classical.choice`, and `Quot.sound`. The complete build passed (3694 jobs).
The analogous limit for the perturbed comparison function remains before the
pair identity yields free-boundary energy minimality. Both rigidity proofs,
full Comparator acceptance, and Palomar registration remain unfinished.

## Calibration identity for perturbed zero extensions

`PerturbedCalibration.lean` proves almost-everywhere convergence of the
averaged gradients of a smooth perturbation of the zero extension. It provides
uniform compact gradient and level bounds and hence convergence of the
competitor's calibration integrals. Passing the smoothed-pair identities to
the limit shows that a compact C¹ perturbation with values in [0,1) has the
same calibration integral as the original phase energy. The conclusion
explicitly includes containment of the original perturbation support in the
integration ball; perturbations may cross the original boundary.
All seven new theorems were individually audited and use only `propext`,
`Classical.choice`, and `Quot.sound`. The complete build passed (3695 jobs).
Integrability of the competitor phase energy and integration of the pointwise
energy inequality remain before claiming free-boundary minimality. Both
rigidity proofs, full Comparator acceptance, and Palomar registration remain
unfinished.

## Cross-boundary energy comparison for compact C¹ perturbations

`CrossBoundaryMinimality.lean` proves compact-set integrability of the perturbed
gradient, its square, phase energy, and calibration density. Integrating the
pointwise calibration bound and using the limiting calibration identity gives
energy comparison on a containing ball. Equality of the two energies outside
the perturbation support transfers this comparison to every compact set
containing that support. The perturbation need not be supported inside the
original epigraph.
The precise result concerns compact C¹ perturbations whose perturbed zero
extension takes values in [0,1), and retains the shift κ²/2 − W(0) in the phase
energy. No claim for all Lipschitz competitors or a vanishing shift is made.
All eight new theorems were individually audited and use only `propext`,
`Classical.choice`, and `Quot.sound`. The full build passed (3697 jobs).
Broader competitor classes, Bernoulli normalization, both rigidity proofs,
full Comparator acceptance, and Palomar registration remain unfinished.

## Interior and exterior tangent balls

`TangentBalls.lean` proves a general contact construction along a continuous
path using the distance to a closed set and a nearest point. Applied to entire
epigraphs, compact upward and downward translations produce interior and
exterior tangent balls of every positive radius, centered on the vertical
axis. The contact points lie on the original graph boundary. Only continuity
of the graph is used; no global slope bound is imposed.
This supplies the geometric input to the boundary-slope comparisons in
[Wang–Wei §5, Lemmas 5.3–5.4](https://arxiv.org/html/1502.04680#S5).
The radial comparison solutions, their large-radius limits, and the slope
inequalities are not yet formalized, so Bernoulli normalization remains open
in this Lean development.
All five new theorems were individually audited and use only `propext`,
`Classical.choice`, and `Quot.sound`. The complete build passed (3698 jobs).
Both rigidity proofs, full Comparator acceptance, and Palomar registration
remain unfinished.

## Radial profile energy dissipation

`RadialEnergy.lean` defines radial ball-profile data with the differential
equation, regular center slope, zero boundary value, and normalized range
explicitly included. It proves the exact energy derivative, monotonicity
from the center to the boundary, a boundary slope bound (strict when the
central value is below equilibrium), and the integrated curvature-energy
loss on intervals away from the radial origin.
These are conditional estimates for a supplied profile, not a proof that
radial comparison solutions exist. No profile existence or external PDE
theorem is introduced as an axiom.
All six new theorems were audited individually and use only `propext`,
`Classical.choice`, and `Quot.sound`. The complete build passed (3699 jobs).
Radial profile existence, large-radius limits, boundary slope comparisons,
Bernoulli normalization, both rigidity proofs, full Comparator acceptance,
and Palomar registration remain unfinished.

## Weighted radial flux and decreasing profiles

`RadialFlux.lean` proves that multiplication by the radial volume weight
cancels the singular drift term, yielding a flux identity integrated from
the center. The weighted flux is nonincreasing; consequently slopes are
nonpositive, values decrease toward the boundary, and the central value is
positive. The mean value theorem and flux monotonicity give a strictly
negative boundary slope.
All seven theorems are conditional on the explicit radial profile data;
profile existence is not inferred from these estimates. Each declaration
was audited and uses only `propext`, `Classical.choice`, and `Quot.sound`.
The full build passed (3700 jobs).
Radial existence and large-radius limits, boundary comparison, Bernoulli
normalization, both rigidity proofs, full Comparator acceptance, and Palomar
registration remain unfinished.

## Nonsingular radial integral operator

`RadialIntegral.lean` adds eight proved theorems for the weighted average
and radial Picard operator, including the quadratic size and difference
estimates with dimension factor 1/(m+1). LSP diagnostics are clean and the
full `lake build SerrinEpigraph Challenge Solution` passed (3701 jobs).
Each new theorem was checked by `#print axioms`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No new proof holes were added.
The two existing rigidity proof holes remain. This is operator infrastructure,
not an existence theorem. Full Comparator acceptance and Palomar registration
remain outstanding.

## Local radial fixed-point construction

`RadialFixedPoint.lean` proves five theorems: continuity of constant endpoint
extension, the quadratic Lipschitz estimate in the continuous-function sup
metric, existence and uniqueness of the short-interval integral solution, and
existence of a continuous profile satisfying the averaged derivative equation
with prescribed central value and zero central derivative. The forcing here
is globally Lipschitz; this is an auxiliary existence theorem, not a change
to either rigidity target's reaction assumptions.
LSP diagnostics are clean. The full build passed (3702 jobs). All five new
theorems were audited with `#print axioms` and use only `propext`,
`Classical.choice`, and `Quot.sound`. No new proof holes were introduced.
The second-order equation, connection to the original reaction, large-radius
profiles, both rigidity proofs, full Comparator, and Palomar registration remain.

## Local profiles under the original reaction assumptions

`RadialReactionExtension.lean` proves six theorems: agreement and Lipschitz
control of the constant endpoint reaction extension, existence of such a
Lipschitz bound for a C¹ reaction on a compact interval, existence of a positive
contraction radius, a local averaged radial solution remaining inside the
original value interval, and specialization to the project's `Hypotheses`
with any central value strictly between zero and one.
All six theorems have clean diagnostics and use only `propext`,
`Classical.choice`, and `Quot.sound`, as checked by `#print axioms`.
The full build passed (3703 jobs). Neither main theorem was altered and no
new proof holes were added. The second-order radial equation, global profiles
and asymptotics, both rigidity proofs, full Comparator acceptance, and Palomar
registration remain unfinished.

## Second-order radial system

`RadialEquation.lean` proves six theorems: the weighted rescaling identity,
the primitive formula for the slope, its derivative formula for continuous
forcing, the corresponding local-interval derivative formula, slope continuity
on the closed radius interval, and existence of a local radial value/slope
system under the original project hypotheses. The system satisfies the
second-order radial equation away from zero, has the prescribed central value
and zero central slope, and remains strictly between zero and one locally.
All six declarations have clean diagnostics and standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`). The complete build passed
(3704 jobs). No main statement changed and no new proof holes were added.
This is a local initial-value construction: the Dirichlet boundary condition,
large-radius profiles and limits, both rigidity proofs, full Comparator, and
Palomar registration remain outstanding.

## Radial local flow away from the center

`RadialLocalFlow.lean` defines the autonomous radius/value/slope vector field
and proves it is C¹ at nonzero radius whenever the reaction is C¹ at the
initial value. Picard–Lindelöf gives a local flow; derivative uniqueness for
the radius coordinate identifies it with time. The resulting theorem gives
local radial-system solutions at every positive radius with arbitrary slope.
Its specialization to the project hypotheses shrinks the interval to keep
both radius and value positive.
All three theorems use only the standard axioms, checked with `#print axioms`.
The full build passed (3710 jobs), with no new proof holes. This does not yet
prove uniqueness/gluing or global continuation of an existing profile.
Large-radius comparisons, both rigidity proofs, full Comparator acceptance,
and Palomar registration remain incomplete.

## Radial uniqueness on common connected domains

`RadialUniqueness.lean` proves four theorems: local uniqueness for a C¹
autonomous field, local uniqueness of the radial value/slope system, its
specialization to the original hypotheses at positive states, and agreement
throughout a connected open domain when two radial states agree at one point.
The last proof uses local uniqueness to make the equality set open and
continuity to make it closed. This is agreement of both values and slopes.
All four declarations have clean diagnostics and only `propext`,
`Classical.choice`, and `Quot.sound` in their axiom audits. The full build
passed (3711 jobs). No target signatures or proof holes were changed.
Actual gluing and continuation, large-radius comparisons, both rigidity
proofs, full Comparator acceptance, and Palomar registration remain unfinished.

## Gluing radial systems

`RadialGluing.lean` introduces `IsRadialSystemOn` and proves five theorems:
restriction, local agreement of piecewise branches on an overlap, preservation
of the radial equations under gluing, existence of a glued system from a
single matching state on a connected overlap, and gluing a local positive
restart to an existing system on an open interval. The construction preserves
both value and slope on the entire original domain.
All five declarations have clean diagnostics and only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The full build passed (3712 jobs).
No new proof holes or target changes were introduced. Restarting at an interior
point does not assert strict enlargement of the domain; finite-endpoint limits
and outward continuation remain. Large-radius comparisons, both rigidity
proofs, full Comparator acceptance, and Palomar registration are still incomplete.

## Finite endpoint limits with bounded slope

`RadialEndpoint.lean` proves seven theorems: a value Lipschitz bound from
bounded slope, the slope derivative bound away from zero, the corresponding
slope Lipschitz bound, finite limits of Lipschitz functions, finite radial
value/slope limits with bounded forcing, boundedness of the original reaction
on [0,1], and finite radial endpoint limits under the original hypotheses
with normalized values and bounded slope.
All seven proofs have clean diagnostics and standard axioms only, checked
with `#print axioms`. The complete build passed (3713 jobs). No proof holes
or target changes were added. The endpoint results still require a slope
bound; they do not assert positive endpoint value or continuation across it.
Those steps, large-radius comparisons, both rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Energy-derived slope bounds and unconditional finite endpoint limits

`RadialBounds.lean` proves three theorems: radial energy monotonicity on
convex positive-radius domains, a slope bound to the right of any interior
radius derived from energy and compact potential bounds, and finite left
limits for both value and slope of normalized radial systems under the
original hypotheses. The last theorem no longer assumes bounded slope;
it also proves the value limit belongs to [0,1].
All three declarations have clean diagnostics and only standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The full build passed (3714 jobs).
No new proof holes or main-statement changes were introduced. These results
do not yet give the differential equation at the endpoint or an extension
past it. Those steps, large-radius comparisons, both rigidity proofs, full
Comparator acceptance, and Palomar registration remain unfinished.

## Differential equations at a completed finite endpoint

`RadialEndpointDerivative.lean` proves four theorems: changing an endpoint
value preserves derivatives elsewhere, completion by a left limit has the
limiting left derivative, both radial equations hold from the left for
completed components, and normalized radial systems under the original
hypotheses admit such completed endpoints. The final result includes endpoint
value zero; it uses reaction continuity within the nonnegative half-line
rather than assuming continuity from negative values.
All four declarations have clean diagnostics and standard axioms only.
The full build passed (3715 jobs), and `#print axioms` audits report only
`propext`, `Classical.choice`, and `Quot.sound`. No new proof holes were added.
Cross-endpoint continuation, large-radius comparisons, both rigidity proofs,
full Comparator acceptance, and Palomar registration remain incomplete.

## Finite radial Dirichlet existence

`RadialRiccati.lean` proves the logarithmic-slope equation, an arctangent
derivative bound, nonexistence of global positive normalized radial systems,
and existence of a finite Dirichlet ball profile for every central value in
(0,1). All five theorem declarations were checked with `#print axioms`;
their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The full build passed (3723 jobs). The two main rigidity proofs still contain
`sorry`; the three independent Challenge declarations are statement placeholders.
Radius control, large-radius comparisons, both rigidity proofs, full Comparator
acceptance, and Palomar registration remain incomplete.

## Continuation beyond a finite positive endpoint

`RadialContinuation.lean` proves five theorems: local agreement with each
splice branch, differentiability at the splice from matching one-sided
and full derivatives, actual extension beyond a positive completed endpoint,
and the zero-limit-or-continuation alternative for normalized radial systems.
The new system preserves both original components throughout the old interval
and satisfies both equations at the junction, not only away from it.
All five declarations have clean diagnostics and only standard axioms, checked
with `#print axioms`. The full build passed (3716 jobs). No new proof holes
or main-statement changes were introduced. Maximal profiles, prescribed-radius
Dirichlet solutions and large-radius comparisons, both rigidity proofs, full
Comparator acceptance, and Palomar registration remain incomplete.

## Strict decrease of regular central radial solutions

`RadialDecrease.lean` proves six theorems: strictly decreasing weighted flux,
negative slope at positive radii, strictly decreasing value on closed radius
intervals, existence of a decreasing local central solution, strict decrease
on half-open intervals, and a finite endpoint limit strictly below the central
value. These results do not assume a zero Dirichlet boundary value.
All six declarations have clean diagnostics and standard axioms only, checked
with `#print axioms`. The complete build passed (3717 jobs). No proof holes
or main-statement changes were added. Maximal profiles, first-zero/radius
control and large-radius comparisons, both rigidity proofs, full Comparator
acceptance, and Palomar registration remain incomplete.

## Normalized continuation preserving the central data

`RadialNormalizedContinuation.lean` proves three theorems: continuation with
values in (0,1) when the endpoint value is interior, continuity of a center
update on the enlarged interval, and the zero-limit-or-normalized-continuation
alternative for regular central profiles. The final theorem preserves value
and slope on the full old half-open interval, including the center, and
proves continuity of both components on the enlarged half-open interval.
All three declarations have clean diagnostics and standard axioms only,
verified by `#print axioms`. The full build passed (3718 jobs). No new proof
holes or main-statement changes were introduced. Maximal positive profiles,
first-zero/radius control, large-radius comparisons, both rigidity proofs,
full Comparator acceptance, and Palomar registration remain incomplete.

## Zero endpoint completion as a Dirichlet ball profile

`RadialZeroEndpoint.lean` proves three theorems: closed-interval continuity
from endpoint completion, construction of a `RadialBallProfile` from a
normalized central solution with zero endpoint limit, and a combined
ball-profile-or-normalized-extension alternative. The ball branch has
strictly negative boundary slope and its squared slope is strictly below
twice the potential at zero. It preserves both original components on the
old half-open interval.
All three declarations have clean diagnostics and standard axioms only,
checked with `#print axioms`. The complete build passed (3719 jobs). No
proof holes or main-statement changes were added. This remains conditional
on a finite zero endpoint; maximal profiles, first-zero existence and radius
control, large-radius comparisons, both rigidity proofs, full Comparator,
and Palomar registration remain incomplete.

## Unions of compatible central radial profiles

`RadialUnion.lean` defines a branch-selected union and proves eight theorems:
agreement on each branch, local agreement at positive radii, continuity on
the whole union including the center, preservation of the radial system,
central values and normalized range, and identification of both half-open
and positive union domains with the interval ending at the radius supremum
when the radii are bounded. Compatibility is an explicit input here.
All eight declarations have clean diagnostics and standard axioms only,
checked by `#print axioms`. The full build passed (3720 jobs). No new proof
holes or main-statement changes were introduced. A maximal compatible family,
first-zero existence/radius control, large-radius comparisons, both rigidity
proofs, full Comparator acceptance, and Palomar registration remain incomplete.

## The bounded maximal-radius branch

`RadialBranches.lean` defines normalized central branches and extensions of
a fixed seed, proves seed existence from the original reaction assumptions,
and proves every pair of seed extensions agrees on its full common domain.
The extension family is nonempty. For bounded radii, it constructs the union
as an extension at their supremum and proves existence of a Dirichlet ball
profile there by ruling out further extension. The resulting ball profile
preserves both seed components on the entire seed interval.
All four theorem declarations and both explicit construction definitions were
audited; only `propext`, `Classical.choice`, and `Quot.sound` occur.
Diagnostics are clean and the full build passed (3721 jobs). No new proof
holes or main-statement changes were introduced. The unbounded-radius
alternative, first-zero radius control, large-radius comparisons, both rigidity
proofs, full Comparator acceptance, and Palomar registration remain incomplete.

## The unbounded-radius alternative

`RadialGlobal.lean` proves four theorems: identification of the two union
domains for unbounded radii, construction of a global normalized radial system
from unbounded seed extensions, and the unconditional ball-or-global
alternative for every central value in (0,1). The global system retains
continuity at the center, central value, zero central slope, normalized
positive values, and both radial differential equations at positive radii.
All four declarations have clean diagnostics and standard axioms only,
checked by `#print axioms`. The full build passed (3722 jobs). No new proof
holes or main-statement changes were introduced. Excluding the global branch,
first-zero radius control, large-radius comparisons, both rigidity proofs,
full Comparator acceptance, and Palomar registration remain incomplete.

## Uniform radial slope and outer-region energy bounds

`RadialSlopeBound.lean` proves five declarations: potential monotonicity,
the squared and absolute slope bounds throughout the closed ball, and two
outer-region energy-loss bounds. All five passed LSP diagnostics and axiom
verification with only `propext`, `Classical.choice`, and `Quot.sound`.
The full build passed (3724 jobs). No main statements were changed. The two
main rigidity proofs remain incomplete, as do full Comparator acceptance
and Palomar registration. The next analytic step is inner-region control
as the central value tends to equilibrium and the corresponding radius limit.

## Quantitative radial equilibrium and radius control

`RadialEquilibrium.lean` proves five theorems: a slope bound proportional
to the equilibrium deficit, exponential control of that deficit, its lower
bound in terms of the boundary radius, a uniform constant for all profiles,
and an explicit criterion forcing the radius above any prescribed threshold.
All five have clean diagnostics and standard axioms only, verified with
the Lean axiom checker. The full build passed (3725 jobs). Both final rigidity
proofs, full Comparator acceptance, and Palomar registration remain unfinished.
## Arbitrarily large balls with asymptotically sharp boundary energy

`RadialBoundaryEnergy.lean` proves four theorems: the boundary-energy deficit
bound by an inner potential and outer loss, its exponential version, uniform
epsilon control as the central value approaches one, and existence of
arbitrarily large ball profiles with arbitrarily small boundary-energy error.
All four passed diagnostics and axiom verification using only `propext`,
`Classical.choice`, and `Quot.sound`. The full build passed (3726 jobs).
This is an ODE comparison-profile result; the spatial PDE comparison and
Hopf steps, the annulus construction, both final rigidity proofs, full
Comparator acceptance, and Palomar registration remain incomplete.

## Spatial realization of radial profiles

`RadialSpatial.lean` defines the centered spatial profile and proves seven
theorems: the Euclidean norm derivative, closed-ball continuity and range,
zero boundary data, interior positivity, and derivative/gradient formulas
away from the center. All seven have clean diagnostics and only the standard
three axioms. The full build passed (3727 jobs). Center regularity, the
Laplacian formula, spatial comparison/Hopf arguments, annulus construction,
both final rigidity proofs, full Comparator acceptance, and Palomar
registration remain unfinished.

## First-order center regularity

`RadialCenter.lean` proves seven theorems covering the zero right derivative,
composition with distance at the center, differentiability throughout the
ball, zero central gradient, the gradient norm formula, and central gradient
continuity. All seven passed diagnostics and axiom verification with only
the standard three axioms. The full build passed (3728 jobs).
Second-order spatial regularity and the Laplacian identity remain pending,
along with comparison/Hopf arguments, annulus construction, both final
rigidity proofs, full Comparator acceptance, and Palomar registration.

## Central radial slope ratio and derivative

`RadialSlopeRatio.lean` proves six theorems: the weighted average at zero,
its continuity on the closed radius interval, the slope/average identity,
the central slope-ratio limit, the central slope-derivative limit, and the
right derivative of the slope at zero. All six have clean diagnostics and
only the standard three axioms. The full build passed (3729 jobs).
The spatial Hessian and Laplacian formulas, comparison/Hopf arguments,
annulus construction, both final rigidity proofs, full Comparator acceptance,
and Palomar registration remain unfinished.

## Central spatial Hessian and PDE identity

`RadialHessianCenter.lean` proves five theorems: differentiation of a continuous
coefficient times displacement, a division-free averaged gradient formula,
the isotropic gradient derivative at the center, the general gradient-trace
formula, and the original semilinear equation at the center. All five have
clean diagnostics and only the standard three axioms. The full build passed
(3730 jobs). Off-center second-order formulas, full second-order continuity,
comparison/Hopf arguments, annulus construction, both final rigidity proofs,
full Comparator acceptance, and Palomar registration remain unfinished.

## Spatial equation throughout the ball

`RadialHessian.lean` proves six theorems: differentiation of radial vector
fields, the slope-ratio derivative, the off-center spatial Hessian, its trace,
the off-center semilinear equation, and the equation on the entire open ball.
All six passed diagnostics and axiom verification with only the standard
three axioms. The full build passed (3731 jobs). Full second-order continuity,
boundary regularity, comparison/Hopf arguments, annulus construction, both
final rigidity proofs, full Comparator acceptance, and Palomar registration
remain unfinished.

## Spatial C1 and punctured-ball C2 regularity

`RadialRegularity.lean` proves five theorems: differentiability of the gradient
on the ball, continuity of the spatial derivative, C1 regularity on the ball,
off-center Hessian continuity, and C2 regularity on the punctured ball.
All five have clean diagnostics and only the standard three axioms.
The full build passed (3732 jobs). Central Hessian continuity, boundary
regularity, comparison/Hopf arguments, annulus construction, both final
rigidity proofs, full Comparator acceptance, and Palomar registration remain
unfinished.

## Full open-ball C2 regularity

`RadialHessianContinuity.lean` proves five theorems: a rank-one operator norm
bound, vanishing of its singular-looking correction, central Hessian
continuity, Hessian continuity on the ball, and C2 regularity throughout the
open ball. All five have clean diagnostics and only the standard three
axioms. The full build passed (3733 jobs). Boundary regularity, comparison/Hopf
arguments, annulus construction, both final rigidity proofs, full Comparator
acceptance, and Palomar registration remain unfinished.

## Closed-ball regularity and normal derivative

`RadialBoundaryDerivative.lean` proves six theorems: the profile's left
boundary derivative, the spatial boundary differential, unique differentials
on a closed ball, the normal derivative formula, the averaged closed-ball
differential, and C1 regularity up to the boundary. All six have clean
diagnostics and only the standard three axioms. The full build passed
(3734 jobs). Comparison with the epigraph solution, the annulus construction,
both final rigidity proofs, full Comparator acceptance, and Palomar
registration remain unfinished.

