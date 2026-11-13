# Proof obligations

## Geometric classification after minimality

`PartitionOverlap.lean` sums pairwise profile differences with the partition
weights, preserving their total mass one rather than introducing a patch-count
factor. Only pairs whose weights are both positive need a discrepancy estimate.
For graph scales bounded by H with nearby inverses on active overlaps, it bounds
the mixture potential defect by a single common-layer indicator. This connects
the scale-mismatch estimate to finite mixtures. Integration of this common-layer
bound, weighted principal energy bounds, and geometric parameter selection
remain necessary for sharp recovery.

`RecoveryScaleMismatch.lean` proves that profiles with positive graph scales
L and M differ only inside their larger transition layer. The integral of
their absolute difference multiplied by the blow-down scale R is bounded by
the profile speed bound times `(T * max L M)^2 * |L⁻¹ - M⁻¹|`, independently
of R. The Euclidean graph-cylinder version multiplies this bound by projected
base volume. For fixed regularization, this controls potential errors as patch
scales approach one another. A finite-cover overlap estimate and a diagonal
choice of cover, regularization, and blow-down scale remain to be assembled.

`PartitionGradientEnergy.lean` bounds the squared norm of a weighted gradient
by the weighted squared norms, with total weight at most one. The recovery
kinetic estimate has an arbitrarily small multiplicative loss and the separate
weight-gradient error; it also holds almost everywhere for locally Lipschitz
inputs. `PartitionPotentialEnergy.lean` derives a Lipschitz constant for the
normalized potential from the reaction assumptions and bounds the potential
defect by weighted profile differences. This does not assume convexity of the
potential. The potential error is multiplied by the blow-down scale in the
energy, so unscaled L1 convergence alone does not make it vanish: quantitative
control of the overlap profiles is still required.

`PartitionRecovery.lean` defines finite weighted recovery competitors, proves
their normalized range and common-phase local L1 convergence, and separates
their gradient into profile and weight contributions. For fixed C1 weights,
the integral of the squared weight-gradient contribution divided by the
blow-down scale tends to zero on every compact set. The potential need not be
convex: a sharp bound for the potential of a weighted mixture is still needed,
as are weighted profile-gradient estimates and perimeter identification.

`GraphPartition.lean` constructs smooth compactly supported weights subordinate
to the finite half-radius ball cover. They are nonnegative, sum to one on the
compact base, and sum to at most one everywhere. The construction also handles
an empty base and empty index set. Estimates for the energy of the weighted
recovery profiles, including derivative and potential errors on overlaps, are
still required before this gives a global sharp recovery competitor.

`FiniteGraphCover.lean` extracts finitely many buffered patches covering any
compact graph base. Each closed half-radius patch retains the local recovery
area bound with the prescribed error. This supplies finite data for gluing;
it does not yet construct a glued competitor or control overlap energy.

`GraphAreaDensity.lean` proves continuity and local oscillation control of the
graph area density. On sufficiently small patches it improves the recovery
coefficient to the area-density integral plus an arbitrarily small base-volume
error. Patching the local competitors and identifying area with variational
perimeter remain necessary for the full geometric recovery result.

`LocalRecoveryBound.lean` removes global slope control from the recovery energy
bound. A C1 coordinate only needs its gradient bounded on the compact integration
region; the graph specialization likewise needs slope control only above that
region. These local bounds still require localization and perimeter identification
to produce the sharp geometric recovery theorem.

`GraphRecoveryBound.lean` assembles unit-Lipschitz normalized graph coordinates,
the Euclidean distribution bound, and recovery energy into an actual energy
upper bound: normalization scale times projected base volume times action.
The same competitors converge locally in L1 to the epigraph indicator.
Localizing the slope factor to obtain perimeter, and extending this to the
required geometric competitors, remain unfinished.

`EuclideanProductVolume.lean` proves volume preservation under the horizontal/
last-coordinate decomposition, then transfers normalized graph-height
distribution bounds from product coordinates to actual Euclidean volume.
Combining this with gradient normalization gives the next local recovery
energy estimate; global perimeter identification and chart assembly remain.

`GraphHeightGradient.lean` computes the differential and Euclidean gradient of
graph height, proves its squared norm is 1 plus the squared graph-gradient
norm, and verifies unit-gradient control after normalization by a positive
upper bound. Linking product-coordinate measures to Euclidean chart integrals
and assembling sharp perimeter bounds remain.

`NormalizedGraphMeasure.lean` tracks the exact measure factor when a real
coordinate is divided by a positive normalization scale. It applies this to
graph-height distributions and proves the corresponding layer integral bound
with that scale times projected base volume. Establishing the sharp coordinate
gradient bounds and assembling charts into a perimeter estimate remain.

`GraphLayerMeasure.lean` proves that vertical flattening of a measurable graph
preserves product volume. It computes graph-strip height distributions and
bounds vertical layer integrals by projected base volume times action.
Vertical height is not unit-speed signed distance: controlling its gradient
factor and relating local projected area to perimeter remain necessary.

`FlatLayerMeasure.lean` proves the coordinate-distribution formula for flat
cylinders with product Lebesgue measure, domination for arbitrary cylinder
subsets, and the exact layer integral equal to base volume times action.
Passing to curved boundary charts with controlled volume distortion, and
identifying their area with variational perimeter, remain geometric obligations.

`RecoveryMeasureBound.lean` connects the analytic recovery construction to
geometry: domination of the pushed-forward transition-layer volume by P
times length implies energy at most P times the exact regularized action.
The measure-domination premise is explicit and remains to be established
from geometric hypotheses; this conditional result is not perimeter minimality.

`RecoveryLayerMass.lean` defines the supported one-dimensional layer density,
proves its nonnegativity and integrability, and computes its exact total mass
as the regularized action independently of the positive spatial scale. This
preserves the sharp interface constant when the geometric layer integral is
compared to a one-dimensional measure. The geometric comparison itself remains.

`DistanceRecovery.lean` specializes the coordinate construction to distance
from the complement. For proper open sets it identifies the positive phase
exactly, proves exterior zero values and global Lipschitz regularity, and
obtains compact-local L1 convergence to the set indicator. Its energy bound
is the explicit interior boundary-layer integral. A sharp geometric estimate
of that layer integral is still required.

`RecoveryEnergyLocalization.lean` proves zero energy at pure phases, including
transition endpoints, and localizes the density bound to the open transition
layer. For a one-Lipschitz coordinate, it integrates this bound on compact
sets using almost-everywhere differentiability. Estimating the resulting
layer integral by geometric perimeter remains the next recovery obligation.

`GeometricRecoveryEnergy.lean` proves the extended-profile ODE on the open
transition interval, the spatial gradient chain rule, and the interior
rescaled energy bound R(2W(v)+δ) when the coordinate gradient has norm at
most one. Exterior energy localization and geometric integration are still
required to obtain the recovery upper bound.

`GeometricRecoveryProfile.lean` defines the scaled profile composed with a
geometric coordinate, proves its normalized range and explicit Lipschitz
bound, and proves compact-local L1 convergence to the indicator of the
coordinate's positive set. The L1 proof uses dominated convergence and does
not require a null zero level set. Energy upper bounds for geometric
coordinates and the ensuing perimeter minimality remain to be proved.

`RecoveryThickness.lean` bounds the transition time by 1/√(2δ), derives
vanishing scaled thickness under the corresponding scale condition, and
proves pointwise convergence of the scaled profiles to the positive half-line
indicator. Positive signed distances eventually have profile exactly one;
nonpositive signed distances have profile exactly zero. Composition with
geometric distance functions and multidimensional energy estimates remain.

`RecoveryActionBounds.lean` bounds the action between the interface constant
and that constant plus √(2δ), then proves convergence for every positive
regularization sequence tending to zero. The next obligation is the
multidimensional geometric recovery construction and its perimeter upper bound.

`RecoveryAction.lean` proves the exact core transition action by differentiating
the phase-coordinate primitive along the inverse profile and applying the
fundamental theorem of calculus. The kinetic-plus-potential integral equals
this action; endpoint derivative values are irrelevant by nonatomicity.
The regularization limit and geometric recovery upper bound remain unfinished.

`RecoveryProfileExtension.lean` extends the inverse profile by clamping time
to the finite transition interval. It proves the core and extended profiles
are Lipschitz with the explicit maximal regularized speed, that the extension
stays in [0,1], and that its exterior phases are exactly zero and one. Total
action and its regularization limit remain needed for geometric recovery.

`RecoveryProfileRegularity.lean` proves continuity of the inverse profile on
its closed transition interval using compactness, identifies interior phase
values, and derives the regularized first-order ODE by inverse differentiation.
It also proves the kinetic-plus-potential density identity 2 W(q) + δ.
Constant-phase extension, its total action, and the regularization limit remain
necessary for the geometric recovery upper bound.

`RecoveryProfileCore.lean` constructs the inverse of regularized travel time
on the finite transition interval. It proves the travel-time image is exactly
that interval, the inverse is normalized, both inverse identities hold, the
endpoint values are zero and one, and the profile is strictly increasing.
Inverse regularity, constant-phase extension, and its energy formula remain
to be established before geometric recovery.

`RecoveryTravelTime.lean` starts the one-dimensional recovery construction
using the reciprocal speed of the potential regularized by a positive δ.
The travel-time coordinate is continuous and strictly increasing on [0,1],
has the expected interior derivative, and reaches one in positive finite time.
Its inverse profile, exact action, and the δ-to-zero energy limit still need
to be constructed and connected to geometric competitors.

`PerimeterComparison.lean` transfers an inner-energy comparison with convergent
candidate energy and vanishing error to a weighted perimeter bound on every
strictly smaller ball. It connects the exact perimeter-energy liminf estimate
to the gluing/minimality comparison. This is conditional on a candidate energy
limit; a recovery upper bound by the candidate set's perimeter is still needed
to establish perimeter minimality.

`InnerEnergyComparison.lean` applies annular gluing and energy cancellation to
the actual rescaled zero extension, eliminating the cutoff from the final
sequence comparison. Under explicit annular common-limit and bounded-energy
hypotheses it produces a vanishing error between inner reference energy and
outer candidate energy. A convergent candidate energy then gives eventual
upper bounds with arbitrary positive tolerance. Suitable recovery inputs and
the connection to perimeter minimality remain to be established.

`GluingEnergyCancellation.lean` bounds the weighted input energy by candidate
energy plus the reference annular energy. It cancels the latter against the
reference total energy and applies rescaled minimality, giving an inner-ball
reference-energy bound by outer-ball candidate energy plus the gluing error.
This removes the cutoff weights from the comparison needed for the geometric
limit. Recovery construction and the geometric classification remain open.

`GluedLimit.lean` proves that the glued function's L1 distance to the candidate
is bounded by the input mismatch outside the region where the cutoff is one.
Consequently, vanishing annular L1 mismatch preserves the candidate's limit
on the whole outer domain. Together with annular gluing energy control, this
provides both convergence and energy tools for a recovery competitor once its
unmodified input sequence has been constructed.

`AnnularGluingSequence.lean` combines annular cutoff selection, the integrated
comparison, and the scale choice into a sequence-level gluing theorem with an
error tending to zero. The input energy bound and common local L1 limit are
required only on the annulus; the inner-ball limits may differ. Recovery
construction and preservation of the candidate limit under gluing still need
to be connected to the geometric comparison.

`AnnularTransitionCost.lean` localizes cutoff selection and the integrated
gluing comparison to the annular cost. The selection argument masks the cost
outside the annulus, so different limiting sets inside the inner ball are
allowed. Only the annulus needs common-limit mismatch control. This refinement
is necessary for a genuine geometric competitor rather than a comparison of
two sequences with the same limit everywhere.

`GluingMismatchConvergence.lean` bounds squared mismatch of normalized inputs
by their two absolute errors to a common limit. It proves common local L1
convergence gives vanishing squared mismatch and hence, under a uniform
energy bound, vanishing averaged gluing cost. This connects the compactness
results to the gluing estimates; constructing suitable recovery inputs and
restricting the comparison to where the limits agree remain necessary.

`GluingScaleChoice.lean` chooses N as the natural ceiling of R. The averaged
majorant is bounded by A E/R + (2 C²/t² + 4 W(0)) D, where E is the sum of
input energies and D their squared mismatch integral. It proves the actual
integral majorant tends to zero for bounded-energy normalized locally Lipschitz
inputs with D tending to zero. Applying this to appropriate recovery inputs,
and controlling the weighted energy in the annulus, remain necessary.

`IntegratedGluing.lean` integrates the localized comparison and combines it
with cutoff selection. The resulting competitor has energy bounded by the
cutoff-weighted input energies plus 1/N of the ambient gluing majorant, with
gradient parameter C N/t. This is an actual integrated competitor estimate;
vanishing errors and a recovery sequence still require scale selection and
geometric construction.

`GluingCostIntegral.lean` establishes local integrability and nonnegativity of
the explicit energy/mismatch majorant, separates its integral into input
energies and squared mismatch, and selects a smooth cutoff using that actual
majorant. Its transition integral is bounded by 1/N of the ambient integral,
with gradient bound C N/t. Integrating the localized gluing comparison and
choosing the scale-dependent layer count are the next analytic steps.

`GluingCostBound.lean` gives a majorant independent of the chosen cutoff except
through its gradient bound G: a fixed multiple of the two input energies plus
the squared mismatch times G²/R + 4 R W(0). Its localized version incurs this
additional cost only on the strict transition set. Substituting the selected
cutoff bound and integrating will expose the competing layer-count terms.

`SelectedTransitionCutoff.lean` combines the radial averaging result with the
existing smooth cutoffs. For any nonnegative integrable cost, it constructs a
normalized compactly supported cutoff equal to one on the inner ball, whose
transition cost is at most the outer-ball cost divided by N. In an annulus of
fixed width t, its gradient is bounded by C N/t, with a universal C. Choosing N
in relation to the diffuse scale and actual mismatch remains necessary.

`TransitionLayerSelection.lean` localizes existing fixed-width cutoffs to radial
annuli and proves a finite disjoint-layer averaging bound for any nonnegative
integrable cost. In particular, one of N consecutive equal-width radial layers
has cost at most the outer-ball cost divided by N. This will allow energy and
mismatch penalties to be selected together. The layer count, widths, recovery
profiles, and their limiting error estimates still need to be coordinated.

`GluingTransition.lean` proves exact energy selection at both cutoff endpoints
and localizes any excess bound to the strict transition region. This includes
boundary points of that region: the cutoff gradient vanishes at its extrema.
The global weighted input energy therefore incurs additional cost only in the
transition region. Selecting a layer and recovery profile with vanishing total
transition cost remains to be proved.

`RescaledMinimality.lean` transports closed-range Lipschitz minimality to every
positive dilation, including the perturbation's topological support. It also
provides the direct comparison with a cutoff-glued competitor in the scaled
ball. These comparisons now use exactly the energy controlled by the gluing
estimates and the perimeter lower bound. Recovery profiles and quantitative
control of their transition errors are still required to deduce perimeter minimality.

`GluingTotalEnergy.lean` combines the kinetic and phase-potential estimates into
an almost-everywhere total rescaled gluing-energy bound for locally Lipschitz
inputs in the closed unit interval. The gradient term is correctly included
on the zero phase using the local-minimum derivative theorem. The remaining
transition argument must select cutoffs and recovery profiles so the explicit
inverse-scale gradient error and scale-weighted squared mismatch vanish.

The analytic reduction to closed-range Lipschitz phase-energy minimality is now
proved. Local integral compactness of the rescaled phase indicators and
solutions is also proved below. The remaining classification is substantial:
identification of limiting minimizing geometry, flatness of the
relevant limits, and an improvement-of-flatness argument recovering the original
one-dimensional solution. The roadmap is informed by
[Wang–Wei, Sections 3–4 and Theorem 1.6](https://arxiv.org/html/1502.04680).
These results are not imported as assumptions or axioms, and neither main
rigidity theorem is currently proved.

`RescaledPhaseEnergy.lean` proves the exact energy change of variables and
a uniform bound on each fixed rescaled ball. Local indicator compactness is
now proved below; identifying the limiting interface geometry remains necessary. `RescaledPotential.lean` also
proves that the positive-phase potential integral tends to zero on every fixed
positive-radius ball, with an explicit inverse-scale bound.
`TransitionVolume.lean` converts this into vanishing local volume of every
intermediate positive-phase region with a fixed level below equilibrium.
`PhaseIndicatorApproximation.lean` proves local integral convergence of the
difference between the dilated solution and its phase indicator to zero.
`WeightedGradient.lean` supplies uniform potential-weighted gradient integral
bounds. `PhasePrimitive.lean` gives the primitive derivative and separates the
two equilibrium values. `PhasePrimitiveGradient.lean` proves the spatial chain
rule everywhere for the totalized gradient, including the zero phase, and
obtains the uniform primitive-gradient integral bound.
`PhasePrimitiveRegularity.lean` proves Lipschitz regularity of the primitive on
the closed normalized range and local Lipschitz regularity of its composite
with the zero extension across the free boundary. The compactness argument
for phase indicators is completed in the later modules described below. `PrimitiveIndicatorApproximation.lean` proves
that the local integral error between the phase primitive and its two-phase
indicator approximation tends to zero, linking their compactness arguments.
`MollificationFamilyBounds.lean` gives a dilation-independent local Lipschitz
constant for the primitive family at each fixed mollification index. Subsequence
extraction for a fixed ball and fixed index is now proved in
`MollifiedPrimitiveCompactness.lean` using Arzelà–Ascoli. A common diagonal
subsequence is now proved in `SimultaneousMollifiedCompactness.lean` for all
mollification indices and positive integer-radius balls simultaneously.
Uniform control of the mollification error is supplied by the next modules.
`SegmentGradientEstimate.lean` starts its translation estimate with the exact
segment integral formula and gradient bound for continuously differentiable
functions. `TranslationIntegral.lean` completes spatial integration and bounds
the local translation error by displacement times the gradient integral on the
enlarged ball. `LipschitzTranslationIntegral.lean` extends this to locally
Lipschitz functions by dominated convergence and proves a dilation-independent
translation bound for the actual phase primitive family. Averaging this
estimate is completed in `MollificationIntegralError.lean`, yielding an explicit
local error bound proportional to the averaging radius, uniformly in dilation.
`IntegralCauchyApproximation.lean` combines this with the common mollified
subsequence and proves the unsmoothed primitive subsequence is Cauchy in
integral norm on all positive integer balls. `LocalPrimitiveLimits.lean` uses
L¹ completeness to construct actual local integrable limits along that same
subsequence. `LocalLimitCompatibility.lean` proves restriction of integral
convergence and uniqueness almost everywhere, and applies them to show these
local limits agree almost everywhere on nested balls. `GlobalPrimitiveLimit.lean`
glues these representatives into one function and proves local integral
convergence to it on every integer-radius ball. `TwoPhaseLimit.lean` proves
that any such local limit along diverging dilations takes only zero and the
primitive value at one almost everywhere, by transfer from the weighted
phase indicators. `GlobalPhaseSet.lean` packages a single measurable phase
set and local integral convergence of the primitive subsequence to its
weighted indicator on every integer-radius ball. `PhaseSetConvergence.lean`
removes the positive primitive weight using the vanishing approximation error
and identifies the rescaled positive phase exactly with the rescaled epigraph.
Thus the rescaled epigraph indicators converge locally along the subsequence.
`SolutionPhaseConvergence.lean` proves that the scaled zero-extended solutions
converge locally in integral norm to the same measurable phase indicator.
`IntegralLimitTesting.lean` proves convergence against bounded measurable
tests and transfer of uniform tested-integral bounds to the limit. It applies
this to the primitive subsequence with a common phase set for every local
bounded test. `DirectionalTestBound.lean` proves compact-set integration by
parts and bounds unit-bounded directional tests by gradient mass for smooth
functions, then passes the bound through smooth integral approximations with
convergent gradient masses. `LipschitzDirectionalTest.lean` verifies integral
convergence of normalized mollification for bounded nonnegative functions,
obtains the actual locally Lipschitz directional test estimate, and applies it
to the rescaled phase primitives with a uniform surface-order bound.
`LimitingPhaseDirectionalBound.lean` passes all directional test bounds to
the same measurable limiting phase and removes the positive primitive weight.
The indicator itself now satisfies surface-order directional bounds.
`PhaseVectorTestBound.lean` combines scalar components in any orthonormal basis
and obtains the full vector divergence test bound, with the dimension factor
absorbed into the constant. `VariationalPerimeter.lean` defines the extended
nonnegative variational perimeter using the supremum of compact C¹ unit-field
divergence pairings, proves domain monotonicity, and packages finite
surface-order perimeter bounds on integer-radius balls for the same phase
limit. `PerimeterInvariance.lean` identifies divergence with the intrinsic
linear trace, proves orthonormal-basis independence of perimeter, and proves
invariance under almost-everywhere changes of the phase inside the test domain.
`PerimeterLowerSemicontinuity.lean` proves convergence of compact divergence
pairings from local integral convergence of measurable indicators and obtains
the full extended-nonnegative perimeter liminf inequality.
`SharpDivergenceBound.lean` proves exact vector integration by parts and bounds
a unit-field divergence pairing by gradient mass with no dimension factor,
including bounded nonnegative locally Lipschitz coefficients via mollification.
`PrimitiveEnergyLowerBound.lean` proves pointwise and integrated control of
the rescaled primitive gradient by diffuse energy with coefficient one. It
then proves the corresponding divergence test bound and passes each tested
pairing to the diffuse-energy liminf. `PerimeterEnergyLiminf.lean` takes the
weighted supremum and proves that the primitive value at one times the limiting
phase perimeter is bounded by the diffuse-energy liminf. It packages the same
phase and subsequence on every integer-radius ball. `GluedCompetitor.lean`
constructs cutoff interpolation, proves its closed-range and local Lipschitz
admissibility, support control, exact gradient formula, and transition-gradient
bound, and applies the existing phase-energy minimality theorem to it.
`GluingGradientEnergy.lean` derives the adjustable quadratic estimate: the
principal gradient terms incur a factor of one plus an arbitrary positive
parameter, while the mismatch-cutoff term is explicit. The inverse-scale
kinetic version holds almost everywhere for locally Lipschitz inputs.
`GluingPotentialEnergy.lean` controls the phase-restricted potential of the
glued function by the sum of input potentials plus the squared mismatch, with
explicit reaction-dependent constants. Its proof handles zero/positive phase
interfaces separately. Combining total transition-energy control, recovery
profiles, vanishing errors, interface minimality, and classification remain.

`EpigraphRescaling.lean` starts the geometric infrastructure with the exact
rescaled graph/domain identity. For a one-sided bound its intercept is C/R,
so any pointwise graph limit inherits a homogeneous one-sided cone bound.
This is conditional on pointwise convergence; it does not establish compactness,
nor claim that the relevant interface limit must exist as a pointwise graph.

`RadialCutoffCompetitor.lean` constructs the competitor which vanishes in the
radius-R ball and equals U outside radius R+1. It remains locally Lipschitz and
normalized, with compact perturbation support. A minimum-gradient selection
lemma gives a squared-gradient cost of at most one, and a compact potential
bound gives an energy-density increase of at most 1/2+M.
`PhaseEnergyShellBound.lean` now integrates on the unit shell and cancels the
original shell energy using minimality. A single positive constant controls
every ball energy by the outer unit-shell volume. `UnitShellVolume.lean` now
uses Euclidean ball-volume scaling and the difference-of-powers estimate to
bound the shell volume by surface order. Consequently the phase energy in
every centered ball of radius R at least one is bounded by C times R to the
ambient dimension minus one. The rescaling compactness argument remains next.

## Completed analytic reduction

`AnnularComparison.lean` now proves that an increasing annular profile with
outer value one bounds the original solution above whenever its inner closed
ball is strictly separated from the closed epigraph. In particular this holds
for every positive downward shift of an exterior ball. The comparison domain
may be disconnected. `TangentAnnularComparison.lean` passes to zero downward
shift using continuity of the radial profile on its closed interval, then
extends the inequality to the closure of the comparison domain. Comparing
contact derivatives is now implemented in `AnnularContactDerivative.lean` for
every direction in the closed-domain positive tangent cone. Cauchy–Schwarz and
the Neumann condition give an upper bound by the inner radial slope.
`InwardTangent.lean` proves inward-normal cone membership by constructing a
differentiable curve in the closed epigraph. `AnnularSlopeComparison.lean`
applies arbitrary-radius exterior contact and the annular existence theorem to
prove the upper energy bound, then combines it with the lower bound to obtain

$$
\kappa^2=2W(0)=2\int_0^1 f(s)\,ds.
$$

This identity is proved without additional hypotheses. `UnshiftedMinimality.lean`
uses it to remove the energy shift from the compact C¹ comparison, on every
compact set containing the perturbation support and on enclosing balls.
Competitor values are still restricted to [0,1). Next extend minimality to
the required competitor class and complete the geometric rigidity arguments.

`LipschitzCompetitorEnergy.lean` establishes almost-everywhere differentiability
of arbitrary locally Lipschitz competitors by Rademacher on a countable ball
cover. It also proves compact gradient bounds, uniform bounds for normalized
mollifications, and compact integrability of squared gradients and phase
energy. `LipschitzMollificationDerivative.lean` now differentiates convolution
for globally Lipschitz functions using dominated differentiation and Rademacher,
applies Lebesgue differentiation to their derivatives, and localizes through
real-valued Lipschitz extensions on a countable ball cover. Thus normalized
mollification gradients converge almost everywhere for every locally Lipschitz
competitor. `LipschitzCalibration.lean` now proves convergence and integrability
of the calibration density and preservation of its integral under compact
locally Lipschitz perturbations. `LipschitzMinimality.lean` integrates the
pointwise energy comparison, transfers it to any compact set containing the
perturbation support, and removes the energy shift. Thus every locally Lipschitz
competitor valued in [0,1), equal to the zero extension outside a compact set,
has no smaller phase energy. `ClosedLipschitzMinimality.lean` now includes the
endpoint value one using the cap construction below. The geometric
classification remains to be proved.

`CappedCompetitor.lean` constructs the endpoint approximation

$$
v_t=\min\{v,1-t+tU\},\qquad 0<t<1,
$$

where U is the zero extension. It preserves the positive phase and the compact
support of the difference from U, is locally Lipschitz, and is strictly below
one. Its gradients converge at differentiability points of U, including on
the set where v equals one (where the totalized gradient of v vanishes by the
maximum principle for derivatives). `CappedEnergy.lean` proves a parameter-uniform
compact gradient bound, pointwise phase-energy convergence, and dominated
energy-integral convergence. `ClosedLipschitzMinimality.lean` passes the energy
comparison to the limit and proves minimality for all locally Lipschitz
competitors valued in [0,1] whose difference from U has compact support.

The maximum-ratio argument is now proved in `CompactComparison.lean`, including
the boundary contradiction via continuous extension from the open domain.
`RadialBallProfile.spatial_le_solution` applies it to every closed ball contained
in the epigraph. `TangentBallComparison.lean` extends the inequality to closed
balls contained in the closed epigraph, using upward translations and the
solution's continuity on the closure. `BallSlopeComparison.lean` now compares
boundary derivatives through the positive tangent cone of the closed ball,
uses the Neumann gradient norm, and combines arbitrary-radius tangent balls with
the radial boundary-energy approximation to prove

$$
2W(0)\le\kappa^2.
$$

The opposite inequality is now proved by the exterior tangent-ball/annulus route.
`AnnularEnergy.lean` now supplies the increasing-segment estimates for that route:
decreasing slope, curvature energy loss bounded by value increase, a preserved
positive slope margin, and a finite length bound. These are conditional ODE
estimates used by the now completed annular barrier construction and comparison.
`ReactionSmoothExtension.lean` constructs a globally continuously differentiable
reaction agreeing with the original on nonnegative states, and uses it to start
the radial initial value problem at zero at any positive radius.
`AnnularLocal.lean` now constructs a short increasing segment with strictly
positive slope and value below one, and chooses a uniform positive energy margin
for all sufficiently large inner radii whenever the initial slope energy exceeds
the potential drop. Next continue this segment using the annular energy bounds
until its value reaches one.
`AnnularEndpoint.lean` now establishes both left endpoint differential equations,
positivity of the outer value, and a local restart retaining positive slope and
values between zero and one when the endpoint has those strict bounds.
`AnnularContinuation.lean` now glues the restart to a strictly longer increasing
segment, preserving both components on the original closed interval and checking
the radial equations at the junction. A positive energy margin suffices for this
extension whenever the outer value is below one. The maximal continuation and
finite endpoint completion argument remain. `AnnularBranches.lean` defines the
extensions of a fixed seed, proves compatibility on their closed overlaps and a
uniform finite upper bound on their radii, and shows that an extension attaining
the supremal radius must have endpoint value one. Constructing that supremal
extension from the compatible union is the next obligation.
`AnnularUnion.lean` now constructs that union on the half-open interval ending at
the supremum, with both continuous components, the radial equations on the open
interval, the original seed values, normalized value bounds, and nonnegative
slope. `AnnularLimits.lean` now proves finite value and slope limits of this
union, and separately proves that filling such limits creates a closed increasing
segment. The next step is to assemble the completed supremal extension, including
agreement with the seed at its outer endpoint, and apply the value-one criterion.
This assembly is now completed in `AnnularMaximal.lean`: for every positive
initial slope whose squared value exceeds twice the potential drop, all
sufficiently large inner radii admit an increasing radial solution from zero to
one with that prescribed inner slope and positive slope throughout. Next lift
this profile to an annulus in Euclidean space and prove the exterior comparison.
`AnnularSpatial.lean` now supplies the lift, closed-annulus continuity, normalized
range, positivity, zero/one sphere values, gradient and Hessian formulas, and the
original elliptic equation. Continuous second differentiability and the inner
boundary derivative still need to be packaged for the comparison argument.
Both are now proved in `AnnularRegularity.lean`: the spatial profile is C2 on the
open annulus and has the explicit prescribed radial differential within the
closed annulus at the inner sphere. The next obligation is comparison with the
epigraph solution outside an exterior tangent ball.
`ComponentComparison.lean` now removes connectedness from compact-domain
comparison by applying the theorem on each open component. `ExteriorBallGeometry.lean`
proves that positive downward shifts of an exterior ball separate its whole
closed ball strictly from the closed epigraph. These provide the domain and
strict positivity prerequisites for annular comparison.

The monotonicity proof is complete. The two rigidity obligations remain open.
The rigidity targets in `SerrinEpigraph/Main.lean` now include the reaction
assumptions restored from the source context; see [scope correction](scope-correction.md).

## Automatic monotonicity

Write

$$
v=\partial_nu,\quad t=v/u,\quad z=t^-,\quad h(s)=f(s)-sf'(s).
$$

The argument consists of the following steps, now each proved in Lean:

1. **Epigraph geometry and traces.** Identify the boundary and closure, justify
   the within-closure differential, and derive positive vertical boundary
   derivative from the zero trace and constant negative Neumann data.
2. **Local integrability and support.** On every bounded region, the solution and
   its first derivatives extend continuously to the boundary. The negative
   quotient vanishes near the compact boundary portion. Thus the cutoff tests
   below have support in the interior and finite integrals.
3. **Weak differentiation.** Differentiate the equation distributionally and
   justify the quotient identity without adding a third classical derivative
   assumption on the solution.
4. **Kato inequality and power tests.** Prove the weak negative-part inequality

$$
-\operatorname{div}(u^2\nabla z)+u h(u)z\le0.
$$

   Test with nonnegative compactly supported Sobolev approximations and obtain

$$
\int u^2|\nabla(z^{q/2}\eta)|^2\le\int u^2z^q|\nabla\eta|^2,
\qquad q\ge2.
$$

   The current implementation instead uses even powers

$$
q=2p,\qquad p\ge2,
$$

   so that both the testing power and the energy power of the negative part are
   continuously differentiable. `Truncation.lean` and `QuotientTests.lean` prove
   this regularity, including zero points. `SparseMoments.lean` proves that the
   resulting odd moments alone suffice. `PowerEnergy.lean` now proves the actual
   weak PDE testing estimate from the original hypotheses.

5. **Vertical integration by parts and Hölder.** Use the quotient's origin as a
   directional derivative, a high power of a ball cutoff, and Hölder to obtain

$$
\int_{\Omega\cap B_R}u^2z^k
\le\left(\frac{kC_\chi}{R}\right)^k
\int_{\Omega\cap B_{2R}}u^2,\qquad k\in\mathbb N,\quad k\ge3.
$$

6. **Growth contradiction.** If the negative quotient is positive at some point,
   continuity gives a fixed region of positive weighted measure on which it is
   bounded below. Choosing the integer power proportional to the radius forces a
   positive lower exponential mass-growth rate, contradicting the liminf assumption.
7. **Strict positivity.** A local strong maximum principle for the linearized
   equation gives positivity or identical vanishing. Vertical rays, positivity
   of the solution, and its zero boundary values exclude identical vanishing.

Steps 1–6 are proved, culminating in `Hypotheses.verticalDerivative_nonneg` in
`Nonnegative.lean`, with the original hypotheses and no additional assumptions.
`WeakEquation.lean` proves the original PDE's weak formulation from its classical
form with only the stated second derivatives; `WeakLinearization.lean` derives
the linearized equation by differentiating translated integrals. `WeakQuotient.lean`
derives the weighted quotient equation. `IntegrationByParts.lean` proves the
vertical identity. `BallCutoff.lean` constructs the scaled ball cutoffs, and
`Energy.lean`, `CauchyEnergy.lean`, and `MomentInterpolation.lean` prove the
algebraic and integral estimates used by `FirstMoment.lean` and
`CutoffMoments.lean` for the final moment closure.

Step 7 is proved by `StrongMaximum.lean`, completing `verticalDerivative_pos`.
`WeakComparison.lean` proves weak comparison by a smooth cubic negative-part
test, `Barrier.lean` supplies the exponential annular barriers, and
`StrongPositivity.lean` implements shifted-barrier comparison on annuli. This
propagates a positive point through the connected domain without assuming a
third classical derivative of the original solution.

## Rigidity

One reduction is now fully proved in `ReactionReduction.lean`: a negative
reaction value at any positive threshold forces a global upper bound at that
threshold. The proof uses a smooth positive-part test, an exact squared-excess
estimate, fixed-width radial cutoffs, and an exponential growth contradiction.
Consequently unbounded solutions require nonnegative reaction everywhere on
the nonnegative half-line, and all solutions are superharmonic. See the
[complete argument and Lean declarations](reaction-reduction.md).

The next [variational reduction](variational-reduction.md) is a complete
informal argument, not a Lean implementation: entire-space Liouville and
Harnack compactness give a common vertical limit; a foliation calibration
proves general one-phase minimization, including the phase cost; comparison
on large zero-phase balls makes the normalized potential nonnegative. In the
unbounded branch this forces a finite reaction primitive, and in the bounded
branch the potential vanishes at the limiting equilibrium. The proof uses
classical analytic ingredients not yet implemented in this project.

For the corrected targets, the equilibrium is nondegenerate and the solution lies
strictly between zero and one. `NormalizedPotential.lean` now defines the potential as the integral of the
reaction from the argument to one. It proves strict positivity on the interval
from zero up to one, the unique zero at one, the derivative formulas on the
positive half-line, and the strictly positive second derivative at one.
`EquilibriumEstimates.lean` strengthens the equilibrium result to a uniform
positive lower bound on the second derivative in a full neighborhood. It also
proves a positive linear lower bound for the reaction in terms of the distance
to equilibrium from below. The remaining potential work includes a suitable
extension beyond the solution range. `QuadraticPotential.lean` now integrates
the linear reaction lower bound and combines it with compactness away from one
to prove a uniform positive quadratic lower bound on the entire interval from
zero to one. Continuity at zero is proved using the interval primitive theorem.
`PotentialComparison.lean` supplies the matching upper bound: a compact bound
on the reaction derivative on the upper half interval gives a linear reaction
bound and hence a quadratic potential bound. A compact potential bound controls
the remaining interval. The resulting two-sided comparison holds on the full
closed solution range, with no additional hypotheses. `VerticalLimit.lean` now derives strict monotonicity of each vertical section
from its directional derivative and proves that each ray has a positive limit
at most one. Every finite interior value is strictly smaller than its ray limit.
The identification with one is now proved by `LimitOne.lean`, as described below.
`TranslatedDomain.lean` proves that upward translations eventually place any
fixed compact set inside the epigraph. Strict vertical monotonicity and the
positive minimum of one fixed translate provide a common positive lower bound
on that compact set for every later translate. These facts prepare the domain
exhaustion and nonvanishing steps of the translation-limit argument.
`LimitProfile.lean` selects the proved ray limits as a horizontal function,
proves its measurability by continuous graph sections at increasing integer
heights, and proves pointwise convergence of ambient vertical translates and
of their nonlinear reactions. `TranslateIntegrals.lean` now proves convergence
of compact weighted integrals for every continuous observable on the solution
range, including the solution and reaction. It uses eventual compact-domain
inclusion, compact bounds, and filter dominated convergence. `DistributionalEquation.lean` now proves the second integration-by-parts
identity, the distributional equation, and its translated form for every fixed
compact test at sufficiently large heights. `LimitEquation.lean` proves continuity and support control of the test
Laplacian, restricts the integrals to the compact test support, and combines the
established limits with uniqueness of limits. The lifted horizontal profile now
satisfies the semilinear equation in distributions and is distributionally
superharmonic. The identification with one uses the reaction structure and the
classical comparison argument below, not merely bounded superharmonicity.
`PolynomialBarrier.lean` now constructs the squared quadratic on a ball,
computes its first and second derivatives and exact Laplacian, and proves its
positive interior values, zero sphere values, and an explicit inverse-radius-
squared bound for the negative Laplacian relative to the polynomial. The next
comparison step now has its differential contradiction in `LocalMinimum.lean`:
a local minimum has nonnegative Laplacian, and positive contact is impossible
when the reaction coefficient strictly exceeds the barrier coefficient. The
compact optimization is now proved in `CompactContact.lean`: maximizing the
comparison-to-solution quotient produces an interior contact with a scale
strictly between zero and one. Combining this with the differential contradiction
proves comparison on compact sets under a strict coefficient gap. Applying the
comparison theorem to the polynomial is completed in `BallLowerBound.lean`:
the solution exceeds any positive threshold at the center once the ball's
coefficient is below the reaction quotient at that threshold. `LimitOne.lean`
then uses upward domain exhaustion to prove that every vertical ray limit equals
one. This proof uses the classical original solution directly and does not
assume extra regularity of the limit profile. The remaining work includes the
variational minimization argument and the dimension/geometric classification.
`LevelHeight.lean` now parameterizes each vertical ray by its solution value:
every value in the open unit interval is attained at exactly one interior height,
the inverse height is strictly increasing and continuous in that value, and it
recovers the height of each original interior point.
`LevelHeightContinuity.lean` proves joint continuity in horizontal location and
level using strict order comparisons and continuous horizontal sections.
`LevelHeightDerivative.lean` proves differentiability with respect to the level,
with derivative the reciprocal of the positive vertical derivative.
`LevelHeightSmooth.lean` now proves joint C² regularity by the implicit function
theorem, identifying the local implicit solution with the globally unique
level height. Its explicit differential solves the differentiated level equation.
`LevelGradient.lean` defines the gradient along the vertical foliation, proves
its joint C¹ regularity and explicit differential, and proves the pointwise
affine energy bound with equality on the original solution. `FoliationEquation.lean` proves the chain-rule equation and cancellation
of the spatial divergence with the level derivative of the calibration energy
component. `VectorIntegrationByParts.lean` supplies the compact-test vector
integration identity. `FoliationPullback.lean` proves the comparison field
regularity, divergence formula, and resulting integrated identity for arbitrary
C¹ comparison functions taking values in (0,1). `CalibrationVariation.lean`
defines the calibrated density, proves its derivative along differentiable
level/gradient paths, and proves that its integrated first variation vanishes
for compact variations. `CalibrationIntegral.lean` proves a uniform interval
of admissible variation on compact sets, differentiates the calibrated energy
under the compact spatial integral, and proves the resulting derivative is zero
for compact variations. `CalibrationPath.lean` proves constancy along admissible
affine comparison paths and energy minimality against C¹ perturbations compactly
supported inside the epigraph that keep the solution strictly between zero and
one. `ClosedRangeMinimality.lean` extends this comparison to perturbations
whose resulting values lie in the closed interval [0,1], using continuity of
compact spatial integrals. This is an interior fixed-domain comparison, not yet the free-boundary
minimization allowing changes to the positive phase. `LevelBoundary.lean` proves
joint continuity of inverse heights and level points at level zero, and the
trace of the interior foliation gradient as the gradient within the closed
epigraph. Its vertical component agrees with the Neumann boundary formula.
`BoundaryGradient.lean` proves the full boundary gradient is minus κ times
the outward unit normal, hence has norm κ. The calibration energy component
converges to κ²/2 − W(0); this constant has not been proved to vanish.
For this normalization step, Wang–Wei §5, Lemmas 5.3–5.4 use interior
radial-ball and exterior-annulus comparisons to bound the boundary slope from
both sides. `TangentBalls.lean` now supplies the geometric input: every
positive radius admits an interior and an exterior tangent ball with center
on the vertical axis, assuming only continuity of the graph. The radial
comparison solutions, their large-radius limits, and slope comparisons still
need proofs; the geometric contact result alone does not normalize κ.
`RadialEnergy.lean` now formalizes the radial profile equation and proves its
energy dissipation formula, monotonicity through the center-to-boundary
interval, boundary slope bounds, and the integrated energy loss away from
the origin. These are conditional estimates for a supplied radial profile;
existence of the profile is not assumed as an axiom or proved yet.
`RadialFlux.lean` removes the singular radial drift by multiplying by the
radial volume weight. It proves the flux integral identity including the
center, nonpositive slopes, decreasing values, a positive central value, and
a strictly negative boundary slope. These conclusions still require a
supplied radial profile.
`ZeroExtension.lean` constructs the whole-space extension, proves continuity,
identifies its positive phase, preserves vertical monotonicity and the limit
one, and establishes the original PDE and gradient identities in the interior.
`ZeroExtensionRegularity.lean` proves local Lipschitz regularity across the
free boundary by flattening the epigraph and clamping the vertical coordinate
to the closed half-space. It also gives a Lipschitz constant on each compact
set. `ZeroExtensionDifferentiability.lean` proves almost-everywhere
differentiability via Rademacher, identifies the totalized gradient with the
interior gradient extended by zero, and proves non-differentiability at every
boundary point from the nonzero Neumann slope. Consequently the frontier has
zero ambient volume. `PhaseEnergy.lean` defines positive-phase energy with an
explicit additive constant, proves local integrability of the zero extension’s
squared gradient and phase energy, and identifies the whole-space integral
with the original interior integral. `BoundaryCalibration.lean` shifts the closed
calibration by the actual boundary energy constant. It vanishes at zero level
and zero gradient, bounds the phase energy of every nonnegative competitor
pointwise, and agrees with that energy on the zero extension. The deficit in
the positive phase is half the squared gradient mismatch. `BoundaryCalibrationIntegral.lean` proves continuity of the closed field on
the half-closed level strip and local integrability of calibration and phase
energy for smooth competitors taking values in [0,1). Thus the pointwise
bound integrates even when a competitor touches zero. `ClosedCalibrationPath.lean` proves invariance of the calibration integral
under compact smooth changes between globally smooth functions valued in
[0,1), including changes of their positive phases. It regularizes both
endpoints toward one half and passes to zero regularization using continuity
of compact-set integrals. Extension of this invariance to the locally
Lipschitz zero extension remains; the smooth result alone does not establish
free-boundary energy minimality. `CalibrationConvergence.lean` supplies the
compact-set dominated-convergence step: almost-everywhere convergence of
levels and vector fields implies convergence of calibration integrals under
uniform level bounds below one and uniform vector bounds. Its specialization
to smooth approximations of the zero extension recovers the phase energy.
`Mollification.lean` constructs an explicit normalized convolution sequence
for the zero extension. Every term is smooth, nonnegative, and strictly below
one, and the sequence converges pointwise to the extension. `MollificationBounds.lean` proves that averaging preserves a Lipschitz bound
from a slightly larger ball. Hence all normalized approximations have a common
gradient bound on each compact set. It also supplies a uniform compact level
bound strictly below one. `MollificationSupport.lean` proves uniform support control for jointly
smoothing compact comparison pairs and additivity of the normalized
convolution. The calibration integrals of each smoothed pair agree on one
fixed ball for all indices. `MollificationDerivative.lean` proves gradient convergence on open C¹
regions by compact localization and locality of convolution. The null
boundary then gives almost-everywhere gradient convergence for the zero
extension. Combined with the established bounds, the explicit sequence’s
calibration integrals converge to the original phase energy, without extra
approximation assumptions. `PerturbedCalibration.lean` completes the analogous bounds and limiting
argument for a smooth compact perturbation whose values stay in [0,1). The
calibration integral of that perturbed zero extension equals the original
phase energy on a ball explicitly containing the perturbation support.
`CrossBoundaryMinimality.lean` proves integrability of the perturbed
gradient, its square, its phase energy, and its calibration. It integrates
the pointwise bound and transfers the comparison from the construction ball
to every compact set containing the perturbation support. Thus the shifted
phase energy is minimal against compact C¹ perturbations with values in
[0,1), even across the original boundary. `UnshiftedMinimality.lean` now removes
the shift using the proved boundary energy identity. `LipschitzMinimality.lean`
extends this comparison to locally Lipschitz competitors valued in [0,1).
The free-boundary minimization argument and the low-dimensional or one-sided-graph rigidity
classification also remain. These must be proved in Lean; citing
a paper or assuming a classification conclusion is not sufficient.

## Radial integral construction

`RadialIntegral.lean` defines the nonsingular weighted unit-interval average
and radial Picard operator. It proves continuity of the average, the prescribed
center value and zero center derivative, the derivative formula, a quadratic
size bound, and a quadratic difference bound for continuous forcings.
`RadialFixedPoint.lean` uses these bounds on continuous functions on a compact
radius interval. For globally Lipschitz forcing and a sufficiently small radius,
it proves existence and uniqueness of an integral solution. It produces a
continuous real-valued extension with the prescribed initial value, zero center
derivative, and the averaged radial derivative formula throughout the interval.
`RadialReactionExtension.lean` now connects this construction to the original
reaction hypotheses. Constant endpoint extension is globally Lipschitz for a
reaction that is C¹ on a compact value interval. A positive contraction radius
exists, and continuity allows shrinking it so the constructed profile remains
strictly inside the original value interval. The averaged derivative equation
then uses the original reaction, without an extra global Lipschitz assumption.
`RadialEquation.lean` recovers the second-order radial system by rescaling the
average to a weighted primitive and differentiating away from the center.
It proves slope continuity on the closed radius interval and constructs a local
value/slope pair satisfying the original reaction equation, with central value
in (0,1), zero central slope, and values in (0,1).
`RadialLocalFlow.lean` proves local existence at every positive radius and
positive value, with arbitrary initial slope, under the original reaction
hypotheses. It uses the autonomous radius/value/slope field and proves that
the radius coordinate equals time. A smaller neighborhood preserves positive
radius and positive value. `RadialUniqueness.lean` proves local uniqueness
through a matching radial value/slope state, and propagates agreement over
any connected open set of positive radii and positive values. This supplies
the consistency needed for the restart step. `RadialGluing.lean` now constructs
a radial system on the union of two open domains with connected overlap,
preserving each original value and slope. It also glues a local restart at an
interior positive state to the existing profile. This union need not strictly
enlarge the old interval. `RadialEndpoint.lean` proves finite value and slope
limits when the slope is bounded and values stay in [0,1], on an interval
separated from zero. It derives the forcing bound from the original reaction
regularity and obtains the limits through Lipschitz extensions.
`RadialBounds.lean` removes the slope-bound assumption for solutions valued
in (0,1): energy decreases on positive-radius convex domains, so slope is
bounded to the right of any interior radius. Both left endpoint limits then
exist, and the value limit lies in [0,1]. `RadialEndpointDerivative.lean`
completes both components by their endpoint limits and proves both radial
equations as left derivatives there, including when the value limit is zero.
`RadialContinuation.lean` now splices the original solution to a local
solution through a positive completed endpoint and proves the full derivative
at the junction. The resulting interval is strictly larger. It proves the
alternative that a normalized radial solution has zero endpoint value or
continues past the finite endpoint. This does not yet construct maximal
profiles or prove that a first zero occurs at a desired radius.
`RadialDecrease.lean` proves strict decrease of weighted flux and value for
regular central profiles, with strictly negative slope at every positive
radius. It packages a decreasing local initial-value solution, propagates
strict decrease to half-open intervals, and shows a finite endpoint limit
is strictly below the central value. No prescribed boundary value is used.
`RadialNormalizedContinuation.lean` strengthens the continuation alternative:
the extended solution stays in (0,1), preserves both original components
including their center values, and remains continuous up to the center.
It repairs the center by updating the extended components and verifies that
the differential equations at positive radii are unaffected.
`RadialZeroEndpoint.lean` completes the zero-limit branch into a genuine
`RadialBallProfile`, preserving value and slope before the endpoint. The
combined alternative now yields either a ball profile with strictly negative
boundary slope and the strict energy bound, or a normalized extension.
`RadialUnion.lean` constructs the union of an arbitrary compatible family of
central profiles. It preserves branch values, central data, continuity,
normalized range, and the differential equations. For bounded branch radii,
the union domain ends at their supremum. `RadialBranches.lean` supplies the
family of all normalized extensions of a fixed seed and proves automatic
compatibility by uniqueness at a shared positive radius. The family is
nonempty. If its radii are bounded, their union is an extension at the
supremal radius and must complete to a Dirichlet ball profile: the alternative
extension would contradict the supremum. `RadialGlobal.lean` constructs
the union on the whole nonnegative half-line when extension radii are
unbounded. Thus each central value in (0,1) gives either a finite Dirichlet
ball profile or a global normalized positive radial system. `RadialRiccati.lean`
rules out the latter: the negative logarithmic derivative satisfies a Riccati
equation whose arctangent eventually has a strictly positive lower derivative
bound, contradicting boundedness of arctangent. Thus every central value in
(0,1) yields a finite positive Dirichlet ball profile.
Still required: control these radii as the central value tends to one,
construct annulus profiles, and prove the large-radius boundary-slope limits.

`RadialSlopeBound.lean` bounds every radial slope by the one-dimensional
energy scale and bounds outer-region energy loss by the value drop times
that scale and the curvature factor. For inner radius a and outer radius b,
the loss is at most m/a times that scale. This supplies the uniform
outer-region error estimate; control of the inner-region energy as the
central value tends to one remains.

`RadialEquilibrium.lean` gives a uniform reaction-dependent constant K > 0
such that the deficit at radius r is at most the central deficit times exp(Kr).
At the zero boundary this implies exp(-KR) is at most the central deficit.
The explicit threshold theorem forces R > T whenever the central deficit
is less than exp(-KT). This supplies fixed-radius value control and the
quantitative radius divergence criterion. The boundary-slope limit still
needs to combine this control with the outer-region energy-loss estimate.

`RadialBoundaryEnergy.lean` completes that combination. It proves a uniform
epsilon estimate for the boundary energy as the center approaches one,
then combines finite existence, radius control, and this estimate to produce
balls of arbitrarily large radius with boundary energy arbitrarily close
to the one-dimensional value. The next comparison steps require realizing
these profiles as classical spatial PDE solutions, comparison/Hopf arguments
at tangent balls, and the complementary exterior-annulus construction.

`RadialSpatial.lean` defines the spatial realization centered at any point.
It proves continuity and range on the closed ball, positivity throughout
the open ball, zero boundary data, and the radial derivative and gradient
formulas away from the center. The center regularity and second-derivative
Laplacian formula are still required before using it as a classical PDE solution.

`RadialCenter.lean` supplies the first-order center argument: the right
derivative of the profile at zero vanishes, composition with distance has
zero spatial derivative at the center, and the spatial profile is
differentiable throughout the ball. Its gradient norm equals the absolute
radial slope, including the center, and its gradient is continuous there.
Second-order regularity and the Laplacian identity remain to be established.

`RadialSlopeRatio.lean` identifies slope/radius with a continuous weighted
reaction average. It proves the central limit is minus the central reaction
divided by m+1. The radial equation then gives the same limit for the slope
derivative and a right derivative of the slope at zero. These are the
central second-order radial data needed for the spatial Hessian formula.

`RadialHessianCenter.lean` now proves the spatial gradient derivative at the
center is the scalar -f(value(0))/(m+1) times the identity. It also proves a
general gradient-trace formula requiring only differentiability of the
gradient, and uses it to establish the semilinear PDE at the center.
The off-center Hessian/PDE formula and full second-order continuity are
still required for the classical comparison-solution package.

`RadialHessian.lean` proves the off-center radial Hessian and its trace,
then establishes the original semilinear equation throughout the open ball
by combining the off-center computation with the center theorem. Full
second-order continuity and boundary regularity remain to be packaged before
the classical comparison and boundary derivative arguments.

`RadialRegularity.lean` packages differentiability of the spatial gradient
throughout the ball and proves the spatial function is C1 there. It also
proves Hessian continuity away from the center and C2 regularity on the
punctured ball. Central Hessian continuity and boundary regularity are the
remaining regularity steps for classical ball comparison.

`RadialHessianContinuity.lean` bounds the normalized rank-one correction by
its scalar coefficient, proves that coefficient vanishes at the center,
and establishes central Hessian continuity. The spatial radial profile is
now C2 throughout the open ball and satisfies the semilinear PDE there.
Boundary regularity and comparison against the epigraph solution remain.

`RadialBoundaryDerivative.lean` completes the C1 regularity on the closed
ball and identifies the outward normal derivative with the radial boundary
slope. The ball profiles now have C2 interior regularity, C1 closed-ball
regularity, the PDE, positivity, zero boundary data, and the sharp boundary
energy approximation. Comparison with the original epigraph solution and
the complementary annulus construction remain.

## Acceptance

All three proof targets must compile without proof holes, use only the standard
Lean axioms, match independent Challenge statements under Comparator, and pass
the complete pinned Palomar mechanical workflow before registry intake.
