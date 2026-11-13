# Proof obligations

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
[0,1), even across the original boundary. This does not yet cover all
Lipschitz competitors or prove that the energy shift vanishes.
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

## Acceptance

All three proof targets must compile without proof holes, use only the standard
Lean axioms, match independent Challenge statements under Comparator, and pass
the complete pinned Palomar mechanical workflow before registry intake.
