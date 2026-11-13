# Verification record

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
