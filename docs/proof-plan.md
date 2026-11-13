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
The calibration identities remain to be proved.
The monotone-solution
minimization argument and the low-dimensional or one-sided-graph rigidity
classification also remain. These must be proved in Lean; citing
a paper or assuming a classification conclusion is not sufficient.

## Acceptance

All three proof targets must compile without proof holes, use only the standard
Lean axioms, match independent Challenge statements under Comparator, and pass
the complete pinned Palomar mechanical workflow before registry intake.
