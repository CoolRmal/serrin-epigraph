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
