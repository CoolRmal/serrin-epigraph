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
