# Verification record

The strict monotonicity theorem is proved. The two rigidity theorems remain
unproved, so this is not a completed three-theorem formalization or a Palomar
registration.

## Public snapshot checked

Commit: [`4b1b13ef839e9766ed4605b482138e8b07bd154c`](https://github.com/CoolRmal/serrin-epigraph/commit/4b1b13ef839e9766ed4605b482138e8b07bd154c).

On 2026-11-13 the [independent monotonicity job](https://github.com/CoolRmal/serrin-epigraph/actions/runs/43377717405/job/131728003364)
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
