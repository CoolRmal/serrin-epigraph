# Serrin epigraph monotonicity and rigidity

A Lean 4 project depending on Mathlib that proves the three statements of the author's
unpublished notes, reproduced as [images](docs/source). The
[restored reaction assumptions](docs/scope-correction.md), taken from the same notes and the
original conversation, apply to both rigidity targets. The two rigidity theorems adapt a
theorem of Beuvin and Farina; see [sources and related work](#sources-and-related-work).

**Lean status: all three theorems proved.** `SerrinEpigraph.verticalDerivative_pos`,
`SerrinEpigraph.rigidity_of_dimension_le_eight` and
`SerrinEpigraph.rigidity_of_oneSidedLinearBound` are proved, the rigidity targets under the
restored reaction assumptions. `python3 scripts/check-proof-status.py` reports that each
depends only on `propext`, `Classical.choice` and `Quot.sound`; the development has no
proof holes (the three `sorry`s in `Challenge.lean` are the specification holes).
The sandboxed Linux Comparator in CI accepted all three statements with the Lean, NanoDa
and con-ron kernels on commit `d057a0d`
([run 44746773713](https://github.com/CoolRmal/serrin-epigraph/actions/runs/44746773713));
see the [verification record](docs/verification.md).

The [detailed mathematical proofs of both rigidity theorems](docs/rigidity-proof/theorems.md)
and [formalization execution plan](docs/rigidity-proof/formalization-plan.md) are the
informal blueprint of the Lean proof; see the
[chapter index and review notes](docs/rigidity-proof/README.md). The Lean proof follows it
except for the flux identification HA4.1, which is proved by a phase-primitive calibration
(`AlignedFluxCalibration*.lean`, `PhaseCalibration*.lean`) instead of a level-set change of
variables.

**Rigidity:** `SerrinEpigraph/RigidityReduction.lean` assembles both rigidity theorems. A
blow-down of the solution gives a directed perimeter-minimizing cone, which is a half-space
or a vertical cylinder. In dimension at most eight, cone classification (De Giorgi
ε-regularity, Schauder smoothness, Simons' theorem including the planar chord argument, and
dimension reduction) excludes the cylinder; under a one-sided linear bound the cylinder is
excluded in every dimension. From a half-space blow-down, the Wang-type tilt-excess decay of
the diffuse one-phase problem (harmonic approximation HA0–HA12) gives a uniform boundary
coarse cone, and the sliding method yields the affine one-dimensional conclusion.

**Proved:** `SerrinEpigraph.verticalDerivative_pos` establishes strict vertical
monotonicity. Its proof includes boundary geometry, weak linearization with only
the stated regularity, the quotient energy estimate, cutoff moments, Hölder
interpolation, the mass-growth contradiction, and a weak strong-maximum principle
proved using cubic comparison tests and exponential annular barriers. The entire
chain uses only `propext`, `Classical.choice`, and `Quot.sound`, with no proof holes.
Its [sandboxed three-kernel Comparator check passed](docs/verification.md).

The [reaction reduction](docs/reaction-reduction.md) is also proved: any positive
argument with negative reaction value bounds the solution from above. Thus an
unbounded solution requires nonnegative reaction on the entire nonnegative
half-line. For every solution, the reaction is nonnegative on its range and the
solution is superharmonic. These consequences retain the original hypotheses.

Under the restored rigidity assumptions, **the solution converges to one along
every vertical ray**. `BallLowerBound.lean` and `LimitOne.lean` prove this using
an explicit polynomial comparison on large interior balls, compact contact,
and the reaction quotient condition. It is one ingredient of the rigidity proofs.

The **Modica gradient estimate** and **surface-scaled ball-energy monotonicity**
are also proved under the original rigidity assumptions. The proof obtains a
global gradient bound by a weak Bernstein argument and controls maxima escaping
to infinity by quadratic penalization. It requires no extra regularity or
assumed gradient estimate.

An [informal variational reduction](docs/variational-reduction.md) now derives a
common vertical limit and minimization of the general free-boundary energy.
The development now proves phase-energy minimality against normalized locally
Lipschitz compact perturbations, together with compactness and perimeter
minimality against **arbitrary measurable competitors** agreeing with the limit
outside a smaller concentric closed ball. Agreement may hold almost everywhere.
That same phase is invariant almost everywhere under each positive dilation,
has finite local perimeter and vertical order, and both phases have positive
measure; see the [proof obligations](docs/proof-plan.md).
Along one common sequence, potential and kinetic energies balance locally, and
diffuse energy agrees asymptotically with primitive gradient mass. On every
origin-centered ball, their positive homogeneous mass limit is now identified
with the interface constant times the limiting phase's perimeter.
General finite-perimeter recovery is proved: smooth phase averages, positive
variable transition widths, and threshold averaging give competitors with the
sharp asymptotic action-perimeter bound along the original scale sequence's
subsequences. Under either one-sided cone constraint, a nontrivial phase cannot
be invariant under all vertical translations.
The [reaction-regime audit](docs/rigidity-regimes.md)
concerns a broader reaction class investigated before the source-context correction;
those degenerate and unbounded cases are not part of the corrected rigidity targets.

## Statements

Let

$$
n\ge2,\qquad g\in C^1(\mathbb R^{n-1}),\qquad
\Omega=\{(x',x_n):x_n>g(x')\}.
$$

The common assumptions are

$$
u\in C^2(\Omega)\cap C^1_{\mathrm{loc}}(\overline\Omega),\qquad
-\Delta u=f(u),\qquad u>0\quad\text{in }\Omega,
$$

$$
u=0,\qquad \partial_\nu u=-\kappa\quad\text{on }\partial\Omega,
\qquad\kappa>0,
$$

$$
f\in C^1_{\mathrm{loc}}([0,\infty)),\qquad f(s)-sf'(s)\ge0\quad(s>0),
$$

$$
\liminf_{R\to\infty}\frac{\log\left(1+\int_{\Omega\cap B_R}u^2\,dx\right)}R=0.
$$

For targets 2 and 3, the source context additionally requires

$$
f(s)>0\quad(0<s<1),\qquad f(1)=0,\qquad f'(1)<0,\qquad 0<u<1.
$$

These include the original example of the reaction given by

$$
f(s)=s-s^p,\qquad p>1.
$$

The three targets are:

1. Strict vertical monotonicity throughout the domain.
2. If the ambient dimension is at most eight, an affine graph and a profile in
   the inward normal direction.
3. If the ambient dimension is at least nine, the same rigidity when the graph
   has either a global linear lower bound or a global linear upper bound.

The rigidity conclusion is

$$
g(x')=a\cdot x'+b,\qquad
u(x',x_n)=U\!\left(\frac{x_n-a\cdot x'-b}{\sqrt{1+|a|^2}}\right)
\quad\text{in }\Omega.
$$

The reaction assumptions were restored after consulting the original conversation
and project notes. See the [scope correction](docs/scope-correction.md).
The rigidity targets do not classify arbitrary reactions outside that source setting.
The proof of the third theorem does not use its dimension restriction: under a one-sided
linear bound the argument works in every dimension.

## Sources and related work

The three statements come from the author's unpublished notes. The vertical monotonicity
theorem is the author's own. The two rigidity theorems adapt published results:

- N. Beuvin and A. Farina, *Serrin's overdetermined problems on epigraphs*,
  [arXiv:2502.04812](https://arxiv.org/abs/2502.04812). Their Theorem 2.1 proves the same
  rigidity conclusion for **vertically monotone** solutions with a specified Allen–Cahn type
  nonlinearity: in dimension at most eight without further conditions, and in dimension at
  least nine under a global linear lower or upper bound of the graph. The second and third
  theorems here replace the monotonicity hypothesis by the first theorem, for the reaction
  class above. The Lean proof follows the route of their proof: a blow-down to a
  perimeter-minimizing cone, followed by the flatness argument of Wang and Wei.
- K. Wang and J. Wei, *On Serrin's overdetermined problem and a conjecture of Berestycki,
  Caffarelli and Nirenberg*, [arXiv:1502.04680](https://arxiv.org/abs/1502.04680). Their
  Theorem 1.4 proves half-space rigidity in dimension at most eight for vertically monotone
  solutions under standing assumptions W1–W5, which the reaction class above satisfies
  ([check](docs/rigidity-proof/low-dimensional.md)).
- K. Wang, *A new proof of Savin's theorem on Allen-Cahn equations*,
  [arXiv:1401.6480](https://arxiv.org/abs/1401.6480). The tilt-excess decay of the Lean proof
  follows this method, re-derived for the one-phase problem used here.
- M. del Pino, F. Pacard and J. Wei, *Serrin's overdetermined problem and constant mean
  curvature surfaces*, Duke Math. J. 164 (2015), [arXiv:1310.4528](https://arxiv.org/abs/1310.4528).
  They construct epigraphs in dimension at least nine that are not half-spaces and carry
  solutions of the overdetermined problem, so the third theorem needs a hypothesis on the graph.

None of these results is assumed in Lean: every step is proved from Mathlib. Novelty of the
statements has not been established by a literature search. A GitHub search (November 2026)
found no other Lean formalization of these results.

## Layout and verification

- `Challenge.lean`: independent specification, importing only Mathlib, with
  three deliberate specification holes.
- `SerrinEpigraph/Basic.lean`: Euclidean geometry, PDE hypotheses, growth, and conclusions.
- `SerrinEpigraph/Main.lean`: the three proved targets.
- `SerrinEpigraph/RigidityReduction.lean`: assembly of the two rigidity theorems.
- `Solution.lean`: imports the development, never `Challenge`.
- `comparator.json`: exact target names and the three standard permitted axioms.
- `comparator-monotonicity.json`: separate verification of the monotonicity theorem alone.
- `.github/workflows/verify.yml`: build, proof audit, sandboxed Comparator, and
  manually requested full Palomar preflight.

The horizontal dimension in Lean is `m`; the source's ambient dimension is `m + 1`.
The mass condition uses an extended-real liminf, so divergence to positive
infinity cannot masquerade as zero. Boundary derivatives are taken within the
closure, and the metric and volume are Euclidean.

```sh
lake exe cache get
lake build SerrinEpigraph Challenge Solution
python3 scripts/check-proof-status.py
./scripts/verify-comparator.sh
```

The final command requires Linux and Bubblewrap. On macOS,
`./scripts/verify-comparator.sh --preliminary` can run a local check without the
Linux sandbox; it is not a Palomar mechanical-verification report.
The additional CI job uses `--config comparator-monotonicity.json` to check the
first theorem independently. It does not replace the three-theorem acceptance
configuration.

## Reproducibility and attribution

Lean is pinned to `v4.35.0-rc2`; Mathlib and transitive dependencies are locked in
`lake-manifest.json`. Yongxi (Aaron) Lin is the author of the three statements and the
responsible maintainer; the images in `docs/source` reproduce the author's notes. AI agents
produced most of the development under the author's direction: Codex agents worked on the
transcription, implementation and review, and Claude Code agents (Claude Opus 5.5) completed
the two rigidity formalizations. The author checked that `Challenge.lean` states the intended
results. No independent human review of the proofs is claimed.

Code is licensed under Apache-2.0. The supplied source images retain their
original attribution and rights; the code license does not assert ownership of them.
