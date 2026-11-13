# Serrin epigraph monotonicity and rigidity

A Lean 4 project depending on Mathlib, targeting the three statements in the
[source images](docs/source) together with the original conversation and notes.
The [restored reaction assumptions](docs/scope-correction.md) apply to both rigidity targets.

**Status: one of three theorems proved.** The strict vertical monotonicity theorem
is complete under the original assumptions. The two rigidity proofs remain open.
A successful `lake build` is not a certificate for all three: the full Comparator
configuration must still reject the two proof holes. No Palomar registration is claimed.

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
solution is superharmonic. These consequences retain the original hypotheses;
the two rigidity proofs remain incomplete.

Under the restored rigidity assumptions, **the solution converges to one along
every vertical ray**. `BallLowerBound.lean` and `LimitOne.lean` prove this using
an explicit polynomial comparison on large interior balls, compact contact,
and the reaction quotient condition. This is a proved prerequisite for the
remaining rigidity argument, not a proof of either classification theorem.

The **Modica gradient estimate** and **surface-scaled ball-energy monotonicity**
are also proved under the original rigidity assumptions. The proof obtains a
global gradient bound by a weak Bernstein argument and controls maxima escaping
to infinity by quadratic penalization. It requires no extra regularity or
assumed gradient estimate. The geometric classification and transfer of flatness
to the original solution remain unfinished.

An [informal variational reduction](docs/variational-reduction.md) now derives a
common vertical limit and minimization of the general free-boundary energy.
The development now proves phase-energy minimality against normalized locally
Lipschitz compact perturbations, together with compactness and graph-competitor
perimeter comparison for a limiting phase. That same phase can now be chosen
invariant almost everywhere under each positive dilation, with finite local
perimeter and vertical order; see the [proof obligations](docs/proof-plan.md).
Nontriviality, the remaining hypotheses for geometric classification,
classification itself, and transfer of flatness remain open.
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
The remaining work is to formalize the rigidity arguments, not to classify
arbitrary reactions outside that source setting.

## Layout and verification

- `Challenge.lean`: independent specification, importing only Mathlib, with
  three deliberate specification holes.
- `SerrinEpigraph/Basic.lean`: Euclidean geometry, PDE hypotheses, growth, and conclusions.
- `SerrinEpigraph/Main.lean`: the proved monotonicity theorem and two open rigidity targets.
- `Solution.lean`: imports the development, never `Challenge`.
- `comparator.json`: exact target names and the three standard permitted axioms.
- `comparator-monotonicity.json`: separate verification of the one completed theorem.
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
completed first theorem independently. It does not replace the three-theorem
acceptance configuration.

## Reproducibility and attribution

Lean is pinned to `v4.35.0-rc2`; Mathlib and transitive dependencies are locked in
`lake-manifest.json`. The user-supplied images are the source of the three claims.
No authorship of the images is inferred. Codex agents assisted with transcription,
implementation, and review. No independent human mathematical review is claimed.

Code is licensed under Apache-2.0. The supplied source images retain their
original attribution and rights; the code license does not assert ownership of them.
