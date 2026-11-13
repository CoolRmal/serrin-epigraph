# Serrin epigraph monotonicity and rigidity

A Lean 4 project depending on Mathlib, targeting the three statements in the
[source images](docs/source). The original assumptions are preserved.

**Status: incomplete.** The definitions and three theorem statements compile.
The three main proofs are still missing. A successful `lake build` is not a proof
certificate: Comparator must reject the current `Solution` because of `sorryAx`.
No Palomar registration or successful Comparator result is claimed.

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

The cited Wang–Wei and Beuvin–Farina theorems have additional Allen–Cahn-type
assumptions absent from these images. They do not directly establish the two
rigidity targets as stated. This is a gap in the supplied justification, not a
proved counterexample. See the [independent statement audit](docs/statement-audit.md)
and [proof plan](docs/proof-plan.md).

## Layout and verification

- `Challenge.lean`: independent specification, importing only Mathlib, with
  three deliberate specification holes.
- `SerrinEpigraph/Basic.lean`: Euclidean geometry, PDE hypotheses, growth, and conclusions.
- `SerrinEpigraph/Main.lean`: the three unproved proof-development targets.
- `Solution.lean`: imports the development, never `Challenge`.
- `comparator.json`: exact target names and the three standard permitted axioms.
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

## Reproducibility and attribution

Lean is pinned to `v4.35.0-rc2`; Mathlib and transitive dependencies are locked in
`lake-manifest.json`. The user-supplied images are the source of the three claims.
No authorship of the images is inferred. Codex agents assisted with transcription,
implementation, and review. No independent human mathematical review is claimed.

Code is licensed under Apache-2.0. The supplied source images retain their
original attribution and rights; the code license does not assert ownership of them.
