# Rigidity hypotheses requiring a proof

The three supplied images are the project's target statements. A detailed
informal proof of the first statement is present in the existing research
files. Those files also prove rigidity under additional reaction hypotheses.
They do not supply a proof of the two rigidity conclusions with exactly the
general hypotheses in the images. This note records the scope of those proofs
and the remaining deduction, not a counterexample to either conclusion.

## Comparison with the existing research files

The following references are to the original `EllipticPDEs` workspace sources,
audited through their concluding sections on 2026-11-13. These source files are
outside this standalone Lean repository.

| Original source and lines | What the proof establishes |
| --- | --- |
| `reports/商矩证明简化与无界解进展.md`, lines 9–69, 252–364 | General reaction monotonicity, with the same structural inequality and the first image's local regularity and Serrin boundary data. The final exponential lower bound also proves the image's weaker `liminf` mass condition. |
| `reports/三维七次反应Serrin上图域刚性证明.md`, lines 9–36, 553–690 | A full three-dimensional rigidity argument using Robin/Picone and Bochner identities with a quadratic energy bound. This part is explicitly derived rather than merely quoted from Wang–Wei, but it uses the seventh-power reaction, bounded solution range, and its specified Neumann constant. |
| `reports/任意维上图域单调性与八维Serrin刚性.md`, lines 7–30, 286–356 | Arbitrary-dimensional monotonicity and rigidity in dimensions at most eight for the power reaction with exponent greater than one and solution values strictly between zero and one. Lines 300–340 verify W1–W5 before invoking Wang–Wei. |
| `reports/一般非线性的高阶商矩与Serrin刚性.md`, lines 82–129 | A broader rigidity corollary, still assuming a positive reaction on the solution interval and a nondegenerate positive equilibrium. The proof explicitly separates these hypotheses from those needed for monotonicity. |
| `research_notes/商矩证明简化与无界解进展/literature.md`, lines 9–20, 73–83, 152–156 | The low-dimensional and one-sided-linear classifications are recorded for the specified Allen–Cahn class. The separate general-reaction, low-energy route in dimensions two and three has an additional energy hypothesis, which the mass assumption alone is not shown to supply. |
| `reports/商矩证明简化与无界解进展.md`, lines 555–765; `reports/Killing单调性与圆柱刚性再核查.md`, lines 443–449 | A complete harmonic classification for a product cylinder with a closed, compact, connected base. The later audit explicitly excludes extrapolation to a noncompact base or a different reaction. |
| `research_notes/商矩证明简化与无界解进展/simplified_proof.md`, lines 468–480, 723 | The argument yields fixed-domain stability and strict Killing monotonicity; it explicitly does not infer free-boundary stability or a complete Serrin-domain classification. |
| `research_notes/反例的几何推广与欧氏障碍/euclidean_transfer.md`, lines 113–179, 302–321 | The new nonmonotone Euclidean example has nonconstant Neumann data. These notes explicitly do not give a full Euclidean Serrin counterexample. The companion geometric and analytic notes construct examples on non-Euclidean products with exponential mass growth. |

In particular, the first proof is not merely a proposed route. Set

$$z=(u_n/u)^-,\qquad V(R)=\int_{\Omega\cap B_{2R}}u^2.$$

The report proves, for each integer greater than or equal to three,

$$\left(\int_{\Omega\cap B_R}u^2z^m\right)^{1/m}
\leq\frac{mC_\chi}{R}V(R)^{1/m}.$$

If the negative quotient is positive at one interior point, continuity supplies
a fixed ball with positive weighted mass and a positive lower bound there.
Lines 336–364 then give

$$\liminf_{R\to\infty}\frac{\log V(R)}R>0.$$

Replacing the radius by twice the radius shows that this contradicts precisely
the `liminf` condition in the first image, even though the report initially
states a limit condition. The final Harnack argument gives strict positivity.
The remaining issue is the passage from this valid monotonicity conclusion to
the two general-reaction rigidity statements, not the absence of the original
monotonicity proof.

The first image assumes

$$f(s)-s f'(s)\geq 0\qquad(s>0),$$

together with subexponential lower growth of the square mass. The second and
third images cite Wang–Wei and Beuvin–Farina after obtaining vertical
monotonicity. Their cited rigidity theorems require additional conditions on
the nonlinearity.

- [Wang–Wei, Theorem 1.4](https://arxiv.org/abs/1502.04680) assumes the
  specified potential conditions W1–W5; it does not assert rigidity for every
  reaction satisfying the displayed inequality.
- [Beuvin–Farina, Theorem 2.1](https://arxiv.org/html/2502.04812v2)
  explicitly assumes a specified Allen–Cahn nonlinearity, defined immediately
  beforehand by W1–W4. In particular, the potential has a positive second
  derivative near its positive equilibrium. Its one-sided linear graph bound
  does not replace those reaction assumptions.

## The harmonic case is included in the target

The reaction

$$f\equiv 0$$

satisfies the target's structural inequality, but not the cited Allen–Cahn
conditions. Normalizing the boundary gradient to one gives the graphical
one-phase Bernoulli problem. Its global viscosity solutions have a dimensional
gradient bound, so the square mass grows at most polynomially and the target's
mass condition does not eliminate this case.

[Engelstein–Fernández-Real–Yu](https://arxiv.org/html/2212.08847), Theorem 1.1,
proves graphical rigidity for

$$n\leq n_{\mathrm{local}}^*+1,$$

where their critical flat-cone dimension is at most six. Thus even the maximal
value in that theorem gives dimension seven, rather than the target's eight.
Their Lemma 2.5 supplies the gradient bound just used. This is a precise limit
of that cited theorem, not a claim that no later theorem could settle the case.

## Degenerate equilibria are also permitted

The structural inequality does not force a nondegenerate equilibrium, even for
bounded solutions on a half-space. For example, take

$$f(s)=(1-s)^3,\qquad
U(t)=1-\frac{1}{1+t/\sqrt{2}}\qquad(t\geq0).$$

Direct differentiation gives

$$f(s)-s f'(s)=(1-s)^2(1+2s)\geq0,\qquad
-U''=f(U),\qquad U'(0)=\frac1{\sqrt2}.$$

The solution is positive and bounded for positive height, with polynomial
square mass. But

$$f(1)=f'(1)=0,$$

so the required strict potential-convexity condition at the equilibrium fails.
This is a positive example of the target hypotheses, not a nonrigid example.

## Boundedness and low energy cannot be inferred

There are also unbounded solutions satisfying every common target assumption.
On the horizontal half-space, direct differentiation verifies

$$f(s)=(1+s)^{-3},\qquad U(t)=\sqrt{1+2t}-1,\qquad
-U''=f(U),\qquad U'(0)=1.$$

Here

$$f(s)-sf'(s)=\frac{1+4s}{(1+s)^4}>0,\qquad
0<U(t)^2\leq2t\quad(t>0).$$

Thus the square mass has polynomial growth, while the solution is unbounded
and the reaction has no finite positive equilibrium. A similar example is
already given in the original `literature.md`, lines 107–150. Consequently,
boundedness and a finite equilibrium cannot be recovered from the target
assumptions as an intermediate lemma.

Likewise, the low-energy hypothesis in
[Beuvin–Farina, Theorem 3.1](https://arxiv.org/html/2502.04812v2) is not a
consequence of the target mass condition: the harmonic half-space solution has

$$u(x)=\kappa x_n,\qquad
\int_{\{x_n>0\}\cap B_R}|\nabla u|^2
=\frac{\kappa^2\omega_n}{2}R^n.$$

In dimension three this fails the required little-oh bound relative to

$$R^2\log R.$$

These examples already have the desired rigidity. They disprove proposed
intermediate reductions, not the target conclusions.

## The perimeter energy estimate is not automatic

The admissible flat example

$$
f(s)=(1+s)^{-3},\qquad U(t)=\sqrt{1+2t}-1,\qquad \kappa=1
$$

also obstructs extending the cited perimeter-blowdown proof unchanged. The
structural remainder is positive, and its square mass has polynomial growth:

$$
f(s)-sf'(s)=\frac{1+4s}{(1+s)^4}>0,\qquad U(t)^2\leq2t.
$$

Nevertheless, the potential normalized by the boundary gradient and the
one-dimensional energy density are

$$
W_\kappa(s)=\frac{\kappa^2}{2}-\int_0^s f(r)\,dr
=\frac1{2(1+s)^2},\qquad
\frac12U'(t)^2+W_\kappa(U(t))=\frac1{1+2t}.
$$

Integration in the vertical variable gives

$$
\int_0^T\left(\frac12U'(t)^2+W_\kappa(U(t))\right)dt
=\frac12\log(1+2T).
$$

Bounding the horizontal cross-sections above by their radius at height zero,
and below by their radius at height half the ball radius, consequently gives

$$
E(B_R\cap\Omega)\asymp R^{n-1}\log R.
$$

Thus a uniform energy bound proportional to boundary area does not follow
from the pictured hypotheses, even when the primitive of the reaction is
finite and both linear graph bounds hold. Beuvin–Farina's perimeter-phase
compactness argument needs replacement in this regime. The example is flat;
it refutes that proposed intermediate estimate, not either rigidity target.

The structural inequality does make the fixed-domain energy convex after
writing the squared solution as the dependent variable: if the derivative of
the primitive is the reaction, then

$$
\frac{d^2}{ds^2}\bigl[-F(\sqrt s)\bigr]
=\frac{f(t)-tf'(t)}{4t^3}\geq0,\qquad t=\sqrt s.
$$

The free-boundary energy additionally has the positive phase-cost term. The
fixed-domain convexity alone does not prove the free-boundary minimization
needed in the cited geometric classification.

## A route for the harmonic one-sided case

There is a concrete proof route for the harmonic subclass of the third image.
After normalizing the boundary slope, the zero extension is a graphical
Bernoulli solution. [Engelstein–Fernández-Real–Yu, Theorem 1.4 and Lemma
2.8](https://arxiv.org/html/2212.08847) give global minimization and homogeneous
blowdowns, including convergence of the phases.
[Edelen–Li–Zhu, Theorem 2.2](https://arxiv.org/html/2606.01715v1#S2.SS1)
then gives a dichotomy: the solution is flat, or every blowdown is nonflat and
invariant under vertical translations.

The following deduction combines these results. A one-sided linear lower
bound for the graph preserves a downward cone in the zero phase of each
blowdown. Vertical invariance would then make the entire blowdown zero,
contradicting nondegeneracy. An upper bound preserves an upward cone in the
positive phase; vertical invariance would eliminate the zero phase, again
contradicting the nontrivial Bernoulli free boundary. Thus the flat alternative
holds, in every dimension. This is an informal deduction for the harmonic
subclass, not yet a Lean proof or a proof for general reactions.

Without the one-sided bound, this argument leaves the nonflat cylindrical
blowdown alternative in ambient dimension eight. For nonzero reactions,
neither the harmonic minimization theorem nor its blowdown dichotomy applies
directly. Establishing an appropriate general variational reduction and
classification remains necessary for this route to prove the exact targets.

The examined local proofs and cited primary sources do not supply the full
general classification. No counterexample satisfying all target assumptions has
been established in this audit. A complete proof must establish that broader
rigidity result or another argument. Adding
Allen–Cahn hypotheses would change the requested statements and is not done.

## Subsequent general variational reduction

The [variational argument](variational-reduction.md) now supplies a common
vertical limit and free-boundary minimization under the exact hypotheses.
It is an informal proof using additional classical analytic ingredients,
not a Lean theorem. It addresses the minimization issue identified above,
including the phase cost, without extending the cited Allen–Cahn theorems.

The remaining step is classification of these general minimizers. The
[reaction-regime audit](rigidity-regimes.md) checks newer primary results
and explicit admissible examples: the bounded branch allows infinitely flat
wells, and unbounded branches have several distinct energy scalings. None
of the checked classification theorems covers all of these cases. The
harmonic dimension-eight case remains a separate unresolved proof obligation.
