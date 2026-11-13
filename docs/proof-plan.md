# Proof obligations

The monotonicity proof is complete. The two rigidity obligations remain open.
All three target statements in `SerrinEpigraph/Main.lean` remain unchanged from
the source images.

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

This does not close the classification step. The exact hypotheses still
admit infinitely flat finite equilibria, negative-power potential tails, and
the harmonic problem in ambient dimension eight. The [newer-literature and
scaling audit](rigidity-regimes.md) identifies the additional results that
would be needed; it does not assert a classification or a counterexample.

The supplied citations do not currently discharge either rigidity obligation.
The Allen–Cahn assumptions in Wang–Wei and Beuvin–Farina are not among the common
image hypotheses. The zero reaction is a concrete admissible edge case that
prevents simply importing those informal theorems unchanged.

Both rigidity targets require a proof for the exact general reaction class,
followed by formalization of its analytic and geometric dependencies. A new
reference, a missing argument, or an actual counterexample would change this
assessment. No counterexample has been established. The project must not claim
completion while these targets remain open.

## Acceptance

All three proof targets must compile without proof holes, use only the standard
Lean axioms, match independent Challenge statements under Comparator, and pass
the complete pinned Palomar mechanical workflow before registry intake.
