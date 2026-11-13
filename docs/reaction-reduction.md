# A negative reaction value forces boundedness

This reduction is proved in
[`ReactionReduction.lean`](../SerrinEpigraph/ReactionReduction.lean), under the
unchanged common image hypotheses, with no proof holes and only the standard
Lean axioms. It does not prove either rigidity target or justify applying an
Allen–Cahn classification.

Assume the common hypotheses from the images. Write

$$
V(R)=\int_{\Omega\cap B_R}u^2,\qquad
\liminf_{R\to\infty}\frac{\log(1+V(R))}{R}=0.
$$

If there is a positive number with negative reaction value, then

$$
s_0>0,\quad f(s_0)<0
\quad\Longrightarrow\quad
u(x)\leq s_0\quad\text{for every }x\in\Omega.
$$

The declaration is `Hypotheses.solution_le_of_reaction_neg`. In particular,
`Hypotheses.reaction_nonneg_of_unbounded` proves that an unbounded solution requires

$$
f(s)\geq0\qquad\text{for every }s\geq0.
$$

## 1. The reaction has a negative linear upper bound

The structural inequality gives

$$
\left(\frac{f(s)}s\right)'
=\frac{sf'(s)-f(s)}{s^2}\leq0\qquad(s>0).
$$

Consequently, with

$$
\lambda=-\frac{f(s_0)}{s_0}>0,
$$

we have

$$
f(s)\leq-\lambda s\qquad(s\geq s_0).
$$

## 2. The positive excess satisfies a coercive cutoff estimate

Extend the solution by zero outside the domain and let

$$
w=(u-s_0)_+\quad\text{in }\Omega,\qquad
w=0\quad\text{outside }\Omega.
$$

The zero trace and continuity make the excess vanish in an interior
neighborhood of every boundary point. Multiplying it by a compactly supported
cutoff therefore gives support in a compact subset of the domain. To obtain
continuously differentiable tests, define, for a positive parameter,

$$
T_\varepsilon(t)=\frac{t_+^2}{t_++\varepsilon},\qquad
T_\varepsilon'(t)=\frac{t_+(t_++2\varepsilon)}{(t_++\varepsilon)^2}.
$$

`SmoothExcess.lean` proves these formulas, continuous differentiability,
convergence to the positive part, and

$$
0\le T_\varepsilon(t)\le t_+,\qquad
0\le T_\varepsilon'(t)\le1,\qquad
T_\varepsilon(t)^2\le T_\varepsilon'(t)t_+^2.
$$

Test the weak equation with the zero extension of

$$
T_\varepsilon(u-s_0)\eta^2.
$$

The derivative inequality gives the pointwise Young estimate needed to
absorb the mixed gradient term. The negative reaction tail then implies

$$
\lambda\int_\Omega T_\varepsilon(u-s_0)^2\eta^2
\le\int_\Omega w^2|\nabla\eta|^2.
$$

Dominated convergence removes the smoothing parameter. The resulting theorem
`Hypotheses.excess_coercive_estimate` in `CoerciveEstimate.lean` is

$$
\lambda\int_\Omega w^2\eta^2\le\int_\Omega w^2|\nabla\eta|^2.
$$

`Excess.lean` proves all test-support, regularity, and integrability facts used
here. In particular the estimate controls the squared excess, so the original
square-mass assumption suffices without a fourth-moment bound.

## 3. Fixed-width cutoffs force exponential square mass

Set

$$
W(R)=\int_{B_R}w^2.
$$

`FixedWidthCutoff.lean` constructs a positive universal constant and, for every
positive radius and width, a compactly supported continuously differentiable
cutoff satisfying

$$
0\le\eta_R\le1,\quad
\eta_R=1\text{ on }B_R,\quad
\operatorname{supp}\eta_R\subset B_{R+L},\quad
|\nabla\eta_R|\le\frac C L.
$$

Choose a fixed width large enough. `ExcessGrowth.lean` proves

$$
L=\frac{2C}{\sqrt\lambda},\qquad
\lambda W(R)\leq\frac{C^2}{L^2}W(R+L),\qquad
W(R+L)\geq2W(R).
$$

If the excess is nonzero, continuity supplies a positive radius with positive
square mass. Iterating from that radius gives

$$
W(R_0+kL)\geq2^kW(R_0),\qquad W(R_0)>0,
\qquad k=0,1,2,\ldots.
$$

For an arbitrary larger radius, take the integer part of the radius
difference divided by the width, and use monotonicity of the square mass.
This gives a bound at **every** sufficiently large radius, not merely along
a subsequence:

$$
W(R)\geq\frac{W(R_0)}2
\exp\left(\frac{\log2}{L}(R-R_0)\right)
\qquad(R\geq R_0).
$$

Since the nonnegative excess is at most the original solution,

$$
V(R)\geq W(R),\qquad
\liminf_{R\to\infty}\frac{\log(1+V(R))}{R}
\geq\frac{\log2}{L}>0.
$$

`CoerciveGrowth.lean` proves the contradiction with the exact extended-real
liminf hypothesis using an eventual exponential lower bound. The excess is
therefore zero, which proves the asserted bound. The conclusion about an
unbounded solution follows by contraposition for positive arguments;
`reaction_nonneg_zero` also proves nonnegativity at zero directly from the
reaction structure and continuity.

## 4. Nonnegativity throughout the solution range

If the reaction were negative at an interior solution value, the bound just
proved would make that point a global maximum in the domain. Fermat's theorem
would give zero gradient there, contradicting strict vertical monotonicity.
The final two corollaries, `Hypotheses.reaction_nonneg_on_solution` and
`Hypotheses.laplacian_nonpos`, establish

$$
f(u(x))\ge0,\qquad \Delta u(x)\le0\qquad(x\in\Omega).
$$

The boundedness argument uses the structural inequality, the equation, the zero Dirichlet
trace, and the mass hypothesis. It does not use the constant Neumann datum or
the established strict vertical monotonicity. The solution-range corollary does
use that proved monotonicity theorem. In the remaining unbounded,
nonnegative-reaction case, this reduction supplies neither integrability of
the reaction on the positive half-line nor the finite surface tension needed
by the cited perimeter argument; see [the rigidity audit](rigidity-gap.md).
