# A negative reaction value forces boundedness

This is a self-contained **informal mathematical proof**, not a Lean-verified
result. It is a useful reduction for the remaining rigidity targets, but does
not prove either target or justify applying an Allen–Cahn classification.

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

In particular, an unbounded solution under the common hypotheses requires

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

The zero extension of the solution is continuous because its boundary trace
is zero. On any fixed compact set, the support of the excess is therefore
contained in a compact subset of the domain: on that support the solution is
at least the strictly positive level used above. In particular, the excess
belongs locally to the Sobolev space with one square-integrable derivative,
and its gradient in the domain is

$$
\nabla w=\mathbf1_{\{u>s_0\}}\nabla u
\qquad\text{almost everywhere}.
$$

For any compactly supported Lipschitz cutoff, the weak equation may thus be
tested with the excess times the square of the cutoff. This test is justified
by smooth approximation inside its compact support in the domain. The usual
Sobolev chain rule, or smooth approximation of the positive part, gives

$$
\int\eta^2|\nabla w|^2
+2\int w\eta\,\nabla w\cdot\nabla\eta
=\int_\Omega f(u)w\eta^2
\leq-\lambda\int w^2\eta^2.
$$

Here the reaction bound is used only where the excess is positive, and the
solution is at least its excess there. Completing the square yields

$$
\lambda\int w^2\eta^2
+\int|\nabla(w\eta)|^2
\leq\int w^2|\nabla\eta|^2.
$$

All integrals without an indicated domain are over the ambient Euclidean
space. Compactness and the stated regularity make them finite.

## 3. Fixed-width cutoffs force exponential square mass

Set

$$
W(R)=\int_{B_R}w^2,\qquad
L=\sqrt{\frac2\lambda}>0,
$$

and, for each positive radius, choose

$$
\eta_R(x)=
\min\left\{1,\frac{(R+L-|x|)_+}{L}\right\}.
$$

This cutoff equals one on the ball of radius under consideration, is zero
outside the ball with radius increased by the fixed width, and has gradient
norm at most the reciprocal width almost everywhere. The preceding estimate
therefore implies

$$
\lambda W(R)\leq L^{-2}W(R+L),\qquad
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

This contradicts the exact mass hypothesis. The excess is therefore zero,
which proves the asserted bound. The conclusion about an unbounded solution
follows by contraposition for positive arguments and continuity at zero.

The proof uses the structural inequality, the equation, the zero Dirichlet
trace, and the mass hypothesis. It does not use the constant Neumann datum or
the established strict vertical monotonicity. In the remaining unbounded,
nonnegative-reaction case, this reduction supplies neither integrability of
the reaction on the positive half-line nor the finite surface tension needed
by the cited perimeter argument; see [the rigidity audit](rigidity-gap.md).
