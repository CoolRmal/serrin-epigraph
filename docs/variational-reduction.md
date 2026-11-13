# An informal variational reduction under the exact hypotheses

This is a mathematical argument, **not a Lean proof**. It uses the proved
strict vertical monotonicity and reaction-sign reduction, followed by
classical Harnack inequalities, interior elliptic compactness, positive
harmonic Liouville, and Sobolev extension, trace, and chain rules. Those
additional analytic ingredients and the calibration below have not been
implemented in this project. No hypothesis on the reaction or target has
been changed.

The conclusion is global minimization for a general one-phase energy. It
does not complete either remaining rigidity theorem. In particular, no
classification theorem for all the resulting potentials is asserted.

## Starting assumptions and notation

Let the dimension, graph, solution, reaction, and boundary slope satisfy the
common pictured hypotheses: the graph is continuously differentiable, the
solution is twice continuously differentiable inside the domain and locally
once continuously differentiable up to its boundary, and the reaction is
continuously differentiable on the nonnegative half-line. Write

$$
\Omega=\{(x',x_n):x_n>g(x')\},\qquad
-\Delta u=f(u),\qquad u>0\text{ in }\Omega,
$$

$$
u=0,\qquad \partial_\nu u=-\kappa\text{ on }\partial\Omega,
\qquad \kappa>0.
$$

The existing monotonicity and reaction-sign reductions give

$$u_n>0,\qquad f(u)\geq0\quad\text{in }\Omega.$$

The square-mass assumption has already been used to obtain these two facts.
The argument below needs no further growth assumption or one-sided bound
on the graph. The structural condition and its consequence are

$$f(s)-sf'(s)\geq0\qquad(s>0),$$

$$
q(s)=\frac{f(s)}s\text{ is nonincreasing on }(0,\infty),
\qquad
q'(s)=\frac{sf'(s)-f(s)}{s^2}\leq0.
$$

Define, at each finite nonnegative argument,

$$
F(s)=\int_0^s f(r)\,dr,\qquad
W_\kappa(s)=\frac{\kappa^2}{2}-F(s).
$$

No sign condition on this potential, or finiteness of the primitive at
infinity, is assumed. Denote the zero extension of the solution by

$$
\bar u(x)=\begin{cases}u(x),&x\in\Omega,\\0,&x\notin\Omega.\end{cases}
$$

The prescribed local boundary regularity and zero Dirichlet trace give
continuity and local Sobolev regularity of this extension, with

$$\nabla\bar u=\mathbf1_\Omega\nabla u\quad\text{almost everywhere}.$$

## An entire-space Liouville lemma

Suppose a positive twice continuously differentiable function on the whole
of Euclidean space satisfies

$$-\Delta V=f(V)\geq0,$$

with the same nonincreasing quotient. Then it is constant, and its value
is a zero of the reaction. Here is an elementary comparison argument for
the nonlinear part of this assertion.

If the reaction is positive at an attained value, write

$$a=V(x_0)>0,\qquad c=\frac{f(a)}a>0.$$

The quotient inequality gives

$$f(s)\geq cs\qquad(0<s\leq a).$$

In dimension denoted by the integer below, use the following polynomial
on any ball of radius large enough that the displayed constant is less
than the reaction bound:

$$
\phi_R(x)=\left(1-\frac{|x|^2}{R^2}\right)^2,
\qquad
\lambda_R=\frac{(d+2)^2}{R^2}<c.
$$

It has zero boundary values and maximum one at the center. Its derivatives
inside the ball are

$$
\nabla\phi_R=-\frac{4x}{R^2}
 \left(1-\frac{|x|^2}{R^2}\right),
\qquad
-\Delta\phi_R=\frac{4d-4(d+2)t}{R^2},
\quad t=\frac{|x|^2}{R^2}.
$$

The exact identity

$$
(d+2)^2(1-t)^2-\bigl(4d-4(d+2)t\bigr)
=\bigl((d+2)(1-t)-2\bigr)^2+4
$$

therefore gives

$$-\Delta\phi_R\leq\lambda_R\phi_R.$$

Start a small positive multiple of this polynomial below the entire
solution; this is possible because the solution has a positive minimum
on the closed ball. Increase the multiplier toward the attained value.
A first contact before reaching that multiplier would be interior. At
such a contact, for the contact multiplier, one has

$$
V=\tau\phi_R\leq a,\qquad
-\Delta(V-\tau\phi_R)
\geq(c-\lambda_R)V>0.
$$

This contradicts the second derivative test at a zero minimum. Thus the
comparison reaches the full multiplier. Centering the ball at any point
shows that the entire solution is everywhere at least the attained value.
At its original attaining point this contradicts the equation and the
second derivative test. The reaction consequently vanishes at every
solution value. The solution is now positive and harmonic on the whole
space, so the classical positive harmonic Liouville theorem makes it
constant.

## A common vertical limit

For sufficiently large translation parameter on any fixed compact set,
consider

$$u_t(x)=u(x+t e_n).$$

These functions increase with the parameter. On a fixed compact
neighborhood, choose one parameter for which the function is positive
throughout that neighborhood. Its positive minimum gives a common lower
bound, and the quotient inequality gives the locally uniform coefficient
bounds

$$
0\leq q(u_t(x))\leq q(m_K)<\infty,
\qquad u_t(x)\geq m_K>0.
$$

The linear equations satisfied by the translates are

$$-\Delta u_t=q(u_t)u_t.$$

Harnack chains on fixed compact neighborhoods show that, if the vertical
limit is finite at one point, the translates are locally bounded everywhere.
Interior elliptic estimates then give local compactness in twice
continuously differentiable functions. Monotone convergence identifies a
unique positive entire limit solving the same equation; the reaction
remains nonnegative on its range. The preceding Liouville lemma makes the
limit a constant. The convergence is locally uniform, and the gradients
converge locally uniformly to zero.

If any point has infinite limit, no point can have finite limit by the
same Harnack argument. Monotonicity, continuity, and a finite covering of
each compact set make divergence to infinity locally uniform. Hence exactly
one of the following alternatives holds:

$$
u_t\longrightarrow L\in(0,\infty),\qquad
f(L)=0,\qquad 0<u<L\text{ in }\Omega;
$$

$$u_t\longrightarrow+\infty\quad\text{locally uniformly}.$$

The strict inequality in the finite case follows from strict vertical
monotonicity. Thus the original solution is bounded exactly in the first
case. In the second case every vertical fiber covers the whole positive
half-line. No nondegeneracy of a finite equilibrium is used.

## Calibration from the vertical foliation

In this section, let the upper endpoint mean the finite common limit or
positive infinity, according to the alternative just proved. For every
positive height below that endpoint, there is a unique translation such
that

$$
u(x+\tau(x,s)e_n)=s,
\qquad
p(x,s)=\nabla u(x+\tau(x,s)e_n).
$$

Strict vertical monotonicity and the implicit function theorem make this
field continuously differentiable at positive heights. The common-limit
property and boundary regularity extend it continuously to height zero,
uniformly on compact horizontal sets. The boundary condition gives

$$
p(x,0)=\frac{\kappa(-\nabla g(x'),1)}
 {\sqrt{1+|\nabla g(x')|^2}},
\qquad |p(x,0)|=\kappa.
$$

In particular, the field is bounded on any compact set of spatial points
and heights in a closed interval strictly below the upper endpoint.
Implicit differentiation, with derivatives of the original solution
evaluated at the translated point, gives

$$
\partial_s\tau=\frac1{u_n},\qquad
\partial_{x_i}\tau=-\frac{u_i}{u_n},\qquad
\operatorname{div}_x p=-f(s)-p\cdot\partial_s p.
$$

Set

$$
Q(x,s)=\frac12|p(x,s)|^2+F(s)-\frac{\kappa^2}{2}
      =\frac12|p(x,s)|^2-W_\kappa(s).
$$

The two essential identities are

$$\operatorname{div}_x p+\partial_sQ=0,\qquad Q(x,0)=0.$$

Let the comparison domain be bounded and Lipschitz. Initially consider a
nonnegative bounded Sobolev competitor with the same boundary trace as
the zero extension, and with both functions bounded by some height strictly
below the upper endpoint. In precise notation the competitor class is

$$v\in H^1(D),\qquad v\geq0,\qquad v-\bar u\in H^1_0(D).$$

To justify the flux computation without assuming
second derivatives at the free boundary, for a positive cutoff height use

$$A_\delta(x,s)=\int_\delta^{\max\{s,\delta\}}p(x,z)\,dz.$$

This is locally Lipschitz in the variables relevant to the competitor.
The Sobolev chain rule gives

$$
\operatorname{div}\bigl[A_\delta(x,v(x))\bigr]
=\mathbf1_{\{v>\delta\}}
 \left(p(x,v)\cdot\nabla v-Q(x,v)+Q(x,\delta)\right).
$$

The analogous vector fields for the competitor and solution have identical
boundary traces. Integrating their difference therefore gives zero.
Continuity at height zero makes the last term tend uniformly to zero on
the comparison domain. Boundedness of the field and the integrable
Sobolev gradient justify dominated convergence for the other terms. This
proves the flux identity

$$
\mathcal C_D(v)=\mathcal C_D(\bar u),\qquad
\mathcal C_D(v)=\int_{D\cap\{v>0\}}
 \left(p(x,v)\cdot\nabla v-Q(x,v)\right)dx.
$$

For the energy

$$
J_D(v)=\int_{D\cap\{v>0\}}
 \left(\frac12|\nabla v|^2+W_\kappa(v)\right)dx,
$$

completion of a square gives

$$
J_D(v)-\mathcal C_D(v)
=\frac12\int_{D\cap\{v>0\}}|\nabla v-p(x,v)|^2dx\geq0.
$$

For the original solution the square vanishes, since its foliation
parameter is zero in its positive phase. Consequently

$$J_D(\bar u)\leq J_D(v).$$

This calculation includes the phase cost. It does not assume that the
potential is nonnegative.

## Removing restrictions on competitor height

In the finite-limit case, the reaction at the limit is zero and the
quotient is nonincreasing. Therefore, without changing the reaction,

$$
f(s)\leq0\quad(s\geq L),\qquad
W_\kappa(s)\geq W_\kappa(L)\quad(s\geq L).
$$

Clamping any nonnegative Sobolev competitor at the limit decreases its
gradient energy and does not increase its potential energy; its positive
phase is unchanged. The potential has a global finite lower bound, so
the original energy is well-defined, possibly positive infinity. Compare
first with

$$v_\eta=\min\{v,L-\eta\},\qquad
L-\eta>\sup_{\overline D}\bar u.$$

This preserves the boundary trace. Letting the cutoff approach the limit
gives energy convergence to the competitor clamped at the limit, by
boundedness of the potential on the finite interval and the Sobolev
truncation rule. Thus

$$J_D(\bar u)\leq J_D(\min\{v,L\})\leq J_D(v).$$

In the infinite-limit case, every positive value is attained, so the
reaction-sign reduction gives nonnegativity of the reaction everywhere
on the positive half-line. For large arguments the structural inequality
also gives

$$0\leq f(s)\leq f(1)s\qquad(s\geq1).$$

Local boundedness near zero then implies

$$|W_\kappa(s)|\leq C(1+s^2)\qquad(s\geq0).$$

Truncate an arbitrary nonnegative Sobolev competitor at finite heights
above the maximum of the original solution on the comparison domain.
The traces remain correct. The quadratic bound, dominated convergence,
and the gradient truncation rule give convergence of the energies.
This proves minimality for all such competitors. Finiteness of the
primitive at infinity was not used.

We have therefore proved, informally, global minimization on every bounded
Lipschitz comparison domain, with the original reaction unchanged.

## Nonnegativity of the potential follows from minimality

The zero phase of any continuous entire epigraph contains arbitrarily
large balls. Indeed, on a horizontal closed ball define the minimum graph
height. A ball of the same radius centered two radii below that minimum
lies strictly below the graph.

If the potential were negative at any finite positive value, put a
competitor equal to that value on the concentric ball of radius one less,
and decrease it to zero across a shell of fixed width. It agrees with the
original zero solution on the outer boundary. Its energy satisfies

$$
J_{B_R}(v)\leq W_\kappa(a)|B_{R-1}|+C_aR^{n-1}<0
\qquad\text{for sufficiently large }R.
$$

The constant in the shell estimate is finite because the competitor's
height lies in a fixed compact interval and its gradient is bounded.
This contradicts minimality of the original zero function on that ball.
Consequently the potential is nonnegative on its entire nonnegative
domain:

$$W_\kappa(s)\geq0\qquad(s\geq0).$$

In the unbounded-solution case, the reaction is everywhere nonnegative,
and this gives the new necessary restriction

$$0\leq\int_0^\infty f(s)\,ds\leq\frac{\kappa^2}{2}<\infty.$$

This conclusion is obtained after the calibration, so there is no circular
assumption about the primitive.

## Exact normalization at a finite limiting equilibrium

In the bounded case, translated solutions converge locally uniformly to
the positive constant limit, and their gradients converge locally
uniformly to zero. Their zero extensions are also global minimizers by
translation invariance of the energy. The constant limit inherits the
required comparison inequality as follows.

Fix a bounded comparison domain and a bounded nonnegative Sobolev
competitor whose boundary trace is the constant limit. For large
translation parameters the translated solution is positive on the whole
closed domain. Define

$$w_t=(w+u_t-L)_+.$$

It has boundary trace equal to the translated solution. Since the
translated solution is strictly below the limit, this modification is
zero wherever the competitor is zero, and it converges to the competitor
in Sobolev norm. Its positive-phase indicators converge almost everywhere
to that of the competitor. Boundedness of the potential on the relevant
finite interval therefore also gives energy convergence. Passing to the
limit in the minimizing inequality yields

$$W_\kappa(L)|D|\leq J_D(w).$$

Apply this with a ball and a competitor that is zero on the concentric
ball of radius one less and rises to the constant boundary value across
a shell of fixed width. Then

$$0\leq W_\kappa(L)|B_R|\leq C_LR^{n-1}.$$

First the translation parameter was sent to infinity for each fixed
radius; only now send the radius to infinity. This proves

$$W_\kappa(L)=0,\qquad F(L)=\frac{\kappa^2}{2}.$$

No convergence estimate uniform in arbitrarily large radii was assumed.
The equilibrium may still be degenerate.

## Scope and remaining classification

The calibration is an explicit general-reaction argument. For comparison,
[Wang–Wei, Lemma 5.5](https://personal.math.ubc.ca/~jcwei/serrin-2015-2-13.pdf)
proves minimization under its stated hypotheses by sliding against an
energy minimizer. The argument here supplies its own common-limit and
phase-cost reasoning; it does not assert that the later classification
theorems in that paper apply to these broader potentials.

The bounded branch now has a nonnegative potential vanishing at its
possibly degenerate limiting equilibrium. The unbounded branch has a
nonnegative nonincreasing potential with a finite nonnegative limit.
These are useful restrictions, but they do not by themselves classify
entire graphical minimizers.

In particular, the admissible reactions

$$
f_p(s)=\frac{p-1}{2}(1+s)^{-p},\qquad
1<p<3,\qquad\kappa=1
$$

give

$$W_\kappa(s)=\frac12(1+s)^{1-p}.$$

Their slow potential tails are compatible with all the reductions above.
[Savin–Zhang, introduction](https://arxiv.org/html/2503.02029v1#S1)
distinguishes power-decaying tails from the truncated double-well setting
of its unbounded-minimizer results. An applicable graphical or one-sided
growth classification for every potential arising here remains an
additional step. The separate harmonic obstruction in ambient dimension
eight also remains as described in
[the harmonic audit](harmonic-dimension-eight.md).

Thus this document establishes an informal general minimization reduction,
not the remaining pictured rigidity conclusions or their Lean proofs.
