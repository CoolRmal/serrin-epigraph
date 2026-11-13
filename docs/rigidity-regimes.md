# Reaction regimes and newer rigidity literature

> Historical audit of the broader statement inferred from the cropped images.
> The user has corrected that interpretation: reaction and boundedness conditions
> in the original conversation also apply. See [scope correction](scope-correction.md).
> The exclusions discussed below are not blockers for the corrected targets.


The proved reaction reduction establishes nonnegativity of the reaction on
the solution range, and boundedness whenever the reaction is negative at a
positive argument. It does not recover the extra hypotheses of the cited
Wang–Wei or Beuvin–Farina rigidity theorems.

This note records exact calculations and the scope of newer primary sources,
checked on 2026-11-13. **The examples and scaling calculations below are not
formalized in Lean.** Every example here is a flat half-space solution and
therefore satisfies the desired rigidity conclusion. None is a counterexample
to the images. These calculations identify missing steps; they do not complete
either remaining rigidity proof or the three-theorem goal.

## 1. An admissible family with several energy scales

For any exponent greater than one, set

$$
p>1,\qquad \beta=\frac{2}{p+1},\qquad b=\frac{p+1}{2},\qquad
f_p(s)=\frac{p-1}{2}(1+s)^{-p}\quad(s\geq0).
$$

On the horizontal half-space take

$$
\Omega=\{x_n>0\},\qquad
u(x)=U_p(x_n),\qquad
U_p(t)=(1+bt)^\beta-1.
$$

Direct differentiation gives

$$
U_p'(t)=(1+bt)^{\beta-1},\qquad
-U_p''(t)=\frac{p-1}{2}(1+U_p(t))^{-p},\qquad
U_p(0)=0,\qquad U_p'(0)=1.
$$

Thus the outward Neumann datum is minus one. The reaction is smooth on the
nonnegative half-line and satisfies

$$
f_p(s)-s f_p'(s)
=\frac{p-1}{2}\frac{1+(p+1)s}{(1+s)^{p+1}}>0\qquad(s>0).
$$

The solution has polynomial square mass:

$$
U_p(t)^2\leq(1+bt)^{2\beta},\qquad
\int_{\Omega\cap B_R}u^2=O(R^{n+2\beta})\qquad(R\to\infty).
$$

In particular, it satisfies the exact logarithmic lower-limit hypothesis in
the images. Both one-sided linear graph bounds hold because the graph is zero.

The primitive and the potential normalized by the boundary slope are

$$
F_p(s)=\int_0^s f_p(r)\,dr
=\frac12\left(1-(1+s)^{1-p}\right),\qquad
W_p(s)=\frac12-F_p(s)=\frac12(1+s)^{1-p}.
$$

The primitive is finite at infinity for every exponent in this family. The
one-dimensional energy density nevertheless has different integrability
regimes:

$$
\frac12U_p'(t)^2+W_p(U_p(t))
=U_p'(t)^2=(1+bt)^{-q},\qquad
q=\frac{2(p-1)}{p+1}=2-2\beta.
$$

Writing its integral up to height as follows gives the exact transition:

$$
A_p(T)=\int_0^T(1+bt)^{-q}\,dt
=\begin{cases}
\displaystyle\frac{(1+bT)^{1-q}-1}{b(1-q)},&p\ne3,\\[6pt]
\displaystyle\frac12\log(1+2T),&p=3.
\end{cases}
$$

Consequently, the ball energy satisfies

$$
\int_{\Omega\cap B_R}\left(\frac12|\nabla u|^2+W_p(u)\right)dx
\asymp
\begin{cases}
R^{n-q},&1<p<3,\\
R^{n-1}\log R,&p=3,\\
R^{n-1},&p>3.
\end{cases}
$$

Indeed, its exact cross-section integral is

$$
\omega_{n-1}\int_0^R
(R^2-t^2)^{(n-1)/2}(1+bt)^{-q}\,dt.
$$

Bounding the cross-section from above by its value at zero and from below on
the interval from zero to half the radius proves the stated comparisons.
The surface-tension integral is

$$
\int_0^\infty\sqrt{2W_p(s)}\,ds
=\int_0^\infty(1+s)^{(1-p)/2}\,ds
=\begin{cases}
\infty,&1<p\leq3,\\
\displaystyle\frac2{p-3},&p>3.
\end{cases}
$$

Thus a finite reaction primitive does not supply finite surface tension or a
uniform area-order energy bound.

## 2. Exact rescaling, without an asserted convergence theorem

Zero-extend a solution with this reaction and boundary slope one. Define

$$
v_R(x)=R^{-\beta}u(Rx),\qquad
\Omega_R=R^{-1}\Omega,\qquad R>0.
$$

The equation and the boundary gradient, interpreted as the trace from the
positive phase, rescale exactly to

$$
-\Delta v_R=\frac{p-1}{2}(v_R+R^{-\beta})^{-p}
\quad\text{in }\Omega_R,\qquad
|\nabla v_R|=R^{1-\beta}\quad\text{on }\partial\Omega_R.
$$

The rescaled boundary gradient tends to infinity. It is not the fixed
Bernoulli gradient condition.

For the energy with its positive-phase indicator, change of variables gives
the following identity on any bounded region where the integrals are defined:

$$
J_p(u;D)=\int_D\left(\frac12|\nabla u|^2+
W_p(u)\mathbf1_{\{u>0\}}\right)dx,
$$

$$
R^{-(n+2\beta-2)}J_p(u;RD)
=\int_D\left(\frac12|\nabla v_R|^2+
\frac12(v_R+R^{-\beta})^{1-p}\mathbf1_{\{v_R>0\}}\right)dx.
$$

The cancellation uses precisely the identity

$$
2-2\beta+\beta(1-p)=0.
$$

At each fixed positive argument, the rescaled potential tends to

$$
\frac12 v^{1-p}.
$$

For exponents strictly between one and three this is a negative-power
Alt–Phillips potential: its singular power lies strictly between minus two
and zero. These are **scaling identities and pointwise potential limits**.
They do not establish compactness, preservation of minimizing properties,
convergence of free boundaries, or Gamma-convergence for the Serrin solutions.
Those would require separate proofs.

The existing Alt–Phillips classification therefore cannot simply be replaced
by a minimal-perimeter classification. In the notation of
[De Silva–Savin, *Compactness estimates for minimizers of the Alt–Phillips
functional of negative exponents*](https://arxiv.org/html/2211.00553v1), the
positive singularity parameter is the reaction exponent minus one. Their
global-minimizer rigidity results cover parameters sufficiently close to two
in dimensions at most seven, or sufficiently close to zero in dimensions at
most four. They do not provide the unrestricted graphical classification
required here. No Gamma-convergence theorem from that paper is being asserted
for the rescaling above.

## 3. What the newer Savin–Zhang results cover

[Savin–Zhang, *Minimizers of the Allen-Cahn energy with sub-quadratic
growth*](https://arxiv.org/html/2503.02029v1), Theorems 1.2 and 1.3, uses the
specific potential

$$
W(t)=\begin{cases}(1-t^2)^2,&|t|\leq1,\\0,&|t|>1.\end{cases}
$$

The results assume pointwise subquadratic growth. The minimizer theorem gives
one-dimensionality through dimension seven; the monotone whole-space theorem
with a graphical zero level gives it through dimension eight. Neither is a
theorem for arbitrary decreasing positive-phase potentials. The introduction
explicitly discusses power-decaying tails as prospective extensions, and
distinguishes Alt–Phillips limits from Dirichlet/perimeter limits. Thus the
paper identifies relevant mechanisms but does not supply the missing theorem
for this project's reaction class. Moreover, the project's square-mass
lower-limit condition has not been converted into its pointwise growth
hypothesis.

[Savin–Zhang, *Density estimates for Ginzburg-Landau energies with degenerate
double-well potentials*](https://arxiv.org/html/2506.17000v1), Theorems 1.1,
1.2, and 3.1, establishes density estimates under power-comparability
conditions near the wells. These are not general improvement-of-flatness or
Serrin classification theorems. Its broader potential formulation still
requires upper and lower power bounds, together with corresponding
derivative bounds. The next example shows why even that enlargement does not
cover all bounded solutions permitted by the images.

## 4. Bounded solutions can have an infinitely flat equilibrium

Consider the smooth reaction on the nonnegative half-line

$$
f(s)=\begin{cases}
\exp\!\left(-\dfrac1{(1-s)^2}\right),&0\leq s<1,\\[4pt]
0,&s\geq1.
\end{cases}
$$

For positive arguments below one,

$$
f(s)-sf'(s)
=f(s)\left(1+\frac{2s}{(1-s)^3}\right)>0.
$$

At and above one the structural remainder is zero. Put

$$
\kappa=\sqrt{2\int_0^1 f(r)\,dr},\qquad
W(s)=\int_s^1 f(r)\,dr\quad(0\leq s\leq1).
$$

Define the increasing half-line profile by

$$
t=\int_0^{U(t)}\frac{ds}{\sqrt{2W(s)}}.
$$

This determines a profile at every nonnegative height. To see why it never
reaches its limiting value in finite time, note that

$$
0<W(s)\leq(1-s)\exp\!\left(-\frac1{(1-s)^2}\right)
\qquad(0\leq s<1),
$$

so the defining integral diverges as its upper endpoint tends to one.
Differentiating gives

$$
U'=\sqrt{2W(U)}>0,\qquad -U''=f(U),\qquad
U(0)=0,\qquad U'(0)=\kappa,\qquad \lim_{t\to\infty}U(t)=1.
$$

This is another admissible flat Serrin solution, with bounded solution values
and polynomial square mass. Yet for every positive finite exponent,

$$
\lim_{s\uparrow1}\frac{W(s)}{(1-s)^m}=0\qquad(m>0).
$$

No positive lower power-comparability bound near the equilibrium can hold.
Also the reaction derivative at the equilibrium and the potential's second
derivative there are zero. Modifying the reaction only outside the attained
solution range cannot repair this: the profile attains every value strictly
between zero and one, and any continuously differentiable extension has the
same limiting derivative at one.

The remaining mathematical obligation is therefore a rigidity argument that
handles both arbitrary well degeneracy in the bounded branch and the distinct
tail regimes in the unbounded branch. The reaction reduction alone, and the
newer sources checked here, do not supply that argument.
