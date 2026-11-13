# Harmonic rigidity in ambient dimension eight: source audit

> Historical audit of the broader statement inferred from the cropped images.
> The user has corrected that interpretation: reaction and boundedness conditions
> in the original conversation also apply. See [scope correction](scope-correction.md).
> The exclusions discussed below are not blockers for the corrected targets.


Checked against primary papers on 2026-11-13. This supplements
[the general rigidity audit](rigidity-gap.md).

The examined papers do not establish the exact harmonic case of Image 2 in
ambient dimension eight. They also do not provide a counterexample satisfying
its entire-epigraph hypothesis. I did not find a primary statement explicitly
declaring that precise dimension-eight problem open as of the audit date.
Accordingly, the defensible conclusion is a missing proof in the examined
sources, rather than a claim that the problem is globally known to be open.

## The precise harmonic specialization

Taking the zero reaction in Image 1 leaves

$$
\Omega=\{(x',x_8):x_8>g(x')\},\qquad
\Delta u=0,\quad u>0\ \text{in }\Omega,
\qquad u=0,\quad\partial_\nu u=-\kappa\ \text{on }\partial\Omega,
\quad\kappa>0.
$$

The graph is continuously differentiable, and the solution is twice
continuously differentiable in the domain and locally once continuously
differentiable up to its boundary. The normalized zero extension

$$
v(x)=\begin{cases}u(x)/\kappa,&x\in\Omega,\\0,&x\notin\Omega\end{cases}
$$

is the classical graphical one-phase Bernoulli configuration. The required
conclusion is that the graph is affine. This is a free-boundary graph in
eight-dimensional space; it is not an eight-dimensional minimal graph in
nine-dimensional space.

## What the graphical classification actually supplies

[Engelstein–Fernández-Real–Yu](https://arxiv.org/html/2212.08847#S1.SS1),
Theorems 1.1 and 1.4, prove minimization for continuous entire graphical
solutions and flatness when

$$n\leq n^*_{\mathrm{local}}+1,\qquad n^*_{\mathrm{local}}\leq6.$$

Thus their criterion cannot reach eight, even if the critical flat-cone
dimension attains its largest possible value. Their introduction explicitly
says that no analogue of the Bombieri–De Giorgi–Giusti counterexample
construction had been found; it expresses an expectation of failure in
sufficiently high dimensions, without identifying eight as a proved failure.
This is direct evidence about the authors' stated status in that paper,
not a current nonexistence theorem for all later constructions.

Their Lemma 2.5 gives a dimensional Lipschitz bound for the normalized
solution. Fixing a boundary point then gives the elementary implication

$$
u(x)\leq C(1+|x|),\qquad
\int_{\Omega\cap B_R}u^2\leq C'(1+R)^{10}.
$$

Consequently, the square-mass growth assumption does not remove this harmonic
case. This polynomial-growth implication is a deduction from the cited
gradient bound.

## The newer blowdown dichotomy

[Edelen–Li–Zhu, Theorem 2.2](https://arxiv.org/html/2606.01715v1#S2.SS1)
assumes an entire nonzero Alt–Caffarelli minimizer with nonnegative vertical
derivative. It proves that either the solution is flat, or every blowdown is
nonflat and invariant under vertical translations. Its stated dimensional
consequence is

$$n\leq k_*(0),\qquad k_*(0)\leq7.$$

The two papers use different critical-dimension conventions:

$$k_*(0)=n^*_{\mathrm{local}}+1.$$

There is no additional dimension gained by combining those displayed bounds.
In dimension eight the second alternative is not eliminated by this theorem.
A product of a seven-dimensional minimizing cone with a line illustrates
the type of blowdown left by the argument. It does **not** construct an
entire smooth graph having that blowdown.

## Why the known smooth constructions do not close the question

[De Silva–Jerison–Shahgholian, Theorem 1.1](https://arxiv.org/html/2106.14576#S1.SS2)
constructs analytic free boundaries asymptotic to a minimizing cone whose
only singularity is its vertex. The “graphs” in its abstract are graphs of
solution functions in one additional dimension, not an assertion that their
free boundaries are entire graphs over a hyperplane.

In particular, applying that theorem directly to a seven-dimensional cone
times a line would violate its isolated-singularity hypothesis: the product
has a singular line. A separate construction and graphicality proof would
be required. This is an inference from the theorem's hypotheses.

[Minlend–Weth–Wu, Theorem 1.1](https://link.springer.com/article/10.1007/s12220-025-02243-6)
does give new smooth exceptional domains with bounded harmonic roof functions
in dimensions at least four. Its domains are perturbations of cylinder
exteriors. Their boundaries have the topology of a sphere times a line,
rather than that of an entire Euclidean graph. They therefore do not supply
the requested counterexample; the topology comparison is an immediate
deduction from the paper's domain definition (1.7).

The remaining precise step is to exclude the nonflat cylindrical blowdown
alternative for this eight-dimensional entire-graph problem, or to construct
an entire graph realizing it. None of the checked primary statements does
either. No Lean theorem, hypothesis, or target was changed by this audit.

## A stronger harmonic consequence: a bound along a sequence suffices

The following is an informal deduction from
[Engelstein–Fernández-Real–Yu, Lemma 2.8](https://arxiv.org/html/2212.08847)
and [Edelen–Li–Zhu, Theorem 2.2](https://arxiv.org/html/2606.01715v1#S2.SS1).
It has not been formalized in Lean and is not a general-reaction theorem.

Define the extrema of the continuous graph on horizontal balls by

$$
M_+(R)=\max_{|x'|\leq R}g(x'),\qquad
M_-(R)=\min_{|x'|\leq R}g(x').
$$

A nonflat entire graphical harmonic Bernoulli solution must satisfy

$$
\frac{M_+(R)}R\longrightarrow+\infty,
\qquad
\frac{M_-(R)}R\longrightarrow-\infty.
$$

Indeed, suppose instead that some sequence tending to infinity satisfies

$$M_+(R_j)\leq C R_j.$$

The normalized zero extensions rescaled as

$$v_j(x)=\frac{v(R_jx)}{R_j}$$

are harmonic on the fixed connected cylinder

$$D=B'_1\times(C,\infty).$$

By the cited compactness and dichotomy, a subsequence converges locally
uniformly to a nonzero, nonnegative, one-homogeneous minimizer whose vertical
translations leave it unchanged. The limit is harmonic on the whole of
this cylinder, including any points at which it vanishes. Homogeneity gives
its value zero at the origin; vertical invariance gives its value zero at
the interior point with horizontal coordinate zero and height greater than
the cylinder's lower endpoint. The strong maximum principle forces the
limit to vanish throughout the cylinder. Vertical invariance and homogeneity
then force it to vanish everywhere, a contradiction.

If instead a sequence satisfies

$$M_-(R_j)\geq-C R_j,$$

the rescaled zero extensions vanish on

$$B'_1\times(-\infty,-C).$$

Their limit does too; vertical invariance and homogeneity again force the
limit to be identically zero. This proves both necessary divergence
conditions. In particular, either one-sided linear bound in Image 3 excludes
the nonflat alternative in the harmonic specialization, in every dimension.
The argument for the upper bound uses harmonic convergence and the strong
maximum principle, so it does not need an inference from positivity of each
rescaled function to positivity of its limit.

## Why smoothness and positive vertical derivative do not add a uniform bound

[De Silva–Jerison, Theorem 1.1, pp. 1–2](https://math.mit.edu/~jerison/gbf.finaldraft.pdf)
proves smoothness of monotone minimizing free-boundary graphs. Its local
graph-gradient estimate depends on the cylinder height and the clearance
from its top and bottom. Together with the graphical minimization and
monotonicity results above, this makes smoothness automatic for continuous
entire graphical Bernoulli solutions. The target's local regularity therefore
does not supply an additional scale-independent estimate. After rescaling
a horizontal radius to one, the relevant cylinder height is controlled by
the graph's oscillation divided by that radius; the polynomial square-mass
bound for the solution does not bound this quantity.

On a smooth graph, the constant normal derivative gives the exact identity

$$
u_n(x',g(x'))=\frac{\kappa}{\sqrt{1+|\nabla g(x')|^2}}.
$$

Thus nondegeneracy of the full boundary gradient and strict positivity of
its vertical component do not give a uniform positive lower bound on that
component when graph slopes are unbounded. Under rescaling,

$$
\partial_n\!\left(\frac{u(Rx)}R\right)=u_n(Rx),
$$

so pointwise positivity can be lost in a blowdown. Excluding that loss,
or deriving either subsequential height bound above from the exact
dimension-eight hypotheses, remains an additional mathematical step.
These observations do not construct a counterexample and do not settle
the dimension-eight target.
