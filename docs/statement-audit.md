# Independent statement audit

The three supplied images are the source of the formalization targets. This audit
separates faithful transcription from mathematical proof. A compiled declaration
containing `sorry` is not a proved theorem; unfinished proof targets are **ineligible
for Palomar registration**. A successful statement comparator check does not change
that proof status.

## What the images assert

All three statements use the same assumptions: an entire continuously differentiable
epigraph, a positive classical solution with locally continuous first derivatives
up to its boundary, zero Dirichlet data, constant strictly negative outward Neumann
data, and a locally continuously differentiable reaction satisfying

$$
f(s)-sf'(s)\geq0\qquad(s>0).
$$

They also retain the square-mass hypothesis

$$
\liminf_{R\to\infty}\frac{1}{R}
\log\left(1+\int_{\Omega\cap B_R}u^2\,dx\right)=0.
$$

The first target concludes strict vertical monotonicity. The second adds ambient
dimension between two and eight and concludes that the graph is affine and the
solution depends only on inward normal distance. The third adds ambient dimension
at least nine and **either** a global linear lower bound **or** a global linear
upper bound for the graph, with the same rigidity conclusion. The profile identity
is an identity on the domain, not a restriction on arbitrary values outside it.

## The rigidity citations need additional hypotheses

[Wang–Wei, Theorem 1.4](https://arxiv.org/html/1502.04680#S1) is subject to the
paper's standing potential assumptions W1–W5. It is not a theorem for every
reaction satisfying the displayed structural inequality. Its boundary-origin
normalization can be achieved by translation, but its reaction assumptions cannot
simply be discarded.

[Beuvin–Farina, Theorem 2.1 and the definition preceding it](https://arxiv.org/html/2502.04812v2#S2)
explicitly require a *specified Allen–Cahn-type nonlinearity*. In their normalized
form, the potential

$$
W(t)=\int_0^1 f(s)\,ds-\int_0^t f(s)\,ds
$$

is twice continuously differentiable on the nonnegative half-line and satisfies:

- Nonnegativity everywhere, vanishing at one, and strict positivity below one.
- Strictly negative first derivative between zero and one; at zero, either the
  first derivative is nonzero or it vanishes and the second derivative is nonzero.
- A strictly positive uniform lower bound for the second derivative on an
  interval ending at one.
- A superlinear lower bound for the first derivative above one: there are positive
  constants and an exponent greater than one such that

$$
W'(t)\geq c(t-1)^p\qquad(t>1),\qquad c>0,\quad p>1.
$$

The structural inequality in the images does not imply these conditions. For
example, the zero reaction satisfies that inequality but has identically zero
potential. This example demonstrates the mismatch of hypotheses; it is **not a
counterexample to either pictured rigidity assertion**.

Consequently, combining the pictured monotonicity claim with these citations does
not establish the two rigidity claims as written. No counterexample to those full
claims is supplied by this audit. A faithful formalization must preserve the
images' hypotheses and leave their proofs open unless an additional argument is
provided. Adding Allen–Cahn assumptions would instead produce revised statements.

## Representation checks

- Euclidean balls and the graph's linear bound use Euclidean norms. An ordinary
  product of normed spaces has the maximum norm by default, so its metric balls
  should not silently stand for the displayed Euclidean balls.
- Boundary Neumann data use the derivative taken from the closure, or an explicitly
  justified continuously differentiable ambient extension. An arbitrary ambient
  extension need not have the intended derivative on the boundary.
- Local differentiability up to the boundary imposes no global bound on the
  solution or its derivatives. The source does not assume a bounded solution.
- The growth assumption is a liminf, not convergence of the entire normalized
  mass function. Nonnegative real integration must not hide a missing local
  integrability argument.
- The high-dimensional bound is a disjunction with a positive constant; imposing
  both bounds would strengthen the source hypothesis.
- With a horizontal dimension parameter, the ambient dimension is one larger.
  The low-dimensional range is horizontal dimension one through seven, and the
  high-dimensional range begins at horizontal dimension eight.

Mathlib supplies the Laplacian and differential, norm, and measure primitives
needed for these statements. The cited rigidity proofs additionally involve
elliptic regularity, variational minimizers, blow-down limits, and minimal-cone
classification. Those dependencies must be proved or imported from actual Lean
proofs before claiming kernel verification of the three targets.

## Review of the Lean declarations

The independent source-level review of `SerrinEpigraph/Basic.lean` and
`SerrinEpigraph/Main.lean` found that the declarations preserve the three images'
mathematical content:

- `Hypotheses` includes every common assumption, without adding boundedness,
  Allen–Cahn conditions, or a pre-existing monotonicity assumption.
- `Space`, `horizontal`, `point`, and `verticalDirection` implement the intended
  Euclidean coordinates with the final coordinate vertical.
- `outwardNormal` has the correct outward sign; `neumann` uses the derivative
  within the closure. The graph parametrization describes the whole boundary
  because the graph function is continuous.
- `HasSubexponentialMass` uses an extended-real liminf of the exact real-valued
  expression. Local integrability follows mathematically from continuity on the
  closure and compactness of closed bounded sets. `Mass.lean` now proves this
  integrability before `squareMass` is used in subsequent estimates.
- `IsAffineOneDimensional` quantifies the same affine coefficients in both
  formulas. A profile on the entire real line is harmless because only its
  positive arguments are used on the epigraph.
- The two dimension restrictions and `HasOneSidedLinearBound` match the source.

This section reviews statement fidelity. The monotonicity declaration in
`Main.lean` is now proved with only standard axioms. The two rigidity declarations
still contain `sorry`.

## Additional investigation of the general-reaction case

The citation gap alone is not an impossibility result. One must still investigate
whether another theorem, a new argument, or a counterexample settles the exact
claims. No counterexample satisfying all the pictured assumptions was found in
this review.

The harmonic subcase deserves particular attention. The zero reaction is allowed,
so the second claim includes a graphical Bernoulli free-boundary rigidity problem.
[Engelstein–Fernández-Real–Yu, Theorems 1.1 and 1.4](https://arxiv.org/html/2212.08847#S1)
prove that graphical solutions are energy minimizers and classify them in a
dimension range expressed using the critical dimension of flat minimizing cones:

$$
n\leq n^*_{\mathrm{local}}+1,
\qquad 4\leq n^*_{\mathrm{local}}\leq6.
$$

That result does not provide the entire range through dimension eight asserted in
Image 2. The paper's introduction discusses the expectation of nonflat graphical
solutions in higher dimensions without supplying such a construction. This is a
concrete indication that the general-reaction formulation requires additional
mathematical work; it is not a certification of the present literature's ultimate
scope and does not establish that the pictured assertion is false.

## Verified support for the monotonicity argument

`SerrinEpigraph/MassGrowth.lean` proves the final abstract growth contradiction.
If a nonnegative mass function has zero lower exponential growth rate and positive
constants satisfy the moment estimates

$$
\mu a^k\leq\left(\frac{Ck}{R}\right)^k V(2R)
\qquad(k\geq3)
$$

for all sufficiently large radii, then the local descent rate cannot be positive.
The proof chooses an integer power proportional to the radius and derives an
exponential lower bound for the mass. This support theorem was checked by Lean
and uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
Those moment estimates are now derived from the original PDE in
`PowerEnergy.lean` and `FirstMoment.lean`. `Nonnegative.lean` applies them, and
`StrongMaximum.lean` supplies strict positivity through the weak comparison and
annular-barrier argument. Thus `SerrinEpigraph.verticalDerivative_pos` is proved
under the exact original assumptions; its complete axiom dependency list is the
same three standard axioms above.
