# Rigidity hypotheses requiring a proof

The three supplied images are the project's target statements. The two rigidity
conclusions are **not yet proved** under their stated general hypotheses. This
note records a gap in the proposed literature deduction, not a counterexample
to either conclusion.

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

The source search found no counterexample satisfying all target assumptions,
and no theorem that supplies the missing general reduction. A complete proof
must establish that broader rigidity result or another argument. Adding
Allen–Cahn hypotheses would change the requested statements and is not done.
