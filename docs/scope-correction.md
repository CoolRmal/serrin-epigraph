# Restored reaction assumptions

On 2026-11-13 the user corrected the interpretation of the cropped source images:
the original conversation and project notes are part of the statement source.
The previous claim that no boundedness or stable-equilibrium assumptions were
intended was incorrect.

The conversation “查找近期相关文献” (thread
`01a1c41e-d03e-7f52-bbfd-a4a5c73b0682`) explicitly uses

$$
f(s)=s-s^p,\qquad p>1,\qquad 0<u<1.
$$

The project note `reports/一般非线性的高阶商矩与Serrin刚性.md`, section 2,
records the more general normalized conditions

$$
f\in C^1([0,1]),\quad f(s)>0\ (0<s<1),\quad
f(1)=0,\quad f'(1)<0,\quad f(s)-sf'(s)\ge0\ (0<s<1),\quad 0<u<1.
$$

The current targets retain the general monotonicity hypotheses in `Hypotheses`
and restore the additional positivity, stable equilibrium, and upper solution
bound in `RigidityHypotheses`. Both rigidity targets take this additional
structure. The first target is unchanged. `Challenge.lean` independently repeats
exactly these definitions and target signatures, importing Mathlib only.
The real-power reaction above is an example, not an additional restriction.

The earlier investigations of the zero reaction, flat equilibria and unbounded
solutions concern a broader problem that was mistakenly substituted for this
one. They are research notes, not blockers for the corrected task.

## Remaining work

The monotonicity proof is complete. The two rigidity proofs still contain proof
holes. Restoring assumptions does not formalize the classification theorems:
the analytic and geometric arguments underlying the cited Wang–Wei and
Beuvin–Farina results still need Lean proofs. No external theorem is admitted
as an axiom. Full Comparator acceptance and Palomar registration remain required.
