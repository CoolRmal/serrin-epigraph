# Project instructions

- Use `$$` for LaTeX in Markdown so that GitHub renders it.
- Preserve the three source statements using both the images and the user-confirmed
  conversation context. The rigidity reaction assumptions are recorded in
  `docs/scope-correction.md`. Do not omit them or redefine analytic concepts to
  imply conclusions. Keep the independent Challenge and implementation aligned.
- All Lean files use the `module` header and explicit public visibility.
- `Challenge.lean` imports trusted libraries only; `Solution` must never import it.
- The three `sorry` occurrences in Challenge are specification holes. Any proof
  hole in the development is unfinished work and must fail the proof audit.
- Never permit `sorryAx`, custom axioms, or `Lean.ofReduceBool` in Comparator.
- Use Euclidean norms and Lebesgue volume, and within-closure boundary derivatives.
- Distinguish a successful build from complete proof verification and Palomar registration.
- Stage only explicit task-owned files, and keep credentials outside the repository.
