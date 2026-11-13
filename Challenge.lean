module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Independent specification of the three image statements

This file imports only Mathlib. Its three deliberate proof holes specify the targets.
The horizontal dimension is `m`, so the ambient dimension in the source is `n = m + 1`.
All norms, balls, inner products and volume measures use the Euclidean structure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Laplacian

namespace SerrinEpigraph

/-- Euclidean coordinate space of dimension `d`. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Horizontal coordinates, with the last coordinate omitted. -/
def horizontal {m : ℕ} (x : Space (m + 1)) : Space m :=
  WithLp.toLp 2 (fun i ↦ x i.castSucc)

/-- A point assembled from horizontal coordinates and its height. -/
def point {m : ℕ} (y : Space m) (t : ℝ) : Space (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i ↦ y i) t)

/-- The open epigraph of `g`. -/
def epigraph {m : ℕ} (g : Space m → ℝ) : Set (Space (m + 1)) :=
  {x | g (horizontal x) < x (Fin.last m)}

/-- The upward unit coordinate vector. -/
def verticalDirection (m : ℕ) : Space (m + 1) :=
  EuclideanSpace.single (Fin.last m) 1

/-- The vertical derivative in the interior of the epigraph. -/
def verticalDerivative {m : ℕ} (u : Space (m + 1) → ℝ) (x : Space (m + 1)) : ℝ :=
  fderiv ℝ u x (verticalDirection m)

/-- The outward unit normal to the epigraph at `(y, g y)`. -/
def outwardNormal {m : ℕ} (g : Space m → ℝ) (y : Space m) : Space (m + 1) :=
  (Real.sqrt (1 + ‖gradient g y‖ ^ 2))⁻¹ • point (gradient g y) (-1)

/-- The squared mass inside the Euclidean ball of radius `R` centered at zero. -/
def squareMass {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (R : ℝ) : ℝ :=
  ∫ x in epigraph g ∩ Metric.ball 0 R, u x ^ 2

/-- Zero lower exponential growth rate of squared mass; the liminf is extended-real. -/
def HasSubexponentialMass {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ) : Prop :=
  Filter.liminf (fun R : ℝ ↦
    ((Real.log (1 + squareMass g u R) / R : ℝ) : EReal)) atTop = 0

/-- Exactly the common regularity, equation, boundary and growth assumptions in Image 1. -/
structure Hypotheses {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (f : ℝ → ℝ) (κ : ℝ) : Prop where
  dimension : 1 ≤ m
  graph_contDiff : ContDiff ℝ 1 g
  solution_contDiffOn : ContDiffOn ℝ 2 u (epigraph g)
  solution_contDiffOn_closure : ContDiffOn ℝ 1 u (closure (epigraph g))
  reaction_contDiffOn : ContDiffOn ℝ 1 f (Set.Ici 0)
  reaction_structure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s
  equation : ∀ x ∈ epigraph g, -(Δ u) x = f (u x)
  positive : ∀ x ∈ epigraph g, 0 < u x
  dirichlet : ∀ y : Space m, u (point y (g y)) = 0
  neumann : ∀ y : Space m,
    fderivWithin ℝ u (closure (epigraph g)) (point y (g y)) (outwardNormal g y) = -κ
  kappa_pos : 0 < κ
  mass_growth : HasSubexponentialMass g u

/-- The normalized reaction and bounded-solution assumptions recovered from the source notes.
Together with `Hypotheses`, these specify the reaction class for the two rigidity targets. -/
structure RigidityHypotheses {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (f : ℝ → ℝ) : Prop where
  reaction_pos : ∀ s ∈ Set.Ioo (0 : ℝ) 1, 0 < f s
  reaction_one : f 1 = 0
  reaction_deriv_one_neg : deriv f 1 < 0
  solution_lt_one : ∀ x ∈ epigraph g, u x < 1

/-- Either a global linear lower bound or a global linear upper bound, with positive constant. -/
def HasOneSidedLinearBound {m : ℕ} (g : Space m → ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ y, -C * (1 + ‖y‖) ≤ g y) ∨
    (∃ C : ℝ, 0 < C ∧ ∀ y, g y ≤ C * (1 + ‖y‖))

/-- An affine graph and a profile depending only on inward normal distance. -/
def IsAffineOneDimensional {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ) : Prop :=
  ∃ (a : Space m) (b : ℝ) (U : ℝ → ℝ),
    (∀ y, g y = inner ℝ a y + b) ∧
    ∀ x ∈ epigraph g,
      u x = U ((x (Fin.last m) - inner ℝ a (horizontal x) - b) /
        Real.sqrt (1 + ‖a‖ ^ 2))


/-- Image 1: strict vertical monotonicity from zero lower exponential squared-mass growth. -/
theorem verticalDerivative_pos {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ) :
    ∀ x ∈ epigraph g, 0 < verticalDerivative u x := by
  sorry

/-- Image 2: affine and one-dimensional rigidity in ambient dimensions two through eight. -/
theorem rigidity_of_dimension_le_eight {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hr : RigidityHypotheses g u f) (hdim : m + 1 ≤ 8) :
    IsAffineOneDimensional g u := by
  sorry

/-- Image 3: rigidity in ambient dimension at least nine under either one-sided linear bound. -/
theorem rigidity_of_oneSidedLinearBound {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hr : RigidityHypotheses g u f)
    (hdim : 9 ≤ m + 1) (hg : HasOneSidedLinearBound g) :
    IsAffineOneDimensional g u := by
  sorry

end SerrinEpigraph
