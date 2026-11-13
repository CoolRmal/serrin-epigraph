module

public import SerrinEpigraph.CoerciveGrowth
public import SerrinEpigraph.ExcessGrowth
public import SerrinEpigraph.ReactionTail
public import SerrinEpigraph.Nonnegative
public import SerrinEpigraph.StrongMaximum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!+# Boundedness forced by a negative reaction value

The original square-mass hypothesis rules out every positive excess above a negative
reaction threshold. Consequently the reaction is nonnegative on the solution range;
an unbounded solution requires a nonnegative reaction on the whole positive half-line.
-/

public section

open Filter Set
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ s : ℝ}

/-- Fixed-width doubling is incompatible with a positive excess and the exact mass hypothesis. -/
theorem Hypotheses.solution_le_of_excessMass_doubling (h : Hypotheses g u f κ)
    (hs : 0 ≤ s) {L : ℝ} (hL : 0 < L)
    (hstep : ∀ R : ℝ, 0 < R →
      2 * excessMass g u s R ≤ excessMass g u s (R + L)) :
    ∀ x ∈ epigraph g, u x ≤ s := by
  have hmass := nonpos_of_fixedWidth_doubling hL ((monotone_excessMass h).monotoneOn _)
    (fun R _ ↦ excessMass_le_squareMass h hs R) h.mass_growth hstep
  intro x hx
  by_contra! hxs
  obtain ⟨R, hR, hpos⟩ := exists_excessMass_pos h hx hxs
  exact (not_lt_of_ge (hmass R hR)) hpos

/-- A coercive negative linear reaction tail bounds the solution by its threshold. -/
theorem Hypotheses.solution_le_of_coercive_reaction_tail (h : Hypotheses g u f κ)
    (hs : 0 < s) {c : ℝ} (hc : 0 < c)
    (htail : ∀ x ∈ epigraph g, s < u x → f (u x) ≤ -c * u x) :
    ∀ x ∈ epigraph g, u x ≤ s := by
  obtain ⟨L, hL, hstep⟩ := h.exists_excessMass_doubling hs hc htail
  exact h.solution_le_of_excessMass_doubling hs.le hL hstep

/-- Any positive argument with a negative reaction value is an upper bound for the solution. -/
theorem Hypotheses.solution_le_of_reaction_neg (h : Hypotheses g u f κ)
    (hs : 0 < s) (hfs : f s < 0) : ∀ x ∈ epigraph g, u x ≤ s := by
  obtain ⟨hc, htail⟩ := h.reaction_tail_coercive hs hfs
  exact h.solution_le_of_coercive_reaction_tail hs hc (fun x _ hxs ↦ htail _ hxs.le)

/-- An unbounded solution forces the reaction to be nonnegative on the nonnegative half-line. -/
theorem Hypotheses.reaction_nonneg_of_unbounded (h : Hypotheses g u f κ)
    (hunbounded : ∀ M : ℝ, ∃ x ∈ epigraph g, M < u x) :
    ∀ s : ℝ, 0 ≤ s → 0 ≤ f s := by
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hs
  · exact reaction_nonneg_zero h.reaction_contDiffOn h.reaction_structure
  · by_contra! hfs
    obtain ⟨x, hx, hxs⟩ := hunbounded s
    exact (not_lt_of_ge (h.solution_le_of_reaction_neg hs hfs x hx)) hxs

/-- Even for bounded solutions, the reaction cannot be negative at an interior solution value. -/
theorem Hypotheses.reaction_nonneg_on_solution (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) : 0 ≤ f (u x) := by
  by_contra! hf
  have hbound := h.solution_le_of_reaction_neg (h.positive x hx) hf
  have hmax : IsLocalMax u x := by
    filter_upwards [(isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx] with y hy
    exact hbound y hy
  have hpos := h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg x hx
  have hz : verticalDerivative u x = 0 := by
    simp only [verticalDerivative, hmax.fderiv_eq_zero, zero_apply]
  exact (ne_of_gt hpos) hz

/-- Under the source hypotheses the solution is superharmonic throughout the epigraph. -/
theorem Hypotheses.laplacian_nonpos (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) : (Δ u) x ≤ 0 := by
  linarith [h.equation x hx, h.reaction_nonneg_on_solution hx]

end SerrinEpigraph
