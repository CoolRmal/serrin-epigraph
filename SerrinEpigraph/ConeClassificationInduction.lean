module

public import SerrinEpigraph.RegularBoundary

/-!
# Classification of minimizing cones in low dimensions (GR16), relative to regularity inputs

This module carries out the induction of GR16 in `docs/rigidity-proof/gmt-regularity.md`
relative to two explicit inputs which later modules discharge:

* `EpsilonRegularityHyp` (GR9–GR14, ε-regularity): if some tangent cone of a local perimeter
  minimizer at a measure-theoretic boundary point is a.e. a half-space, then that point is a `C¹`
  boundary point (`IsC1BoundaryPoint`);
* `SimonsHyp k` (GR1–GR4, Simons with Schauder smoothness): a minimizing cone in `Space k` all of
  whose nonzero boundary points are `C¹` boundary points is a.e. a half-space.

The base cases are proved here: `Space 0` carries no minimizing cone and minimizing cones in
`Space 1` are half-lines. The induction step uses cone splitting (GR5) and cylindrical reduction
(GR6) from `SerrinEpigraph.ConeSplitting`: a tangent cone at a nonzero boundary point splits off
the direction of that point, so by the induction hypothesis it is a half-space, so the point is
regular by ε-regularity. Simons then classifies the cone.

Main results: `coneClassification_succ`, `coneClassification_of_simonsHyp` and
`IsMinimizingCone.ae_eq_positiveHalfspace_of_le_seven_of_regularity`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- **ε-regularity (GR9–GR14), as a hypothesis.** If some tangent cone of a local perimeter
minimizer at a measure-theoretic boundary point is a.e. a half-space, then the point is a `C¹`
boundary point. -/
def EpsilonRegularityHyp : Prop :=
  ∀ (d : ℕ) (E Ω : Set (Space d)) (x : Space d),
    IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) E Ω →
    x ∈ measureTheoreticBoundary E ∩ Ω →
    (∃ T : Set (Space d), IsTangentCone E x T ∧
      ∃ e : Space d, ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e) →
    IsC1BoundaryPoint E x

/-- **Simons' theorem (GR1–GR4) with boundary regularity, as a hypothesis in `Space k`.** A
minimizing cone whose boundary points other than the vertex are all `C¹` boundary points is a.e.
a half-space. It holds for `k ≤ 7`. -/
def SimonsHyp (k : ℕ) : Prop :=
  ∀ T : Set (Space k), IsMinimizingCone T →
    (∀ x ∈ measureTheoreticBoundary T, x ≠ 0 → IsC1BoundaryPoint T x) →
    ∃ e : Space k, ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e

/-- Classification of minimizing cones in `Space k`: every minimizing cone is a.e. a half-space. -/
def ConeClassification (k : ℕ) : Prop :=
  ∀ T : Set (Space k), IsMinimizingCone T →
    ∃ e : Space k, ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e

/-- `Space 0` is a point, so it carries no nontrivial set. -/
theorem not_isMinimizingCone_space_zero (T : Set (Space 0)) : ¬ IsMinimizingCone T := by
  intro hT
  have hsub : ∀ x y : Space 0, x = y := fun x y ↦ by
    ext i
    exact i.elim0
  rcases T.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact hT.nontrivial.1 (by rw [h, measure_empty])
  · have hc : Tᶜ = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy ↦ hy ?_
      rw [hsub y x]
      exact hx
    exact hT.nontrivial.2 (by rw [hc, measure_empty])

theorem coneClassification_zero : ConeClassification 0 :=
  fun T hT ↦ absurd hT (not_isMinimizingCone_space_zero T)

theorem coneClassification_one : ConeClassification 1 :=
  fun _ hT ↦ hT.ae_eq_positiveHalfspace_one

theorem simonsHyp_one : SimonsHyp 1 :=
  fun _ hT _ ↦ hT.ae_eq_positiveHalfspace_one

/-- **No singularities away from the vertex.** If the minimizing cones one dimension lower are
classified, every nonzero boundary point of a minimizing cone is a `C¹` boundary point: a tangent
cone there splits off the direction of the point (GR5, GR6), hence is a half-space, and
ε-regularity applies. -/
theorem IsMinimizingCone.isC1BoundaryPoint_of_coneClassification
    (hreg : EpsilonRegularityHyp) {k : ℕ} (hlow : ConeClassification k)
    {T : Set (Space (k + 1))} (hT : IsMinimizingCone T) {x : Space (k + 1)}
    (hx : x ∈ measureTheoreticBoundary T) (hx0 : x ≠ 0) : IsC1BoundaryPoint T x := by
  obtain ⟨C, hC, -, -⟩ := hT.exists_isTangentCone hx
  obtain ⟨e, he, -, hCe⟩ := hT.isTangentCone_ae_eq_halfspace_of_lower hlow hx hx0 hC
  exact hreg (k + 1) T univ x hT.minimizer ⟨hx, mem_univ x⟩ ⟨C, hC, e, he, hCe⟩

/-- **Induction step of GR16.** -/
theorem coneClassification_succ (hreg : EpsilonRegularityHyp) {k : ℕ}
    (hk : ConeClassification k) (hs : SimonsHyp (k + 1)) : ConeClassification (k + 1) :=
  fun T hT ↦ hs T hT fun _ hx hx0 ↦ hT.isC1BoundaryPoint_of_coneClassification hreg hk hx hx0

/-- **GR16.** Given ε-regularity and Simons' theorem in the dimensions `2, …, n`, every minimizing
cone in `Space k`, `k ≤ n`, is a.e. a half-space. -/
theorem coneClassification_of_simonsHyp (hreg : EpsilonRegularityHyp) {n : ℕ}
    (hs : ∀ k, 2 ≤ k → k ≤ n → SimonsHyp k) : ∀ k ≤ n, ConeClassification k := by
  intro k hk
  induction k with
  | zero => exact coneClassification_zero
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      exact coneClassification_one
    · exact coneClassification_succ hreg (ih (by omega)) (hs (k + 1) (by omega) hk)

/-- **GR16 in ambient dimension at most seven**, relative to ε-regularity and Simons' theorem. -/
theorem IsMinimizingCone.ae_eq_positiveHalfspace_of_le_seven_of_regularity
    (hreg : EpsilonRegularityHyp) (hs : ∀ k, 2 ≤ k → k ≤ 7 → SimonsHyp k) {k : ℕ} (hk : k ≤ 7)
    {T : Set (Space k)} (hT : IsMinimizingCone T) :
    ∃ e : Space k, ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e :=
  coneClassification_of_simonsHyp hreg hs k hk T hT

/-- Under the same inputs, minimizing cones in dimension at most seven have no singular points. -/
theorem IsMinimizingCone.singularSet_eq_empty_of_le_seven_of_regularity
    (hreg : EpsilonRegularityHyp) (hs : ∀ k, 2 ≤ k → k ≤ 7 → SimonsHyp k) {k : ℕ} (hk : k ≤ 7)
    {T : Set (Space k)} (hT : IsMinimizingCone T) : singularSet T = ∅ := by
  obtain ⟨e, he, hTe⟩ := hT.ae_eq_positiveHalfspace_of_le_seven_of_regularity hreg hs hk
  have he0 : e ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at he
    exact zero_ne_one he
  exact singularSet_eq_empty_of_ae_eq_positiveHalfspace he0 hTe

end SerrinEpigraph
