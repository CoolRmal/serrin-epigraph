module

public import SerrinEpigraph.CompactContact
public import SerrinEpigraph.PolynomialBarrier
public import SerrinEpigraph.Reaction
public import SerrinEpigraph.Geometry

/-!
# A uniform lower bound at the center of a large interior ball
-/

public section

noncomputable section

open Metric InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive solution with a coercive reaction below `a` lies above `a` at the center
of any interior ball whose comparison coefficient is smaller than the reaction coefficient. -/
theorem ball_center_lower_bound {Ω : Set E} {u : E → ℝ} {z : E} {R a c : ℝ}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hR : 0 < R) (ha : 0 < a)
    (hsub : closedBall z R ⊆ Ω) (hupos : ∀ x ∈ closedBall z R, 0 < u x)
    (hgap : ((Module.finrank ℝ E : ℝ) + 2) ^ 2 / R ^ 2 < c)
    (huineq : ∀ x ∈ closedBall z R, u x ≤ a → c * u x ≤ -(Δ u) x) : a ≤ u z := by
  let k := a / R ^ 4
  let ψ : E → ℝ := fun x ↦ k * polynomialBallBarrier z R x
  have hk : 0 < k := div_pos ha (pow_pos hR 4)
  have hψ : ContDiff ℝ 2 ψ := contDiff_const.mul (contDiff_polynomialBallBarrier z R)
  have hboundary : ∀ x ∈ closedBall z R, x ∉ interior (closedBall z R) → ψ x = 0 := by
    intro x hx hn
    have hd : dist x z = R := by
      apply le_antisymm hx
      by_contra hnot
      have hball : x ∈ ball z R := lt_of_not_ge hnot
      exact hn ((interior_maximal ball_subset_closedBall isOpen_ball) hball)
    simp [ψ, polynomialBallBarrier_sphere z x R hd]
  have hupper : ∀ x ∈ closedBall z R, ψ x ≤ a := by
    intro x hx
    have hn : ‖x - z‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hsq : ‖x - z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x - z)]
    have hb : polynomialBallBarrier z R x ≤ R ^ 4 := by
      dsimp [polynomialBallBarrier]
      nlinarith [sq_nonneg (‖x - z‖ ^ 2), sq_nonneg (R ^ 2 - ‖x - z‖ ^ 2)]
    have hs := mul_le_mul_of_nonneg_left hb hk.le
    have hcenter : k * R ^ 4 = a := by dsimp [k]; field_simp
    exact hs.trans_eq hcenter
  have hlap (x : E) : (Δ ψ) x = k * (Δ (polynomialBallBarrier z R)) x := by
    change (Δ (k • polynomialBallBarrier z R)) x = _
    exact laplacian_smul k (contDiff_polynomialBallBarrier z R (n := 2)).contDiffAt
  have hb := compact_comparison_of_coefficient_gap (isCompact_closedBall z R) hΩ hsub
    hu hψ.contDiffOn hupos hboundary hupper hgap huineq
    (fun x _ ↦ ?_) z (mem_closedBall_self hR.le)
  · simpa [ψ, polynomialBallBarrier_center, k, hR.ne'] using hb
  · rw [hlap]
    have hb := mul_le_mul_of_nonneg_left (neg_laplacian_polynomialBallBarrier_le z x hR) hk.le
    dsimp [ψ]
    nlinarith

/-- The reaction quotient condition supplies the large-ball lower bound for the original PDE. -/
theorem Hypotheses.solution_ge_at_ball_center {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    {z : Space (m + 1)} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hsub : closedBall z R ⊆ epigraph g)
    (hgap : ((Module.finrank ℝ (Space (m + 1)) : ℝ) + 2) ^ 2 / R ^ 2 < f a / a) :
    a ≤ u z := by
  apply ball_center_lower_bound (isOpen_epigraph h.graph_contDiff.continuous)
    h.solution_contDiffOn hR ha hsub (fun x hx ↦ h.positive x (hsub hx)) hgap
  intro x hx hua
  rw [h.equation x (hsub hx)]
  exact (le_div_iff₀ (h.positive x (hsub hx))).mp
    (antitoneOn_reaction_div h.reaction_contDiffOn h.reaction_structure
      (h.positive x (hsub hx)) ha hua)

end SerrinEpigraph
