module

public import SerrinEpigraph.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

/-!
# Ball cutoffs with a uniform scaled derivative bound
-/

@[expose] public section

noncomputable section

namespace SerrinEpigraph

private def unitBallBump (d : ℕ) : ContDiffBump (0 : Space d) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

private theorem norm_fderiv_scaled_le {d : ℕ} {φ : Space d → ℝ}
    (hφ : Differentiable ℝ φ) {C R : ℝ} (hC : ∀ x, ‖fderiv ℝ φ x‖ ≤ C) (hR : 0 < R)
    (x : Space d) : ‖fderiv ℝ (fun y ↦ φ (R⁻¹ • y)) x‖ ≤ C / R := by
  have hd := (hφ (R⁻¹ • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul R⁻¹)
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, Function.comp_def] at hd
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr hR.le)

private theorem support_unitBallBump_scaled {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Function.support (fun x : Space d ↦ unitBallBump d (R⁻¹ • x)) = Metric.ball 0 (2 * R) := by
  change Function.support ((unitBallBump d) ∘ fun x : Space d ↦ R⁻¹ • x) = _
  rw [Function.support_comp_eq_preimage]
  rw [(unitBallBump d).support_eq]
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hR, unitBallBump, ← div_eq_inv_mul]
  exact div_lt_iff₀ hR

/-- A dimension-dependent constant controls the derivatives of all scaled ball cutoffs. -/
theorem exists_ball_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∃ χ : Space d → ℝ,
      ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      Function.support χ ⊆ Metric.ball 0 (2 * R) ∧
      (∀ x ∈ Metric.ball 0 R, χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x, ‖fderiv ℝ χ x‖ ≤ C / R := by
  have hb : ContDiff ℝ 1 (unitBallBump d) := (unitBallBump d).contDiff
  obtain ⟨B, hB⟩ := ((unitBallBump d).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv (by norm_num))
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun R hR ↦ ?_⟩
  let χ : Space d → ℝ := fun x ↦ unitBallBump d (R⁻¹ • x)
  have hsupp : Function.support χ = Metric.ball 0 (2 * R) := support_unitBallBump_scaled hR
  have hscale : ContDiff ℝ 1 (fun x : Space d ↦ R⁻¹ • x) := by fun_prop
  refine ⟨χ, hb.comp hscale, ?_, hsupp.subset, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (2 * R))
    rw [hsupp]
    exact Metric.ball_subset_closedBall
  · intro x hx
    apply (unitBallBump d).one_of_mem_closedBall
    change ‖R⁻¹ • x - 0‖ ≤ 1
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ← div_eq_inv_mul]
    apply (div_le_one hR).2
    exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  · intro x
    exact ⟨(unitBallBump d).nonneg, (unitBallBump d).le_one⟩
  · exact norm_fderiv_scaled_le hb.differentiable_one (fun x ↦ (hB x).trans (le_max_left _ _)) hR

end SerrinEpigraph
