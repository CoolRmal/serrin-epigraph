module

public import SerrinEpigraph.BallCutoff
public import SerrinEpigraph.CutoffDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Radial cutoffs with a fixed transition width

The gradient constant depends only on a scalar transition profile, not on the inner radius.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace SerrinEpigraph

private theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  intro t ht
  by_cases h0 : 0 ≤ t
  · by_cases h1 : t ≤ 1
    · exact ⟨h0, h1⟩
    · exfalso
      apply ht
      have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge h1)] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      exact ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq).deriv
  · exfalso
    apply ht
    have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge h0)] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq).deriv

private def radialTransition {d : ℕ} (R H : ℝ) (x : Space d) : ℝ :=
  Real.smoothTransition ((R + H - ‖x‖) / H)

private theorem radialTransition_one {d : ℕ} {R H : ℝ} (hH : 0 < H)
    {x : Space d} (hx : ‖x‖ ≤ R) : radialTransition R H x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div hH]
  linarith

private theorem radialTransition_locally_one {d : ℕ} {R H : ℝ} (hR : 0 < R) (hH : 0 < H) :
    radialTransition (d := d) R H =ᶠ[𝓝 0] fun _ ↦ (1 : ℝ) := by
  filter_upwards [Metric.ball_mem_nhds (0 : Space d) hR] with x hx
  apply radialTransition_one hH
  exact (mem_ball_zero_iff.mp hx).le

private theorem contDiff_radialTransition {d : ℕ} {R H : ℝ} (hR : 0 < R) (hH : 0 < H) :
    ContDiff ℝ 1 (radialTransition (d := d) R H) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      (radialTransition_locally_one hR hH)
  · apply Real.smoothTransition.contDiffAt.comp
    exact ((contDiffAt_const.sub (contDiffAt_id.norm ℝ hx)).div_const H)

private theorem tsupport_radialTransition_subset {d : ℕ} {R H : ℝ} (hH : 0 < H) :
    tsupport (radialTransition (d := d) R H) ⊆ Metric.closedBall 0 (R + H) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hpos : 0 < (R + H - ‖x‖) / H := by
    apply lt_of_not_ge
    intro hnonpos
    apply hx
    exact Real.smoothTransition.zero_of_nonpos hnonpos
  have := (div_pos_iff_of_pos_right hH).mp hpos
  linarith

private theorem norm_fderiv_radialTransition_le {d : ℕ} {R H B : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hB : 0 ≤ B)
    (hderiv : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ B) (x : Space d) :
    ‖fderiv ℝ (radialTransition R H) x‖ ≤ B / H := by
  by_cases hx : x = 0
  · subst x
    have hz := ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) (0 : Space d)).congr_of_eventuallyEq
      (radialTransition_locally_one hR hH)).fderiv
    rw [hz, norm_zero]
    exact div_nonneg hB hH.le
  · have hn : DifferentiableAt ℝ (fun y : Space d ↦ ‖y‖) x :=
      (contDiffAt_norm ℝ (n := 1) hx).differentiableAt one_ne_zero
    have hi : HasFDerivAt (fun y : Space d ↦ (R + H - ‖y‖) / H)
        (H⁻¹ • -fderiv ℝ (fun y : Space d ↦ ‖y‖) x) x := by
      simpa only [smul_eq_mul, div_eq_inv_mul] using
        (hn.hasFDerivAt.const_sub (R + H)).fun_const_smul H⁻¹
    have ht := (Real.smoothTransition.contDiff (n := 1)).differentiable_one
      ((R + H - ‖x‖) / H)
    have hd := ht.hasDerivAt.comp_hasFDerivAt x hi
    simp only [Function.comp_def] at hd
    have hnorm : ‖fderiv ℝ (fun y : Space d ↦ ‖y‖) x‖ ≤ 1 := by
      simpa using (norm_fderiv_le_of_lipschitz ℝ
        (f := fun y : Space d ↦ ‖y‖) (x₀ := x) lipschitzWith_one_norm)
    change ‖fderiv ℝ (fun y ↦ Real.smoothTransition ((R + H - ‖y‖) / H)) x‖ ≤ _
    rw [hd.fderiv]
    simp only [norm_smul, Real.norm_eq_abs, norm_neg, abs_of_pos (inv_pos.mpr hH)]
    calc
      _ ≤ B * (H⁻¹ * 1) :=
        mul_le_mul (hderiv _)
          (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hH.le)) (by positivity) hB
      _ = B / H := by ring

/-- The same positive constant works for all dimensions, inner radii, and transition widths. -/
theorem exists_fixedWidth_ball_cutoffs :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (R L : ℝ), 0 < R → 0 < L →
      ∃ χ : Space d → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ Metric.ball 0 (R + L) ∧
        (∀ x ∈ Metric.ball 0 R, χ x = 1) ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
        ∀ x, ‖gradient χ x‖ ≤ C / L := by
  obtain ⟨B, hB⟩ := hasCompactSupport_deriv_smoothTransition.exists_bound_of_continuous
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one
  refine ⟨2 * max B 1, by positivity, fun d R L hR hL ↦ ?_⟩
  let χ : Space d → ℝ := radialTransition R (L / 2)
  have hH : 0 < L / 2 := by positivity
  have hsupp := tsupport_radialTransition_subset (d := d) (R := R) hH
  refine ⟨χ, contDiff_radialTransition hR hH, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall 0 (R + L / 2)).of_isClosed_subset isClosed_closure hsupp
  · exact hsupp.trans (Metric.closedBall_subset_ball (by linarith))
  · intro x hx
    exact radialTransition_one hH (mem_ball_zero_iff.mp hx).le
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x
    rw [norm_gradient_eq_norm_fderiv]
    have hh := norm_fderiv_radialTransition_le hR hH
      (le_trans zero_le_one (le_max_right B 1)) (fun t ↦ (hB t).trans (le_max_left B 1)) x
    convert hh using 1
    ring

end SerrinEpigraph
