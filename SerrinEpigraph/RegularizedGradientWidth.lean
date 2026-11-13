module

public import SerrinEpigraph.ThresholdRecoveryEnergy

/-!
# Positive smooth widths approximating gradient norm
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace

namespace SerrinEpigraph

/-- A positive regularization of gradient norm used as the transition width. -/
@[expose] def regularizedGradientWidth {d : ℕ} (φ : Space d → ℝ) (ε : ℝ)
    (x : Space d) : ℝ := Real.sqrt (ε ^ 2 + ‖gradient φ x‖ ^ 2)

/-- The regularized width is positive and differs from gradient norm by at most ε. -/
theorem regularizedGradientWidth_bounds {d : ℕ} (φ : Space d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (x : Space d) : 0 < regularizedGradientWidth φ ε x ∧
      ‖gradient φ x‖ ≤ regularizedGradientWidth φ ε x ∧
      regularizedGradientWidth φ ε x ≤ ‖gradient φ x‖ + ε := by
  have hp : 0 < ε ^ 2 + ‖gradient φ x‖ ^ 2 := by positivity
  have hpos : 0 < regularizedGradientWidth φ ε x := Real.sqrt_pos.mpr hp
  have hs : regularizedGradientWidth φ ε x ^ 2 = ε ^ 2 + ‖gradient φ x‖ ^ 2 :=
    Real.sq_sqrt hp.le
  exact ⟨hpos, by nlinarith [norm_nonneg (gradient φ x)],
    by nlinarith [norm_nonneg (gradient φ x)]⟩

/-- A twice continuously differentiable phase has a C1 positive regularized width. -/
theorem regularizedGradientWidth_contDiff {d : ℕ} {φ : Space d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (regularizedGradientWidth φ ε) := by
  have hg : ContDiff ℝ 1 (gradient φ) :=
    (toDual ℝ (Space d)).symm.contDiff.comp (hφ.fderiv_right (by norm_num))
  exact (contDiff_const.add (hg.norm_sq (𝕜 := ℝ))).sqrt
    (fun x ↦ (show 0 < ε ^ 2 + ‖gradient φ x‖ ^ 2 by positivity).ne')

/-- Regularizing the width adds at most ε times volume to its local mass. -/
theorem integral_regularizedGradientWidth_le {d : ℕ} {φ : Space d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {ε : ℝ} (hε : 0 < ε) {K : Set (Space d)} (hK : IsCompact K) :
    (∫ x in K, regularizedGradientWidth φ ε x) ≤
      (∫ x in K, ‖gradient φ x‖) + ε * (volume K).toReal := by
  have hg : Continuous (gradient φ) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hφ.continuous_fderiv (by norm_num))
  have hi := (regularizedGradientWidth_contDiff hφ hε).continuous.continuousOn.integrableOn_compact
    (μ := volume) hK
  have hj := hg.norm.continuousOn.integrableOn_compact (μ := volume) hK
  have hc : IntegrableOn (fun _ : Space d ↦ ε) K := continuousOn_const.integrableOn_compact hK
  have he := integral_mono hi (hj.add hc)
    (fun x ↦ (regularizedGradientWidth_bounds φ hε x).2.2)
  simpa only [Pi.add_apply, integral_add hj hc, integral_const, smul_eq_mul,
    measureReal_def, Measure.restrict_apply_univ, mul_comm] using he

/-- On a compact region both the width and its relative gradient have finite
nonnegative bounds, uniformly for all threshold parameters. -/
theorem exists_regularizedGradientWidth_bounds {d : ℕ} {φ : Space d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {ε : ℝ} (hε : 0 < ε) {K : Set (Space d)} (hK : IsCompact K) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ x ∈ K,
      regularizedGradientWidth φ ε x ≤ A ∧
        ‖gradient (regularizedGradientWidth φ ε) x‖ / regularizedGradientWidth φ ε x ≤ C := by
  have ha := regularizedGradientWidth_contDiff hφ hε
  have hpos := fun x ↦ (regularizedGradientWidth_bounds φ hε x).1
  have hg : Continuous (gradient (regularizedGradientWidth φ ε)) :=
    (toDual ℝ (Space d)).symm.continuous.comp (ha.continuous_fderiv one_ne_zero)
  have hc := hg.norm.div ha.continuous (fun x ↦ (hpos x).ne')
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn ha.continuous.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max A 0, max C 0, le_max_right _ _, le_max_right _ _, fun x hx ↦ ⟨?_, ?_⟩⟩
  · exact ((Real.le_norm_self _).trans (hA x hx)).trans (le_max_left _ _)
  · exact ((Real.le_norm_self _).trans (hC x hx)).trans (le_max_left _ _)

end SerrinEpigraph
