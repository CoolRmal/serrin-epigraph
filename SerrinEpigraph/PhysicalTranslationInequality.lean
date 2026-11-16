module

public import SerrinEpigraph.BoundaryWeakInequality
public import SerrinEpigraph.PhysicalTranslationEquation

/-!
# The boundary inequality retained by physical translation limits

The global distributional inequality survives arbitrary physical translations
and locally uniform limits, including points on the limiting free boundary.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The zero extension's distributional inequality is invariant under translation. -/
theorem RigidityHypotheses.translated_zeroExtension_distributional_inequality
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (p : Space (m + 1)) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∫ x, f (zeroExtension g u (p + x)) * φ x) ≤
      ∫ x, zeroExtension g u (p + x) * (Δ φ) x := by
  let ψ : Space (m + 1) → ℝ := fun x ↦ φ (x + -p)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ :=
    hc.comp_isClosedEmbedding (isometry_add_right (-p)).isClosedEmbedding
  have hi := hr.zeroExtension_distributional_inequality h hψ hcψ (fun x ↦ hφ0 _)
  have hleft := integral_add_right_eq_self (μ := volume)
    (fun x ↦ f (zeroExtension g u x) * ψ x) p
  have hright := integral_add_right_eq_self (μ := volume)
    (fun x ↦ zeroExtension g u x * (Δ ψ) x) p
  simp only [ψ, laplacian_comp_add_right, add_neg_cancel_right] at hi hleft hright
  rw [← hleft, ← hright] at hi
  simpa only [add_comm] using hi

/-- Physical translation limits retain the global inequality across their zero set. -/
theorem RigidityHypotheses.physical_translation_limit_distributional_inequality
    {m : ℕ} {g : Space m → ℝ} {u V φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ x, Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝 (V x)))
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∫ x, f (V x) * φ x) ≤ ∫ x, V x * (Δ φ) x := by
  have hleft := hr.physical_translation_observable_tendsto h hval hlim hc
    hφ.continuous.continuousOn (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hright := hr.physical_translation_observable_tendsto h hval hlim hc
    (continuous_laplacian_of_contDiff hφ).continuousOn (A := id) continuousOn_id
  simp only [setIntegral_mul_test] at hleft
  simp only [id_eq, setIntegral_mul_laplacian_test] at hright
  exact le_of_tendsto_of_tendsto' hleft.neg hright
    (fun j ↦ hr.translated_zeroExtension_distributional_inequality h (p j) hφ hc hφ0)

end SerrinEpigraph
