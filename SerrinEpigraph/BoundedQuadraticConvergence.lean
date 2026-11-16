module

public import SerrinEpigraph.PhysicalTranslationEnergy

/-!
# Quadratic expressions of bounded strongly convergent gradients
-/

public section

noncomputable section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Quadratic fluxes are Lipschitz on a bounded vector ball. -/
theorem norm_inner_linear_sub_le {d : ℕ} (B : Space d →L[ℝ] Space d)
    {q r : Space d} {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hq : ‖q‖ ≤ L) (hr : ‖r‖ ≤ L) (hB : ‖B‖ ≤ D) :
    ‖inner ℝ q (B q) - inner ℝ r (B r)‖ ≤ 2 * L * D * ‖q - r‖ := by
  have he : inner ℝ q (B q) - inner ℝ r (B r) =
      inner ℝ (q - r) (B q) + inner ℝ r (B (q - r)) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  have hBq : ‖B q‖ ≤ D * L := (B.le_opNorm q).trans
    (mul_le_mul hB hq (norm_nonneg _) hD)
  have hBd : ‖B (q - r)‖ ≤ D * ‖q - r‖ := (B.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  apply (norm_add_le _ _).trans
  have h₁ := (norm_inner_le_norm (𝕜 := ℝ) (q - r) (B q)).trans
    (mul_le_mul_of_nonneg_left hBq (norm_nonneg _))
  have h₂ := (norm_inner_le_norm (𝕜 := ℝ) r (B (q - r))).trans
    (mul_le_mul hr hBd (norm_nonneg _) hL)
  nlinarith

/-- Bounded measurable quadratic fluxes are locally integrable. -/
theorem integrableOn_inner_linear_of_bounds {d : ℕ}
    {q : Space d → Space d} {B : Space d → Space d →L[ℝ] Space d}
    (hq : Measurable q) (hB : Continuous B) {L D : ℝ}
    (hL : ∀ x, ‖q x‖ ≤ L) (hD : ∀ x, ‖B x‖ ≤ D)
    {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ inner ℝ (q x) (B x (q x))) K := by
  apply (continuousOn_const.integrableOn_compact hK
    (f := fun _ : Space d ↦ L * (D * L))).mono'
    (hq.inner (𝕜 := ℝ) ((continuous_fst.clm_apply continuous_snd).measurable.comp
      (hB.measurable.prodMk hq))).aestronglyMeasurable
  filter_upwards with x
  have hL0 := (norm_nonneg _).trans (hL x)
  have hD0 := (norm_nonneg _).trans (hD x)
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul (hL x) ((B x).le_opNorm _ |>.trans
      (mul_le_mul (hD x) (hL x) (norm_nonneg _) hD0)) (norm_nonneg _) hL0)

/-- Integral-norm convergence of bounded vectors passes to continuous bounded
quadratic fluxes on a compact set. -/
theorem integral_norm_quadratic_sub_tendsto
    {d : ℕ} {q : ℕ → Space d → Space d} {r : Space d → Space d}
    {B : Space d → Space d →L[ℝ] Space d} {L D : ℝ}
    (hq : ∀ j, Measurable (q j)) (hr : Measurable r) (hB : Continuous B)
    (hqL : ∀ j x, ‖q j x‖ ≤ L) (hrL : ∀ x, ‖r x‖ ≤ L) (hBD : ∀ x, ‖B x‖ ≤ D)
    {K : Set (Space d)} (hK : IsCompact K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖q j x - r x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖inner ℝ (q j x) (B x (q j x)) - inner ℝ (r x) (B x (r x))‖) atTop (𝓝 0) := by
  have hL0 := (norm_nonneg _).trans (hrL 0)
  have hD0 := (norm_nonneg _).trans (hBD 0)
  have hbound := ht.const_mul (2 * L * D)
  simp only [mul_zero] at hbound
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ hbound
  intro j
  have hiq := integrableOn_inner_linear_of_bounds (hq j) hB (hqL j) hBD hK
  have hir := integrableOn_inner_linear_of_bounds hr hB hrL hBD hK
  have hid : IntegrableOn (fun x ↦ ‖q j x - r x‖) K := by
    apply (continuousOn_const.integrableOn_compact hK
      (f := fun _ : Space d ↦ 2 * L)).mono' ((hq j).sub hr).norm.aestronglyMeasurable
    filter_upwards with x
    change ‖‖q j x - r x‖‖ ≤ 2 * L
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by linarith [hqL j x, hrL x])
  rw [← integral_const_mul]
  apply integral_mono (hiq.sub hir).norm (hid.const_mul _)
  intro x
  exact norm_inner_linear_sub_le (B x) hL0 hD0 (hqL j x) (hrL x) (hBD x)

end SerrinEpigraph
