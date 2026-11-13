module

public import SerrinEpigraph.GraphHeightGradient
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Product-coordinate decomposition of Euclidean volume
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace SerrinEpigraph

/-- Splitting off the last Euclidean coordinate preserves Lebesgue volume. -/
theorem measurePreserving_horizontal_last (d : ℕ) :
    MeasurePreserving (fun x : Space (d + 1) ↦ (horizontal x, x (Fin.last d)))
      volume ((volume : Measure (Space d)).prod volume) := by
  have h₁ := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).comp
    (PiLp.volume_preserving_ofLp (Fin (d + 1)))
  have h₂ := Measure.measurePreserving_swap.comp h₁
  have h₃ := ((PiLp.volume_preserving_toLp (Fin d)).prod (MeasurePreserving.id (volume : Measure ℝ))).comp h₂
  convert h₃ using 1
  ext x <;> simp [horizontal, Function.comp_def, MeasurableEquiv.piFinSuccAbove,
    Fin.insertNthEquiv, Fin.init]

/-- Normalized graph-height distributions in Euclidean space satisfy the product-coordinate bound. -/
theorem map_euclidean_graphHeight_volume_le {d : ℕ} {b : Space d → ℝ} (hb : Measurable b)
    {A : Set (Space d)} (hA : MeasurableSet A) {K : Set (Space (d + 1))}
    (hK : ∀ x ∈ K, horizontal x ∈ A) {L : ℝ} (hL : 0 < L) :
    Measure.map (fun x ↦ graphHeight b x / L) (volume.restrict K) ≤
      (volume A * ENNReal.ofReal L) • (volume : Measure ℝ) := by
  let σ : Space (d + 1) → Space d × ℝ := fun x ↦ (horizontal x, x (Fin.last d))
  have hσ := measurePreserving_horizontal_last d
  have hs : K ⊆ σ ⁻¹' (A ×ˢ (univ : Set ℝ)) := fun x hx ↦ ⟨hK x hx, mem_univ _⟩
  have hm := Measure.map_mono (Measure.restrict_mono hs (le_refl volume)) hσ.measurable
  rw [(hσ.restrict_preimage (hA.prod MeasurableSet.univ)).map_eq] at hm
  have hc : Measurable (fun p : Space d × ℝ ↦ (-b p.1 + p.2) / L) :=
    ((hb.comp measurable_fst).neg.add measurable_snd).div_const L
  have he := (Measure.map_mono hm hc).trans
    (map_normalizedGraphHeight_volume_le hb hA (fun p hp ↦ hp.1) hL)
  rw [Measure.map_map hc hσ.measurable] at he
  simpa only [Function.comp_def, σ, graphHeight, sub_eq_neg_add] using he

end SerrinEpigraph
