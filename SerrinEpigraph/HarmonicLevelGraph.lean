module

public import SerrinEpigraph.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Quantitative level graphs

A positive normal derivative and opposite face values produce unique level
graphs. The normal derivative lower bound and horizontal oscillation bound give
the precise joint estimate in base point and level.
-/

public section
noncomputable section

open Set Metric

namespace SerrinEpigraph

/-- A lower derivative bound controls the inverse separation on the whole
closed interval, including its endpoints. -/
theorem mul_abs_sub_le_abs_image_sub_of_deriv_lower_bound
    {F : ℝ → ℝ} {a b κ : ℝ} (hκ : 0 < κ)
    (hc : ContinuousOn F (Icc a b))
    (hd : DifferentiableOn ℝ F (Ioo a b))
    (hb : ∀ t ∈ Ioo a b, κ ≤ deriv F t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    κ * |s - t| ≤ |F s - F t| := by
  have hg := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc
    (by simpa only [interior_Icc] using hd) (by simpa only [interior_Icc] using hb)
  rcases le_total s t with hst | hts
  · have hh := hg s hs t ht hst
    have hf : F s ≤ F t := by nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hst), abs_of_nonpos (sub_nonpos.mpr hf)]
    linarith
  · have hh := hg t ht s hs hts
    have hf : F t ≤ F s := by nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr hts), abs_of_nonneg (sub_nonneg.mpr hf)]
    exact hh

/-- A continuous increasing section whose face values bracket a level has a
unique height in the closed section. -/
theorem existsUnique_height_of_deriv_lower_bound
    {F : ℝ → ℝ} {a b κ t : ℝ} (hab : a ≤ b) (hκ : 0 < κ)
    (hc : ContinuousOn F (Icc a b))
    (hd : DifferentiableOn ℝ F (Ioo a b))
    (hb : ∀ s ∈ Ioo a b, κ ≤ deriv F s)
    (ht : t ∈ Icc (F a) (F b)) :
    ∃! s : ℝ, s ∈ Icc a b ∧ F s = t := by
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc hab hc ht
  refine ⟨s, ⟨hs, hst⟩, ?_⟩
  intro z hz
  have hh := mul_abs_sub_le_abs_image_sub_of_deriv_lower_bound hκ hc hd hb hz.1 hs
  rw [hz.2, hst, sub_self, abs_zero] at hh
  have he : |z - s| = 0 := by nlinarith [abs_nonneg (z - s)]
  exact sub_eq_zero.mp (abs_eq_zero.mp he)

/-- Quantitative joint level graphs on any base set. A horizontal Lipschitz
bound and a positive normal derivative give the graph estimate without any
assumed existence or uniqueness of graph heights. -/
theorem exists_quantitative_level_graph {d : ℕ}
    (F : Space d → ℝ → ℝ) (S : Set (Space d)) {a b α β κ L : ℝ}
    (hab : a ≤ b) (hκ : 0 < κ)
    (hc : ∀ y ∈ S, ContinuousOn (F y) (Icc a b))
    (hd : ∀ y ∈ S, DifferentiableOn ℝ (F y) (Ioo a b))
    (hderiv : ∀ y ∈ S, ∀ s ∈ Ioo a b, κ ≤ deriv (F y) s)
    (hlower : ∀ y ∈ S, F y a ≤ α) (hupper : ∀ y ∈ S, β ≤ F y b)
    (hhorizontal : ∀ y ∈ S, ∀ z ∈ S, ∀ s ∈ Icc a b,
      |F y s - F z s| ≤ L * dist y z) :
    ∃ H : S → Icc α β → ℝ,
      (∀ y t, H y t ∈ Icc a b ∧ F y (H y t) = t) ∧
      (∀ (y : S) (t : Icc α β) (s : ℝ), s ∈ Icc a b → F y s = t → s = H y t) ∧
      ∀ y z t q, κ * |H y t - H z q| ≤ L * dist y.val z.val + |t.val - q.val| := by
  have hex (y : S) (t : Icc α β) :
      ∃! s : ℝ, s ∈ Icc a b ∧ F y s = t := by
    apply existsUnique_height_of_deriv_lower_bound hab hκ (hc y y.property)
      (hd y y.property) (hderiv y y.property)
    exact ⟨(hlower y y.property).trans t.property.1,
      t.property.2.trans (hupper y y.property)⟩
  choose H hH using fun (y : S) (t : Icc α β) ↦ (hex y t).exists
  refine ⟨H, hH, ?_, ?_⟩
  · intro y t s hs ht
    exact (hex y t).unique ⟨hs, ht⟩ (hH y t)
  · intro y z t q
    have hnormal := mul_abs_sub_le_abs_image_sub_of_deriv_lower_bound hκ
      (hc y y.property) (hd y y.property) (hderiv y y.property)
      (hH y t).1 (hH z q).1
    have hbase := hhorizontal y y.property z z.property (H z q) (hH z q).1
    have htri := abs_sub_le (F y (H y t)) (F z (H z q)) (F y (H z q))
    rw [abs_sub_comm (F z (H z q)) (F y (H z q))] at htri
    rw [(hH y t).2] at hnormal
    rw [(hH y t).2, (hH z q).2] at htri
    rw [(hH z q).2] at hbase
    linarith

end SerrinEpigraph
