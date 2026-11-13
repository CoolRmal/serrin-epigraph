module

public import SerrinEpigraph.LevelHeight

/-!
# Joint continuity of the inverse height
-/

public section

open Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Comparing an interior height with an inverse level is equivalent to comparing solution values. -/
theorem RigidityHypotheses.lt_levelHeight_iff (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : g y < t) :
    t < hr.levelHeight h y s ↔ u (point y t) < s := by
  have hs := hr.levelHeight_spec h y s
  simpa only [hs.2] using ((h.vertical_section_strictMonoOn y).lt_iff_lt ht hs.1).symm

/-- The reverse strict comparison with an inverse level. -/
theorem RigidityHypotheses.levelHeight_lt_iff (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (y : Space m) (s : Set.Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : g y < t) :
    hr.levelHeight h y s < t ↔ (s : ℝ) < u (point y t) := by
  have hs := hr.levelHeight_spec h y s
  simpa only [hs.2] using ((h.vertical_section_strictMonoOn y).lt_iff_lt hs.1 ht).symm

/-- A horizontal section is continuous at every point lying strictly above the graph. -/
theorem Hypotheses.continuousAt_horizontal_section (h : Hypotheses g u f κ)
    {y : Space m} {t : ℝ} (ht : g y < t) :
    ContinuousAt (fun z ↦ u (point z t)) y := by
  have hp : Continuous (fun z : Space m ↦ point z t) :=
    pointContinuousLinearMap.continuous.comp (continuous_id.prodMk continuous_const)
  have hx : point y t ∈ epigraph g := by simpa [epigraph] using ht
  exact (h.solution_contDiffOn.continuousOn.continuousAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)).comp (f := fun z ↦ point z t) hp.continuousAt

/-- The inverse height varies continuously in both the horizontal location and the level. -/
theorem RigidityHypotheses.levelHeight_joint_continuous (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    Continuous (fun p : Space m × Set.Ioo (0 : ℝ) 1 ↦ hr.levelHeight h p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hs := hr.levelHeight_spec h p.1 p.2
  have hg : ContinuousAt (fun q : Space m × Set.Ioo (0 : ℝ) 1 ↦ g q.1) p :=
    (h.graph_contDiff.continuous.comp continuous_fst).continuousAt
  have hv : ContinuousAt (fun q : Space m × Set.Ioo (0 : ℝ) 1 ↦ (q.2 : ℝ)) p :=
    (continuous_subtype_val.comp continuous_snd).continuousAt
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨t, ht, hth⟩ := exists_between (max_lt ha hs.1)
    have hgt : g p.1 < t := (le_max_right _ _).trans_lt ht
    have hat : a < t := (le_max_left _ _).trans_lt ht
    have hval : u (point p.1 t) < (p.2 : ℝ) := (hr.lt_levelHeight_iff h _ _ hgt).mp hth
    have hcont := (h.continuousAt_horizontal_section hgt).comp continuous_fst.continuousAt
    have he₁ : ∀ᶠ q in 𝓝 p, g q.1 < t := hg.eventually (eventually_lt_nhds hgt)
    have he₂ := hcont.eventually_lt hv hval
    filter_upwards [he₁, he₂] with q hq₁ hq₂
    exact hat.trans ((hr.lt_levelHeight_iff h q.1 q.2 hq₁).mpr hq₂)
  · intro b hb
    have hgb : g p.1 < b := hs.1.trans hb
    have hval : (p.2 : ℝ) < u (point p.1 b) := (hr.levelHeight_lt_iff h _ _ hgb).mp hb
    have hcont := (h.continuousAt_horizontal_section hgb).comp continuous_fst.continuousAt
    have he₁ : ∀ᶠ q in 𝓝 p, g q.1 < b := hg.eventually (eventually_lt_nhds hgb)
    have he₂ := hv.eventually_lt hcont hval
    filter_upwards [he₁, he₂] with q hq₁ hq₂
    exact (hr.levelHeight_lt_iff h q.1 q.2 hq₁).mpr hq₂

end SerrinEpigraph
