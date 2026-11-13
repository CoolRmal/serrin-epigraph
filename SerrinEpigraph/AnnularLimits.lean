module

public import SerrinEpigraph.AnnularUnion

/-!
# Finite endpoint limits of the supremal annular union
-/

public section
noncomputable section

open Set Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- The union of all extensions has finite normalized value and nonnegative slope limits. -/
theorem IncreasingRadialSegment.annularUnion_endpoint_limits
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (seed : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hb : BddAbove (range (fun v : AnnularExtension seed ↦ v.radius))) :
    let R := fun v : AnnularExtension seed ↦ v.radius
    let Q := annularUnion a R (fun v ↦ v.segment.value)
    let P := annularUnion a R (fun v ↦ v.segment.slope)
    ∃ q p : ℝ, q ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ p ∧
      Tendsto Q (𝓝[<] (sSup (range R))) (𝓝 q) ∧
      Tendsto P (𝓝[<] (sSup (range R))) (𝓝 p) := by
  let R := fun v : AnnularExtension seed ↦ v.radius
  let Q := annularUnion a R (fun v ↦ v.segment.value)
  let P := annularUnion a R (fun v ↦ v.segment.slope)
  let S := sSup (range R)
  have hbS : b ≤ S := le_csSup hb (mem_range_self seed.selfExtension)
  have haS : a < S := seed.radii_lt.trans_le hbS
  have hQ := fun v w : AnnularExtension seed ↦ (v.compatible h w).1
  have hP := fun v w : AnnularExtension seed ↦ (v.compatible h w).2
  have hdom := annularUnion_domain_eq_Ioo (a := a) hb
  have hsys : IsRadialSystemOn m f Q P (Ioo a S) := by
    rw [← hdom]
    exact annularUnion_isRadialSystemOn hQ hP
      (fun v t ht ↦ ⟨v.segment.value_derivative t ht, v.segment.slope_derivative t ht⟩)
  have hbounds : ∀ t ∈ Ioo a S, Q t ∈ Icc (0 : ℝ) 1 ∧ P t ∈ Icc 0 (seed.slope a) := by
    intro t ht
    rw [← hdom] at ht
    obtain ⟨v, hv⟩ := mem_iUnion.mp ht
    have htc : t ∈ Icc a v.radius := ⟨hv.1.le, hv.2.le⟩
    have hqeq : Q t = v.segment.value t := annularUnion_eqOn hQ v ⟨hv.1.le, hv.2⟩
    have hpeq : P t = v.segment.slope t := annularUnion_eqOn hP v ⟨hv.1.le, hv.2⟩
    rw [hqeq, hpeq]
    refine ⟨v.segment.value_range t htc, v.segment.slope_nonneg t htc, ?_⟩
    have he := v.segment.slope_antitoneOn hr
      ⟨le_rfl, v.segment.radii_lt.le⟩ htc hv.1.le
    rwa [v.slope_eq ⟨le_rfl, seed.radii_lt.le⟩] at he
  let B : ℝ≥0 := ⟨seed.slope a, seed.slope_nonneg a ⟨le_rfl, seed.radii_lt.le⟩⟩
  have hnorm : ∀ t ∈ Ioo a S, ‖P t‖ ≤ B := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hbounds t ht).2.1]
    exact (hbounds t ht).2.2
  obtain ⟨q, p, hq, hp⟩ := h.radial_exists_endpoint_limits hsys seed.inner_pos hnorm
    (fun t ht ↦ (hbounds t ht).1)
  rw [nhdsWithin_Ioo_eq_nhdsLT haS] at hq hp
  have hqval : q ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hq (by
    filter_upwards [Ioo_mem_nhdsLT haS] with t ht
    exact (hbounds t ht).1)
  have hpval : 0 ≤ p := ge_of_tendsto hp (by
    filter_upwards [Ioo_mem_nhdsLT haS] with t ht
    exact (hbounds t ht).2.1)
  exact ⟨q, p, hqval, hpval, hq, hp⟩

/-- Filling a finite left limit preserves continuity on the completed closed interval. -/
theorem continuousOn_update_outer_of_tendsto {F : ℝ → ℝ} {a R q : ℝ}
    (hF : ContinuousOn F (Ico a R)) (hq : Tendsto F (𝓝[<] R) (𝓝 q)) :
    ContinuousOn (Function.update F R q) (Icc a R) := by
  have hc : ContinuousOn (Function.update F R q) (Ico a R) := by
    apply hF.congr
    intro t ht
    exact Function.update_of_ne ht.2.ne q F
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · apply (hc t ⟨ht.1, hlt⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with s hs hsR
    exact ⟨hs.1, hsR⟩
  · rw [continuousWithinAt_update_same]
    apply hq.mono_left (nhdsWithin_mono _ ?_)
    intro s hs
    exact lt_of_le_of_ne hs.1.2 (by simpa only [mem_singleton_iff] using hs.2)

/-- A bounded increasing radial system completed by its endpoint limits is a closed segment. -/
theorem increasingRadialSegment_of_endpoint_limits
    {m : ℕ} {f Q P : ℝ → ℝ} {a R q p : ℝ} (ha : 0 < a) (haR : a < R)
    (hQc : ContinuousOn Q (Ico a R)) (hPc : ContinuousOn P (Ico a R))
    (hsys : IsRadialSystemOn m f Q P (Ioo a R))
    (hbounds : ∀ t ∈ Ico a R, Q t ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ P t)
    (hpos : ∀ t ∈ Ioo a R, 0 < Q t) (hzero : Q a = 0)
    (hq : Tendsto Q (𝓝[<] R) (𝓝 q)) (hp : Tendsto P (𝓝[<] R) (𝓝 p))
    (hqrange : q ∈ Icc (0 : ℝ) 1) (hp0 : 0 ≤ p) :
    ∃ v : IncreasingRadialSegment f m a R,
      EqOn v.value Q (Ico a R) ∧ EqOn v.slope P (Ico a R) := by
  let W := Function.update Q R q
  let Z := Function.update P R p
  have hW : EqOn W Q (Ico a R) := fun t ht ↦ Function.update_of_ne ht.2.ne q Q
  have hZ : EqOn Z P (Ico a R) := fun t ht ↦ Function.update_of_ne ht.2.ne p P
  refine ⟨{
    value := W
    slope := Z
    inner_pos := ha
    radii_lt := haR
    value_continuous := continuousOn_update_outer_of_tendsto hQc hq
    slope_continuous := continuousOn_update_outer_of_tendsto hPc hp
    value_range := ?_
    value_pos := fun t ht ↦ by rw [hW ⟨ht.1.le, ht.2⟩]; exact hpos t ht
    slope_nonneg := ?_
    value_derivative := ?_
    slope_derivative := ?_
    inner_zero := (hW ⟨le_rfl, haR⟩).trans hzero }, hW, hZ⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · rw [hW ⟨ht.1, hlt⟩]
      exact (hbounds t ⟨ht.1, hlt⟩).1
    · simpa [W] using hqrange
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · rw [hZ ⟨ht.1, hlt⟩]
      exact (hbounds t ⟨ht.1, hlt⟩).2
    · simpa [Z] using hp0
  · intro t ht
    rw [hZ ⟨ht.1.le, ht.2⟩]
    exact hasDerivAt_update_endpoint ht.2.ne (hsys t ht).1
  · intro t ht
    rw [hW ⟨ht.1.le, ht.2⟩, hZ ⟨ht.1.le, ht.2⟩]
    exact hasDerivAt_update_endpoint ht.2.ne (hsys t ht).2

end SerrinEpigraph
