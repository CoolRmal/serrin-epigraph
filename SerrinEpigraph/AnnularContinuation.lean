module

public import SerrinEpigraph.AnnularEndpoint
public import SerrinEpigraph.RadialContinuation

/-!
# Extending increasing radial segments before reaching one
-/

public section
noncomputable section

open Set
open scoped Topology

namespace SerrinEpigraph

/-- A positive endpoint slope and value below one allow a strictly longer increasing segment. -/
theorem IncreasingRadialSegment.exists_extension
    {m : ℕ} {f : ℝ → ℝ} {a b : ℝ} (v : IncreasingRadialSegment f m a b)
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (hval : v.value b < 1) (hslope : 0 < v.slope b) :
    ∃ d : ℝ, b < d ∧ ∃ w : IncreasingRadialSegment f m a d,
      EqOn w.value v.value (Icc a b) ∧ EqOn w.slope v.slope (Icc a b) := by
  obtain ⟨ε, hε, Q, P, hQ, hP, hd⟩ := v.exists_local_restart hf hval hslope
  let W := radialSplice b v.value Q
  let Z := radialSplice b v.slope P
  have hWb : W b = v.value b := by simp [W, radialSplice, hQ]
  have hZb : Z b = v.slope b := by simp [Z, radialSplice, hP]
  have hWeq : EqOn W v.value (Icc a b) := by
    intro r hr
    rcases lt_or_eq_of_le hr.2 with hlt | rfl
    · exact (radialSplice_eventuallyEq_left hlt).eq_of_nhds
    · exact hWb
  have hZeq : EqOn Z v.slope (Icc a b) := by
    intro r hr
    rcases lt_or_eq_of_le hr.2 with hlt | rfl
    · exact (radialSplice_eventuallyEq_left hlt).eq_of_nhds
    · exact hZb
  have hsys : IsRadialSystemOn m f W Z (Ioo a (b + ε)) := by
    intro r hr
    rcases lt_trichotomy r b with hlt | heq | hgt
    · have heW := radialSplice_eventuallyEq_left (F := v.value) (G := Q) hlt
      have heZ := radialSplice_eventuallyEq_left (F := v.slope) (G := P) hlt
      change HasDerivAt W (Z r) r ∧ HasDerivAt Z (-f (W r) - (m : ℝ) / r * Z r) r
      rw [show W r = v.value r from heW.eq_of_nhds,
        show Z r = v.slope r from heZ.eq_of_nhds]
      exact ⟨(v.value_derivative r ⟨hr.1, hlt⟩).congr_of_eventuallyEq heW,
        (v.slope_derivative r ⟨hr.1, hlt⟩).congr_of_eventuallyEq heZ⟩
    · subst r
      have hb : b ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, by linarith⟩
      have hq := (hd b hb).2.2.1
      have hp := (hd b hb).2.2.2
      rw [hP] at hq
      rw [hQ, hP] at hp
      have hvq : HasDerivWithinAt (Function.update v.value b (v.value b))
          (v.slope b) (Iic b) b := by simpa using v.value_hasDerivWithinAt_outer
      have hvp : HasDerivWithinAt (Function.update v.slope b (v.slope b))
          (-f (v.value b) - (m : ℝ) / b * v.slope b) (Iic b) b := by
        simpa using v.slope_hasDerivWithinAt_outer hf
      change HasDerivAt W (Z b) b ∧ HasDerivAt Z (-f (W b) - (m : ℝ) / b * Z b) b
      rw [hWb, hZb]
      exact ⟨radialSplice_hasDerivAt hvq hq hQ, radialSplice_hasDerivAt hvp hp hP⟩
    · have hr' : r ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, hr.2⟩
      have heW := radialSplice_eventuallyEq_right (F := v.value) (G := Q) hgt
      have heZ := radialSplice_eventuallyEq_right (F := v.slope) (G := P) hgt
      change HasDerivAt W (Z r) r ∧ HasDerivAt Z (-f (W r) - (m : ℝ) / r * Z r) r
      rw [show W r = Q r from heW.eq_of_nhds, show Z r = P r from heZ.eq_of_nhds]
      exact ⟨(hd r hr').2.2.1.congr_of_eventuallyEq heW,
        (hd r hr').2.2.2.congr_of_eventuallyEq heZ⟩
  let d := b + ε / 2
  have hbd : b < d := by dsimp [d]; linarith
  have hdε : d < b + ε := by dsimp [d]; linarith
  have hWc : ContinuousOn W (Icc a d) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | hlt
    · have hc := v.value_continuous a ⟨le_rfl, v.radii_lt.le⟩
      have hn : Icc a b ∈ 𝓝[Icc a d] a := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        exact ⟨Iio b, Iio_mem_nhds v.radii_lt, fun x hx ↦ ⟨hx.2.1, hx.1.le⟩⟩
      exact (hc.mono_of_mem_nhdsWithin hn).congr_of_eventuallyEq
        ((radialSplice_eventuallyEq_left v.radii_lt).filter_mono nhdsWithin_le_nhds)
        (hWeq ⟨le_rfl, v.radii_lt.le⟩)
    · exact (hsys r ⟨hlt, hr.2.trans_lt hdε⟩).1.continuousAt.continuousWithinAt
  have hZc : ContinuousOn Z (Icc a d) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | hlt
    · have hc := v.slope_continuous a ⟨le_rfl, v.radii_lt.le⟩
      have hn : Icc a b ∈ 𝓝[Icc a d] a := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        exact ⟨Iio b, Iio_mem_nhds v.radii_lt, fun x hx ↦ ⟨hx.2.1, hx.1.le⟩⟩
      exact (hc.mono_of_mem_nhdsWithin hn).congr_of_eventuallyEq
        ((radialSplice_eventuallyEq_left v.radii_lt).filter_mono nhdsWithin_le_nhds)
        (hZeq ⟨le_rfl, v.radii_lt.le⟩)
    · exact (hsys r ⟨hlt, hr.2.trans_lt hdε⟩).2.continuousAt.continuousWithinAt
  have hbounds : ∀ r ∈ Icc a d, W r ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ Z r := by
    intro r hr
    by_cases hle : r ≤ b
    · rw [hWeq ⟨hr.1, hle⟩, hZeq ⟨hr.1, hle⟩]
      exact ⟨v.value_range r ⟨hr.1, hle⟩, v.slope_nonneg r ⟨hr.1, hle⟩⟩
    · have hgt := lt_of_not_ge hle
      have hr' : r ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, hr.2.trans_lt hdε⟩
      simp only [W, Z, radialSplice, ite_eq_right (not_lt.mpr hgt.le)]
      exact ⟨⟨(hd r hr').1.1.le, (hd r hr').1.2.le⟩, (hd r hr').2.1.le⟩
  refine ⟨d, hbd, {
    value := W
    slope := Z
    inner_pos := v.inner_pos
    radii_lt := v.radii_lt.trans hbd
    value_continuous := hWc
    slope_continuous := hZc
    value_range := fun r hr ↦ (hbounds r hr).1
    value_pos := ?_
    slope_nonneg := fun r hr ↦ (hbounds r hr).2
    value_derivative := fun r hr ↦ (hsys r ⟨hr.1, hr.2.trans hdε⟩).1
    slope_derivative := fun r hr ↦ (hsys r ⟨hr.1, hr.2.trans hdε⟩).2
    inner_zero := (hWeq ⟨le_rfl, v.radii_lt.le⟩).trans v.inner_zero }, hWeq, hZeq⟩
  intro r hr
  rcases lt_trichotomy r b with hlt | rfl | hgt
  · rw [hWeq ⟨hr.1.le, hlt.le⟩]
    exact v.value_pos r ⟨hr.1, hlt⟩
  · rw [hWb]
    exact v.outer_value_pos
  · have hr' : r ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, hr.2.trans hdε⟩
    simpa only [W, radialSplice, ite_eq_right (not_lt.mpr hgt.le)] using (hd r hr').1.1

/-- The preserved energy margin supplies the endpoint slope needed for extension. -/
theorem IncreasingRadialSegment.exists_extension_of_energy_margin
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (v : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (hval : v.value b < 1)
    (hmargin : 0 < v.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * v.slope a)) :
    ∃ d : ℝ, b < d ∧ ∃ w : IncreasingRadialSegment f m a d,
      EqOn w.value v.value (Icc a b) ∧ EqOn w.slope v.slope (Icc a b) := by
  have hsq := v.slope_sq_lower_bound hr h ⟨v.radii_lt.le, le_rfl⟩
  have hslope : 0 < v.slope b := by
    have hn := v.slope_nonneg b ⟨v.radii_lt.le, le_rfl⟩
    nlinarith
  exact v.exists_extension h.reaction_contDiffOn hval hslope

end SerrinEpigraph
