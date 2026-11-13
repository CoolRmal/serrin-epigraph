module

public import SerrinEpigraph.AnnularLocal
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Endpoint data of increasing radial segments
-/

public section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {f : ℝ → ℝ} {a b : ℝ}

/-- The value equation extends to the outer endpoint as a left derivative. -/
theorem IncreasingRadialSegment.value_hasDerivWithinAt_outer
    (v : IncreasingRadialSegment f m a b) :
    HasDerivWithinAt v.value (v.slope b) (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
    (fun r hr ↦ (v.value_derivative r hr).differentiableAt.differentiableWithinAt)
  · exact (v.value_continuous b ⟨v.radii_lt.le, le_rfl⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsLT v.radii_lt
  · have hp := v.slope_continuous b ⟨v.radii_lt.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE v.radii_lt] at hp
    apply (hp.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)).congr'
    filter_upwards [Ioo_mem_nhdsLT v.radii_lt] with r hr
    exact (v.value_derivative r hr).deriv.symm

/-- Increasing profiles are nondecreasing on their closed interval. -/
theorem IncreasingRadialSegment.value_monotoneOn (v : IncreasingRadialSegment f m a b) :
    MonotoneOn v.value (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) v.value_continuous
    (f' := v.slope)
  · intro r hr
    have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
    exact (v.value_derivative r hr').hasDerivWithinAt
  · intro r hr
    have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
    exact v.slope_nonneg r ⟨hr'.1.le, hr'.2.le⟩

/-- The outer endpoint value is strictly positive, even without a strict slope assumption. -/
theorem IncreasingRadialSegment.outer_value_pos (v : IncreasingRadialSegment f m a b) :
    0 < v.value b := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith [v.radii_lt], by linarith [v.radii_lt]⟩
  exact (v.value_pos _ hmid).trans_le
    (v.value_monotoneOn ⟨hmid.1.le, hmid.2.le⟩ ⟨v.radii_lt.le, le_rfl⟩ hmid.2.le)

/-- The slope equation also extends to the outer endpoint as a left derivative. -/
theorem IncreasingRadialSegment.slope_hasDerivWithinAt_outer
    (v : IncreasingRadialSegment f m a b) (hf : ContDiffOn ℝ 1 f (Ici 0)) :
    HasDerivWithinAt v.slope (-f (v.value b) - (m : ℝ) / b * v.slope b) (Iic b) b := by
  have hQ : Tendsto v.value (𝓝[<] b) (𝓝 (v.value b)) := by
    have hc := v.value_continuous b ⟨v.radii_lt.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE v.radii_lt] at hc
    exact hc.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hP : Tendsto v.slope (𝓝[<] b) (𝓝 (v.slope b)) := by
    have hc := v.slope_continuous b ⟨v.radii_lt.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE v.radii_lt] at hc
    exact hc.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hfc : ContinuousAt f (v.value b) :=
    (hf.continuousOn _ v.outer_value_pos.le).continuousAt (Ici_mem_nhds v.outer_value_pos)
  have hlim := (hfc.tendsto.comp hQ).neg.sub
    (((tendsto_const_nhds (x := (m : ℝ))).div (continuousAt_id.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] b ≤ 𝓝 b)) (v.inner_pos.trans v.radii_lt).ne').mul hP)
  apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
    (fun r hr ↦ (v.slope_derivative r hr).differentiableAt.differentiableWithinAt)
  · exact (v.slope_continuous b ⟨v.radii_lt.le, le_rfl⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsLT v.radii_lt
  · apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsLT v.radii_lt] with r hr
    exact (v.slope_derivative r hr).deriv.symm

/-- Before reaching one, a segment with positive endpoint slope has a local radial restart
that retains the required value range and positive slope. -/
theorem IncreasingRadialSegment.exists_local_restart
    (v : IncreasingRadialSegment f m a b) (hf : ContDiffOn ℝ 1 f (Ici 0))
    (hval : v.value b < 1) (hslope : 0 < v.slope b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Q P : ℝ → ℝ, Q b = v.value b ∧ P b = v.slope b ∧
      ∀ r ∈ Ioo (b - ε) (b + ε), Q r ∈ Ioo (0 : ℝ) 1 ∧ 0 < P r ∧
        HasDerivAt Q (P r) r ∧ HasDerivAt P (-f (Q r) - (m : ℝ) / r * P r) r := by
  have hfb : ContDiffAt ℝ 1 f (v.value b) :=
    (hf _ v.outer_value_pos.le).contDiffAt (Ici_mem_nhds v.outer_value_pos)
  obtain ⟨ε, hε, Q, P, hQ, hP, hd⟩ := exists_radial_system_at_positive_radius m
    (p := v.slope b) (v.inner_pos.trans v.radii_lt) hfb
  have hb : b ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, by linarith⟩
  have hQc := (hd b hb).1.continuousAt
  have hPc := (hd b hb).2.continuousAt
  have hn : {r : ℝ | Q r ∈ Ioo (0 : ℝ) 1 ∧ 0 < P r} ∈ 𝓝 b := by
    have hnQ := hQc.preimage_mem_nhds
      (Ioo_mem_nhds (by simpa only [hQ] using v.outer_value_pos)
        (by simpa only [hQ] using hval))
    have hnP := hPc.preimage_mem_nhds (Ioi_mem_nhds (by simpa only [hP] using hslope))
    filter_upwards [hnQ, hnP] with r hrQ hrP
    exact ⟨hrQ, hrP⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hn
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ δ := min_le_right _ _
  refine ⟨η, hη, Q, P, hQ, hP, ?_⟩
  intro r hr
  have hrε : r ∈ Ioo (b - ε) (b + ε) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hrδ : r ∈ Metric.ball b δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  exact ⟨(hδsub hrδ).1, (hδsub hrδ).2, hd r hrε⟩

end SerrinEpigraph
