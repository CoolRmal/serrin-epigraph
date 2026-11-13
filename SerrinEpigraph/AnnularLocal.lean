module

public import SerrinEpigraph.ReactionSmoothExtension
public import SerrinEpigraph.AnnularEnergy

/-!
# Starting an increasing radial segment from the inner sphere
-/

public section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- Positive initial slope yields a nontrivial increasing radial segment starting at zero. -/
theorem exists_increasingRadialSegment {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (m : ℕ) {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    ∃ b : ℝ, ∃ v : IncreasingRadialSegment f m a b,
      v.slope a = p ∧ (∀ r ∈ Icc a b, 0 < v.slope r ∧ v.value r < 1) := by
  obtain ⟨ε, hε, Q, P, hQ, hP, hd, hdeq⟩ := exists_radial_system_from_zero hf m ha (p := p)
  have haI : a ∈ Ioo (a - ε) (a + ε) := ⟨by linarith, by linarith⟩
  have hQc := (hd a haI).1.continuousAt
  have hPc := (hd a haI).2.continuousAt
  have hn : {r : ℝ | r ∈ Ioo (a - ε) (a + ε) ∧ 0 < P r ∧ Q r < 1} ∈ 𝓝 a := by
    have hnP := hPc.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hP] using hp))
    have hnQ := hQc.preimage_mem_nhds (Iio_mem_nhds (by rw [hQ]; norm_num : Q a < 1))
    filter_upwards [isOpen_Ioo.mem_nhds haI, hnP, hnQ] with r hr hpr hqr
    exact ⟨hr, hpr, hqr⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hn
  let b := a + δ / 2
  have hab : a < b := by dsimp [b]; linarith
  have hgood : ∀ r ∈ Icc a b, r ∈ Ioo (a - ε) (a + ε) ∧ 0 < P r ∧ Q r < 1 := by
    intro r hr
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [b] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hcontQ : ContinuousOn Q (Icc a b) :=
    fun r hr ↦ (hd r (hgood r hr).1).1.continuousAt.continuousWithinAt
  have hcontP : ContinuousOn P (Icc a b) :=
    fun r hr ↦ (hd r (hgood r hr).1).2.continuousAt.continuousWithinAt
  have hmono : StrictMonoOn Q (Icc a b) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hcontQ
      (f' := P)
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      exact (hd r (hgood r ⟨hr'.1.le, hr'.2.le⟩).1).1.hasDerivWithinAt
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      exact (hgood r ⟨hr'.1.le, hr'.2.le⟩).2.1
  have hQnonneg : ∀ r ∈ Icc a b, 0 ≤ Q r := by
    intro r hr
    have hh := hmono.monotoneOn ⟨le_rfl, hab.le⟩ hr hr.1
    simpa only [hQ] using hh
  let v : IncreasingRadialSegment f m a b := {
    value := Q
    slope := P
    inner_pos := ha
    radii_lt := hab
    value_continuous := hcontQ
    slope_continuous := hcontP
    value_range := fun r hr ↦ ⟨hQnonneg r hr, (hgood r hr).2.2.le⟩
    value_pos := fun r hr ↦ by
      have hh := hmono ⟨le_rfl, hab.le⟩ ⟨hr.1.le, hr.2.le⟩ hr.1
      simpa only [hQ] using hh
    slope_nonneg := fun r hr ↦ (hgood r hr).2.1.le
    value_derivative := fun r hr ↦ (hd r (hgood r ⟨hr.1.le, hr.2.le⟩).1).1
    slope_derivative := fun r hr ↦ hdeq r (hgood r ⟨hr.1.le, hr.2.le⟩).1
      (hQnonneg r ⟨hr.1.le, hr.2.le⟩)
    inner_zero := hQ }
  exact ⟨b, v, hP, fun r hr ↦ (hgood r hr).2⟩

/-- Initial energy strictly above the potential drop allows a positive curvature margin
at every sufficiently large inner radius. -/
theorem exists_annular_energy_margin (m : ℕ) {W p : ℝ} (hp : 0 < p)
    (henergy : 2 * W < p ^ 2) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ a : ℝ, A ≤ a →
      δ ^ 2 ≤ p ^ 2 - 2 * W - 2 * ((m : ℝ) / a * p) := by
  let D := p ^ 2 - 2 * W
  have hD : 0 < D := by dsimp [D]; linarith
  let A := (4 * (m : ℝ) * p + 1) / D
  have hA : 0 < A := div_pos (by positivity) hD
  refine ⟨A, Real.sqrt (D / 2), hA, Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro a ha
  have ha0 : 0 < a := hA.trans_le ha
  have hAD : A * D = 4 * (m : ℝ) * p + 1 := by
    dsimp [A]
    exact div_mul_cancel₀ _ hD.ne'
  have hlarge := mul_le_mul_of_nonneg_right ha hD.le
  have hcurv : 2 * ((m : ℝ) / a * p) ≤ D / 2 := by
    have he : 2 * ((m : ℝ) / a * p) = (2 * (m : ℝ) * p) / a := by ring
    rw [he, div_le_iff₀ ha0]
    nlinarith
  rw [Real.sq_sqrt (by positivity : 0 ≤ D / 2)]
  dsimp [D] at hcurv ⊢
  linarith

end SerrinEpigraph
