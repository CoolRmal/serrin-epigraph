module

public import SerrinEpigraph.RecoveryProfileCore
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Regularity of the inverse transition profile
-/

public section

open Set
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ δ : ℝ}

/-- Compactness of the normalized interval gives continuity of the inverse profile,
including both transition endpoints. -/
theorem RigidityHypotheses.recoveryProfileCore_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ) :
    ContinuousOn (recoveryProfileCore f δ) (Icc 0 (recoveryTravelTime f δ 1)) := by
  let T : Icc (0 : ℝ) 1 → ℝ := fun s ↦ recoveryTravelTime f δ s
  have hc : Continuous T := (hr.recoveryTravelTime_continuousOn h hδ).domRestrict
  have hi : Function.Injective T := (hr.recoveryTravelTime_strictMonoOn h hδ).injOn.injective
  have he := hc.isClosedEmbedding hi
  let Q : Icc (0 : ℝ) (recoveryTravelTime f δ 1) → Icc (0 : ℝ) 1 :=
    fun t ↦ ⟨recoveryProfileCore f δ t, (hr.recoveryProfileCore_spec h hδ t.property).1⟩
  have hq : Continuous Q := by
    apply he.isEmbedding.continuous_iff.mpr
    have hid : T ∘ Q = fun t : Icc (0 : ℝ) (recoveryTravelTime f δ 1) ↦ (t : ℝ) := by
      funext t
      exact (hr.recoveryProfileCore_spec h hδ t.property).2
    rw [hid]
    exact continuous_subtype_val
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_subtype_val.comp hq

/-- Interior times correspond to strictly intermediate phase values. -/
theorem RigidityHypotheses.recoveryProfileCore_mem_Ioo
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Ioo 0 (recoveryTravelTime f δ 1)) :
    recoveryProfileCore f δ t ∈ Ioo (0 : ℝ) 1 := by
  have hT := hr.recoveryTravelTime_one_pos h hδ
  have hmono := hr.recoveryProfileCore_strictMonoOn h hδ
  have hleft := hmono (left_mem_Icc.mpr hT.le) ⟨ht.1.le, ht.2.le⟩ ht.1
  have hright := hmono ⟨ht.1.le, ht.2.le⟩ (right_mem_Icc.mpr hT.le) ht.2
  rw [hr.recoveryProfileCore_zero h hδ] at hleft
  rw [hr.recoveryProfileCore_end h hδ] at hright
  exact ⟨hleft, hright⟩

/-- The inverse profile solves the regularized first-order transition equation. -/
theorem RigidityHypotheses.recoveryProfileCore_hasDerivAt
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Ioo 0 (recoveryTravelTime f δ 1)) :
    HasDerivAt (recoveryProfileCore f δ)
      (Real.sqrt (2 * (normalizedPotential f (recoveryProfileCore f δ t) + δ))) t := by
  have hq := hr.recoveryProfileCore_mem_Ioo h hδ ht
  have hco := (hr.recoveryProfileCore_continuousOn h hδ).mono Ioo_subset_Icc_self
  have hc := hco.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hd := hr.recoveryTravelTime_hasDerivAt h hδ hq
  have hw := hr.normalizedPotential_nonneg h ⟨hq.1.le, hq.2.le⟩
  have hn : (Real.sqrt (2 * (normalizedPotential f (recoveryProfileCore f δ t) + δ)))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne'
  have he : ∀ᶠ s in 𝓝 t, recoveryTravelTime f δ (recoveryProfileCore f δ s) = s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hr.recoveryProfileCore_spec h hδ ⟨hs.1.le, hs.2.le⟩).2
  simpa only [inv_inv] using HasDerivAt.of_local_left_inverse hc hd hn he

/-- The profile's kinetic-plus-potential density has the regularized equipartition formula. -/
theorem RigidityHypotheses.recoveryProfileCore_energy_identity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Ioo 0 (recoveryTravelTime f δ 1)) :
    (deriv (recoveryProfileCore f δ) t) ^ 2 / 2 +
      normalizedPotential f (recoveryProfileCore f δ t) =
      2 * normalizedPotential f (recoveryProfileCore f δ t) + δ := by
  have hq := hr.recoveryProfileCore_mem_Ioo h hδ ht
  have hw := hr.normalizedPotential_nonneg h ⟨hq.1.le, hq.2.le⟩
  rw [(hr.recoveryProfileCore_hasDerivAt h hδ ht).deriv,
    Real.sq_sqrt (show 0 ≤ 2 * (normalizedPotential f (recoveryProfileCore f δ t) + δ)
      by positivity)]
  ring

end SerrinEpigraph
