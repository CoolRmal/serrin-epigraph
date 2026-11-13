module

public import SerrinEpigraph.CappedEnergy

/-!
# Free-boundary minimality for closed-range Lipschitz competitors
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- The zero extension minimizes unshifted phase energy against every locally Lipschitz
competitor valued in [0,1] with compactly supported difference. -/
theorem RigidityHypotheses.phaseEnergy_minimal_lipschitz_closedRange
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (hsupp : tsupport (fun x ↦ v x - zeroExtension g u x) ⊆ K)
    (hval : ∀ x, v x ∈ Icc (0 : ℝ) 1) :
    (∫ x in K, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
      ∫ x in K, phaseEnergyDensity f 0 v x := by
  have hUval : ∀ x, zeroExtension g u x ∈ Ico (0 : ℝ) 1 :=
    fun x ↦ ⟨h.zeroExtension_nonneg x, hr.zeroExtension_lt_one x⟩
  have ht := h.capped_phaseEnergy_integral_tendsto h.zeroExtension_locallyLipschitz hv
    hUval hval hK
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  apply hr.phaseEnergy_minimal_lipschitz_competitor h
    (cappedCompetitor_locallyLipschitz h.zeroExtension_locallyLipschitz hv t) hK
    ((cappedCompetitor_tsupport_sub_subset (fun x ↦ (hUval x).2.le)
      ⟨ht.1.le, ht.2.le⟩).trans hsupp)
    (cappedCompetitor_mem_Ico hUval hval ht)

end SerrinEpigraph
