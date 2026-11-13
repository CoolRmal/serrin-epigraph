module

public import SerrinEpigraph.CappedCompetitor

/-!
# Dominated energy convergence for endpoint caps
-/

public section
noncomputable section

open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Capped competitors have a common compact gradient bound for all parameters in [0,1]. -/
theorem cappedCompetitor_gradient_bound {d : ℕ} {U v : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v)
    {K : Set (Space d)} (hK : IsCompact K) :
    ∃ C : NNReal, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖gradient (cappedCompetitor U v t) x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨A, hA⟩ := hU.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space d) R)
  obtain ⟨B, hB⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space d) R)
  refine ⟨max B A, fun t ht x hx ↦ ?_⟩
  have hc : LipschitzOnWith A (fun z ↦ 1 - t + t * U z) (closedBall 0 R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    rw [dist_add_left, dist_eq_norm, ← mul_sub, norm_mul, Real.norm_of_nonneg ht.1]
    have he := hA.dist_le_mul z hz w hw
    rw [dist_eq_norm] at he
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans he
  have hcap : LipschitzOnWith (max B A) (cappedCompetitor U v t) (closedBall 0 R) := by
    have hh := lipschitzWith_min.comp_lipschitzOnWith (hB.prodMk hc)
    convert hh using 1
    · simp only [one_mul]
    · rfl
  have hd := norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem (hR hx)) hcap
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hd

/-- Phase preservation allows pointwise energy convergence, even where the competitor vanishes. -/
theorem cappedCompetitor_phaseEnergy_tendsto {d : ℕ} {U v : Space d → ℝ} {f : ℝ → ℝ}
    (hU : Continuous U) (hv : Continuous v) (hUval : ∀ x, U x ∈ Ico (0 : ℝ) 1)
    (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hW : ContinuousOn (normalizedPotential f) (Icc (0 : ℝ) 1))
    {x : Space d} (hd : DifferentiableAt ℝ U x) :
    Tendsto (fun t : ℝ ↦ phaseEnergyDensity f 0 (cappedCompetitor U v t) x)
      (𝓝[>] 0) (𝓝 (phaseEnergyDensity f 0 v x)) := by
  have hval : Tendsto (fun t ↦ cappedCompetitor U v t x) (𝓝[>] 0) (𝓝 (v x)) :=
    (cappedCompetitor_tendsto (U := U) (fun z ↦ (hvval z).2) x).mono_left nhdsWithin_le_nhds
  have hwithin : Tendsto (fun t ↦ cappedCompetitor U v t x) (𝓝[>] 0)
      (𝓝[Icc (0 : ℝ) 1] (v x)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hval, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact Ico_subset_Icc_self (cappedCompetitor_mem_Ico hUval hvval ht x)
  have hp := (hW (v x) (hvval x)).tendsto.comp hwithin
  have hg := cappedCompetitor_gradient_tendsto hU hv
    (fun z ↦ (hUval z).2) (fun z ↦ (hvval z).2) hd
  by_cases hx : 0 < v x
  · have he := ((hg.norm.pow 2).div_const 2).add hp
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_true, add_zero]
    apply he.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hpos := (cappedCompetitor_pos_iff (fun z ↦ (hUval z).1) ht x).mpr hx
    simp only [hpos, ite_true, Function.comp_def]
  · have he : phaseEnergyDensity f 0 v x = 0 := by
      simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_false]
    rw [he]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hnot : ¬0 < cappedCompetitor U v t x :=
      fun hh ↦ hx ((cappedCompetitor_pos_iff (fun z ↦ (hUval z).1) ht x).mp hh)
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hnot, ite_false]

/-- The energies of endpoint caps converge on every compact set. -/
theorem Hypotheses.capped_phaseEnergy_integral_tendsto
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {U v : Space (m + 1) → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v)
    (hUval : ∀ x, U x ∈ Ico (0 : ℝ) 1) (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun t : ℝ ↦ ∫ x in K, phaseEnergyDensity f 0 (cappedCompetitor U v t) x)
      (𝓝[>] 0) (𝓝 (∫ x in K, phaseEnergyDensity f 0 v x)) := by
  obtain ⟨C, hC⟩ := cappedCompetitor_gradient_bound hU hv hK
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h.normalizedPotential_continuousOn
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (C : ℝ) ^ 2 / 2 + |M|)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (h.integrableOn_lipschitz_phaseEnergy (cappedCompetitor_locallyLipschitz hU hv t)
      (fun x ↦ Ico_subset_Icc_self (cappedCompetitor_mem_Ico hUval hvval ht x)) 0 hK).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hnorm := hC t ⟨ht.1.le, ht.2.le⟩ x hx
    have hpot := hM (cappedCompetitor U v t x)
      (Ico_subset_Icc_self (cappedCompetitor_mem_Ico hUval hvval ht x))
    by_cases hp : 0 < cappedCompetitor U v t x
    · simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_true,
        add_zero]
      calc
        _ ≤ ‖‖gradient (cappedCompetitor U v t) x‖ ^ 2 / 2‖ +
            ‖normalizedPotential f (cappedCompetitor U v t x)‖ := norm_add_le _ _
        _ ≤ (C : ℝ) ^ 2 / 2 + |M| := by
          rw [Real.norm_of_nonneg (by positivity)]
          have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
          linarith [le_abs_self M]
    · simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hp, ite_false,
        norm_zero]
      positivity
  · exact continuousOn_const.integrableOn_compact hK
  · filter_upwards [ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hU)] with x hx
    exact cappedCompetitor_phaseEnergy_tendsto hU.continuous hv.continuous hUval hvval
      h.normalizedPotential_continuousOn hx

end SerrinEpigraph
