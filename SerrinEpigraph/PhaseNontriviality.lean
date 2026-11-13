module

public import SerrinEpigraph.EnergyNondegeneracy

/-!
# The limiting phase is neither empty nor full modulo null sets
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Both constant phases have zero rescaled energy. -/
theorem rescaledPhaseEnergyDensity_constant_phase {d : ℕ} (f : ℝ → ℝ) (R : ℝ)
    {c : ℝ} (hc : c = 0 ∨ c = 1) (x : Space d) :
    rescaledPhaseEnergyDensity f R (fun _ ↦ c) x = 0 := by
  rcases hc with rfl | rfl <;> simp [rescaledPhaseEnergyDensity, gradient]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- A dilated solution cannot converge locally to either constant phase: comparison with that
constant would force its energy to zero, contradicting the monotonicity lower bound. -/
theorem RigidityHypotheses.not_constant_phase_limit (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j)
    (hRt : Tendsto R atTop atTop) {c : ℝ} (hc : c = 0 ∨ c = 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) - c‖) atTop (𝓝 0)) : False := by
  let A := closedBall (0 : Space (m + 1)) (2 + 1) \ ball 0 2
  have hA : IsCompact A := (isCompact_closedBall _ _).diff isOpen_ball
  have hU (j : ℕ) : LocallyLipschitz (fun x ↦ zeroExtension g u (R j • x)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hval (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hR0 (j : ℕ) : 0 < R j := zero_lt_one.trans_le (hR j)
  have hcval : c ∈ Icc (0 : ℝ) 1 := by rcases hc with rfl | rfl <;> norm_num
  have he (j : ℕ) (x : Space (m + 1)) :
      rescaledPhaseEnergyDensity f (R j) (fun _ ↦ c) x = 0 :=
    rescaledPhaseEnergyDensity_constant_phase f (R j) hc x
  obtain ⟨C, _, hbound⟩ := hr.rescaledPhaseEnergy_bound h
  have hEB (j : ℕ) :
      (∫ x in A, rescaledPhaseEnergyDensity f (R j)
        (fun y ↦ zeroExtension g u (R j • y)) x) +
      (∫ x in A, rescaledPhaseEnergyDensity f (R j) (fun _ ↦ c) x) ≤ C * (2 + 1) ^ m := by
    simp only [he, integral_zero, add_zero]
    apply (setIntegral_mono_set
      (h.integrableOn_rescaledPhaseEnergy (hU j) (hval j) (R j) (isCompact_closedBall 0 (2 + 1)))
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hR0 j).le (hval j)))
      (Eventually.of_forall sdiff_subset)).trans
    exact hbound (R j) (2 + 1) (hR0 j) (by linarith [hR j])
  obtain ⟨ε, hε, hcomp⟩ := hr.exists_inner_energy_comparison_error h
    (v := fun _ _ ↦ c) (z := fun _ ↦ c) (r := 2) (t := 1)
    (fun _ ↦ (contDiff_const (c := c) : ContDiff ℝ 1 _).locallyLipschitz)
    (fun _ _ ↦ hcval) (by norm_num) (by norm_num)
    (continuousOn_const.integrableOn_compact hA) hR hRt hEB (hlim A hA)
    (by simp)
  have hupper (j : ℕ) :
      (∫ x in closedBall 0 1, rescaledPhaseEnergyDensity f (R j)
        (fun y ↦ zeroExtension g u (R j • y)) x) ≤ ε j := by
    have hi := (h.integrableOn_rescaledPhaseEnergy (hU j) (hval j) (R j)
      (isCompact_closedBall 0 2)).mono_set ball_subset_closedBall
    have hle := setIntegral_mono_set hi
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hR0 j).le (hval j)))
      (Eventually.of_forall (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)))
    have hh := hcomp j
    simp only [he, integral_zero, zero_add] at hh
    exact hle.trans hh
  obtain ⟨b, hb, hlower⟩ := hr.rescaledEnergy_eventually_pos h
  obtain ⟨j, hj, hjε⟩ := ((hRt.eventually hlower).and
    (hε.eventually (gt_mem_nhds hb))).exists
  exact (hj.trans (hupper j)).not_gt hjε

/-- Every local phase limit of diverging dilations has both phases of positive measure. -/
theorem RigidityHypotheses.phase_limit_nontrivial (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j)
    (hRt : Tendsto R atTop atTop) {E : Set (Space (m + 1))}
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    volume E ≠ 0 ∧ volume Eᶜ ≠ 0 := by
  have hnot {c : ℝ} (hc : c = 0 ∨ c = 1)
      (he : ∀ᵐ x ∂volume, E.indicator (fun _ ↦ (1 : ℝ)) x = c) : False := by
    apply hr.not_constant_phase_limit h hR hRt hc
    intro K hK
    convert hlim K hK using 1
    funext j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae he] with x hx
    rw [hx]
  constructor
  · intro hz
    apply hnot (c := 0) (Or.inl rfl)
    have he : ∀ᵐ x ∂volume, x ∉ E := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hz
    filter_upwards [he] with x hx
    exact indicator_of_notMem hx _
  · intro hz
    apply hnot (c := 1) (Or.inr rfl)
    have he : ∀ᵐ x ∂volume, x ∈ E := mem_ae_iff.mpr hz
    filter_upwards [he] with x hx
    exact indicator_of_mem hx _

end SerrinEpigraph
