module

public import SerrinEpigraph.AnnularGluingSequence
public import SerrinEpigraph.GluingEnergyCancellation

/-!
# Inner-energy comparison with vanishing error
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

/-- A normalized competitor sequence agreeing with the rescaled solution in the annular
limit gives an inner-ball energy comparison with a vanishing error. -/
theorem RigidityHypotheses.exists_inner_energy_comparison_error
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : ℕ → Space (m + 1) → ℝ} {z : Space (m + 1) → ℝ}
    (hv : ∀ j, LocallyLipschitz (v j))
    (hvval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {r t B : ℝ} (hradius : 0 < r) (ht : 0 < t)
    (hz : IntegrableOn z (closedBall 0 (r + t) \ ball 0 r))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    (hEB : ∀ j,
      (∫ x in closedBall 0 (r + t) \ ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x) +
      (∫ x in closedBall 0 (r + t) \ ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B)
    (hUz : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t) \ ball 0 r,
      ‖zeroExtension g u (R j • x) - z x‖) atTop (𝓝 0))
    (hvz : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t) \ ball 0 r,
      ‖v j x - z x‖) atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ j,
      (∫ x in ball 0 r,
        rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x) ≤
      (∫ x in closedBall 0 (r + t), rescaledPhaseEnergyDensity f (R j) (v j) x) + ε j := by
  have hU : ∀ j, LocallyLipschitz (fun y ↦ zeroExtension g u (R j • y)) :=
    fun j ↦ h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hUval : ∀ j x, zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    fun j x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  obtain ⟨η, ε, he, hη⟩ := hr.exists_annular_gluing_sequence h hU hv hUval hvval
    hradius ht hz hR hRtop hEB hUz hvz
  refine ⟨ε, he, fun j ↦ ?_⟩
  obtain ⟨hd, _, hs, hone, hval, hcomp⟩ := hη j
  exact hr.inner_energy_le_of_glued_comparison h (lt_of_lt_of_le zero_lt_one (hR j)) ht.le
    (hv j) hd.locallyLipschitz (hvval j) hval (hs.trans ball_subset_closedBall) hone hcomp

/-- A convergent candidate-energy sequence bounds the reference inner energy eventually
up to every positive tolerance whenever the comparison error vanishes. -/
theorem inner_energy_eventually_le_of_comparison {E F ε : ℕ → ℝ} {L : ℝ}
    (hcomp : ∀ j, E j ≤ F j + ε j) (hF : Tendsto F atTop (𝓝 L))
    (hε : Tendsto ε atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, E j ≤ L + δ := by
  have ht := hF.add hε
  simp only [add_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (show L < L + δ by linarith))] with j hj
  exact (hcomp j).trans hj.le

end SerrinEpigraph
