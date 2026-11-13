module

public import SerrinEpigraph.OneSidedPhaseLimit
public import SerrinEpigraph.PhasePerimeterAE

/-!
# Vertical translation monotonicity of the limiting phase
-/

public section

open Set MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Local integral convergence admits an almost-everywhere convergent subsequence
for the same measure and the same limiting function. -/
theorem exists_subsequence_tendsto_ae_of_integral_norm_sub
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {F : ℕ → X → ℝ} {v : X → ℝ}
    (hF : ∀ j, Integrable (F j) μ) (hv : Integrable v μ)
    (ht : Tendsto (fun j ↦ ∫ x, ‖F j x - v x‖ ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂μ, Tendsto (fun j ↦ F (φ j) x) atTop (𝓝 (v x)) := by
  have hLp : Tendsto (fun j ↦ eLpNorm (F j - v) 1 μ) atTop (𝓝 0) := by
    have he (j : ℕ) : eLpNorm (F j - v) 1 μ = ENNReal.ofReal (∫ x, ‖F j x - v x‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hF j).sub hv).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hF j).sub hv)]
      rfl
    simpa only [he, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp).exists_seq_tendsto_ae

/-- Nonnegative rescalings preserve the whole-space solution's vertical order. -/
theorem Hypotheses.rescaled_zeroExtension_vertical_le
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ R t : ℝ}
    (h : Hypotheses g u f κ) (hR : 0 ≤ R) (ht : 0 ≤ t) (x : Space (m + 1)) :
    zeroExtension g u (R • x) ≤
      zeroExtension g u (R • (x + t • verticalDirection m)) := by
  have hm := h.zeroExtension_vertical_mono (horizontal (R • x))
    (show (R • x) (Fin.last m) ≤ (R • x) (Fin.last m) + R * t by
      linarith [mul_nonneg hR ht])
  dsimp only at hm
  rw [point_horizontal_last, ← point_add_vertical, point_horizontal_last,
    ← smul_smul, ← smul_add] at hm
  exact hm

/-- Every local L1 phase limit inherits upward translation inclusion almost
everywhere, for each nonnegative translation distance. -/
theorem Hypotheses.phase_limit_vertical_translation
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {R : ℕ → ℝ} (hR : ∀ j, 0 ≤ R j)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E := by
  let z := t • verticalDirection m
  let F := fun j x ↦ zeroExtension g u (R j • x)
  let v := E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))
  have hlocal (k : ℕ) : ∀ᵐ x ∂volume,
      x ∈ closedBall 0 (k + 1 : ℝ) → x ∈ E → x + z ∈ E := by
    let K := closedBall (0 : Space (m + 1)) ((k + 1 : ℝ) + ‖z‖)
    have hK : IsCompact K := isCompact_closedBall _ _
    have hiF (j : ℕ) : IntegrableOn (F j) K :=
      (h.zeroExtension_continuous.comp (continuous_id.const_smul (R j)))
        |>.continuousOn.integrableOn_compact hK
    have hiv : IntegrableOn v K := (continuousOn_const.integrableOn_compact hK).indicator hE
    obtain ⟨φ, _, hpoint⟩ := exists_subsequence_tendsto_ae_of_integral_norm_sub
      (volume.restrict K) hiF hiv (hlim K hK)
    have hp : ∀ᵐ x ∂volume, x ∈ K → Tendsto (fun j ↦ F (φ j) x) atTop (𝓝 (v x)) :=
      (ae_restrict_iff' hK.measurableSet).mp hpoint
    have hpz := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae hp
    filter_upwards [hp, hpz] with x hx hxz
    intro hxball hxE
    have hn : ‖x‖ ≤ (k + 1 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hxball
    have hxK : x ∈ K := by
      change dist x 0 ≤ (k + 1 : ℝ) + ‖z‖
      rw [dist_zero_right]
      linarith [norm_nonneg z]
    have hxzK : x + z ∈ K := by
      change dist (x + z) 0 ≤ (k + 1 : ℝ) + ‖z‖
      rw [dist_zero_right]
      exact (norm_add_le x z).trans (add_le_add hn le_rfl)
    have horder : v x ≤ v (x + z) := le_of_tendsto_of_tendsto (hx hxK) (hxz hxzK)
      (Eventually.of_forall (fun j ↦ h.rescaled_zeroExtension_vertical_le (hR _) ht x))
    by_contra hnot
    simp only [v, indicator_of_mem hxE, indicator_of_notMem hnot] at horder
    norm_num at horder
  filter_upwards [ae_all_iff.mpr hlocal] with x hx
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  exact hx k (by simpa only [mem_closedBall, dist_zero_right] using
    (show ‖x‖ ≤ (k + 1 : ℝ) by linarith))

end SerrinEpigraph
