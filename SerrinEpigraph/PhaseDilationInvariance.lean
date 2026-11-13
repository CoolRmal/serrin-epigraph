module

public import SerrinEpigraph.LipschitzDilationEstimate

/-!
# Dilation invariance of the phase selected by vanishing radial defects
-/

public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology Pointwise

namespace SerrinEpigraph

/-- Vanishing radial variation on integer balls implies vanishing local dilation differences. -/
theorem dilation_error_tendsto_of_radial_tendsto
    {d : ℕ} {F : ℕ → Space d → ℝ} (hF : ∀ j, LocallyLipschitz (F j))
    {B : ℝ} (hval : ∀ j x, F j x ∈ Icc (0 : ℝ) B)
    (hrad : ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
      ‖inner ℝ (gradient (F j) x) x‖) atTop (𝓝 0))
    {r a : ℝ} (hr : 0 ≤ r) (ha : 1 ≤ a) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r, ‖F j (a • x) - F j x‖) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (a * r)
  have ht := (hrad k).const_mul (a - 1)
  simp only [mul_zero] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
  intro j
  apply (integral_norm_dilation_sub_le_of_locallyLipschitz (hF j) (hval j) hr ha).trans
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ha)
  exact setIntegral_mono_set
    (integrableOn_radial_magnitude_of_locallyLipschitz (hF j) (isCompact_closedBall _ _))
    (Eventually.of_forall (fun x ↦ norm_nonneg _))
    (Eventually.of_forall (closedBall_subset_closedBall (show a * r ≤ (k + 1 : ℝ) by linarith)))

/-- A nonzero weighted phase limit of bounded locally Lipschitz functions with vanishing radial
variation is invariant almost everywhere under each positive dilation. -/
theorem phase_dilation_ae_of_radial_vanishing
    {d : ℕ} {F : ℕ → Space d → ℝ} (hF : ∀ j, LocallyLipschitz (F j))
    {B c : ℝ} (hval : ∀ j x, F j x ∈ Icc (0 : ℝ) B) (hc : c ≠ 0)
    {E : Set (Space d)} (hE : MeasurableSet E)
    (hlim : ∀ K : Set (Space d), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖F j x - E.indicator (fun _ ↦ c) x‖) atTop (𝓝 0))
    (hrad : ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
      ‖inner ℝ (gradient (F j) x) x‖) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) : ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E := by
  let V := E.indicator (fun _ : Space d ↦ c)
  have hout {a : ℝ} (ha : 1 ≤ a) : ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E := by
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    have hlocal (k : ℕ) : ∀ᵐ x ∂volume,
        x ∈ closedBall 0 (k + 1 : ℝ) → (x ∈ E ↔ a • x ∈ E) := by
      let r : ℝ := k + 1
      have hK : IsCompact (closedBall (0 : Space d) r) := isCompact_closedBall _ _
      have hiF (j : ℕ) : IntegrableOn (F j) (closedBall 0 r) :=
        (hF j).continuous.continuousOn.integrableOn_compact hK
      have hiFa (j : ℕ) : IntegrableOn (fun x ↦ F j (a • x)) (closedBall 0 r) :=
        ((hF j).continuous.comp (continuous_id.const_smul a)).continuousOn.integrableOn_compact hK
      have hiV : IntegrableOn V (closedBall 0 r) :=
        (continuousOn_const.integrableOn_compact hK).indicator hE
      have hiVa : IntegrableOn (fun x ↦ V (a • x)) (closedBall 0 r) := by
        change IntegrableOn (((fun x : Space d ↦ a • x) ⁻¹' E).indicator (fun _ ↦ c)) _
        exact (continuousOn_const.integrableOn_compact hK).indicator
          (hE.preimage (continuous_id.const_smul a).measurable)
      have hscaled : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
          ‖F j (a • x) - V (a • x)‖) atTop (𝓝 0) := by
        have ht := (hlim (closedBall 0 (a * r)) (isCompact_closedBall _ _)).const_mul ((a ^ d)⁻¹)
        simp only [mul_zero] at ht
        convert ht using 1
        funext j
        rw [Measure.setIntegral_comp_smul_of_pos volume (fun x ↦ ‖F j x - V x‖) _ ha0]
        simp only [smul_closedBall' ha0.ne', smul_zero, Real.norm_of_nonneg ha0.le,
          finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
        rfl
      have hdiff := dilation_error_tendsto_of_radial_tendsto hF hval hrad
        (show 0 ≤ r by dsimp [r]; positivity) ha
      have ht := hscaled.add (hdiff.add (hlim (closedBall 0 r) hK))
      simp only [zero_add] at ht
      have hzero : (∫ x in closedBall 0 r, ‖V (a • x) - V x‖) = 0 := by
        apply le_antisymm _ (integral_nonneg (fun x ↦ norm_nonneg _))
        apply ge_of_tendsto ht
        exact Eventually.of_forall (fun j ↦ by
          have h1 := integral_norm_sub_triangle hiVa (hiFa j) hiV
          have h2 := integral_norm_sub_triangle (hiFa j) (hiF j) hiV
          simp_rw [norm_sub_rev (V (a • _)) (F j (a • _))] at h1
          exact h1.trans (add_le_add le_rfl h2))
      have heq := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall (fun x ↦ norm_nonneg (V (a • x) - V x)))
        (hiVa.sub hiV).norm).mp hzero
      apply (ae_restrict_iff' hK.measurableSet).mp
      filter_upwards [heq] with x hx
      have hv : V (a • x) = V x := sub_eq_zero.mp (norm_eq_zero.mp hx)
      by_cases hxE : x ∈ E <;> by_cases haE : a • x ∈ E <;> simp_all [V]
    filter_upwards [ae_all_iff.mpr hlocal] with x hx
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    exact hx k (by simpa only [mem_closedBall, dist_zero_right] using
      (show ‖x‖ ≤ (k + 1 : ℝ) by linarith))
  by_cases ha1 : 1 ≤ a
  · exact hout ha1
  · have hi : 1 ≤ a⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ ha).mpr (by linarith)
    have hp := (Measure.quasiMeasurePreserving_smul volume ha.ne').ae (hout hi)
    filter_upwards [hp] with x hx
    simpa only [inv_smul_smul₀ ha.ne'] using hx.symm

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The actual PDE phase limit along the chosen defect scales is dilation invariant. -/
theorem RigidityHypotheses.phase_limit_dilation_invariant
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j)
    (hD : ∀ k : ℕ, Tendsto (fun j ↦
      radialEnergyDefect g u radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) : ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E := by
  have hv (j : ℕ) : LocallyLipschitz (fun x ↦ zeroExtension g u (R j • x)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hval (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  apply phase_dilation_ae_of_radial_vanishing
    (fun j ↦ hr.phasePrimitive_comp_locallyLipschitz h (hv j) (hval j))
    (fun j x ↦ h.phasePrimitive_mem_Icc (hval j x)) (hr.phasePrimitive_one_pos h).ne' hE
    (fun K hK ↦ hr.competitorPrimitive_integral_limit h hv hval hE hK (hlim K hK))
    (fun k ↦ hr.rescaledPrimitive_radial_tendsto_zero h hR hD k) ha

end SerrinEpigraph
