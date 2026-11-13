module

public import SerrinEpigraph.CalibrationPath
public import SerrinEpigraph.QuadraticPotential

/-!
# Interior energy comparisons including endpoint values
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Integrating a continuous function over a compact spatial set preserves continuity
on a compact parameter set. -/
theorem continuousOn_setIntegral_compact {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    {J : Set ℝ} (hJ : IsCompact J) {F : ℝ × Space d → ℝ}
    (hF : ContinuousOn F (J ×ˢ K)) :
    ContinuousOn (fun t ↦ ∫ x in K, F (t, x)) J := by
  obtain ⟨C, hC⟩ := (hJ.prod hK).exists_bound_of_continuousOn hF
  intro t ht
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx ↦ ⟨hr, hx⟩)).aestronglyMeasurable hK.measurableSet
  · filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC (r, x) ⟨hr, hx⟩
  · exact continuousOn_const.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr ↦ ⟨hr, hx⟩)) t ht

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Interior C¹ perturbations may attain either endpoint of the normalized solution range. -/
theorem RigidityHypotheses.energy_minimal_compact_closedRange (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {φ : Space (m + 1) → ℝ} {K : Set (Space (m + 1))}
    (hφ : ContDiff ℝ 1 φ) (hK : IsCompact K) (hsub : K ⊆ epigraph g)
    (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x ∈ epigraph g, u x + φ x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in K, ‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) ≤
      ∫ x in K, ‖gradient (fun y ↦ u y + φ y) x‖ ^ 2 / 2 +
        normalizedPotential f (u x + φ x) := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hg : ContinuousOn (gradient u) K :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      ((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hsub)
  have hgφ : Continuous (gradient φ) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  let A := fun t ↦ ∫ x in K, ‖gradient u x + t • gradient φ x‖ ^ 2 / 2 +
    normalizedPotential f (u x + t * φ x)
  have hc : ContinuousOn A (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_setIntegral_compact hK isCompact_Icc
      (F := fun p ↦ ‖gradient u p.2 + p.1 • gradient φ p.2‖ ^ 2 / 2 +
        normalizedPotential f (u p.2 + p.1 * φ p.2))
    have hgc : ContinuousOn (fun p : ℝ × Space (m + 1) ↦
        gradient u p.2 + p.1 • gradient φ p.2) (Set.Icc (0 : ℝ) 1 ×ˢ K) :=
      (hg.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)).add
        (continuous_fst.continuousOn.smul (hgφ.comp continuous_snd).continuousOn)
    have hsc : ContinuousOn (fun p : ℝ × Space (m + 1) ↦ u p.2 + p.1 * φ p.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ K) :=
      ((hu.continuousOn.mono hsub).comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)).add
        (continuous_fst.continuousOn.mul (hφ.continuous.comp continuous_snd).continuousOn)
    refine (hgc.norm.pow 2 |>.div_const 2).add
      (h.normalizedPotential_continuousOn.comp hsc ?_)
    intro p hp
    have h0 : u p.2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(h.positive _ (hsub hp.2)).le, (hr.solution_lt_one _ (hsub hp.2)).le⟩
    have he := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1) h0 (hval _ (hsub hp.2))
      (sub_nonneg.mpr hp.1.2) hp.1.1 (by ring : 1 - p.1 + p.1 = 1)
    convert he using 1
    simp only [smul_eq_mul]
    ring
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, A 0 ≤ A t := by
    intro t ht
    have hv : ∀ x ∈ epigraph g, u x + t * φ x ∈ Set.Ioo (0 : ℝ) 1 := by
      intro x hx
      have h0 := h.positive x hx
      have h1 := hr.solution_lt_one x hx
      have hend := hval x hx
      have hp := mul_pos (sub_pos.mpr ht.2) h0
      have hq := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr h1)
      constructor <;> nlinarith [mul_nonneg ht.1 hend.1,
        mul_nonneg ht.1 (sub_nonneg.mpr hend.2)]
    have hm := hr.energy_minimal_compact h (contDiff_const.mul hφ) hK hsub
      ((tsupport_mul_subset_right (f := fun _ ↦ t) (g := φ)).trans hsupp) hv
    have hg' (x : Space (m + 1)) (hx : x ∈ K) := gradient_affine_variation
      ((hu.differentiableOn_one x (hsub hx)).differentiableAt (hΩ.mem_nhds (hsub hx)))
      (hφ.differentiable_one x) t
    simpa only [A, zero_smul, add_zero, zero_mul] using hm.trans_eq
      (setIntegral_congr_fun hK.measurableSet (fun x hx ↦ by rw [hg' x hx]))
  have he : A 0 ≤ A 1 := ContinuousWithinAt.closure_le
    (by rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]; simp)
    continuousWithinAt_const ((hc 1 (by simp)).mono Set.Ico_subset_Icc_self) hbound
  have hend : A 1 = ∫ x in K, ‖gradient (fun y ↦ u y + φ y) x‖ ^ 2 / 2 +
      normalizedPotential f (u x + φ x) := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    have hg' := gradient_affine_variation
      ((hu.differentiableOn_one x (hsub hx)).differentiableAt (hΩ.mem_nhds (hsub hx)))
      (hφ.differentiable_one x) 1
    simp only [one_mul, one_smul] at hg' ⊢
    rw [hg']
  rw [hend] at he
  simpa only [A, zero_smul, add_zero, zero_mul] using he

end SerrinEpigraph
