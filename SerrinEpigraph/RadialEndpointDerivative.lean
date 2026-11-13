module

public import SerrinEpigraph.RadialBounds
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Topology.Piecewise

/-!
# Left derivatives of radial solutions completed at a finite endpoint
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- Updating one endpoint preserves the derivative at every other point. -/
theorem hasDerivAt_update_endpoint {F : ℝ → ℝ} {R b t d : ℝ}
    (ht : t ≠ R) (hd : HasDerivAt F d t) : HasDerivAt (Function.update F R b) d t := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds ht] with s hs
  exact Function.update_of_ne hs b F

/-- Completing a function by its left limit gives the left derivative when derivatives converge. -/
theorem hasDerivWithinAt_endpoint_update {F G : ℝ → ℝ} {δ R b p : ℝ}
    (hδ : δ < R) (hd : ∀ t ∈ Ioo δ R, HasDerivAt F (G t) t)
    (hF : Filter.Tendsto F (𝓝[<] R) (𝓝 b))
    (hG : Filter.Tendsto G (𝓝[<] R) (𝓝 p)) :
    HasDerivWithinAt (Function.update F R b) p (Iic R) R := by
  have hu : ∀ t ∈ Ioo δ R, HasDerivAt (Function.update F R b) (G t) t :=
    fun t ht ↦ hasDerivAt_update_endpoint ht.2.ne (hd t ht)
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo δ R) (fun t ht ↦ (hu t ht).differentiableAt.differentiableWithinAt)
  · rw [continuousWithinAt_update_same]
    exact hF.mono_left (nhdsWithin_mono _ (fun _ ht ↦ ht.1.2))
  · exact Ioo_mem_nhdsLT hδ
  · apply hG.congr'
    filter_upwards [Ioo_mem_nhdsLT hδ] with t ht
    exact (hu t ht).deriv.symm

/-- The two completed radial components satisfy the radial equations from the left at the endpoint. -/
theorem radial_system_endpoint_derivatives {m : ℕ} {f Q P : ℝ → ℝ} {δ R b p : ℝ}
    (hδ : δ < R) (hR : R ≠ 0) (hQP : IsRadialSystemOn m f Q P (Ioo δ R))
    (hf : ContinuousAt f b)
    (hQ : Filter.Tendsto Q (𝓝[<] R) (𝓝 b))
    (hP : Filter.Tendsto P (𝓝[<] R) (𝓝 p)) :
    HasDerivWithinAt (Function.update Q R b) p (Iic R) R ∧
      HasDerivWithinAt (Function.update P R p) (-f b - (m : ℝ) / R * p) (Iic R) R := by
  refine ⟨hasDerivWithinAt_endpoint_update hδ (fun t ht ↦ (hQP t ht).1) hQ hP, ?_⟩
  apply hasDerivWithinAt_endpoint_update hδ (fun t ht ↦ (hQP t ht).2) hP
  exact (hf.tendsto.comp hQ).neg.sub
    ((tendsto_const_nhds.div (continuousAt_id.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] R ≤ 𝓝 R)) hR).mul hP)

/-- Normalized radial systems can be completed at the endpoint with both left differential equations. -/
theorem Hypotheses.exists_completed_radial_endpoint
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {a δ R : ℝ}
    (ha : 0 ≤ a) (hδ : δ ∈ Ioo a R)
    (hQP : IsRadialSystemOn m f Q P (Ioo a R))
    (hval : ∀ t ∈ Ioo a R, Q t ∈ Ioo (0 : ℝ) 1) :
    ∃ b p : ℝ, b ∈ Icc (0 : ℝ) 1 ∧
      Filter.Tendsto Q (𝓝[<] R) (𝓝 b) ∧ Filter.Tendsto P (𝓝[<] R) (𝓝 p) ∧
      HasDerivWithinAt (Function.update Q R b) p (Iic R) R ∧
      HasDerivWithinAt (Function.update P R p) (-f b - (m : ℝ) / R * p) (Iic R) R := by
  obtain ⟨b, p, hb, hQ, hP⟩ := h.radial_endpoint_limits_of_normalized_values ha hδ hQP hval
  have hsub : Ioo δ R ⊆ Ioo a R := fun _ ht ↦ ⟨hδ.1.trans ht.1, ht.2⟩
  have hQwithin : Filter.Tendsto Q (𝓝[<] R) (𝓝[Ici 0] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hQ, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hδ.2] with t ht
    exact (hval t (hsub ht)).1.le
  have hfQ : Filter.Tendsto (fun t ↦ f (Q t)) (𝓝[<] R) (𝓝 (f b)) :=
    (h.reaction_contDiffOn.continuousOn b hb.1).tendsto.comp hQwithin
  have hR : R ≠ 0 := (ha.trans_lt (hδ.1.trans hδ.2)).ne'
  refine ⟨b, p, hb, hQ, hP,
    hasDerivWithinAt_endpoint_update hδ.2 (fun t ht ↦ (hQP t (hsub ht)).1) hQ hP, ?_⟩
  apply hasDerivWithinAt_endpoint_update hδ.2 (fun t ht ↦ (hQP t (hsub ht)).2) hP
  exact hfQ.neg.sub ((tendsto_const_nhds.div (continuousAt_id.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] R ≤ 𝓝 R)) hR).mul hP)

end SerrinEpigraph
