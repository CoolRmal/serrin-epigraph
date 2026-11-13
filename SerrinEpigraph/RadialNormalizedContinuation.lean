module

public import SerrinEpigraph.RadialDecrease

/-!
# Preserving normalized values during radial continuation
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- An endpoint value strictly between zero and one permits normalized continuation. -/
theorem Hypotheses.radial_continue_normalized (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {a R b p : ℝ} (haR : a < R) (hR : 0 < R)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hQP : IsRadialSystemOn m f Q P (Ioo a R))
    (hval : ∀ t ∈ Ioo a R, Q t ∈ Ioo (0 : ℝ) 1)
    (hQend : HasDerivWithinAt (Function.update Q R b) p (Iic R) R)
    (hPend : HasDerivWithinAt (Function.update P R p)
      (-f b - (m : ℝ) / R * p) (Iic R) R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W Z : ℝ → ℝ,
      IsRadialSystemOn m f W Z (Ioo a (R + ε)) ∧
      EqOn W Q (Ioo a R) ∧ EqOn Z P (Ioo a R) ∧ W R = b ∧ Z R = p ∧
      (∀ t ∈ Ioo a (R + ε), W t ∈ Ioo (0 : ℝ) 1) := by
  obtain ⟨ε, hε, W, Z, hWZ, hWQ, hZP, hWR, hZR⟩ :=
    h.radial_continue_of_endpoint_derivatives hR hb.1 hQP hQend hPend
  have hRc : ContinuousAt W R := (hWZ R ⟨haR, by linarith⟩).1.continuousAt
  have hn : W ⁻¹' Ioo (0 : ℝ) 1 ∈ 𝓝 R :=
    hRc.preimage_mem_nhds (Ioo_mem_nhds (hWR ▸ hb.1) (hWR ▸ hb.2))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let η := min ε (δ / 2)
  have hη : 0 < η := lt_min hε (by positivity)
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ δ / 2 := min_le_right _ _
  refine ⟨η, hη, W, Z, hWZ.mono (fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩),
    hWQ, hZP, hWR, hZR, ?_⟩
  intro t ht
  by_cases htR : t < R
  · rw [hWQ ⟨ht.1, htR⟩]
    exact hval t ⟨ht.1, htR⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.2, not_lt.mp htR]

/-- Restoring the central value preserves continuity on an enlarged half-open interval. -/
theorem continuousOn_update_center_of_extension {F G : ℝ → ℝ} {R T : ℝ}
    (hR : 0 < R) (hF : ContinuousOn F (Ico 0 R))
    (heq : EqOn G F (Ioo 0 R)) (hG : ContinuousOn G (Ioo 0 T)) :
    ContinuousOn (Function.update G 0 (F 0)) (Ico 0 T) := by
  have hF0 : ContinuousWithinAt F (Ici 0) 0 := by
    have hc := hF 0 ⟨le_rfl, hR⟩
    simpa only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsGE hR] using hc
  have he : Function.update G 0 (F 0) =ᶠ[𝓝[≥] 0] F := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with t ht hlt
    by_cases hz : t = 0
    · simp [hz]
    · rw [Function.update_of_ne hz]
      exact heq ⟨lt_of_le_of_ne ht (Ne.symm hz), hlt⟩
  have hc0 : ContinuousWithinAt (Function.update G 0 (F 0)) (Ici 0) 0 :=
    hF0.congr_of_eventuallyEq he (by simp)
  intro t ht
  by_cases hz : t = 0
  · subst t
    exact hc0.mono (fun _ hs ↦ hs.1)
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    have hGc : ContinuousAt G t := (hG t ⟨htpos, ht.2⟩).continuousAt
      (Ioo_mem_nhds htpos ht.2)
    apply ContinuousAt.continuousWithinAt
    apply hGc.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hz] with s hs
    exact Function.update_of_ne hs (F 0) G

/-- A regular central profile either reaches zero or continues with all values still in (0,1). -/
theorem RigidityHypotheses.radial_zero_limit_or_normalized_continuation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hQc : ContinuousOn Q (Ico 0 R)) (hPc : ContinuousOn P (Ico 0 R))
    (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ t ∈ Ioo (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1)
    (hQ0 : Q 0 < 1) (hP0 : P 0 = 0) :
    Filter.Tendsto Q (𝓝[<] R) (𝓝 0) ∨
      ∃ ε : ℝ, 0 < ε ∧ ∃ W Z : ℝ → ℝ,
        IsRadialSystemOn m f W Z (Ioo 0 (R + ε)) ∧
        ContinuousOn W (Ico 0 (R + ε)) ∧ ContinuousOn Z (Ico 0 (R + ε)) ∧
        EqOn W Q (Ico 0 R) ∧ EqOn Z P (Ico 0 R) ∧
        (∀ t ∈ Ioo (0 : ℝ) (R + ε), W t ∈ Ioo (0 : ℝ) 1) := by
  obtain ⟨b, p, hb, hQ, _, hQend, hPend⟩ := h.exists_completed_radial_endpoint
    (a := 0) (δ := R / 2) le_rfl ⟨by positivity, by linarith⟩ hQP hval
  have hb1 : b < 1 := (radial_endpoint_lt_center hR
    (hr.radial_value_strictAntiOn_Ico h hQc hPc hQP hval hP0) hQ).trans hQ0
  rcases eq_or_lt_of_le hb.1 with hz | hbpos
  · exact Or.inl (hz ▸ hQ)
  · obtain ⟨ε, hε, W, Z, hWZ, hWQ, hZP, _, _, hWval⟩ :=
      h.radial_continue_normalized hR hR ⟨hbpos, hb1⟩ hQP hval hQend hPend
    let W' := Function.update W 0 (Q 0)
    let Z' := Function.update Z 0 (P 0)
    have hsys : IsRadialSystemOn m f W' Z' (Ioo 0 (R + ε)) := by
      intro t ht
      change HasDerivAt W' (Z' t) t ∧
        HasDerivAt Z' (-f (W' t) - (m : ℝ) / t * Z' t) t
      simp only [W', Z', Function.update_of_ne ht.1.ne']
      exact ⟨hasDerivAt_update_endpoint ht.1.ne' (hWZ t ht).1,
        hasDerivAt_update_endpoint ht.1.ne' (hWZ t ht).2⟩
    refine Or.inr ⟨ε, hε, W', Z', hsys,
      continuousOn_update_center_of_extension hR hQc hWQ
        (fun t ht ↦ (hWZ t ht).1.continuousAt.continuousWithinAt),
      continuousOn_update_center_of_extension hR hPc hZP
        (fun t ht ↦ (hWZ t ht).2.continuousAt.continuousWithinAt), ?_, ?_, ?_⟩
    · intro t ht
      by_cases hz : t = 0
      · simp [W', hz]
      · rw [show W' t = W t from Function.update_of_ne hz _ _]
        exact hWQ ⟨lt_of_le_of_ne ht.1 (Ne.symm hz), ht.2⟩
    · intro t ht
      by_cases hz : t = 0
      · simp [Z', hz]
      · rw [show Z' t = Z t from Function.update_of_ne hz _ _]
        exact hZP ⟨lt_of_le_of_ne ht.1 (Ne.symm hz), ht.2⟩
    · intro t ht
      rw [show W' t = W t from Function.update_of_ne ht.1.ne' _ _]
      exact hWval t ht

end SerrinEpigraph
