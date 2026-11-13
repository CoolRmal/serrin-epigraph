module

public import SerrinEpigraph.RadialEndpointDerivative

/-!
# Continuation across a positive finite endpoint
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- Join a left profile to a right profile, using the right value at the junction. -/
@[expose] def radialSplice (R : ℝ) (F G : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < R then F t else G t

/-- The splice agrees locally with its left branch strictly before the junction. -/
theorem radialSplice_eventuallyEq_left {R t : ℝ} {F G : ℝ → ℝ} (ht : t < R) :
    radialSplice R F G =ᶠ[𝓝 t] F := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  change s < R at hs
  simp only [radialSplice, ite_eq_left hs]

/-- The splice agrees locally with its right branch strictly after the junction. -/
theorem radialSplice_eventuallyEq_right {R t : ℝ} {F G : ℝ → ℝ} (ht : R < t) :
    radialSplice R F G =ᶠ[𝓝 t] G := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [radialSplice, ite_eq_right (not_lt.mpr hs.le)]

/-- Matching left and right derivatives give a genuine derivative of the splice. -/
theorem radialSplice_hasDerivAt {R b d : ℝ} {F G : ℝ → ℝ}
    (hF : HasDerivWithinAt (Function.update F R b) d (Iic R) R)
    (hG : HasDerivAt G d R) (hGb : G R = b) : HasDerivAt (radialSplice R F G) d R := by
  have hl : HasDerivWithinAt (radialSplice R F G) d (Iic R) R := by
    apply hF.congr_of_mem _ le_rfl
    intro t ht
    rcases lt_or_eq_of_le ht with hlt | rfl
    · simp [radialSplice, hlt, Function.update_of_ne hlt.ne]
    · simp [radialSplice, hGb]
  have hr : HasDerivWithinAt (radialSplice R F G) d (Ici R) R := by
    apply hG.hasDerivWithinAt.congr_of_mem _ le_rfl
    intro t ht
    simp [radialSplice, not_lt.mpr ht]
  have hu := hl.union hr
  rw [Iic_union_Ici] at hu
  exact hu.hasDerivAt Filter.univ_mem

/-- A positive completed endpoint permits extension to a strictly larger radial interval. -/
theorem Hypotheses.radial_continue_of_endpoint_derivatives
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {a R b p : ℝ}
    (hR : 0 < R) (hb : 0 < b) (hQP : IsRadialSystemOn m f Q P (Ioo a R))
    (hQend : HasDerivWithinAt (Function.update Q R b) p (Iic R) R)
    (hPend : HasDerivWithinAt (Function.update P R p)
      (-f b - (m : ℝ) / R * p) (Iic R) R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W Z : ℝ → ℝ,
      IsRadialSystemOn m f W Z (Ioo a (R + ε)) ∧
      EqOn W Q (Ioo a R) ∧ EqOn Z P (Ioo a R) ∧ W R = b ∧ Z R = p := by
  obtain ⟨ε, hε, _, U, V, hU0, hV0, hUV⟩ :=
    h.exists_radial_system_near_positive_state (p := p) hR hb
  let W := radialSplice R Q U
  let Z := radialSplice R P V
  have hWR : W R = b := by simp [W, radialSplice, hU0]
  have hZR : Z R = p := by simp [Z, radialSplice, hV0]
  refine ⟨ε, hε, W, Z, ?_, ?_, ?_, hWR, hZR⟩
  · intro t ht
    rcases lt_trichotomy t R with hlt | heq | hgt
    · have htold : t ∈ Ioo a R := ⟨ht.1, hlt⟩
      have heQ := radialSplice_eventuallyEq_left (F := Q) (G := U) hlt
      have heP := radialSplice_eventuallyEq_left (F := P) (G := V) hlt
      change HasDerivAt W (Z t) t ∧ HasDerivAt Z (-f (W t) - (m : ℝ) / t * Z t) t
      rw [show W t = Q t from heQ.eq_of_nhds, show Z t = P t from heP.eq_of_nhds]
      exact ⟨(hQP t htold).1.congr_of_eventuallyEq heQ,
        (hQP t htold).2.congr_of_eventuallyEq heP⟩
    · subst t
      have hmid : R ∈ Ioo (R - ε) (R + ε) := ⟨by linarith, by linarith⟩
      have hdU := (hUV R hmid).2.1
      have hdV := (hUV R hmid).2.2
      rw [hV0] at hdU
      rw [hU0, hV0] at hdV
      change HasDerivAt W (Z R) R ∧ HasDerivAt Z (-f (W R) - (m : ℝ) / R * Z R) R
      rw [hWR, hZR]
      exact ⟨radialSplice_hasDerivAt hQend hdU hU0, radialSplice_hasDerivAt hPend hdV hV0⟩
    · have htnew : t ∈ Ioo (R - ε) (R + ε) := ⟨by linarith, ht.2⟩
      have heQ := radialSplice_eventuallyEq_right (F := Q) (G := U) hgt
      have heP := radialSplice_eventuallyEq_right (F := P) (G := V) hgt
      change HasDerivAt W (Z t) t ∧ HasDerivAt Z (-f (W t) - (m : ℝ) / t * Z t) t
      rw [show W t = U t from heQ.eq_of_nhds, show Z t = V t from heP.eq_of_nhds]
      exact ⟨(hUV t htnew).2.1.congr_of_eventuallyEq heQ,
        (hUV t htnew).2.2.congr_of_eventuallyEq heP⟩
  · intro t ht
    exact (radialSplice_eventuallyEq_left ht.2).eq_of_nhds
  · intro t ht
    exact (radialSplice_eventuallyEq_left ht.2).eq_of_nhds

/-- A normalized radial solution either reaches zero at a finite endpoint or continues beyond it. -/
theorem Hypotheses.radial_zero_limit_or_continuation
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {a δ R : ℝ}
    (ha : 0 ≤ a) (hδ : δ ∈ Ioo a R)
    (hQP : IsRadialSystemOn m f Q P (Ioo a R))
    (hval : ∀ t ∈ Ioo a R, Q t ∈ Ioo (0 : ℝ) 1) :
    Filter.Tendsto Q (𝓝[<] R) (𝓝 0) ∨
      ∃ ε : ℝ, 0 < ε ∧ ∃ W Z : ℝ → ℝ,
        IsRadialSystemOn m f W Z (Ioo a (R + ε)) ∧
        EqOn W Q (Ioo a R) ∧ EqOn Z P (Ioo a R) ∧ 0 < W R := by
  obtain ⟨b, p, hb, hQ, _, hQend, hPend⟩ :=
    h.exists_completed_radial_endpoint ha hδ hQP hval
  rcases eq_or_lt_of_le hb.1 with hz | hbpos
  · exact Or.inl (hz ▸ hQ)
  · obtain ⟨ε, hε, W, Z, hWZ, hWQ, hZP, hWR, _⟩ :=
      h.radial_continue_of_endpoint_derivatives (ha.trans_lt (hδ.1.trans hδ.2)) hbpos
        hQP hQend hPend
    exact Or.inr ⟨ε, hε, W, Z, hWZ, hWQ, hZP, hWR ▸ hbpos⟩

end SerrinEpigraph
