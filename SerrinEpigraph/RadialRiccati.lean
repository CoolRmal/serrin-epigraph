module

public import SerrinEpigraph.RadialGlobal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Riccati estimates for positive radial systems
-/

public section
noncomputable section
open Set

namespace SerrinEpigraph

/-- Negative logarithmic derivative of a radial value. -/
@[expose] def radialLogSlope (Q P : ℝ → ℝ) (r : ℝ) : ℝ := -P r / Q r

/-- The negative logarithmic derivative satisfies the Riccati equation. -/
theorem radialLogSlope_hasDerivAt {m : ℕ} {f Q P : ℝ → ℝ} {r : ℝ}
    (hQ : HasDerivAt Q (P r) r)
    (hP : HasDerivAt P (-f (Q r) - (m : ℝ) / r * P r) r) (hq : Q r ≠ 0) :
    HasDerivAt (radialLogSlope Q P)
      (f (Q r) / Q r - (m : ℝ) / r * radialLogSlope Q P r + radialLogSlope Q P r ^ 2) r := by
  convert hP.neg.div hQ hq using 1
  · rfl
  · simp only [radialLogSlope, Pi.neg_apply]
    field_simp
    ring

/-- A positive forcing ratio dominates sufficiently small radial drift. -/
theorem riccati_arctan_lower_bound {c k z A : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hk : k ≤ c) (hz : 0 ≤ z) (hA : c ≤ A) :
    c / 2 ≤ (1 / (1 + z ^ 2)) * (A - k * z + z ^ 2) := by
  have hden : 0 < 1 + z ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hden]
  have hkz : k * z ≤ c * z := mul_le_mul_of_nonneg_right hk hz
  have hcz : c * z ^ 2 ≤ z ^ 2 := mul_le_of_le_one_left (sq_nonneg z) hc1
  nlinarith [mul_nonneg hc.le (sq_nonneg (z - 1))]

/-- A globally defined nonnegative Riccati solution with positive forcing cannot exist. -/
theorem no_global_riccati {z A k : ℝ → ℝ} {T c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hz : ∀ t ∈ Ici T, 0 ≤ z t) (hA : ∀ t ∈ Ici T, c ≤ A t)
    (hk : ∀ t ∈ Ici T, k t ≤ c)
    (hd : ∀ t ∈ Ici T, HasDerivAt z (A t - k t * z t + z t ^ 2) t) : False := by
  let F := fun t ↦ Real.arctan (z t)
  have hF : ∀ t ∈ Ici T, HasDerivAt F
      ((1 / (1 + z t ^ 2)) * (A t - k t * z t + z t ^ 2)) t := by
    intro t ht
    exact (Real.hasDerivAt_arctan (z t)).comp t (hd t ht)
  have hbound : ∀ t ∈ Ici T, c / 2 ≤ deriv F t := by
    intro t ht
    rw [(hF t ht).deriv]
    exact riccati_arctan_lower_bound hc hc1 (hk t ht) (hz t ht) (hA t ht)
  let U := T + 2 * (Real.pi + 1) / c
  have hTU : T ≤ U := le_add_of_nonneg_right (by positivity)
  have he := (convex_Ici T).mul_sub_le_image_sub_of_le_deriv
    (fun t ht ↦ (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ hbound t (interior_subset ht)) T le_rfl U hTU hTU
  have halg : c / 2 * (U - T) = Real.pi + 1 := by dsimp [U]; field_simp; ring
  rw [halg] at he
  have hupper := Real.arctan_lt_pi_div_two (z U)
  have hlower := Real.neg_pi_div_two_lt_arctan (z T)
  dsimp only [F] at he
  linarith

/-- The restored reaction hypotheses exclude global normalized positive central radial systems. -/
theorem RigidityHypotheses.no_global_positive_radial_system
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} (hQc : ContinuousOn Q (Ici 0)) (hPc : ContinuousOn P (Ici 0))
    (hP0 : P 0 = 0) (hval : ∀ t ∈ Ici (0 : ℝ), Q t ∈ Ioo (0 : ℝ) 1)
    (hsys : IsRadialSystemOn m f Q P (Ioi 0)) : False := by
  have hq0 := hval 0 le_rfl
  let c := min (f (Q 0) / Q 0) 1
  have hc : 0 < c := lt_min (div_pos (hr.reaction_pos _ hq0) hq0.1) zero_lt_one
  have hc1 : c ≤ 1 := min_le_right _ _
  have hca : c ≤ f (Q 0) / Q 0 := min_le_left _ _
  have hdecrease : ∀ t > 0, Q t ≤ Q 0 ∧ P t < 0 := by
    intro t ht
    have hQc' := hQc.mono (show Icc (0 : ℝ) t ⊆ Ici 0 from fun _ hs ↦ hs.1)
    have hPc' := hPc.mono (show Icc (0 : ℝ) t ⊆ Ici 0 from fun _ hs ↦ hs.1)
    have hsys' := hsys.mono (show Ioo (0 : ℝ) t ⊆ Ioi 0 from fun _ hs ↦ hs.1)
    have hval' : ∀ s ∈ Ioo (0 : ℝ) t, Q s ∈ Ioo (0 : ℝ) 1 :=
      fun s hs ↦ hval s hs.1.le
    exact ⟨(hr.radial_value_strictAntiOn h hQc' hPc' hsys' hval' hP0
      ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht).le,
      hr.radial_slope_neg h hPc' hsys' hval' hP0 ⟨ht, le_rfl⟩⟩
  let T := (m : ℝ) / c + 1
  have hT : 0 < T := by dsimp [T]; positivity
  apply no_global_riccati (z := radialLogSlope Q P) (A := fun t ↦ f (Q t) / Q t)
    (k := fun t ↦ (m : ℝ) / t) (T := T) hc hc1
  · intro t ht
    have htpos := hT.trans_le ht
    exact div_nonneg (neg_nonneg.mpr (hdecrease t htpos).2.le) (hval t htpos.le).1.le
  · intro t ht
    have htpos := hT.trans_le ht
    exact hca.trans (antitoneOn_reaction_div h.reaction_contDiffOn h.reaction_structure
      (hval t htpos.le).1 hq0.1 (hdecrease t htpos).1)
  · intro t ht
    have htpos := hT.trans_le ht
    apply (div_le_iff₀ htpos).mpr
    have hmt : (m : ℝ) / c ≤ t := by
      change (m : ℝ) / c + 1 ≤ t at ht
      linarith
    have he := (div_le_iff₀ hc).mp hmt
    nlinarith
  · intro t ht
    have htpos := hT.trans_le ht
    exact radialLogSlope_hasDerivAt (hsys t htpos).1 (hsys t htpos).2
      (hval t htpos.le).1.ne'

/-- Every normalized central value generates a positive radial Dirichlet solution at a finite radius. -/
theorem RigidityHypotheses.exists_radialBallProfile
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ R : ℝ, ∃ v : RadialBallProfile f m R, v.value 0 = a := by
  rcases hr.radial_ball_or_global h ha with hb | hg
  · exact hb
  · obtain ⟨Q, P, hQc, hPc, _, hP0, hval, hsys⟩ := hg
    exact (hr.no_global_positive_radial_system h hQc hPc hP0 hval hsys).elim

end SerrinEpigraph
