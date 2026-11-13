module

public import SerrinEpigraph.RadialReactionExtension

/-!
# Recovering the radial differential equation from weighted averages
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- Rescaling the weighted unit average gives the radial primitive. -/
theorem radialAverage_mul_pow (m : ℕ) (F : ℝ → ℝ) (r : ℝ) :
    r ^ (m + 1) * radialAverage m F r = ∫ t in (0 : ℝ)..r, t ^ m * F t := by
  have he := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ ↦ t ^ m * F t) (a := 0) (b := 1) r
  simp only [smul_eq_mul, mul_zero, mul_one, mul_pow, mul_assoc,
    intervalIntegral.integral_const_mul] at he
  simpa only [radialAverage, pow_succ, mul_assoc, mul_left_comm] using he

/-- Away from the origin, the averaged slope is the weighted primitive divided by volume. -/
theorem radialAverage_slope_eq (m : ℕ) (F : ℝ → ℝ) {r : ℝ} (hr : r ≠ 0) :
    -r * radialAverage m F r = -(∫ t in (0 : ℝ)..r, t ^ m * F t) / r ^ m := by
  rw [← radialAverage_mul_pow m F r, pow_succ]
  field_simp

/-- The averaged slope satisfies the singular radial equation at positive radii. -/
theorem radialAverage_slope_hasDerivAt (m : ℕ) {F : ℝ → ℝ} (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t ↦ -t * radialAverage m F t)
      (-F r - (m : ℝ) / r * (-r * radialAverage m F r)) r := by
  have hc : Continuous (fun t : ℝ ↦ t ^ m * F t) := (continuous_id.pow m).mul hF
  have hi := (hc.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hd := hi.neg.div (hasDerivAt_pow m r) (pow_ne_zero m hr.ne')
  have heq : (fun t ↦ -t * radialAverage m F t) =ᶠ[𝓝 r]
      (fun t ↦ -(∫ s in (0 : ℝ)..t, s ^ m * F s) / t ^ m) := by
    filter_upwards [isOpen_ne.mem_nhds hr.ne'] with t ht
    exact radialAverage_slope_eq m F ht
  convert hd.congr_of_eventuallyEq heq using 1
  simp only [Pi.neg_apply]
  rw [← radialAverage_mul_pow m F r]
  cases m with
  | zero => simp
  | succ k =>
    simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]
    field_simp [hr.ne']

/-- The slope equation only needs forcing continuity on the radius interval. -/
theorem radialAverage_slope_hasDerivAt_on (m : ℕ) {F : ℝ → ℝ} {R r : ℝ}
    (hF : ContinuousOn F (Icc 0 R)) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt (fun t ↦ -t * radialAverage m F t)
      (-F r - (m : ℝ) / r * (-r * radialAverage m F r)) r := by
  have hR : 0 ≤ R := (hr.1.trans hr.2).le
  let G := intervalReaction F hR
  have hG : Continuous G := hF.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t ↦ (projIcc 0 R hR t).property)
  have heq : ∀ t ∈ Icc (0 : ℝ) R, radialAverage m G t = radialAverage m F t := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    have hts : t * s ∈ Icc (0 : ℝ) R :=
      ⟨mul_nonneg ht.1 hs'.1, (mul_le_of_le_one_right ht.1 hs'.2).trans ht.2⟩
    change s ^ m * G (t * s) = s ^ m * F (t * s)
    rw [show G (t * s) = F (t * s) from intervalReaction_eq hR hts]
  have hd := radialAverage_slope_hasDerivAt m hG hr.1
  rw [show G r = F r from intervalReaction_eq hR ⟨hr.1.le, hr.2.le⟩,
    heq r ⟨hr.1.le, hr.2.le⟩] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  rw [heq t ⟨ht.1.le, ht.2.le⟩]

/-- The averaged slope is continuous up to the center and the outer radius. -/
theorem radialAverage_slope_continuousOn (m : ℕ) {F : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hF : ContinuousOn F (Icc 0 R)) :
    ContinuousOn (fun t ↦ -t * radialAverage m F t) (Icc 0 R) := by
  let G := intervalReaction F hR
  have hG : Continuous G := hF.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t ↦ (projIcc 0 R hR t).property)
  have hc : Continuous (fun t ↦ -t * radialAverage m G t) :=
    continuous_id.neg.mul (radialAverage_continuous m hG)
  apply hc.continuousOn.congr
  intro t ht
  change -t * radialAverage m F t = -t * radialAverage m G t
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  have hts : t * s ∈ Icc (0 : ℝ) R :=
    ⟨mul_nonneg ht.1 hs'.1, (mul_le_of_le_one_right ht.1 hs'.2).trans ht.2⟩
  change s ^ m * F (t * s) = s ^ m * G (t * s)
  rw [show G (t * s) = F (t * s) from intervalReaction_eq hR hts]

/-- The original hypotheses give local solutions of the second-order radial system. -/
theorem Hypotheses.exists_local_radial_system
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ Q P : ℝ → ℝ,
      Continuous Q ∧ ContinuousOn P (Icc 0 R) ∧ Q 0 = a ∧ P 0 = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) R, Q r ∈ Ioo (0 : ℝ) 1) ∧
      (∀ r ∈ Icc (0 : ℝ) R, HasDerivAt Q (P r) r) ∧
      ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt P (-f (Q r) - (m : ℝ) / r * P r) r := by
  obtain ⟨R, hR, Q, hQ, hQ0, _, hrange, hd⟩ :=
    h.exists_local_radial_averaged_solution ha
  let P := fun r ↦ -r * radialAverage m (f ∘ Q) r
  have hF : ContinuousOn (f ∘ Q) (Icc 0 R) :=
    h.reaction_contDiffOn.continuousOn.comp hQ.continuousOn
      (fun t ht ↦ (hrange t ht).1.le)
  refine ⟨R, hR, Q, P, hQ, radialAverage_slope_continuousOn m hR.le hF,
    hQ0, by simp [P], hrange, hd, ?_⟩
  intro r hr
  exact radialAverage_slope_hasDerivAt_on m hF hr

end SerrinEpigraph
