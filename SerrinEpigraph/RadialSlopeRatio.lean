module

public import SerrinEpigraph.RadialCenter
public import SerrinEpigraph.RadialEquation

/-!
# Removing the central singularity of the radial slope ratio
-/

public section
noncomputable section
open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- At zero the weighted average is the forcing value divided by the dimension. -/
theorem radialAverage_zero (m : ℕ) (F : ℝ → ℝ) :
    radialAverage m F 0 = F 0 / (m + 1 : ℝ) := by
  simp only [radialAverage, zero_mul, intervalIntegral.integral_mul_const]
  rw [integral_pow]
  simp
  ring

/-- A forcing continuous on the radius interval has a continuous weighted average there. -/
theorem radialAverage_continuousOn (m : ℕ) {F : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hF : ContinuousOn F (Icc 0 R)) :
    ContinuousOn (radialAverage m F) (Icc 0 R) := by
  let G := intervalReaction F hR
  have hG : Continuous G := hF.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t ↦ (projIcc 0 R hR t).property)
  apply (radialAverage_continuous m hG).continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  have hts : t * s ∈ Icc (0 : ℝ) R :=
    ⟨mul_nonneg ht.1 hs'.1, (mul_le_of_le_one_right ht.1 hs'.2).trans ht.2⟩
  change s ^ m * F (t * s) = s ^ m * G (t * s)
  rw [show G (t * s) = F (t * s) from intervalReaction_eq hR hts]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ R : ℝ}

/-- The radial slope divided by radius equals the negative weighted reaction average. -/
theorem RadialBallProfile.slope_div_eq_average (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) R) :
    v.slope r / r = -radialAverage m (f ∘ v.value) r := by
  have he := v.flux_eq_integral h ⟨hr.1.le, hr.2⟩
  have hav := radialAverage_mul_pow m (f ∘ v.value) r
  simp only [Function.comp_apply] at hav
  rw [← hav, pow_succ] at he
  apply (div_eq_iff hr.1.ne').mpr
  have hp : r ^ m ≠ 0 := pow_ne_zero _ hr.1.ne'
  apply mul_left_cancel₀ hp
  nlinarith [he]

/-- The central slope ratio has the finite limit dictated by the reaction and dimension. -/
theorem RadialBallProfile.slope_div_tendsto_zero (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) :
    Tendsto (fun r ↦ v.slope r / r) (𝓝[>] 0)
      (𝓝 (-f (v.value 0) / (m + 1 : ℝ))) := by
  have hF : ContinuousOn (f ∘ v.value) (Icc 0 R) :=
    h.reaction_contDiffOn.continuousOn.comp v.value_continuous
      (fun t ht ↦ (v.value_range t ht).1)
  have hc := radialAverage_continuousOn m v.radius_pos.le hF 0
    (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, v.radius_pos.le⟩)
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE v.radius_pos] at hc
  have he := (hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).neg
  simp only [radialAverage_zero, Function.comp_apply, neg_div] at he ⊢
  apply he.congr'
  filter_upwards [Ioo_mem_nhdsGT v.radius_pos] with r hr
  exact (v.slope_div_eq_average h ⟨hr.1, hr.2.le⟩).symm

/-- The derivative of the radial slope has the same finite central limit as its ratio. -/
theorem RadialBallProfile.slope_deriv_tendsto_zero (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) :
    Tendsto (deriv v.slope) (𝓝[>] 0) (𝓝 (-f (v.value 0) / (m + 1 : ℝ))) := by
  have hF : ContinuousOn (f ∘ v.value) (Icc 0 R) :=
    h.reaction_contDiffOn.continuousOn.comp v.value_continuous
      (fun t ht ↦ (v.value_range t ht).1)
  have hc := hF 0 ⟨le_rfl, v.radius_pos.le⟩
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE v.radius_pos] at hc
  have he := (hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).neg.sub
    ((v.slope_div_tendsto_zero h).const_mul (m : ℝ))
  have halg : -f (v.value 0) - (m : ℝ) * (-f (v.value 0) / (m + 1 : ℝ)) =
      -f (v.value 0) / (m + 1 : ℝ) := by
    field_simp
    ring
  simp only [Function.comp_apply, halg] at he
  apply he.congr'
  filter_upwards [Ioo_mem_nhdsGT v.radius_pos] with r hr
  rw [(v.slope_derivative r hr).deriv]
  ring

/-- The radial slope has a right derivative at the center with the required isotropic value. -/
theorem RadialBallProfile.slope_hasDerivWithinAt_zero (v : RadialBallProfile f m R)
    (h : Hypotheses g u f κ) :
    HasDerivWithinAt v.slope (-f (v.value 0) / (m + 1 : ℝ)) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo (0 : ℝ) R)
    (fun t ht ↦ (v.slope_derivative t ht).differentiableAt.differentiableWithinAt)
  · exact (v.slope_continuous 0 ⟨le_rfl, v.radius_pos.le⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT v.radius_pos
  · exact v.slope_deriv_tendsto_zero h

end SerrinEpigraph
