module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-!
# Smooth approximations to the positive excess

These continuously differentiable truncations permit square-mass tests without invoking
Sobolev approximation. The parameter will tend to zero through positive values.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace SerrinEpigraph

def smoothExcess (ε t : ℝ) : ℝ := max t 0 ^ 2 / (max t 0 + ε)

def smoothExcessSlope (ε t : ℝ) : ℝ :=
  max t 0 * (max t 0 + 2 * ε) / (max t 0 + ε) ^ 2

theorem smoothExcess_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ smoothExcess ε t :=
  div_nonneg (sq_nonneg _) (by linarith [le_max_right t 0])

theorem smoothExcess_eq_zero_of_nonpos (ε : ℝ) {t : ℝ} (ht : t ≤ 0) :
    smoothExcess ε t = 0 := by simp [smoothExcess, max_eq_right ht]

theorem smoothExcess_le_positivePart {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    smoothExcess ε t ≤ max t 0 := by
  rw [smoothExcess, div_le_iff₀ (by linarith [le_max_right t 0])]
  nlinarith [mul_nonneg (le_max_right t 0) hε.le]

theorem smoothExcessSlope_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ smoothExcessSlope ε t := by
  apply div_nonneg _ (sq_nonneg _)
  exact mul_nonneg (le_max_right _ _) (by linarith [le_max_right t 0])

theorem smoothExcessSlope_le_one {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    smoothExcessSlope ε t ≤ 1 := by
  rw [smoothExcessSlope, div_le_iff₀ (sq_pos_of_pos (by linarith [le_max_right t 0]))]
  nlinarith [sq_nonneg ε]

theorem smoothExcess_sq_le_slope_mul_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    smoothExcess ε t ^ 2 ≤ smoothExcessSlope ε t * max t 0 ^ 2 := by
  have hz : 0 ≤ max t 0 := le_max_right _ _
  have hd : 0 < max t 0 + ε := by linarith
  dsimp [smoothExcess, smoothExcessSlope]
  rw [div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (sq_pos_of_pos hd)]
  nlinarith [mul_nonneg (mul_nonneg hε.le hz) (sq_nonneg (max t 0))]

private theorem hasDerivAt_rationalExcess {ε t : ℝ} (hne : t + ε ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ s ^ 2 / (s + ε))
      (t * (t + 2 * ε) / (t + ε) ^ 2) t := by
  have hd := (hasDerivAt_pow 2 t).div ((hasDerivAt_id t).add_const ε) hne
  simp only [Pi.div_def, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hd
  convert hd using 1
  ring

/-- The derivative exists even at the zero of the positive-part truncation. -/
theorem hasDerivAt_smoothExcess {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (smoothExcess ε) (smoothExcessSlope ε t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have heq : smoothExcess ε =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact smoothExcess_eq_zero_of_nonpos ε hs.le
    simpa [smoothExcessSlope, max_eq_right ht.le] using
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  · have hp : HasDerivWithinAt (smoothExcess ε) 0 (Ici 0) 0 := by
      have hd : HasDerivAt (fun s : ℝ ↦ s ^ 2 / (s + ε)) 0 0 := by
        simpa using hasDerivAt_rationalExcess (t := 0) (by simpa using hε.ne')
      exact hd.hasDerivWithinAt.congr_of_mem
        (fun s hs ↦ by simp only [smoothExcess, max_eq_left hs]) self_mem_Ici
    have hn : HasDerivWithinAt (smoothExcess ε) 0 (Iic 0) 0 :=
      (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        (fun s hs ↦ smoothExcess_eq_zero_of_nonpos ε hs) self_mem_Iic
    simpa [Ici_union_Iic, smoothExcessSlope] using hp.union hn
  · have heq : smoothExcess ε =ᶠ[𝓝 t] fun s ↦ s ^ 2 / (s + ε) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp only [smoothExcess, max_eq_left hs.le]
    simpa only [smoothExcessSlope, max_eq_left ht.le] using
      (hasDerivAt_rationalExcess (ne_of_gt (add_pos ht hε))).congr_of_eventuallyEq heq

theorem continuous_smoothExcessSlope {ε : ℝ} (hε : 0 < ε) :
    Continuous (smoothExcessSlope ε) := by
  unfold smoothExcessSlope
  apply ((continuous_id.max continuous_const).mul
    ((continuous_id.max continuous_const).add continuous_const)).div
    (((continuous_id.max continuous_const).add continuous_const).pow 2)
  intro t
  exact pow_ne_zero _ (ne_of_gt (by linarith [le_max_right t 0] : 0 < max t 0 + ε))

theorem contDiff_smoothExcess {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (smoothExcess ε) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t ↦ (hasDerivAt_smoothExcess hε t).differentiableAt, ?_⟩
  have heq : deriv (smoothExcess ε) = smoothExcessSlope ε :=
    funext fun t ↦ (hasDerivAt_smoothExcess hε t).deriv
  rw [heq]
  exact continuous_smoothExcessSlope hε

/-- The smooth excess converges pointwise to the positive part as the parameter vanishes. -/
theorem tendsto_smoothExcess_zero (t : ℝ) :
    Tendsto (fun ε ↦ smoothExcess ε t) (𝓝 0) (𝓝 (max t 0)) := by
  by_cases ht : t ≤ 0
  · simpa only [smoothExcess_eq_zero_of_nonpos _ ht, max_eq_right ht] using
      (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝 (0 : ℝ)))
  · have hz : 0 < max t 0 := lt_of_lt_of_le (lt_of_not_ge ht) (le_max_left _ _)
    have hc : ContinuousAt (fun ε : ℝ ↦ max t 0 ^ 2 / (max t 0 + ε)) 0 :=
      continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simpa using hz.ne')
    simpa [smoothExcess, pow_two, hz.ne'] using hc.tendsto

end SerrinEpigraph
