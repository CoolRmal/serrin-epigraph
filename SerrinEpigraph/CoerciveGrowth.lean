module

public import SerrinEpigraph.MassGrowth

/-!
# A fixed-width coercive estimate contradicts subexponential mass growth
-/

public section

open Filter Set

namespace SerrinEpigraph

/-- Doubling the mass at each fixed radial increment forces a positive exponential rate. -/
theorem nonpos_of_fixedWidth_doubling {W V : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hmono : MonotoneOn W (Ioi 0)) (hsub : ∀ R : ℝ, 0 < R → W R ≤ V R)
    (hV : Filter.liminf (fun R ↦ ((Real.log (1 + V R) / R : ℝ) : EReal)) atTop = 0)
    (hstep : ∀ R : ℝ, 0 < R → 2 * W R ≤ W (R + L)) :
    ∀ R : ℝ, 0 < R → W R ≤ 0 := by
  intro R₀ hR₀
  by_contra! hpos
  have hind (k : ℕ) : W R₀ * (2 : ℝ) ^ k ≤ W (R₀ + k * L) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = 2 * (W R₀ * (2 : ℝ) ^ k) := by rw [pow_succ]; ring
        _ ≤ 2 * W (R₀ + k * L) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ W (R₀ + k * L + L) := hstep _ (by positivity)
        _ = W (R₀ + (k + 1 : ℕ) * L) := by congr 1; push_cast; ring
  have hc : 0 < Real.log 2 / (2 * L) :=
    div_pos (Real.log_pos (by norm_num)) (by positivity)
  apply not_eventually_exponential_lowerBound hV hpos hc
  filter_upwards [eventually_ge_atTop (2 * (R₀ + L))] with R hR
  have hRpos : 0 < R := by linarith
  have ht : 0 ≤ (R - R₀) / L := div_nonneg (by linarith) hL.le
  let k := ⌊(R - R₀) / L⌋₊
  have hkupper : (k : ℝ) ≤ (R - R₀) / L := Nat.floor_le ht
  have hpoint : R₀ + k * L ≤ R := by
    have hh := (le_div_iff₀ hL).mp hkupper
    linarith
  have hklower : R / (2 * L) ≤ (k : ℝ) := by
    have hh := Nat.lt_floor_add_one ((R - R₀) / L)
    change (R - R₀) / L < (k : ℝ) + 1 at hh
    have hh' := (div_lt_iff₀ hL).mp hh
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).mpr
    nlinarith
  have hexp : Real.exp (Real.log 2 / (2 * L) * R) ≤ (2 : ℝ) ^ k := by
    calc
      _ = Real.exp ((R / (2 * L)) * Real.log 2) := by congr 1; ring
      _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hklower (Real.log_pos (by norm_num)).le)
      _ = (2 : ℝ) ^ k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  exact (mul_le_mul_of_nonneg_left hexp hpos.le).trans
    ((hind k).trans
      ((hmono (by change 0 < R₀ + k * L; positivity) hRpos hpoint).trans (hsub R hRpos)))

end SerrinEpigraph
