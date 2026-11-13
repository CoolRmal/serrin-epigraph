module

public import SerrinEpigraph.SurfaceEnergyLimit
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A common sequence with vanishing logarithmic derivatives

The mean value theorem is applied to finite sums at integer multiples of a scale.
Their uniform energy bounds permit one diagonal sequence controlling every fixed multiple.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- A bounded differentiable function with nonnegative logarithmic derivative admits
one sequence tending to infinity on which those derivatives vanish at every integer multiple. -/
theorem exists_scales_log_derivative_tendsto_zero {F F' : ℝ → ℝ} {C : ℝ}
    (hderiv : ∀ r : ℝ, 0 < r → HasDerivAt F (F' r) r)
    (hnonneg : ∀ r : ℝ, 0 < r → 0 ≤ r * F' r)
    (hbound : ∀ r : ℝ, 1 ≤ r → F r ∈ Icc (0 : ℝ) C) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∀ k : ℕ, Tendsto (fun j ↦ ((k + 1 : ℝ) * R j) * F' ((k + 1 : ℝ) * R j))
        atTop (𝓝 0) := by
  have hselect (j : ℕ) : ∃ r : ℝ, (j + 1 : ℝ) ≤ r ∧
      ∀ k : ℕ, k ≤ j → ((k + 1 : ℝ) * r) * F' ((k + 1 : ℝ) * r) ≤ C / (j + 1 : ℝ) := by
    let S := fun t : ℝ ↦ ∑ k ∈ Finset.range (j + 1), F ((k + 1 : ℝ) * Real.exp t)
    let D := fun t : ℝ ↦ ∑ k ∈ Finset.range (j + 1),
      ((k + 1 : ℝ) * Real.exp t) * F' ((k + 1 : ℝ) * Real.exp t)
    have hSd (t : ℝ) : HasDerivAt S (D t) t := by
      apply HasDerivAt.fun_sum
      intro k _
      have hh := (hderiv ((k + 1 : ℝ) * Real.exp t) (by positivity)).comp t
        ((Real.hasDerivAt_exp t).const_mul (k + 1 : ℝ))
      convert hh using 1
      · rfl
      · ring
    have hSb (t : ℝ) (ht : 0 ≤ t) : 0 ≤ S t ∧ S t ≤ (j + 1 : ℝ) * C := by
      have hb (k : ℕ) : F ((k + 1 : ℝ) * Real.exp t) ∈ Icc (0 : ℝ) C := by
        apply hbound
        have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      refine ⟨Finset.sum_nonneg (fun k _ ↦ (hb k).1), ?_⟩
      have hh := Finset.sum_le_sum (s := Finset.range (j + 1)) (fun k _ ↦ (hb k).2)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one] using hh
    let a := (j + 1 : ℝ)
    let b := a + a ^ 2
    have ha : 0 < a := by dsimp only [a]; positivity
    have hab : a < b := by dsimp only [b]; nlinarith
    have hSc : Continuous S :=
      (show Differentiable ℝ S from fun t ↦ (hSd t).differentiableAt).continuous
    obtain ⟨s, hs, heq⟩ := exists_deriv_eq_slope S hab hSc.continuousOn
      (fun t _ ↦ (hSd t).differentiableAt.differentiableWithinAt)
    have hspos : 0 < s := ha.trans hs.1
    have hnum : S b - S a ≤ a * C := by
      have hb := hSb b (ha.le.trans hab.le)
      have hba := hSb a ha.le
      change S b - S a ≤ (j + 1 : ℝ) * C
      linarith
    have hsum : D s ≤ C / a := by
      calc
        D s = (S b - S a) / a ^ 2 := by
          rw [← (hSd s).deriv, heq]
          dsimp only [b]
          ring
        _ ≤ (a * C) / a ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
        _ = C / a := by field_simp
    refine ⟨Real.exp s, ?_, fun k hk ↦ ?_⟩
    · have he := Real.add_one_le_exp s
      change a ≤ Real.exp s
      linarith [hs.1]
    · have hkD : ((k + 1 : ℝ) * Real.exp s) * F' ((k + 1 : ℝ) * Real.exp s) ≤ D s := by
        dsimp only [D]
        apply Finset.single_le_sum (s := Finset.range (j + 1)) (a := k)
          (f := fun i : ℕ ↦ ((i + 1 : ℝ) * Real.exp s) * F' ((i + 1 : ℝ) * Real.exp s))
        · intro i _
          exact hnonneg _ (by positivity)
        · exact Finset.mem_range.mpr (by omega)
      exact hkD.trans hsum
  choose R hRlow hRbound using hselect
  have hR (j : ℕ) : 1 ≤ R j := (by norm_num : (1 : ℝ) ≤ j + 1).trans (hRlow j)
  have hRt : Tendsto R atTop atTop := tendsto_atTop_mono hRlow
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ⟨R, hR, hRt, fun k ↦ ?_⟩
  have hlim : Tendsto (fun j : ℕ ↦ C / (j + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun j ↦ hnonneg _
    (mul_pos (by positivity) (zero_lt_one.trans_le (hR j))))) _ hlim
  filter_upwards [eventually_ge_atTop k] with j hj
  exact hRbound j k hj

end SerrinEpigraph
