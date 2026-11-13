module

public import SerrinEpigraph.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

/-!
# The final growth contradiction for the monotonicity argument

These lemmas concern real-valued mass functions independently of the PDE estimates.
-/

public section

open Filter

namespace SerrinEpigraph

/-- A zero extended-real lower limit excludes an eventual positive lower bound. -/
theorem not_eventually_pos_le_of_liminf_zero {q : ℝ → ℝ} {c : ℝ}
    (hq : Filter.liminf (fun R ↦ (q R : EReal)) atTop = 0) (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, c ≤ q R := by
  intro h
  have hle : (c : EReal) ≤ Filter.liminf (fun R ↦ (q R : EReal)) atTop := by
    rw [Filter.liminf_eq]
    exact le_sSup (h.mono fun R hR ↦ EReal.coe_le_coe_iff.mpr hR)
  rw [hq] at hle
  exact (not_le_of_gt hc) (by exact_mod_cast hle)

/-- Subexponential lower mass growth excludes an eventual exponential lower bound. -/
theorem not_eventually_exponential_lowerBound {V : ℝ → ℝ} {μ c : ℝ}
    (hV : Filter.liminf (fun R ↦ ((Real.log (1 + V R) / R : ℝ) : EReal)) atTop = 0)
    (hμ : 0 < μ) (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, μ * Real.exp (c * R) ≤ V R := by
  intro h
  apply not_eventually_pos_le_of_liminf_zero hV (half_pos hc)
  filter_upwards [h, eventually_gt_atTop 0,
    eventually_ge_atTop (-2 * Real.log μ / c)] with R hR hRpos hRlarge
  have hlog : Real.log μ + c * R ≤ Real.log (1 + V R) := by
    calc
      Real.log μ + c * R = Real.log (μ * Real.exp (c * R)) := by
        rw [Real.log_mul (ne_of_gt hμ) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      _ ≤ Real.log (1 + V R) :=
        Real.log_le_log (mul_pos hμ (Real.exp_pos _)) (by linarith)
  have hlarge : -2 * Real.log μ ≤ R * c := (div_le_iff₀ hc).mp hRlarge
  exact (le_div_iff₀ hRpos).mpr (by nlinarith)

private theorem two_pow_mul_le_of_moment_aux {μ a V : ℝ} {k : ℕ} (ha : 0 < a)
    (hmoment : μ * a ^ k ≤ (a / 2) ^ k * V) : μ * (2 : ℝ) ^ k ≤ V := by
  apply (mul_le_mul_iff_right₀ (pow_pos ha k)).mp
  calc
    a ^ k * (μ * 2 ^ k) = (μ * a ^ k) * 2 ^ k := by ring
    _ ≤ ((a / 2) ^ k * V) * 2 ^ k :=
      mul_le_mul_of_nonneg_right hmoment (by positivity)
    _ = a ^ k * V := by rw [div_pow]; field_simp

private theorem exp_le_two_pow_floor_aux {t : ℝ} (ht : 3 ≤ t) :
    Real.exp (t / 2 * Real.log 2) ≤ (2 : ℝ) ^ ⌊t⌋₊ := by
  have hk_lower : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one t
    linarith
  calc
    _ ≤ Real.exp ((⌊t⌋₊ : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk_lower
        (Real.log_pos (by norm_num)).le)
    _ = (2 : ℝ) ^ ⌊t⌋₊ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

private theorem exponential_lowerBound_of_moments_aux {V : ℝ → ℝ} {μ a C R : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < a) (hC : 0 < C) (hR : 0 < R)
    (hRlarge : 6 * C / a ≤ R)
    (hV : 0 ≤ V (2 * R))
    (hmom : ∀ k : ℕ, 3 ≤ k → μ * a ^ k ≤ (C * k / R) ^ k * V (2 * R)) :
    μ * Real.exp (a * Real.log 2 / (4 * C) * R) ≤ V (2 * R) := by
  let t := a * R / (2 * C)
  let k := ⌊t⌋₊
  have ht : 3 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ (by positivity : 0 < 2 * C)).mpr
    have := (div_le_iff₀ ha).mp hRlarge
    nlinarith
  have hk : 3 ≤ k := Nat.le_floor ht
  have hk_upper : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hratio : C * k / R ≤ a / 2 := by
    apply (div_le_iff₀ hR).mpr
    have := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hk_upper
    nlinarith
  have hmoment : μ * a ^ k ≤ (a / 2) ^ k * V (2 * R) :=
    (hmom k hk).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hratio k) hV)
  have hpow := two_pow_mul_le_of_moment_aux ha hmoment
  have hexp : Real.exp (a * Real.log 2 / (4 * C) * R) ≤ (2 : ℝ) ^ k := by
    convert exp_le_two_pow_floor_aux ht using 1
    congr 1
    dsimp [t]
    ring
  exact (mul_le_mul_of_nonneg_left hexp hμ).trans hpow

/-- The all-orders moment estimate forces a nonpositive local descent rate. -/
theorem nonpos_of_moment_estimates {V : ℝ → ℝ} {μ a C : ℝ}
    (hVnonneg : ∀ R, 0 ≤ V R)
    (hV : Filter.liminf (fun R ↦ ((Real.log (1 + V R) / R : ℝ) : EReal)) atTop = 0)
    (hμ : 0 < μ) (hC : 0 < C)
    (hmom : ∀ᶠ R in atTop, ∀ k : ℕ, 3 ≤ k →
      μ * a ^ k ≤ (C * k / R) ^ k * V (2 * R)) : a ≤ 0 := by
  by_contra! ha
  apply not_eventually_exponential_lowerBound hV hμ
    (show 0 < a * Real.log 2 / (8 * C) by
      exact div_pos (mul_pos ha (Real.log_pos (by norm_num))) (by positivity))
  have hmom_half : ∀ᶠ R in atTop, ∀ k : ℕ, 3 ≤ k →
      μ * a ^ k ≤ (C * k / (R / 2)) ^ k * V (2 * (R / 2)) :=
    (tendsto_id.atTop_div_const (by norm_num : 0 < (2 : ℝ))).eventually hmom
  filter_upwards [hmom_half, eventually_gt_atTop 0,
    eventually_ge_atTop (12 * C / a)] with R hmoment hR hRlarge
  have hbound := exponential_lowerBound_of_moments_aux hμ.le ha hC
    (half_pos hR) (show 6 * C / a ≤ R / 2 by
      calc
        _ = (12 * C / a) / 2 := by ring
        _ ≤ R / 2 := div_le_div_of_nonneg_right hRlarge (by norm_num))
    (hVnonneg _) hmoment
  have harg : a * Real.log 2 / (8 * C) * R =
      a * Real.log 2 / (4 * C) * (R / 2) := by ring
  simpa only [harg, mul_div_cancel₀ R (by norm_num : (2 : ℝ) ≠ 0)] using hbound

end SerrinEpigraph
