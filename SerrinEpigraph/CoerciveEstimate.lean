module

public import SerrinEpigraph.PowerEnergy
public import SerrinEpigraph.SmoothExcess
public import SerrinEpigraph.Excess
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Coercive estimates for positive excesses

Smooth positive-part approximations allow the weak equation to be tested without assuming a
second derivative of the positive part. The estimates retain the square-mass error density.
-/

public section

open MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- Completing a square controls the cross term of a smooth truncation by the squared excess. -/
theorem truncation_gradient_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a T w η : ℝ} (ha : 0 ≤ a) (hT : T ^ 2 ≤ a * w ^ 2)
    (X Y : E) :
    0 ≤ a * η ^ 2 * ‖X‖ ^ 2 + 2 * T * η * inner ℝ X Y + w ^ 2 * ‖Y‖ ^ 2 := by
  rcases eq_or_lt_of_le ha with ha | ha
  · have hzero : T = 0 := by nlinarith [sq_nonneg T]
    simp only [← ha, hzero, zero_mul, mul_zero, zero_add]
    positivity
  · have hs := sq_nonneg ‖(a * η) • X + T • Y‖
    rw [norm_smul_add_smul_sq] at hs
    have hb := mul_le_mul_of_nonneg_right hT (sq_nonneg ‖Y‖)
    have hp : 0 ≤ a *
        (a * η ^ 2 * ‖X‖ ^ 2 + 2 * T * η * inner ℝ X Y + w ^ 2 * ‖Y‖ ^ 2) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right hp ha

/-- The chain and product rules for a smooth excess test. -/
theorem gradient_comp_sub_mul_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {T : ℝ → ℝ} {u η : E → ℝ} {x : E}
    {s a : ℝ} (hT : HasDerivAt T a (u x - s))
    (hu : DifferentiableAt ℝ u x) (hη : DifferentiableAt ℝ η x) :
    gradient (fun y ↦ T (u y - s) * η y ^ 2) x =
      (η x ^ 2 * a) • gradient u x + (T (u x - s) * (2 * η x)) • gradient η x := by
  have ht := hT.comp_hasFDerivAt x (hu.hasFDerivAt.sub_const s)
  have hd := ht.mul (hη.hasFDerivAt.pow 2)
  have heq : fderiv ℝ (fun y ↦ T (u y - s) * η y ^ 2) x =
      (η x ^ 2 * a) • fderiv ℝ u x +
        (T (u x - s) * (2 * η x)) • fderiv ℝ η x := by
    simpa only [Function.comp_def, Pi.mul_def, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, smul_smul, smul_eq_mul, nsmul_eq_mul, mul_assoc, add_comm] using hd.fderiv
  simp only [gradient, heq, map_add, map_smul]

/-- The weak equation closes a smooth truncation estimate against its squared-excess error. -/
theorem Hypotheses.coercive_estimate_of_test {m : ℕ} {g : Space m → ℝ}
    {u η : Space (m + 1) → ℝ} {f T : ℝ → ℝ} {κ s c : ℝ}
    (h : Hypotheses g u f κ) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hT : ContDiff ℝ 1 T) (hT0 : ∀ t, 0 ≤ T t)
    (hTle : ∀ t, T t ≤ max t 0) (ha : ∀ t, 0 ≤ deriv T t)
    (hTa : ∀ t, T t ^ 2 ≤ deriv T t * max t 0 ^ 2)
    (htail : ∀ x ∈ epigraph g, s < u x → f (u x) ≤ -c * u x)
    (hη : ContDiff ℝ 1 η)
    (hφ : ContDiff ℝ 1 ((epigraph g).indicator (fun x ↦ T (u x - s) * η x ^ 2)))
    (hφc : HasCompactSupport ((epigraph g).indicator (fun x ↦ T (u x - s) * η x ^ 2)))
    (hφs : tsupport ((epigraph g).indicator (fun x ↦ T (u x - s) * η x ^ 2)) ⊆ epigraph g)
    (hE : Integrable ((epigraph g).indicator
      (fun x ↦ max (u x - s) 0 ^ 2 * ‖gradient η x‖ ^ 2))) :
    c * (∫ x in epigraph g, T (u x - s) ^ 2 * η x ^ 2) ≤
      ∫ x in epigraph g, max (u x - s) 0 ^ 2 * ‖gradient η x‖ ^ 2 := by
  let φ := (epigraph g).indicator (fun x ↦ T (u x - s) * η x ^ 2)
  let L := fun x ↦ T (u x - s) * φ x
  let E := (epigraph g).indicator (fun x ↦ max (u x - s) 0 ^ 2 * ‖gradient η x‖ ^ 2)
  let Q := fun x ↦ inner ℝ (gradient u x) (gradient φ x)
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hu : ContDiffOn ℝ 1 u (epigraph g) := h.solution_contDiffOn.of_le (by norm_num)
  have hL : Integrable L := integrable_mul_of_tsupport_subset (μ := volume)
    (hT.continuous.comp_continuousOn (hu.continuousOn.sub continuousOn_const))
    hφ.continuous hφc hφs
  have hQ : Integrable Q := integrable_inner_gradient_of_hasCompactSupport
    hΩ hu hφ hφc hφs
  have hF : Integrable (fun x ↦ f (u x) * φ x) :=
    integrable_mul_of_tsupport_subset (μ := volume)
      (h.reaction_contDiffOn.continuousOn.comp hu.continuousOn
        (fun x hx ↦ (h.positive x hx).le)) hφ.continuous hφc hφs
  have hpoint (x : Space (m + 1)) : -E x ≤ Q x := by
    by_cases hx : x ∈ epigraph g
    · have hux := (hu.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      have htx := (hT.differentiable_one (u x - s)).hasDerivAt
      have hp := truncation_gradient_nonneg (ha (u x - s)) (hTa (u x - s))
        (η := η x) (gradient u x) (gradient η x)
      dsimp only [Q, E, φ]
      rw [Set.indicator_of_mem hx, gradient_indicator_of_mem hΩ hx,
        gradient_comp_sub_mul_sq htx hux (hη.differentiable_one x)]
      simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      nlinarith
    · have hxφ : x ∉ tsupport φ := fun hy ↦ hx (hφs hy)
      simp [Q, E, gradient, fderiv_of_notMem_tsupport ℝ hxφ,
        Set.indicator_of_notMem hx]
  have hreaction (x : Space (m + 1)) : c * L x ≤ -(f (u x) * φ x) := by
    by_cases hx : x ∈ epigraph g
    · by_cases hxs : s < u x
      · have hTu : T (u x - s) ≤ u x :=
          (hTle _).trans (max_le (sub_le_self _ hs) (h.positive x hx).le)
        have hφ0 : 0 ≤ φ x := by
          dsimp only [φ]
          rw [Set.indicator_of_mem hx]
          exact mul_nonneg (hT0 _) (sq_nonneg _)
        calc
          c * L x = (c * T (u x - s)) * φ x := by dsimp [L]; ring
          _ ≤ (c * u x) * φ x :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTu hc) hφ0
          _ ≤ (-f (u x)) * φ x := by
            apply mul_le_mul_of_nonneg_right _ hφ0
            linarith [htail x hx hxs]
          _ = -(f (u x) * φ x) := by ring
      · have hzero : T (u x - s) = 0 := by
          have hh := hTle (u x - s)
          rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hxs))] at hh
          exact le_antisymm hh (hT0 _)
        simp [L, φ, Set.indicator_of_mem hx, hzero]
    · simp [L, φ, Set.indicator_of_notMem hx]
  have hlow := integral_mono hE.neg hQ hpoint
  have hupp := integral_mono (hL.const_mul c) hF.neg hreaction
  change (∫ x, -E x) ≤ ∫ x, Q x at hlow
  change (∫ x, c * L x) ≤ ∫ x, -(f (u x) * φ x) at hupp
  rw [integral_neg] at hlow hupp
  rw [integral_const_mul] at hupp
  have hweak : (∫ x, Q x) = ∫ x, f (u x) * φ x := h.weak_equation hφ hφc hφs
  have hbound : c * (∫ x, L x) ≤ ∫ x, E x := by linarith
  have hLeq : L = (epigraph g).indicator (fun x ↦ T (u x - s) ^ 2 * η x ^ 2) := by
    funext x
    by_cases hx : x ∈ epigraph g
    · simp [L, φ, Set.indicator_of_mem hx, pow_two, mul_assoc]
    · simp [L, φ, Set.indicator_of_notMem hx]
  rw [hLeq, integral_indicator hΩ.measurableSet] at hbound
  simpa only [E, integral_indicator hΩ.measurableSet] using hbound

/-- Dominated convergence removes the smooth truncation without increasing its square-mass bound. -/
theorem integral_positivePart_sq_le_of_smoothExcess_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {t η : X → ℝ} {c B : ℝ}
    (ht : AEStronglyMeasurable t μ) (hη : AEStronglyMeasurable η μ)
    (hbound : Integrable (fun x ↦ max (t x) 0 ^ 2 * η x ^ 2) μ)
    (hineq : ∀ ε > 0, c * (∫ x, smoothExcess ε (t x) ^ 2 * η x ^ 2 ∂μ) ≤ B) :
    c * (∫ x, max (t x) 0 ^ 2 * η x ^ 2 ∂μ) ≤ B := by
  let ε := fun n : ℕ ↦ (1 : ℝ) / (n + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto
      (fun n ↦ ∫ x, smoothExcess (ε n) (t x) ^ 2 * η x ^ 2 ∂μ) atTop
      (𝓝 (∫ x, max (t x) 0 ^ 2 * η x ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x ↦ max (t x) 0 ^ 2 * η x ^ 2)
    · intro n
      exact (((contDiff_smoothExcess (hε n)).continuous.comp_aestronglyMeasurable ht).pow 2).mul
        (hη.pow 2)
    · exact hbound
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (smoothExcess_nonneg (hε n) _) (smoothExcess_le_positivePart (hε n) _) 2)
        (sq_nonneg _)
    · filter_upwards with x
      exact (((tendsto_smoothExcess_zero (t x)).comp hεlim).pow 2).mul tendsto_const_nhds
  exact le_of_tendsto (hlim.const_mul c) (Eventually.of_forall fun n ↦ hineq (ε n) (hε n))

/-- A negative linear reaction tail controls the squared excess by the cutoff gradient error. -/
theorem Hypotheses.excess_coercive_estimate {m : ℕ} {g : Space m → ℝ}
    {u η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ s c : ℝ}
    (h : Hypotheses g u f κ) (hs : 0 < s) (hc : 0 ≤ c)
    (htail : ∀ x ∈ epigraph g, s < u x → f (u x) ≤ -c * u x)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    c * (∫ x in epigraph g, excess u s x ^ 2 * η x ^ 2) ≤
      ∫ x in epigraph g, excess u s x ^ 2 * ‖gradient η x‖ ^ 2 := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hc2 : HasCompactSupport (fun x ↦ η x ^ 2) :=
    hηc.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hbound := integrable_indicator_excess_pow_mul h hs (k := 2) (by norm_num)
    (hη.continuous.pow 2) hc2
  have hE := integrable_indicator_excess_sq_gradient_error h hs hη hηc
  apply integral_positivePart_sq_le_of_smoothExcess_bounds
    ((h.solution_contDiffOn.continuousOn.sub continuousOn_const).aestronglyMeasurable
      hΩ.measurableSet) hη.continuous.aestronglyMeasurable
    ((integrable_indicator_iff hΩ.measurableSet).mp hbound)
  intro ε hε
  obtain ⟨hφc, hφs⟩ := hasCompactSupport_indicator_smoothExcess_mul h hs ε hc2
  apply h.coercive_estimate_of_test hs.le hc (contDiff_smoothExcess hε)
    (smoothExcess_nonneg hε) (smoothExcess_le_positivePart hε) _ _ htail hη
    (contDiff_indicator_smoothExcess_mul h hs hε (hη.pow 2) hc2) hφc hφs hE
  · intro t
    rw [(hasDerivAt_smoothExcess hε t).deriv]
    exact smoothExcessSlope_nonneg hε t
  · intro t
    rw [(hasDerivAt_smoothExcess hε t).deriv]
    exact smoothExcess_sq_le_slope_mul_sq hε t

end SerrinEpigraph
