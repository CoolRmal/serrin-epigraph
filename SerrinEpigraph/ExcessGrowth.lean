module

public import SerrinEpigraph.CoerciveEstimate
public import SerrinEpigraph.FixedWidthCutoff

/-!
# Growth of the squared positive excess

A coercive reaction tail forces fixed-width growth of every nonzero excess mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Squared positive excess on a bounded truncation of the epigraph. -/
def excessMass {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (s R : ℝ) : ℝ :=
  ∫ x in epigraph g ∩ Metric.ball 0 R, excess u s x ^ 2

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ s : ℝ}

theorem excessMass_nonneg (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (s R : ℝ) :
    0 ≤ excessMass g u s R := integral_nonneg (fun x ↦ sq_nonneg (excess u s x))

theorem monotone_excessMass (h : Hypotheses g u f κ) : Monotone (excessMass g u s) := by
  intro R S hRS
  exact setIntegral_mono_set (integrableOn_excess_sq_epigraph_inter_ball h S)
    (Eventually.of_forall fun x ↦ sq_nonneg (excess u s x))
    (Eventually.of_forall fun x hx ↦ ⟨hx.1, Metric.ball_subset_ball hRS hx.2⟩)

theorem excessMass_le_squareMass (h : Hypotheses g u f κ) (hs : 0 ≤ s) (R : ℝ) :
    excessMass g u s R ≤ squareMass g u R := integral_excess_sq_le_squareMass h hs R

/-- A positive point of the excess gives positive squared mass on some positive-radius ball. -/
theorem exists_excessMass_pos (h : Hypotheses g u f κ) {x : Space (m + 1)}
    (hx : x ∈ epigraph g) (hxs : s < u x) : ∃ R, 0 < R ∧ 0 < excessMass g u s R := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hc := (h.solution_contDiffOn.continuousOn x hx).continuousAt (hΩ.mem_nhds hx)
  have hmem : ∀ᶠ y in 𝓝 x, y ∈ epigraph g := hΩ.mem_nhds hx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ epigraph g ∧ s < u y :=
    hmem.and (hc (isOpen_Ioi.mem_nhds hxs))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hsub : Metric.ball x r ⊆ epigraph g ∩ Metric.ball 0 (r + dist x 0) :=
    fun y hy ↦ ⟨(hball hy).1, Metric.ball_subset_ball' (le_refl _) hy⟩
  have hi := integrableOn_excess_sq_epigraph_inter_ball (s₀ := s) h (r + dist x 0)
  have hpos : 0 < ∫ y in Metric.ball x r, excess u s y ^ 2 := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun y ↦ sq_nonneg (excess u s y)) (hi.mono_set hsub)).mpr
    have heq : Function.support (fun y ↦ excess u s y ^ 2) ∩ Metric.ball x r =
        Metric.ball x r := by
      apply Set.inter_eq_self_of_subset_right
      intro y hy
      exact ne_of_gt (sq_pos_of_pos (lt_of_lt_of_le
        (sub_pos.mpr (hball hy).2) (le_max_left _ _)))
    rw [heq]
    exact Metric.measure_ball_pos volume x hr
  refine ⟨r + dist x 0, add_pos_of_pos_of_nonneg hr dist_nonneg, hpos.trans_le ?_⟩
  exact setIntegral_mono_set hi (Eventually.of_forall fun y ↦ sq_nonneg (excess u s y))
    (Eventually.of_forall fun y hy ↦ hsub hy)

/-- A cutoff equal to one on a ball dominates the mass in that ball. -/
theorem excessMass_le_cutoffIntegral (h : Hypotheses g u f κ) (hs : 0 < s)
    {η : Space (m + 1) → ℝ} {R : ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηone : ∀ x ∈ Metric.ball 0 R, η x = 1) :
    excessMass g u s R ≤ ∫ x in epigraph g, excess u s x ^ 2 * η x ^ 2 := by
  have hΩ := (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  have hc2 : HasCompactSupport (fun x ↦ η x ^ 2) :=
    hηc.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hi := (integrable_indicator_iff hΩ).mp
    (integrable_indicator_excess_pow_mul (k := 2) h hs (by norm_num) (hη.pow 2) hc2)
  calc
    _ = ∫ x in epigraph g ∩ Metric.ball 0 R, excess u s x ^ 2 * η x ^ 2 := by
      apply setIntegral_congr_fun (hΩ.inter measurableSet_ball)
      intro x hx
      simp only [hηone x hx.2, one_pow, mul_one]
    _ ≤ _ := setIntegral_mono_set hi
      (Eventually.of_forall fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Eventually.of_forall fun _ hx ↦ hx.1)

/-- A gradient bound and bounded cutoff support control the error by the outer excess mass. -/
theorem excess_gradient_error_le_mass (h : Hypotheses g u f κ) (hs : 0 < s)
    {η : Space (m + 1) → ℝ} {S B : ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hsupp : tsupport η ⊆ Metric.ball 0 S) (hderiv : ∀ x, ‖gradient η x‖ ≤ B) :
    (∫ x in epigraph g, excess u s x ^ 2 * ‖gradient η x‖ ^ 2) ≤
      B ^ 2 * excessMass g u s S := by
  have hΩ := (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  have hmass := (integrable_indicator_iff (hΩ.inter measurableSet_ball)).mpr
    (integrableOn_excess_sq_epigraph_inter_ball (s₀ := s) h S)
  have hcomp := integral_mono (integrable_indicator_excess_sq_gradient_error h hs hη hηc)
    (hmass.const_mul (B ^ 2)) (show ∀ x,
      (epigraph g).indicator (fun y ↦ excess u s y ^ 2 * ‖gradient η y‖ ^ 2) x ≤
        B ^ 2 * (epigraph g ∩ Metric.ball 0 S).indicator (fun y ↦ excess u s y ^ 2) x by
      intro x
      by_cases hx : x ∈ epigraph g
      · by_cases hxS : x ∈ Metric.ball 0 S
        · have hxi : x ∈ epigraph g ∩ Metric.ball 0 S := ⟨hx, hxS⟩
          simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxi]
          simpa only [mul_comm (B ^ 2)] using mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hderiv x) 2) (sq_nonneg (excess u s x))
        · have hxη : x ∉ tsupport η := fun hh ↦ hxS (hsupp hh)
          have hxi : x ∉ epigraph g ∩ Metric.ball 0 S := fun hh ↦ hxS hh.2
          simp [Set.indicator_of_mem hx, Set.indicator_of_notMem hxi,
            gradient, fderiv_of_notMem_tsupport ℝ hxη]
      · have hxi : x ∉ epigraph g ∩ Metric.ball 0 S := fun hh ↦ hx hh.1
        simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxi, mul_zero, le_refl])
  simpa only [integral_indicator hΩ, integral_const_mul,
    integral_indicator (hΩ.inter measurableSet_ball), excessMass] using hcomp

/-- The weak coercive estimate gives a bound between inner and outer squared excess masses. -/
theorem Hypotheses.excessMass_cutoff_bound (h : Hypotheses g u f κ) (hs : 0 < s)
    {η : Space (m + 1) → ℝ} {R S B c : ℝ} (hc : 0 ≤ c)
    (htail : ∀ x ∈ epigraph g, s < u x → f (u x) ≤ -c * u x)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηone : ∀ x ∈ Metric.ball 0 R, η x = 1)
    (hsupp : tsupport η ⊆ Metric.ball 0 S) (hderiv : ∀ x, ‖gradient η x‖ ≤ B) :
    c * excessMass g u s R ≤ B ^ 2 * excessMass g u s S := by
  exact (mul_le_mul_of_nonneg_left
    (excessMass_le_cutoffIntegral h hs hη.continuous hηc hηone) hc).trans
    ((h.excess_coercive_estimate hs hc htail hη hηc).trans
      (excess_gradient_error_le_mass h hs hη hηc hsupp hderiv))

/-- Uniform fixed-width cutoffs force doubling after choosing one sufficiently wide collar. -/
theorem Hypotheses.exists_excessMass_doubling_of_cutoffs (h : Hypotheses g u f κ)
    (hs : 0 < s) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (htail : ∀ x ∈ epigraph g, s < u x → f (u x) ≤ -c * u x)
    (hcutoffs : ∀ R : ℝ, 0 < R → ∀ L : ℝ, 0 < L → ∃ η : Space (m + 1) → ℝ,
      ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
      (∀ x ∈ Metric.ball 0 R, η x = 1) ∧ tsupport η ⊆ Metric.ball 0 (R + L) ∧
      ∀ x, ‖gradient η x‖ ≤ C / L) :
    ∃ L : ℝ, 0 < L ∧ ∀ R : ℝ, 0 < R →
      2 * excessMass g u s R ≤ excessMass g u s (R + L) := by
  let L := 2 * C / Real.sqrt c
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hL : 0 < L := div_pos (by positivity) hsqrt
  have hB : (C / L) ^ 2 = c / 4 := by
    dsimp [L]
    rw [div_div_eq_mul_div, mul_comm 2 C, mul_div_mul_left _ _ hC.ne']
    rw [div_pow, Real.sq_sqrt hc.le]
    norm_num
  refine ⟨L, hL, fun R hR ↦ ?_⟩
  obtain ⟨η, hη, hηc, hηone, hsupp, hderiv⟩ := hcutoffs R hR L hL
  have hh := h.excessMass_cutoff_bound hs hc.le htail hη hηc hηone hsupp hderiv
  rw [hB] at hh
  have hp := excessMass_nonneg g u s (R + L)
  nlinarith

/-- A strictly coercive reaction tail forces squared excess to double at a fixed radial step. -/
theorem Hypotheses.exists_excessMass_doubling (h : Hypotheses g u f κ)
    (hs : 0 < s) {c : ℝ} (hc : 0 < c)
    (htail : ∀ x ∈ epigraph g, s < u x → f (u x) ≤ -c * u x) :
    ∃ L : ℝ, 0 < L ∧ ∀ R : ℝ, 0 < R →
      2 * excessMass g u s R ≤ excessMass g u s (R + L) := by
  obtain ⟨C, hC, hcutoffs⟩ := exists_fixedWidth_ball_cutoffs
  apply h.exists_excessMass_doubling_of_cutoffs hs hc hC htail
  intro R hR L hL
  obtain ⟨η, hη, hηc, hsupp, hηone, _, hderiv⟩ := hcutoffs (m + 1) R L hR hL
  exact ⟨η, hη, hηc, hηone, hsupp, hderiv⟩

end SerrinEpigraph
