module

public import SerrinEpigraph.WeakComparison
public import SerrinEpigraph.WeakQuotient

/-!
# Converting a linearized equation into weak supersolutions
-/

public section

open MeasureTheory InnerProductSpace
open scoped Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Weak supersolutions restrict to smaller open test domains. -/
theorem IsWeakSupersolution.mono {Ω Ω' : Set E} {M : ℝ} {v : E → ℝ}
    (h : IsWeakSupersolution μ Ω M v) (hsub : Ω' ⊆ Ω) :
    IsWeakSupersolution μ Ω' M v := by
  intro φ hφ hc hs hφ0
  exact h φ hφ hc (hs.trans hsub) hφ0

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Values outside the open domain do not affect the weak supersolution inequality. -/
theorem IsWeakSupersolution.congr_on {Ω : Set E} {M : ℝ} {v w : E → ℝ}
    (h : IsWeakSupersolution μ Ω M v) (hΩ : IsOpen Ω) (heq : Set.EqOn v w Ω) :
    IsWeakSupersolution μ Ω M w := by
  intro φ hφ hc hs hφ0
  have hint : (∫ x, inner ℝ (gradient v x) (gradient φ x) + M * v x * φ x ∂μ) =
      ∫ x, inner ℝ (gradient w x) (gradient φ x) + M * w x * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω
    · have hev : v =ᶠ[nhds x] w := by
        filter_upwards [hΩ.mem_nhds hx] with y hy
        exact heq hy
      rw [hev.gradient_eq, heq hx]
    · have hout : x ∉ tsupport φ := fun hy ↦ hx (hs hy)
      have hz : φ x = 0 := Function.notMem_support.mp fun hy ↦ hout (subset_tsupport φ hy)
      simp [hz, gradient, fderiv_of_notMem_tsupport ℝ hout]
  rw [← hint]
  exact h φ hφ hc hs hφ0

/-- A nonnegative weak solution is a supersolution after increasing the zeroth-order term. -/
theorem isWeakSupersolution_of_weak_equation {Ω : Set E} {v a : E → ℝ} {M : ℝ}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 1 v Ω) (ha : ContinuousOn a Ω)
    (hv0 : ∀ x ∈ Ω, 0 ≤ v x) (hM : ∀ x ∈ Ω, 0 ≤ a x + M)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, inner ℝ (gradient v x) (gradient φ x) ∂μ) = ∫ x, a x * v x * φ x ∂μ) :
    IsWeakSupersolution μ Ω M v := by
  intro φ hφ hc hs hφ0
  have hpair := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ hv hφ hc hs
  have hmul : Integrable (fun x ↦ M * v x * φ x) μ := integrable_mul_of_tsupport_subset
    (continuousOn_const.mul hv.continuousOn) hφ.continuous hc hs
  have hsrc : Integrable (fun x ↦ a x * v x * φ x) μ := integrable_mul_of_tsupport_subset
    (ha.mul hv.continuousOn) hφ.continuous hc hs
  rw [integral_add hpair hmul, heq φ hφ hc hs, ← integral_add hsrc hmul]
  apply integral_nonneg
  intro x
  change (0 : ℝ) ≤ a x * v x * φ x + M * v x * φ x
  by_cases hx : x ∈ Ω
  · have hh := mul_nonneg (mul_nonneg (hM x hx) (hv0 x hx)) (hφ0 x)
    nlinarith
  · have hz : φ x = 0 := Function.notMem_support.mp fun hy ↦ hx (hs (subset_tsupport φ hy))
    simp [hz]

/-- Subtracting a classical subsolution and adding a nonnegative constant preserves comparison. -/
theorem IsWeakSupersolution.sub_classical_add_const {Ω : Set E} {v b : E → ℝ} {M δ : ℝ}
    (hweak : IsWeakSupersolution μ Ω M v) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hb : ContDiffOn ℝ 2 b Ω)
    (hbsub : ∀ x ∈ Ω, -(Δ b) x + M * b x ≤ 0) (hδ : 0 ≤ M * δ) :
    IsWeakSupersolution μ Ω M (fun x ↦ v x - b x + δ) := by
  intro φ hφ hc hs hφ0
  have hgrad (x : E) :
      inner ℝ (gradient (fun y ↦ v y - b y + δ) x) (gradient φ x) =
        inner ℝ (gradient v x) (gradient φ x) -
          inner ℝ (gradient b x) (gradient φ x) := by
    by_cases hx : x ∈ Ω
    · have hdv := (hv.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
      have hdb := ((hb.of_le (by norm_num)).differentiableOn_one x hx).differentiableAt
        (hΩ.mem_nhds hx)
      have hd := (hdv.hasFDerivAt.sub hdb.hasFDerivAt).add_const δ
      have heq : fderiv ℝ (fun y ↦ v y - b y + δ) x = fderiv ℝ v x - fderiv ℝ b x := by
        simpa only [Pi.sub_def] using hd.fderiv
      simp only [gradient, heq, map_sub, inner_sub_left]
    · have hout : x ∉ tsupport φ := fun hy ↦ hx (hs hy)
      simp only [gradient, fderiv_of_notMem_tsupport ℝ hout, map_zero, inner_zero_right,
        sub_self]
  have hvpair := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ hv hφ hc hs
  have hbpair := integrable_inner_gradient_of_hasCompactSupport (μ := μ) hΩ
    (hb.of_le (by norm_num)) hφ hc hs
  have hvmul : Integrable (fun x ↦ M * v x * φ x) μ := integrable_mul_of_tsupport_subset
    (continuousOn_const.mul hv.continuousOn) hφ.continuous hc hs
  have hbmul : Integrable (fun x ↦ M * b x * φ x) μ := integrable_mul_of_tsupport_subset
    (continuousOn_const.mul hb.continuousOn) hφ.continuous hc hs
  have hφint := hφ.continuous.integrable_of_hasCompactSupport hc (μ := μ)
  have hdelt := hφint.const_mul (M * δ)
  have hblap : Integrable (fun x ↦ -((Δ b) x * φ x)) μ := by
    simpa only [Pi.neg_def] using
      (integrable_laplacian_mul_of_hasCompactSupport (μ := μ) hΩ hb hφ hc hs).neg
  have hbpde : (∫ x, inner ℝ (gradient b x) (gradient φ x) + M * b x * φ x ∂μ) ≤ 0 := by
    rw [integral_add hbpair hbmul,
      integral_inner_gradient_eq_neg_laplacian_mul hΩ hb hφ hc hs, ← integral_neg,
      ← integral_add hblap hbmul]
    apply integral_nonpos
    intro x
    change -((Δ b) x * φ x) + M * b x * φ x ≤ (0 : ℝ)
    by_cases hx : x ∈ Ω
    · have hh := mul_nonpos_of_nonpos_of_nonneg (hbsub x hx) (hφ0 x)
      nlinarith
    · have hz : φ x = 0 := Function.notMem_support.mp fun hy ↦ hx (hs (subset_tsupport φ hy))
      simp [hz]
  have hδint : 0 ≤ ∫ x, M * δ * φ x ∂μ :=
    integral_nonneg fun x ↦ mul_nonneg hδ (hφ0 x)
  have hpoint (x : E) :
      inner ℝ (gradient (fun y ↦ v y - b y + δ) x) (gradient φ x) +
          M * (v x - b x + δ) * φ x =
        (inner ℝ (gradient v x) (gradient φ x) + M * v x * φ x) -
          (inner ℝ (gradient b x) (gradient φ x) + M * b x * φ x) + M * δ * φ x := by
    rw [hgrad]
    ring
  simp_rw [hpoint]
  have hvi : Integrable (fun x ↦ inner ℝ (gradient v x) (gradient φ x) + M * v x * φ x) μ := by
    simpa only [Pi.add_def] using hvpair.add hvmul
  have hbi : Integrable (fun x ↦ inner ℝ (gradient b x) (gradient φ x) + M * b x * φ x) μ := by
    simpa only [Pi.add_def] using hbpair.add hbmul
  have hdiff : Integrable (fun x ↦
      (inner ℝ (gradient v x) (gradient φ x) + M * v x * φ x) -
        (inner ℝ (gradient b x) (gradient φ x) + M * b x * φ x)) μ := by
    simpa only [Pi.sub_def] using hvi.sub hbi
  rw [integral_add hdiff hdelt, integral_sub hvi hbi]
  have hvtest := hweak φ hφ hc hs hφ0
  linarith

end SerrinEpigraph
