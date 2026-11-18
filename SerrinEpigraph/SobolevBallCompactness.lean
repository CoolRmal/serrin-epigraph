module

public import SerrinEpigraph.LipschitzMollificationDerivative
public import SerrinEpigraph.SegmentGradientEstimate
public import SerrinEpigraph.WeakEquation
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Poincaré inequalities and Rellich compactness on Euclidean balls

For globally Lipschitz functions `f : Space d → ℝ` the gradient is the almost-everywhere
derivative `fderiv ℝ f` given by Rademacher's theorem. Constants depend only on the dimension.

* `integral_sq_translate_sub_le`: `∫_S |f(y+h) - f(y)|² ≤ |h|² ∫_T |∇f|²` whenever the segments
  `[y, y+h]`, `y ∈ S`, lie in `T`.
* `poincare_ball`, `exists_poincare_constant`: `∫_{B_r} |f - f_{B_r}|² ≤ 2^(d+1) r² ∫_{B_r} |∇f|²`;
  `poincare_ball_of_subball`: the same with the average over a concentric sub-ball.
* `integral_sq_convolution_sub_le`, `integral_sq_mollify_sub_le`: the `L²(B_r)` mollification
  error at scale `ε` is at most `ε² ∫_{B_{r+ε}} |∇f|²`.
* `exists_subseq_tendsto_sq_integral_ball`: Rellich compactness in `L²(B_r)`, `r < R`, for
  Lipschitz sequences with bounded `W^{1,2}(B_R)` energy.
* `integral_inner_gradient_eq_neg_integral_mul_laplacian_of_lipschitz`: Green's identity for
  Lipschitz functions; `integral_mul_laplacian_eq_zero_of_sq_tendsto`,
  `weakHarmonic_of_sq_tendsto`, `exists_subseq_tendsto_weakHarmonic`: weak harmonicity passes to
  `L²` limits, in the form used by Weyl's lemma.
* `eventually_integral_norm_fderiv_sq_le`, `integral_norm_fderiv_sq_le_liminf`,
  `integral_norm_fderiv_sq_le_of_bound`: lower semicontinuity of the Dirichlet energy.
* `tendsto_setAverage_ball_of_sq_tendsto`: averages over balls converge along `L²` limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric ContinuousLinearMap InnerProductSpace
open scoped Topology Convolution Laplacian BoundedContinuousFunction

namespace SerrinEpigraph

/-! ### Elementary integral inequalities -/

/-- Weighted Jensen inequality for squares: a probability weight `w` satisfies
`(∫ w g)² ≤ ∫ w g²`. -/
theorem sq_integral_mul_le_integral_mul_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w g : X → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x ∂μ = 1) (hw : Integrable w μ)
    (hwg : Integrable (fun x ↦ w x * g x) μ) (hwg2 : Integrable (fun x ↦ w x * g x ^ 2) μ) :
    (∫ x, w x * g x ∂μ) ^ 2 ≤ ∫ x, w x * g x ^ 2 ∂μ := by
  set c := ∫ x, w x * g x ∂μ with hc
  have hpt : ∀ x, 2 * c * (w x * g x) - c ^ 2 * w x ≤ w x * g x ^ 2 := by
    intro x
    have h := mul_nonneg (hw0 x) (sq_nonneg (g x - c))
    nlinarith
  have hint : Integrable (fun x ↦ 2 * c * (w x * g x) - c ^ 2 * w x) μ :=
    (hwg.const_mul _).sub (hw.const_mul _)
  have hmono := integral_mono hint hwg2 hpt
  rw [integral_sub (hwg.const_mul _) (hw.const_mul _), integral_const_mul,
    integral_const_mul, hw1, ← hc] at hmono
  nlinarith

/-- The Cauchy–Schwarz inequality `(∫ g)² ≤ μ(X) ∫ g²` on a finite measure space. -/
theorem sq_integral_le_measureReal_mul_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun x ↦ g x ^ 2) μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, g x ^ 2 ∂μ := by
  set m := μ.real Set.univ with hm_def
  set A := ∫ x, g x ∂μ with hA
  set Q := ∫ x, g x ^ 2 ∂μ with hQ
  have hm : 0 ≤ m := measureReal_nonneg
  rcases hm.eq_or_lt with h0 | hpos
  · have hu : μ Set.univ = 0 := by
      have h0' : μ.real Set.univ = 0 := h0.symm
      rwa [measureReal_eq_zero_iff (measure_ne_top μ _)] at h0'
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp hu
    have hA0 : A = 0 := by simp [hA, hμ]
    rw [hA0, ← h0]
    simp
  · have hpt : ∀ x, 2 * (A / m) * g x - (A / m) ^ 2 ≤ g x ^ 2 := by
      intro x
      nlinarith [sq_nonneg (g x - A / m)]
    have hint : Integrable (fun x ↦ 2 * (A / m) * g x - (A / m) ^ 2) μ :=
      (hg.const_mul _).sub (integrable_const _)
    have hmono := integral_mono hint hg2 hpt
    rw [integral_sub (hg.const_mul _) (integrable_const _), integral_const_mul, integral_const,
      smul_eq_mul, ← hA, ← hQ, ← hm_def] at hmono
    have he : 2 * (A / m) * A - m * (A / m) ^ 2 = A ^ 2 / m := by
      field_simp
      ring
    rw [he, div_le_iff₀ hpos] at hmono
    linarith

/-! ### Translation estimates -/

/-- A translated set integral of a nonnegative function is bounded by its integral over any set
containing the translated domain. -/
private theorem setIntegral_comp_add_right_le {d : ℕ} {F : Space d → ℝ} {S T : Set (Space d)}
    (hT : IntegrableOn F T) (hF : ∀ y, 0 ≤ F y) (c : Space d) (hST : ∀ y ∈ S, y + c ∈ T) :
    ∫ y in S, F (y + c) ≤ ∫ y in T, F y := by
  have he := (measurePreserving_add_right volume c).setIntegral_image_emb
    (Homeomorph.addRight c).measurableEmbedding F S
  rw [← he]
  apply setIntegral_mono_set hT (Eventually.of_forall hF)
  apply Eventually.of_forall
  rintro y ⟨z, hz, rfl⟩
  exact hST z hz

/-- For a `C¹` function, the squared increment is bounded by the squared length of the
increment times the mean squared gradient along the segment. -/
theorem sq_sub_le_integral_segment_norm_fderiv_sq {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (y h : Space d) :
    (v (y + h) - v y) ^ 2 ≤
      ‖h‖ ^ 2 * ∫ t in Set.Icc (0 : ℝ) 1, ‖fderiv ℝ v (y + t • h)‖ ^ 2 := by
  have hc : Continuous (fun t : ℝ ↦ y + t • h) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hD : Continuous (fun t : ℝ ↦ fderiv ℝ v (y + t • h)) :=
    (hv.continuous_fderiv one_ne_zero).comp hc
  have ha : Continuous (fun t : ℝ ↦ fderiv ℝ v (y + t • h) h) := hD.clm_apply continuous_const
  rw [sub_eq_integral_segment_fderiv hv y h, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hμ : (volume.restrict (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Icc]
    norm_num
  have hi1 : IntegrableOn (fun t : ℝ ↦ fderiv ℝ v (y + t • h) h) (Set.Icc (0 : ℝ) 1) :=
    ha.continuousOn.integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun t : ℝ ↦ fderiv ℝ v (y + t • h) h ^ 2) (Set.Icc (0 : ℝ) 1) :=
    (ha.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hi3 : IntegrableOn (fun t : ℝ ↦ ‖h‖ ^ 2 * ‖fderiv ℝ v (y + t • h)‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul (hD.norm.pow 2)).continuousOn.integrableOn_compact isCompact_Icc
  have h1 := sq_integral_le_measureReal_mul_integral_sq
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) hi1 hi2
  rw [hμ, one_mul] at h1
  refine h1.trans ?_
  rw [← integral_const_mul]
  refine integral_mono hi2 hi3 (fun t ↦ ?_)
  have hle : |fderiv ℝ v (y + t • h) h| ≤ ‖fderiv ℝ v (y + t • h)‖ * ‖h‖ := by
    simpa only [Real.norm_eq_abs] using (fderiv ℝ v (y + t • h)).le_opNorm h
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hle 2
  rw [sq_abs, mul_pow] at hsq
  change fderiv ℝ v (y + t • h) h ^ 2 ≤ ‖h‖ ^ 2 * ‖fderiv ℝ v (y + t • h)‖ ^ 2
  linarith

/-- The `L²` translation estimate for `C¹` Lipschitz functions: if every segment from `S` in the
direction `h` stays in `T`, then `∫_S |v(y+h) - v(y)|² ≤ |h|² ∫_T |∇v|²`. -/
theorem integral_sq_translate_sub_le_of_contDiff {d : ℕ} {v : Space d → ℝ} {K : NNReal}
    (hv : ContDiff ℝ 1 v) (hK : LipschitzWith K v) {S T : Set (Space d)}
    (hSf : volume S ≠ ⊤) (hTf : volume T ≠ ⊤) (h : Space d)
    (hST : ∀ y ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, y + t • h ∈ T) :
    ∫ y in S, (v (y + h) - v y) ^ 2 ≤ ‖h‖ ^ 2 * ∫ y in T, ‖fderiv ℝ v y‖ ^ 2 := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hDc : Continuous (fun y ↦ ‖fderiv ℝ v y‖ ^ 2) :=
    (hv.continuous_fderiv one_ne_zero).norm.pow 2
  have hDb : ∀ y, ‖‖fderiv ℝ v y‖ ^ 2‖ ≤ (K : ℝ) ^ 2 := by
    intro y
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2
  let G : Space d → ℝ → ℝ := fun y t ↦ ‖fderiv ℝ v (y + t • h)‖ ^ 2
  have hG : Continuous (Function.uncurry G) :=
    hDc.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict S).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    apply (integrable_const ((K : ℝ) ^ 2)).mono' hG.aestronglyMeasurable
    exact Eventually.of_forall (fun p ↦ hDb _)
  have hTi : IntegrableOn (fun y ↦ ‖fderiv ℝ v y‖ ^ 2) T :=
    Measure.integrableOn_of_bounded hTf hDc.aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ hDb y))
  have hpt : ∀ y, (v (y + h) - v y) ^ 2 ≤ ‖h‖ ^ 2 * ∫ t in Set.Icc (0 : ℝ) 1, G y t :=
    fun y ↦ sq_sub_le_integral_segment_norm_fderiv_sq hv y h
  have hLm : AEStronglyMeasurable (fun y ↦ (v (y + h) - v y) ^ 2) volume :=
    (((hK.continuous.comp (continuous_id.add continuous_const)).sub
      hK.continuous).pow 2).aestronglyMeasurable
  have hLb : ∀ᵐ y ∂(volume.restrict S), ‖(v (y + h) - v y) ^ 2‖ ≤ ((K : ℝ) * ‖h‖) ^ 2 := by
    apply Eventually.of_forall
    intro y
    have hd := hK.dist_le_mul (y + h) y
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hd
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hab : |v (y + h) - v y| ≤ (K : ℝ) * ‖h‖ := by
      simpa only [Real.norm_eq_abs] using hd
    have := pow_le_pow_left₀ (abs_nonneg _) hab 2
    rwa [sq_abs] at this
  have hL : IntegrableOn (fun y ↦ (v (y + h) - v y) ^ 2) S :=
    Measure.integrableOn_of_bounded hSf hLm hLb
  have hR : IntegrableOn (fun y ↦ ‖h‖ ^ 2 * ∫ t in Set.Icc (0 : ℝ) 1, G y t) S :=
    hGi.integral_prod_left.const_mul _
  have hstep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ y in S, G y t ≤ ∫ y in T, ‖fderiv ℝ v y‖ ^ 2 := by
    intro t ht
    exact setIntegral_comp_add_right_le hTi (fun y ↦ by positivity) (t • h)
      (fun y hy ↦ hST y hy t ht)
  calc ∫ y in S, (v (y + h) - v y) ^ 2
      ≤ ∫ y in S, ‖h‖ ^ 2 * ∫ t in Set.Icc (0 : ℝ) 1, G y t := integral_mono hL hR hpt
    _ = ‖h‖ ^ 2 * ∫ t in Set.Icc (0 : ℝ) 1, ∫ y in S, G y t := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ ≤ ‖h‖ ^ 2 * ∫ t in Set.Icc (0 : ℝ) 1, ∫ y in T, ‖fderiv ℝ v y‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact setIntegral_mono_on hGi.integral_prod_right
          (integrableOn_const (measure_Icc_lt_top.ne)) measurableSet_Icc hstep
    _ = ‖h‖ ^ 2 * ∫ y in T, ‖fderiv ℝ v y‖ ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc]
        norm_num

/-- Averaging does not increase a global Lipschitz constant. -/
private theorem mollify_lipschitzWith {d : ℕ} {v : Space d → ℝ} {K : NNReal}
    (hv : LipschitzWith K v) (n : ℕ) : LipschitzWith K (mollify v n) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  apply mollify_dist_le hv.continuous n y z
  intro t _
  have hd := hv.dist_le_mul (y - t) (z - t)
  rwa [dist_sub_right] at hd

/-- The `L²` translation estimate for Lipschitz functions: if every segment from `S` in the
direction `h` stays in `T`, then `∫_S |f(y+h) - f(y)|² ≤ |h|² ∫_T |∇f|²`. -/
theorem integral_sq_translate_sub_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {S T : Set (Space d)} (hSf : volume S ≠ ⊤) (hTf : volume T ≠ ⊤)
    (h : Space d) (hST : ∀ y ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, y + t • h ∈ T) :
    ∫ y in S, (f (y + h) - f y) ^ 2 ≤ ‖h‖ ^ 2 * ∫ y in T, ‖fderiv ℝ f y‖ ^ 2 := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hTf
  have hA : Tendsto (fun n ↦ ∫ y in S, (mollify f n (y + h) - mollify f n y) ^ 2) atTop
      (𝓝 (∫ y in S, (f (y + h) - f y) ^ 2)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ ((K : ℝ) * ‖h‖) ^ 2)
    · intro n
      have hc := (mollify_lipschitzWith hf n).continuous
      exact (((hc.comp (continuous_id.add continuous_const)).sub hc).pow 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro y
      have hd := (mollify_lipschitzWith hf n).dist_le_mul (y + h) y
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hd
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hab : |mollify f n (y + h) - mollify f n y| ≤ (K : ℝ) * ‖h‖ := by
        simpa only [Real.norm_eq_abs] using hd
      have := pow_le_pow_left₀ (abs_nonneg _) hab 2
      rwa [sq_abs] at this
    · apply Eventually.of_forall
      intro y
      exact ((mollify_tendsto hf.continuous (y + h)).sub
        (mollify_tendsto hf.continuous y)).pow 2
  have hB : Tendsto (fun n ↦ ‖h‖ ^ 2 * ∫ y in T, ‖fderiv ℝ (mollify f n) y‖ ^ 2) atTop
      (𝓝 (‖h‖ ^ 2 * ∫ y in T, ‖fderiv ℝ f y‖ ^ 2)) := by
    apply Tendsto.const_mul
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (K : ℝ) ^ 2)
    · intro n
      exact ((measurable_fderiv ℝ _).norm.pow_const 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro y
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_fderiv_le_of_lipschitz ℝ (mollify_lipschitzWith hf n)) 2
    · filter_upwards [ae_restrict_of_ae (mollify_fderiv_tendsto_ae_of_lipschitz hf)] with y hy
      exact hy.norm.pow 2
  exact le_of_tendsto_of_tendsto' hA hB (fun n ↦ integral_sq_translate_sub_le_of_contDiff
    ((mollify_contDiff hf.continuous n).of_le (by simp)) (mollify_lipschitzWith hf n)
    hSf hTf h hST)

/-! ### The Poincaré inequality on balls -/

/-- The double integral of squared differences over a set of finite positive measure is twice its
measure times the variance. -/
theorem integral_integral_sq_sub_eq {d : ℕ} {B : Set (Space d)} (hB : 0 < volume.real B)
    {f : Space d → ℝ} (hf : IntegrableOn f B) (hf2 : IntegrableOn (fun y ↦ f y ^ 2) B) :
    ∫ y in B, ∫ z in B, (f z - f y) ^ 2 =
      2 * volume.real B * ∫ y in B, (f y - ⨍ z in B, f z) ^ 2 := by
  have hBf : volume B ≠ ⊤ := by
    intro h
    simp [measureReal_def, h] at hB
  set m := volume.real B with hm
  set A := ∫ y in B, f y with hA
  set Q := ∫ y in B, f y ^ 2 with hQ
  set c := ⨍ z in B, f z with hc
  have hcA : c = m⁻¹ * A := by
    rw [hc, setAverage_eq, smul_eq_mul]
  have hquad : ∀ a : ℝ, ∫ z in B, (f z - a) ^ 2 = Q - 2 * a * A + m * a ^ 2 := by
    intro a
    have he : (fun z ↦ (f z - a) ^ 2) = fun z ↦ (f z ^ 2 - (2 * a) * f z) + a ^ 2 := by
      funext z
      ring
    have h1 : IntegrableOn (fun z ↦ f z ^ 2 - (2 * a) * f z) B := hf2.sub (hf.const_mul _)
    have h2 : IntegrableOn (fun z ↦ (2 * a) * f z) B := hf.const_mul _
    have h3 : IntegrableOn (fun _ : Space d ↦ a ^ 2) B := integrableOn_const hBf
    rw [he, integral_add h1 h3, integral_sub hf2 h2, integral_const_mul, setIntegral_const,
      smul_eq_mul]
  have hinner : ∀ y, ∫ z in B, (f z - f y) ^ 2 = Q - 2 * f y * A + m * f y ^ 2 :=
    fun y ↦ hquad (f y)
  have hout : ∫ y in B, ∫ z in B, (f z - f y) ^ 2 = m * Q - 2 * A * A + m * Q := by
    rw [integral_congr_ae (Eventually.of_forall hinner)]
    have h1 : IntegrableOn (fun y ↦ Q - 2 * f y * A) B :=
      (integrableOn_const hBf).sub ((hf.const_mul 2).mul_const A)
    have h2 : IntegrableOn (fun y ↦ m * f y ^ 2) B := hf2.const_mul m
    have h3 : IntegrableOn (fun y ↦ 2 * f y * A) B := (hf.const_mul 2).mul_const A
    have h4 : IntegrableOn (fun _ : Space d ↦ Q) B := integrableOn_const hBf
    rw [integral_add h1 h2, integral_sub h4 h3, setIntegral_const, smul_eq_mul,
      integral_mul_const, integral_const_mul, integral_const_mul]
  have hvar : ∫ y in B, (f y - c) ^ 2 = Q - 2 * c * A + m * c ^ 2 := hquad c
  rw [hout, hvar, hcA]
  field_simp
  ring

/-- The pair-difference energy of a Lipschitz function on a ball is controlled by its Dirichlet
energy on the same ball. -/
theorem integral_integral_sq_sub_le_ball {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (x : Space d) (r : ℝ) :
    ∫ y in ball x r, ∫ z in ball x r, (f z - f y) ^ 2 ≤
      (2 * r) ^ 2 * volume.real (ball (0 : Space d) (2 * r)) *
        ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2 := by
  set B := ball x r with hB
  set I := ∫ y in B, ‖fderiv ℝ f y‖ ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg (fun y ↦ by positivity)
  let P : Set (Space d × Space d) := {p | p.1 ∈ B ∧ p.1 + p.2 ∈ B}
  have hPm : MeasurableSet P :=
    (measurable_fst measurableSet_ball).inter
      ((measurable_fst.add measurable_snd) measurableSet_ball)
  let G : Space d × Space d → ℝ := fun p ↦ (f (p.1 + p.2) - f p.1) ^ 2
  have hGc : Continuous G := ((hf.continuous.comp (continuous_fst.add continuous_snd)).sub
    (hf.continuous.comp continuous_fst)).pow 2
  let Φ : Space d × Space d → ℝ := P.indicator G
  have hshort : ∀ y h : Space d, y ∈ B → y + h ∈ B → ‖h‖ < 2 * r := by
    intro y h hy hyh
    have h1 : dist y x < r := hy
    have h2 : dist (y + h) x < r := hyh
    calc ‖h‖ = dist (y + h) y := by rw [dist_eq_norm, add_sub_cancel_left]
      _ ≤ dist (y + h) x + dist y x := dist_triangle_right _ _ _
      _ < r + r := add_lt_add h2 h1
      _ = 2 * r := by ring
  have hPsub : P ⊆ B ×ˢ ball (0 : Space d) (2 * r) := by
    rintro ⟨y, h⟩ ⟨hy, hyh⟩
    refine ⟨hy, ?_⟩
    rw [mem_ball, dist_zero_right]
    exact hshort y h hy hyh
  have hPf : ((volume : Measure (Space d)).prod volume) P ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hPsub)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne measure_ball_lt_top.ne
  have hGb : ∀ p ∈ P, ‖G p‖ ≤ ((K : ℝ) * (2 * r)) ^ 2 := by
    rintro ⟨y, h⟩ ⟨hy, hyh⟩
    have hd := hf.dist_le_mul (y + h) y
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hd
    have hab : |f (y + h) - f y| ≤ (K : ℝ) * (2 * r) := by
      rw [← Real.norm_eq_abs]
      exact hd.trans (mul_le_mul_of_nonneg_left (hshort y h hy hyh).le K.coe_nonneg)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hab 2
    rw [sq_abs] at hsq
    simpa only [G, Real.norm_of_nonneg (sq_nonneg _)] using hsq
  have hΦi : Integrable Φ ((volume : Measure (Space d)).prod volume) := by
    rw [integrable_indicator_iff hPm]
    exact Measure.integrableOn_of_bounded hPf hGc.aestronglyMeasurable
      ((ae_restrict_iff' hPm).2 (Eventually.of_forall hGb))
  have hΦB : ∀ y h, y ∈ B → Φ (y, h) = B.indicator (fun z ↦ (f z - f y) ^ 2) (y + h) := by
    intro y h hy
    show P.indicator G (y, h) = _
    by_cases hyh : y + h ∈ B
    · have hp : (y, h) ∈ P := ⟨hy, hyh⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hyh]
    · have hp : (y, h) ∉ P := fun hp ↦ hyh hp.2
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hyh]
  have hΦB' : ∀ y h, y ∉ B → Φ (y, h) = 0 := by
    intro y h hy
    have hp : (y, h) ∉ P := fun hp ↦ hy hp.1
    exact Set.indicator_of_notMem hp _
  have hLHS : ∫ y in B, ∫ z in B, (f z - f y) ^ 2 = ∫ y, ∫ h, Φ (y, h) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      dsimp only
      rw [← integral_indicator measurableSet_ball]
      have ht := integral_add_left_eq_self (μ := (volume : Measure (Space d)))
        (B.indicator fun z ↦ (f z - f y) ^ 2) y
      rw [← ht]
      apply integral_congr_ae
      exact Eventually.of_forall (fun h ↦ (hΦB y h hy).symm)
    · rw [Set.indicator_of_notMem hy]
      dsimp only
      simp only [hΦB' y _ hy, integral_zero]
  have hΦi' : Integrable (Function.uncurry fun y h ↦ Φ (y, h))
      ((volume : Measure (Space d)).prod volume) := by
    have he : (Function.uncurry fun y h ↦ Φ (y, h)) = Φ := by
      funext p
      rcases p with ⟨y, h⟩
      rfl
    rw [he]
    exact hΦi
  have hswap : ∫ y, ∫ h, Φ (y, h) = ∫ h, ∫ y, Φ (y, h) :=
    integral_integral_swap hΦi'
  have hJ : ∀ h : Space d, ∫ y, Φ (y, h) ≤
      (ball (0 : Space d) (2 * r)).indicator (fun _ ↦ (2 * r) ^ 2 * I) h := by
    intro h
    let S : Set (Space d) := B ∩ (fun y ↦ y + h) ⁻¹' B
    have hBm : MeasurableSet B := measurableSet_ball
    have hadd : Measurable (fun y : Space d ↦ y + h) := measurable_add_const h
    have hSm : MeasurableSet S := hBm.inter (hadd hBm)
    have hΦS : (fun y ↦ Φ (y, h)) = S.indicator (fun y ↦ (f (y + h) - f y) ^ 2) := by
      funext y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        exact Set.indicator_of_mem (show (y, h) ∈ P from hy) _
      · rw [Set.indicator_of_notMem hy]
        exact Set.indicator_of_notMem (show (y, h) ∉ P from hy) _
    rw [hΦS, integral_indicator hSm]
    by_cases hh : h ∈ ball (0 : Space d) (2 * r)
    · rw [Set.indicator_of_mem hh]
      have hS_sub : S ⊆ B := fun y hy ↦ hy.1
      have hseg : ∀ y ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, y + t • h ∈ B :=
        fun y hy t ht ↦ (convex_ball x r).add_smul_mem hy.1 hy.2 ht
      have hT := integral_sq_translate_sub_le hf
        (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hS_sub))
        measure_ball_lt_top.ne h hseg
      refine hT.trans (mul_le_mul_of_nonneg_right ?_ hI0)
      have hlt : ‖h‖ < 2 * r := by simpa only [mem_ball, dist_zero_right] using hh
      exact pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
    · rw [Set.indicator_of_notMem hh]
      have hS : S = ∅ := by
        ext y
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hy, hyh⟩
        apply hh
        rw [mem_ball, dist_zero_right]
        exact hshort y h hy hyh
      rw [hS, Measure.restrict_empty, integral_zero_measure]
  have hJi : Integrable (fun h ↦ ∫ y, Φ (y, h)) := hΦi.integral_prod_right
  have hCi : Integrable ((ball (0 : Space d) (2 * r)).indicator (fun _ ↦ (2 * r) ^ 2 * I)) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  calc ∫ y in B, ∫ z in B, (f z - f y) ^ 2 = ∫ h, ∫ y, Φ (y, h) := by rw [hLHS, hswap]
    _ ≤ ∫ h, (ball (0 : Space d) (2 * r)).indicator (fun _ ↦ (2 * r) ^ 2 * I) h :=
        integral_mono hJi hCi hJ
    _ = (2 * r) ^ 2 * volume.real (ball (0 : Space d) (2 * r)) * I := by
        rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul]
        ring

/-- Doubling the radius multiplies the volume of a Euclidean ball by `2 ^ d`. -/
private theorem measureReal_ball_two_mul {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball (0 : Space d) (2 * r)) = 2 ^ d * volume.real (ball x r) := by
  rw [measureReal_def, measureReal_def,
    Measure.addHaar_ball_of_pos volume 0 (by positivity : (0 : ℝ) < 2 * r),
    Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), mul_pow]
  ring

/-- Euclidean balls of positive radius have positive finite volume. -/
private theorem measureReal_ball_pos {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball x r) :=
  ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

/-- Continuous functions are integrable on Euclidean balls. -/
private theorem integrableOn_ball_of_continuous {d : ℕ} {f : Space d → ℝ} (hf : Continuous f)
    (x : Space d) (r : ℝ) : IntegrableOn f (ball x r) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set
    ball_subset_closedBall

/-- **Poincaré inequality on balls** for globally Lipschitz functions, with the explicit constant
`2 ^ (d + 1)`. -/
theorem poincare_ball {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) {f : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) :
    ∫ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2 ≤
      2 ^ (d + 1) * r ^ 2 * ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2 := by
  have hm := measureReal_ball_pos x hr
  have he := integral_integral_sq_sub_eq hm (integrableOn_ball_of_continuous hf.continuous x r)
    (integrableOn_ball_of_continuous (hf.continuous.pow 2) x r)
  have hle := integral_integral_sq_sub_le_ball hf x r
  rw [he, measureReal_ball_two_mul x hr] at hle
  set V := ∫ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2
  set I := ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2
  set m := volume.real (ball x r)
  have h2 : 2 * m * V ≤ 2 * m * (2 ^ (d + 1) * r ^ 2 * I) := by
    calc 2 * m * V ≤ (2 * r) ^ 2 * (2 ^ d * m) * I := hle
      _ = 2 * m * (2 ^ (d + 1) * r ^ 2 * I) := by ring
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- **Poincaré inequality on balls**: a dimensional constant works for all centers, radii and
globally Lipschitz functions. -/
theorem exists_poincare_constant (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Space d) (r : ℝ) (f : Space d → ℝ) (K : NNReal),
      0 < r → LipschitzWith K f →
        ∫ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2 ≤
          C * r ^ 2 * ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2 :=
  ⟨2 ^ (d + 1), by positivity, fun x _ _ _ hr hf ↦ poincare_ball x hr hf⟩

/-! ### The `L²` mollification error -/

/-- **Mollification error in `L²`**: convolving a Lipschitz function with the normalized bump of
outer radius `ε` changes it by at most `ε² ∫_{B_{r+ε}} |∇f|²` in squared `L²(B_r)` norm. -/
theorem integral_sq_convolution_sub_le {d : ℕ} (φ : ContDiffBump (0 : Space d))
    {f : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f) (x : Space d) (r : ℝ) :
    ∫ y in ball x r, ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) y - f y) ^ 2 ≤
      φ.rOut ^ 2 * ∫ y in ball x (r + φ.rOut), ‖fderiv ℝ f y‖ ^ 2 := by
  set k := φ.normed volume with hk
  set ε := φ.rOut with hε_def
  set I := ∫ y in ball x (r + ε), ‖fderiv ℝ f y‖ ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg (fun y ↦ by positivity)
  have hk0 : ∀ t, 0 ≤ k t := φ.nonneg_normed
  have hk1 : ∫ t, k t = 1 := φ.integral_normed
  have hki : Integrable k := φ.integrable_normed
  have hkc : Continuous k := φ.continuous_normed
  have hkcs : HasCompactSupport k := φ.hasCompactSupport_normed
  have hk_zero : ∀ t : Space d, ε ≤ ‖t‖ → k t = 0 := by
    intro t ht
    apply Function.notMem_support.mp
    rw [φ.support_normed_eq, mem_ball, dist_zero_right, not_lt]
    exact ht
  have hconv : ∀ y, Integrable (fun t ↦ k t * f (y - t)) := fun y ↦
    (hkcs.convolutionExists_left (lsmul ℝ ℝ) hkc hf.continuous.locallyIntegrable y).integrable
  have hrep : ∀ y, (k ⋆[lsmul ℝ ℝ, volume] f) y - f y = ∫ t, k t * (f (y - t) - f y) := by
    intro y
    simp_rw [mul_sub]
    rw [integral_sub (hconv y) (hki.mul_const _), integral_mul_const, hk1, one_mul]
    rfl
  have hdiff : ∀ y, Continuous (fun t ↦ f (y - t) - f y) := fun y ↦
    (hf.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hpt : ∀ y, ((k ⋆[lsmul ℝ ℝ, volume] f) y - f y) ^ 2 ≤
      ∫ t, k t * (f (y - t) - f y) ^ 2 := by
    intro y
    rw [hrep]
    exact sq_integral_mul_le_integral_mul_sq hk0 hk1 hki
      ((hkc.mul (hdiff y)).integrable_of_hasCompactSupport hkcs.mul_right)
      ((hkc.mul ((hdiff y).pow 2)).integrable_of_hasCompactSupport hkcs.mul_right)
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  let F : Space d → Space d → ℝ := fun y t ↦ k t * (f (y - t) - f y) ^ 2
  have hFc : Continuous (Function.uncurry F) :=
    (hkc.comp continuous_snd).mul (((hf.continuous.comp (continuous_fst.sub continuous_snd)).sub
      (hf.continuous.comp continuous_fst)).pow 2)
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (ball x r)).prod volume) := by
    have hbound : Integrable (fun p : Space d × Space d ↦ (1 : ℝ) * (((K : ℝ) * ε) ^ 2 * k p.2))
        ((volume.restrict (ball x r)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod (hki.const_mul _)
    refine hbound.mono' hFc.aestronglyMeasurable (Eventually.of_forall ?_)
    rintro ⟨y, t⟩
    change ‖k t * (f (y - t) - f y) ^ 2‖ ≤ 1 * (((K : ℝ) * ε) ^ 2 * k t)
    rw [one_mul, Real.norm_of_nonneg (mul_nonneg (hk0 t) (sq_nonneg _))]
    by_cases ht : ‖t‖ < ε
    · have hd := hf.dist_le_mul (y - t) y
      rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hd
      have hab : |f (y - t) - f y| ≤ (K : ℝ) * ε := by
        rw [← Real.norm_eq_abs]
        exact hd.trans (mul_le_mul_of_nonneg_left ht.le K.coe_nonneg)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hab 2
      rw [sq_abs] at hsq
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hsq (hk0 t)
    · rw [hk_zero t (not_lt.mp ht)]
      simp
  have hLi : IntegrableOn (fun y ↦ ((k ⋆[lsmul ℝ ℝ, volume] f) y - f y) ^ 2) (ball x r) := by
    have hcc : Continuous (k ⋆[lsmul ℝ ℝ, volume] f) :=
      hkcs.continuous_convolution_left (lsmul ℝ ℝ) hkc hf.continuous.locallyIntegrable
    exact integrableOn_ball_of_continuous ((hcc.sub hf.continuous).pow 2) x r
  have hRi : IntegrableOn (fun y ↦ ∫ t, F y t) (ball x r) := hFi.integral_prod_left
  have hstep : ∀ t, ∫ y in ball x r, F y t ≤ k t * (ε ^ 2 * I) := by
    intro t
    change ∫ y in ball x r, k t * (f (y - t) - f y) ^ 2 ≤ k t * (ε ^ 2 * I)
    rw [integral_const_mul]
    by_cases ht : ‖t‖ < ε
    · apply mul_le_mul_of_nonneg_left _ (hk0 t)
      have hseg : ∀ y ∈ ball x r, ∀ s ∈ Set.Icc (0 : ℝ) 1, y + s • (-t) ∈ ball x (r + ε) := by
        intro y hy s hs
        rw [mem_ball, dist_eq_norm] at hy ⊢
        have hst : ‖s • (-t)‖ ≤ ‖t‖ := by
          rw [norm_smul, norm_neg, Real.norm_of_nonneg hs.1]
          exact mul_le_of_le_one_left (norm_nonneg _) hs.2
        calc ‖y + s • (-t) - x‖ = ‖(y - x) + s • (-t)‖ := by abel_nf
          _ ≤ ‖y - x‖ + ‖s • (-t)‖ := norm_add_le _ _
          _ < r + ε := add_lt_add_of_lt_of_le hy (hst.trans ht.le)
      have h1 := integral_sq_translate_sub_le hf measure_ball_lt_top.ne measure_ball_lt_top.ne
        (-t) hseg
      simp only [← sub_eq_add_neg, norm_neg] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hI0)
      exact pow_le_pow_left₀ (norm_nonneg _) ht.le 2
    · rw [hk_zero t (not_lt.mp ht)]
      simp
  calc ∫ y in ball x r, ((k ⋆[lsmul ℝ ℝ, volume] f) y - f y) ^ 2
      ≤ ∫ y in ball x r, ∫ t, F y t := integral_mono hLi hRi hpt
    _ = ∫ t, ∫ y in ball x r, F y t := integral_integral_swap hFi
    _ ≤ ∫ t, k t * (ε ^ 2 * I) := integral_mono hFi.integral_prod_right (hki.mul_const _) hstep
    _ = ε ^ 2 * I := by rw [integral_mul_const, hk1, one_mul]

/-- The `L²` error of the project's averaging sequence at scale `1 / (n + 1)`. -/
theorem integral_sq_mollify_sub_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (n : ℕ) (x : Space d) (r : ℝ) :
    ∫ y in ball x r, (mollify f n y - f y) ^ 2 ≤
      (1 / ((n : ℝ) + 1)) ^ 2 * ∫ y in ball x (r + 1 / ((n : ℝ) + 1)), ‖fderiv ℝ f y‖ ^ 2 :=
  integral_sq_convolution_sub_le (averagingBump d n) hf x r

/-! ### Limits in `L²` -/

/-- The squared norm of an element of `L²` is the integral of its square. -/
private theorem Lp_two_norm_sq_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (G : Lp ℝ 2 μ) : ‖G‖ ^ 2 = ∫ x, G x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The squared `L²` distance between two square-integrable functions. -/
private theorem dist_toLp_two_sq_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    dist (ha.toLp a) (hb.toLp b) ^ 2 = ∫ x, (a x - b x) ^ 2 ∂μ := by
  rw [dist_eq_norm, Lp_two_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (ha.toLp a) (hb.toLp b), ha.coeFn_toLp, hb.coeFn_toLp]
    with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- A sequence which is Cauchy for the squared `L²` distance has a strongly measurable `L²`
limit. -/
theorem exists_sq_integral_limit_of_cauchy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (hF : ∀ j, MemLp (F j) 2 μ)
    (hc : ∀ ε, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∫ x, (F i x - F j x) ^ 2 ∂μ < ε) :
    ∃ v : X → ℝ, StronglyMeasurable v ∧ MemLp v 2 μ ∧
      Tendsto (fun j ↦ ∫ x, (F j x - v x) ^ 2 ∂μ) atTop (𝓝 0) := by
  let G : ℕ → Lp ℝ 2 μ := fun j ↦ (hF j).toLp (F j)
  have hG : CauchySeq G := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2) (by positivity)
    refine ⟨N, fun i hi j hj ↦ ?_⟩
    have h := hN i hi j hj
    rw [← dist_toLp_two_sq_eq_integral (hF i) (hF j)] at h
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hG
  have hLm : MemLp (L : X → ℝ) 2 μ := Lp.memLp L
  refine ⟨L, Lp.stronglyMeasurable L, hLm, ?_⟩
  have hd : Tendsto (fun j ↦ dist (G j) L ^ 2) atTop (𝓝 0) := by
    have h0 := (tendsto_iff_dist_tendsto_zero.mp hL).pow 2
    rwa [zero_pow two_ne_zero] at h0
  apply hd.congr'
  filter_upwards with j
  have hL' : hLm.toLp (L : X → ℝ) = L := Lp.toLp_coeFn L hLm
  calc dist (G j) L ^ 2 = dist (G j) (hLm.toLp (L : X → ℝ)) ^ 2 := by rw [hL']
    _ = ∫ x, (F j x - L x) ^ 2 ∂μ := dist_toLp_two_sq_eq_integral (hF j) hLm

/-- Squared-`L²` limits are unique almost everywhere. -/
theorem ae_eq_of_sq_integral_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {v w : X → ℝ} (hF : ∀ j, MemLp (F j) 2 μ) (hv : MemLp v 2 μ)
    (hw : MemLp w 2 μ) (hFv : Tendsto (fun j ↦ ∫ x, (F j x - v x) ^ 2 ∂μ) atTop (𝓝 0))
    (hFw : Tendsto (fun j ↦ ∫ x, (F j x - w x) ^ 2 ∂μ) atTop (𝓝 0)) : v =ᵐ[μ] w := by
  have hvw : Integrable (fun x ↦ (v x - w x) ^ 2) μ := (hv.sub hw).integrable_sq
  have hle : ∀ j, ∫ x, (v x - w x) ^ 2 ∂μ ≤
      2 * ∫ x, (F j x - v x) ^ 2 ∂μ + 2 * ∫ x, (F j x - w x) ^ 2 ∂μ := by
    intro j
    have h1 : Integrable (fun x ↦ 2 * (F j x - v x) ^ 2) μ :=
      ((hF j).sub hv).integrable_sq.const_mul 2
    have h2 : Integrable (fun x ↦ 2 * (F j x - w x) ^ 2) μ :=
      ((hF j).sub hw).integrable_sq.const_mul 2
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
    refine integral_mono hvw (h1.add h2) (fun x ↦ ?_)
    change (v x - w x) ^ 2 ≤ 2 * (F j x - v x) ^ 2 + 2 * (F j x - w x) ^ 2
    nlinarith [sq_nonneg (2 * F j x - v x - w x)]
  have hlim : Tendsto (fun j ↦ 2 * ∫ x, (F j x - v x) ^ 2 ∂μ + 2 * ∫ x, (F j x - w x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    simpa using (hFv.const_mul 2).add (hFw.const_mul 2)
  have h0 : ∫ x, (v x - w x) ^ 2 ∂μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) (integral_nonneg (fun x ↦ sq_nonneg _))
  have hz := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (v x - w x)) hvw).mp h0
  filter_upwards [hz] with x hx
  have hx' : (v x - w x) ^ 2 = 0 := hx
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hx')

/-- Squared-`L²` convergence on a set implies convergence on every subset. -/
theorem tendsto_sq_integral_mono_set {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S T : Set X} (hST : S ⊆ T) {F : ℕ → X → ℝ} {g : X → ℝ}
    (hFT : ∀ j, IntegrableOn (fun x ↦ (F j x - g x) ^ 2) T μ)
    (hT : Tendsto (fun j ↦ ∫ x in T, (F j x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in S, (F j x - g x) ^ 2 ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
    (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun j ↦ setIntegral_mono_set (hFT j) (Eventually.of_forall (fun _ ↦ sq_nonneg _))
      (Eventually.of_forall hST))

/-- A sequence which can be approximated, uniformly in the index, by sequences that are Cauchy
for the squared `L²` distance is itself Cauchy for that distance. -/
private theorem sq_integral_cauchy_of_approx {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (F : ℕ → X → ℝ) (hF : ∀ j, MemLp (F j) 2 μ)
    (happrox : ∀ η, 0 < η → ∃ G : ℕ → X → ℝ, (∀ j, MemLp (G j) 2 μ) ∧
      (∀ j, ∫ x, (F j x - G j x) ^ 2 ∂μ ≤ η) ∧
      ∀ ε, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∫ x, (G i x - G j x) ^ 2 ∂μ < ε) :
    ∀ ε, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∫ x, (F i x - F j x) ^ 2 ∂μ < ε := by
  intro ε hε
  obtain ⟨G, hG, herr, hc⟩ := happrox (ε / 9) (by positivity)
  obtain ⟨N, hN⟩ := hc (ε / 9) (by positivity)
  refine ⟨N, fun i hi j hj ↦ ?_⟩
  have h1 : Integrable (fun x ↦ 3 * (F i x - G i x) ^ 2) μ :=
    ((hF i).sub (hG i)).integrable_sq.const_mul 3
  have h2 : Integrable (fun x ↦ 3 * (G i x - G j x) ^ 2) μ :=
    ((hG i).sub (hG j)).integrable_sq.const_mul 3
  have h3 : Integrable (fun x ↦ 3 * (F j x - G j x) ^ 2) μ :=
    ((hF j).sub (hG j)).integrable_sq.const_mul 3
  have h12 : Integrable (fun x ↦ 3 * (F i x - G i x) ^ 2 + 3 * (G i x - G j x) ^ 2) μ :=
    h1.add h2
  have h0 : Integrable (fun x ↦ (F i x - F j x) ^ 2) μ := ((hF i).sub (hF j)).integrable_sq
  have hsum : Integrable (fun x ↦ 3 * (F i x - G i x) ^ 2 + 3 * (G i x - G j x) ^ 2 +
      3 * (F j x - G j x) ^ 2) μ := h12.add h3
  have hmono := integral_mono h0 hsum (fun x ↦ by
    change (F i x - F j x) ^ 2 ≤ 3 * (F i x - G i x) ^ 2 + 3 * (G i x - G j x) ^ 2 +
      3 * (F j x - G j x) ^ 2
    nlinarith [sq_nonneg ((F i x - G i x) - (G i x - G j x)),
      sq_nonneg ((G i x - G j x) + (F j x - G j x)),
      sq_nonneg ((F i x - G i x) + (F j x - G j x))])
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul] at hmono
  linarith [herr i, herr j, hN i hi j hj]

/-- Sequences that are uniformly Cauchy on a set of finite measure are Cauchy for the squared
`L²` distance there. -/
private theorem sq_integral_cauchy_of_uniform {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S : Set X} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤) (G : ℕ → X → ℝ)
    (hGm : ∀ j, AEStronglyMeasurable (G j) (μ.restrict S))
    (hu : ∀ δ, 0 < δ → ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ x ∈ S, |G i x - G j x| ≤ δ) :
    ∀ ε, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∫ x in S, (G i x - G j x) ^ 2 ∂μ < ε := by
  intro ε hε
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS
  set m := μ.real S with hm_def
  have hm : 0 ≤ m := measureReal_nonneg
  set δ := Real.sqrt (ε / (2 * (m + 1))) with hδ_def
  have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hδ2 : δ ^ 2 = ε / (2 * (m + 1)) := Real.sq_sqrt (by positivity)
  obtain ⟨N, hN⟩ := hu δ hδ
  refine ⟨N, fun i hi j hj ↦ ?_⟩
  have hb : ∀ x ∈ S, (G i x - G j x) ^ 2 ≤ δ ^ 2 := by
    intro x hx
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hN i hi j hj x hx) 2
    rwa [sq_abs] at h2
  have hint : IntegrableOn (fun x ↦ (G i x - G j x) ^ 2) S μ := by
    refine (integrable_const (δ ^ 2)).mono' (((hGm i).sub (hGm j)).pow 2) ?_
    refine (ae_restrict_iff' hSm).2 (Eventually.of_forall (fun x hx ↦ ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hb x hx
  have hle := setIntegral_mono_on hint (integrableOn_const hS) hSm hb
  rw [setIntegral_const, smul_eq_mul, ← hm_def, hδ2] at hle
  have hlt : m * (ε / (2 * (m + 1))) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact hle.trans_lt hlt

/-- Continuous functions are square integrable on Euclidean balls. -/
private theorem memLp_two_ball_of_continuous {d : ℕ} {f : Space d → ℝ} (hf : Continuous f)
    (x : Space d) (r : ℝ) : MemLp f 2 (volume.restrict (ball x r)) := by
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  exact integrableOn_ball_of_continuous (hf.pow 2) x r

/-- Compatible almost-everywhere representatives on countably many measurable sets glue. -/
private theorem exists_ae_gluing_of_compat {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : ℕ → Set X) (hS : ∀ k, MeasurableSet (S k)) (V : ℕ → X → ℝ)
    (hcompat : ∀ k l, k ≤ l → V k =ᵐ[μ.restrict (S k)] V l) :
    ∃ v : X → ℝ, ∀ k, v =ᵐ[μ.restrict (S k)] V k := by
  classical
  let n : X → ℕ := fun y ↦ if h : ∃ k, y ∈ S k then Nat.find h else 0
  refine ⟨fun y ↦ V (n y) y, fun k ↦ ?_⟩
  have hall : ∀ᵐ y ∂μ, ∀ i j, i ≤ j → y ∈ S i → V i y = V j y := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i ≤ j
    · filter_upwards [(ae_restrict_iff' (hS i)).mp (hcompat i j hij)] with y hy
      exact fun _ ↦ hy
    · exact Eventually.of_forall (fun _ h ↦ (hij h).elim)
  rw [EventuallyEq, ae_restrict_iff' (hS k)]
  filter_upwards [hall] with y hy hyk
  have h : ∃ k, y ∈ S k := ⟨k, hyk⟩
  have hn : n y = Nat.find h := dite_eq_left h
  change V (n y) y = V k y
  rw [hn]
  exact hy _ _ (Nat.find_min' h hyk) (Nat.find_spec h)

/-! ### Rellich compactness -/

/-- Inside a ball containing the support of the translated averaging kernel, an average is an
integral over the ball. -/
private theorem mollify_eq_setIntegral_ball {d : ℕ} {v : Space d → ℝ} (n : ℕ) {x y : Space d}
    {R : ℝ} (hy : dist y x + (averagingBump d n).rOut ≤ R) :
    mollify v n y = ∫ t in ball x R, (averagingBump d n).normed volume (y - t) * v t := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact convolution_eq_swap (lsmul ℝ ℝ)
  · intro t ht
    have hk : (averagingBump d n).normed volume (y - t) = 0 := by
      apply Function.notMem_support.mp
      rw [(averagingBump d n).support_normed_eq, mem_ball, dist_zero_right]
      intro hlt
      apply ht
      rw [mem_ball]
      calc dist t x ≤ dist t y + dist y x := dist_triangle _ _ _
        _ = ‖y - t‖ + dist y x := by rw [dist_comm, dist_eq_norm]
        _ < (averagingBump d n).rOut + dist y x := by linarith
        _ ≤ R := by linarith
    rw [hk, zero_mul]

/-- An average is bounded by the kernel bound times the `L¹` norm on a ball containing the
translated kernel support. -/
private theorem abs_mollify_le_of_ball {d : ℕ} {v : Space d → ℝ} (hv : Continuous v) (n : ℕ)
    {x y : Space d} {R B : ℝ} (hy : dist y x + (averagingBump d n).rOut ≤ R)
    (hB : ∀ t, (averagingBump d n).normed volume t ≤ B) :
    |mollify v n y| ≤ B * ∫ t in ball x R, |v t| := by
  rw [mollify_eq_setIntegral_ball n hy, ← integral_const_mul, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le
    ((integrableOn_ball_of_continuous hv.abs x R).const_mul B)
  apply Eventually.of_forall
  intro t
  rw [norm_mul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)

/-- An average is Lipschitz with constant the kernel Lipschitz constant times the `L¹` norm on a
ball containing the translated kernel supports. -/
private theorem abs_mollify_sub_le_of_ball {d : ℕ} {v : Space d → ℝ} (hv : Continuous v) (n : ℕ)
    {x y z : Space d} {R : ℝ} {L : NNReal} (hy : dist y x + (averagingBump d n).rOut ≤ R)
    (hz : dist z x + (averagingBump d n).rOut ≤ R)
    (hL : LipschitzWith L ((averagingBump d n).normed volume)) :
    |mollify v n y - mollify v n z| ≤ L * dist y z * ∫ t in ball x R, |v t| := by
  set k := (averagingBump d n).normed volume with hk
  have hkc : Continuous k := (averagingBump d n).continuous_normed
  have hiy : IntegrableOn (fun t ↦ k (y - t) * v t) (ball x R) :=
    integrableOn_ball_of_continuous ((hkc.comp (continuous_const.sub continuous_id)).mul hv) x R
  have hiz : IntegrableOn (fun t ↦ k (z - t) * v t) (ball x R) :=
    integrableOn_ball_of_continuous ((hkc.comp (continuous_const.sub continuous_id)).mul hv) x R
  rw [mollify_eq_setIntegral_ball n hy, mollify_eq_setIntegral_ball n hz, ← integral_sub hiy hiz,
    ← integral_const_mul, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le
    ((integrableOn_ball_of_continuous hv.abs x R).const_mul _)
  apply Eventually.of_forall
  intro t
  rw [← sub_mul, norm_mul, Real.norm_eq_abs (v t)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h := hL.dist_le_mul (y - t) (z - t)
  rwa [dist_sub_right, dist_eq_norm] at h

/-- Countably many uniformly bounded, uniformly Lipschitz sequences of bounded continuous functions
on compact spaces have a common uniformly convergent subsequence. -/
private theorem exists_simultaneous_uniform_subsequence_abs
    {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]
    (F : ∀ i, ℕ → X i →ᵇ ℝ) (C : I → NNReal) (M : I → ℝ)
    (hC : ∀ i n, LipschitzWith (C i) (F i n)) (hM : ∀ i n x, |F i n x| ≤ M i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ v : X i →ᵇ ℝ,
      TendstoUniformly (fun n x ↦ F i (φ n) x) v atTop := by
  have hc (i : I) : IsCompact (closure (Set.range (F i))) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M i) (M i)) isCompact_Icc
    · intro v x hv
      obtain ⟨n, rfl⟩ := hv
      exact abs_le.mp (hM i n x)
    · apply UniformEquicontinuous.equicontinuous
      apply Metric.uniformEquicontinuous_of_continuity_modulus (fun t : ℝ ↦ (C i : ℝ) * t)
      · simpa only [mul_zero, id_eq] using
          (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)))
      · intro x y v
        obtain ⟨n, hn⟩ := v.property
        rw [← hn]
        exact (hC i n).dist_le_mul x y
  let K (i : I) := closure (Set.range (F i))
  let _ : ∀ i, CompactSpace (K i) := fun i ↦ isCompact_iff_compactSpace.mp (hc i)
  let G : ℕ → ∀ i, K i := fun n i ↦ ⟨F i n, subset_closure (Set.mem_range_self n)⟩
  obtain ⟨v, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq G
  refine ⟨φ, hφ, fun i ↦ ⟨(v i).val, ?_⟩⟩
  have hi := continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp ht i)
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hi

/-- **Rellich compactness on balls.** A sequence of globally Lipschitz functions (with constants
allowed to depend on the index) whose `W^{1,2}(B_R)` energies are bounded has a subsequence that
converges in `L²(B_r)` for every `r < R` to one measurable limit, which is square integrable on
every such ball. -/
theorem exists_subseq_tendsto_sq_integral_ball {d : ℕ} (x : Space d) (R M : ℝ)
    (f : ℕ → Space d → ℝ) (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hM : ∀ j, ∫ y in ball x R, (f j y ^ 2 + ‖fderiv ℝ (f j) y‖ ^ 2) ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Space d → ℝ, Measurable g ∧
      (∀ r < R, MemLp g 2 (volume.restrict (ball x r))) ∧
      ∀ r < R, Tendsto (fun j ↦ ∫ y in ball x r, (f (φ j) y - g y) ^ 2) atTop (𝓝 0) := by
  choose K hK using hf
  have hcont : ∀ j, Continuous (f j) := fun j ↦ (hK j).continuous
  set V := volume.real (ball x R) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hi1 : ∀ j, IntegrableOn (fun y ↦ f j y ^ 2) (ball x R) := fun j ↦
    integrableOn_ball_of_continuous ((hcont j).pow 2) x R
  have hi2 : ∀ j, IntegrableOn (fun y ↦ ‖fderiv ℝ (f j) y‖ ^ 2) (ball x R) := by
    intro j
    refine Measure.integrableOn_of_bounded (M := (K j : ℝ) ^ 2) measure_ball_lt_top.ne
      ((measurable_fderiv ℝ (f j)).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ (hK j)) 2
  have hsplit : ∀ j, ∫ y in ball x R, (f j y ^ 2 + ‖fderiv ℝ (f j) y‖ ^ 2) =
      (∫ y in ball x R, f j y ^ 2) + ∫ y in ball x R, ‖fderiv ℝ (f j) y‖ ^ 2 :=
    fun j ↦ integral_add (hi1 j) (hi2 j)
  have hM1 : ∀ j, ∫ y in ball x R, f j y ^ 2 ≤ M := by
    intro j
    have h := hM j
    rw [hsplit j] at h
    have h0 : 0 ≤ ∫ y in ball x R, ‖fderiv ℝ (f j) y‖ ^ 2 :=
      integral_nonneg (fun y ↦ by positivity)
    linarith
  have hM2 : ∀ j, ∫ y in ball x R, ‖fderiv ℝ (f j) y‖ ^ 2 ≤ M := by
    intro j
    have h := hM j
    rw [hsplit j] at h
    have h0 : 0 ≤ ∫ y in ball x R, f j y ^ 2 := integral_nonneg (fun y ↦ by positivity)
    linarith
  have hM0 : 0 ≤ M := (integral_nonneg (fun y ↦ by positivity)).trans (hM1 0)
  have hL1 : ∀ j, ∫ y in ball x R, |f j y| ≤ V + M := by
    intro j
    have hc1 : IntegrableOn (fun _ : Space d ↦ (1 : ℝ)) (ball x R) :=
      integrableOn_const measure_ball_lt_top.ne
    have hle : ∫ y in ball x R, |f j y| ≤ ∫ y in ball x R, (1 + f j y ^ 2) := by
      refine integral_mono (integrableOn_ball_of_continuous (hcont j).abs x R)
        (hc1.add (hi1 j)) (fun y ↦ ?_)
      change |f j y| ≤ 1 + f j y ^ 2
      nlinarith [sq_abs (f j y), abs_nonneg (f j y), sq_nonneg (|f j y| - 1)]
    rw [integral_add hc1 (hi1 j), setIntegral_const, smul_eq_mul, mul_one] at hle
    linarith [hM1 j]
  -- the radii `ρ n = R - 1/(n+1)` and the compact balls on which the scale-`n` averages live
  set ρ : ℕ → ℝ := fun n ↦ R - 1 / ((n : ℝ) + 1) with hρ_def
  have hρlt : ∀ n, ρ n < R := by
    intro n
    have h0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [ρ]
    linarith
  have hρmono : Monotone ρ := by
    intro k l hkl
    have h1 : ((k : ℝ) + 1) ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkl 1
    have h2 : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) h1
    simp only [ρ]
    linarith
  have hfit : ∀ n (y : Space d), y ∈ closedBall x (ρ n) →
      dist y x + (averagingBump d n).rOut ≤ R := by
    intro n y hy
    have hy' : dist y x ≤ R - 1 / ((n : ℝ) + 1) := hy
    have hr : (averagingBump d n).rOut = 1 / ((n : ℝ) + 1) := rfl
    rw [hr]
    linarith
  have hcpt : ∀ n, CompactSpace (closedBall x (ρ n)) := fun n ↦
    isCompact_iff_compactSpace.mp (isCompact_closedBall x (ρ n))
  have hkB : ∀ n, ∃ B : ℝ, ∀ t, (averagingBump d n).normed volume t ≤ B := by
    intro n
    obtain ⟨B, hB⟩ :=
      ((averagingBump d n).hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous
        (averagingBump d n).continuous_normed
    exact ⟨B, fun t ↦ (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB t)⟩
  choose Bk hBk using hkB
  have hBk0 : ∀ n, 0 ≤ Bk n := fun n ↦ ((averagingBump d n).nonneg_normed 0).trans (hBk n 0)
  have hkL : ∀ n, ∃ L : NNReal, LipschitzWith L ((averagingBump d n).normed volume) := fun n ↦
    ContDiff.lipschitzWith_of_hasCompactSupport (averagingBump d n).hasCompactSupport_normed
      ((averagingBump d n).contDiff_normed (n := (1 : ℕ∞))) (by simp)
  choose Lk hLk using hkL
  let Fam : ∀ n : ℕ, ℕ → closedBall x (ρ n) →ᵇ ℝ := fun n j ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun y ↦ mollify (f j) n y,
        (mollify_contDiff (hcont j) n).continuous.comp continuous_subtype_val⟩
  have hFam : ∀ n j (y : closedBall x (ρ n)), Fam n j y = mollify (f j) n y := fun _ _ _ ↦ rfl
  have hLip : ∀ n j, LipschitzWith (Real.toNNReal (Lk n * (V + M))) (Fam n j) := by
    intro n j
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.coe_toNNReal _ (by positivity), hFam, hFam, Real.dist_eq, Subtype.dist_eq]
    have h := abs_mollify_sub_le_of_ball (hcont j) n (hfit n y y.2) (hfit n z z.2) (hLk n)
    calc |mollify (f j) n y - mollify (f j) n z|
        ≤ Lk n * dist (y : Space d) z * ∫ t in ball x R, |f j t| := h
      _ ≤ Lk n * dist (y : Space d) z * (V + M) :=
          mul_le_mul_of_nonneg_left (hL1 j) (by positivity)
      _ = Lk n * (V + M) * dist (y : Space d) z := by ring
  have hBound : ∀ n j (y : closedBall x (ρ n)), |Fam n j y| ≤ Bk n * (V + M) := by
    intro n j y
    rw [hFam]
    exact (abs_mollify_le_of_ball (hcont j) n (hfit n y y.2) (hBk n)).trans
      (mul_le_mul_of_nonneg_left (hL1 j) (hBk0 n))
  obtain ⟨φ, hφ, hlim⟩ := exists_simultaneous_uniform_subsequence_abs Fam
    (fun n ↦ Real.toNNReal (Lk n * (V + M))) (fun n ↦ Bk n * (V + M)) hLip hBound
  refine ⟨φ, hφ, ?_⟩
  have hFL2 : ∀ j r, MemLp (f (φ j)) 2 (volume.restrict (ball x r)) := fun j r ↦
    memLp_two_ball_of_continuous (hcont _) x r
  -- the subsequence is Cauchy in `L²(B_r)` for every `r < R`
  have hcauchy : ∀ r < R, ∀ ε, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      ∫ y in ball x r, (f (φ i) y - f (φ j) y) ^ 2 < ε := by
    intro r hr
    apply sq_integral_cauchy_of_approx (fun j ↦ f (φ j)) (fun j ↦ hFL2 j r)
    intro η hη
    have ht : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ev1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ R - r :=
      ht.eventually (ge_mem_nhds (by linarith))
    have ht2 : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) ^ 2 * M) atTop (𝓝 0) := by
      have h0 := (ht.pow 2).mul_const M
      rwa [zero_pow two_ne_zero, zero_mul] at h0
    have ev2 : ∀ᶠ n : ℕ in atTop, (1 / ((n : ℝ) + 1)) ^ 2 * M ≤ η :=
      ht2.eventually (ge_mem_nhds hη)
    obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
    refine ⟨fun j ↦ mollify (f (φ j)) n,
      fun j ↦ memLp_two_ball_of_continuous (mollify_contDiff (hcont _) n).continuous x r, ?_, ?_⟩
    · intro j
      have h1 := integral_sq_mollify_sub_le (hK (φ j)) n x r
      have h2 : ∫ y in ball x (r + 1 / ((n : ℝ) + 1)), ‖fderiv ℝ (f (φ j)) y‖ ^ 2 ≤ M :=
        (setIntegral_mono_set (hi2 (φ j)) (Eventually.of_forall (fun y ↦ by positivity))
          (Eventually.of_forall (ball_subset_ball (by linarith)))).trans (hM2 (φ j))
      calc ∫ y in ball x r, (f (φ j) y - mollify (f (φ j)) n y) ^ 2
          = ∫ y in ball x r, (mollify (f (φ j)) n y - f (φ j) y) ^ 2 := by
            congr 1
            funext y
            ring
        _ ≤ (1 / ((n : ℝ) + 1)) ^ 2 *
            ∫ y in ball x (r + 1 / ((n : ℝ) + 1)), ‖fderiv ℝ (f (φ j)) y‖ ^ 2 := h1
        _ ≤ (1 / ((n : ℝ) + 1)) ^ 2 * M := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ η := hn2
    · apply sq_integral_cauchy_of_uniform measurableSet_ball measure_ball_lt_top.ne
      · intro j
        exact (mollify_contDiff (hcont _) n).continuous.aestronglyMeasurable
      · intro δ hδ
        obtain ⟨v, hv⟩ := hlim n
        obtain ⟨N, hN⟩ := eventually_atTop.mp
          (Metric.tendstoUniformly_iff.mp hv (δ / 2) (by positivity))
        refine ⟨N, fun i hi j hj y hy ↦ ?_⟩
        have hyX : y ∈ closedBall x (ρ n) := by
          have hy' : dist y x < r := hy
          change dist y x ≤ R - 1 / ((n : ℝ) + 1)
          linarith
        have h1 : |v ⟨y, hyX⟩ - mollify (f (φ i)) n y| < δ / 2 := hN i hi ⟨y, hyX⟩
        have h2 : |v ⟨y, hyX⟩ - mollify (f (φ j)) n y| < δ / 2 := hN j hj ⟨y, hyX⟩
        obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
        obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
        change |mollify (f (φ i)) n y - mollify (f (φ j)) n y| ≤ δ
        rw [abs_le]
        constructor <;> linarith
  -- `L²` limits on the balls `B_{ρ k}`
  have hlimk : ∀ k, ∃ v : Space d → ℝ, StronglyMeasurable v ∧
      MemLp v 2 (volume.restrict (ball x (ρ k))) ∧
      Tendsto (fun j ↦ ∫ y in ball x (ρ k), (f (φ j) y - v y) ^ 2) atTop (𝓝 0) := fun k ↦
    exists_sq_integral_limit_of_cauchy _ (fun j ↦ f (φ j)) (fun j ↦ hFL2 j (ρ k))
      (hcauchy (ρ k) (hρlt k))
  choose W hWs hWm hWt using hlimk
  have hcompat : ∀ k l, k ≤ l → W k =ᵐ[volume.restrict (ball x (ρ k))] W l := by
    intro k l hkl
    have hsub : ball x (ρ k) ⊆ ball x (ρ l) := ball_subset_ball (hρmono hkl)
    have hWl : MemLp (W l) 2 (volume.restrict (ball x (ρ k))) :=
      (hWm l).mono_measure (Measure.restrict_mono hsub le_rfl)
    have ht := tendsto_sq_integral_mono_set hsub
      (fun j ↦ ((hFL2 j (ρ l)).sub (hWm l)).integrable_sq) (hWt l)
    exact ae_eq_of_sq_integral_tendsto (fun j ↦ hFL2 j (ρ k)) (hWm k) hWl (hWt k) ht
  obtain ⟨w, hw⟩ := exists_ae_gluing_of_compat volume (fun k ↦ ball x (ρ k))
    (fun _ ↦ measurableSet_ball) W hcompat
  have hcover : (⋃ k, ball x (ρ k)) = ball x R := by
    ext y
    simp only [Set.mem_iUnion, mem_ball]
    constructor
    · rintro ⟨k, hk⟩
      exact hk.trans (hρlt k)
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      refine ⟨k, ?_⟩
      simp only [ρ]
      linarith
  have hwm : AEStronglyMeasurable w (volume.restrict (ball x R)) := by
    rw [← hcover, aestronglyMeasurable_iUnion_iff]
    intro k
    exact (hWs k).aestronglyMeasurable.congr (hw k).symm
  have hgw : hwm.mk w =ᵐ[volume.restrict (ball x R)] w := hwm.ae_eq_mk.symm
  have hgW : ∀ k, hwm.mk w =ᵐ[volume.restrict (ball x (ρ k))] W k := by
    intro k
    have h1 : hwm.mk w =ᵐ[volume.restrict (ball x (ρ k))] w :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (hρlt k).le) hgw
    exact h1.trans (hw k)
  have hchoose : ∀ r < R, ∃ k, r ≤ ρ k := by
    intro r hr
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
    refine ⟨k, ?_⟩
    simp only [ρ]
    linarith
  refine ⟨hwm.mk w, hwm.stronglyMeasurable_mk.measurable, fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · obtain ⟨k, hk⟩ := hchoose r hr
    exact ((hWm k).ae_eq (hgW k).symm).mono_measure
      (Measure.restrict_mono (ball_subset_ball hk) le_rfl)
  · obtain ⟨k, hk⟩ := hchoose r hr
    have hgk : MemLp (hwm.mk w) 2 (volume.restrict (ball x (ρ k))) := (hWm k).ae_eq (hgW k).symm
    have htk : Tendsto (fun j ↦ ∫ y in ball x (ρ k), (f (φ j) y - hwm.mk w y) ^ 2) atTop
        (𝓝 0) := by
      apply (hWt k).congr'
      apply Eventually.of_forall
      intro j
      apply integral_congr_ae
      filter_upwards [hgW k] with y hy
      rw [hy]
    exact tendsto_sq_integral_mono_set (ball_subset_ball hk)
      (fun j ↦ ((hFL2 j (ρ k)).sub hgk).integrable_sq) htk

/-! ### Integration by parts for Lipschitz functions and weak harmonicity of limits -/

/-- The Laplacian of a `C²` function is continuous. -/
private theorem continuous_laplacian_aux {d : ℕ} {ψ : Space d → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (Δ ψ) := by
  let b := stdOrthonormalBasis ℝ (Space d)
  have hd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  have heq : (Δ ψ) = fun y ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b i)) y (b i) := by
    funext y
    exact laplacian_eq_sum_fderiv b (hd.differentiable_one y)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  exact ((hd.clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The Laplacian vanishes off the topological support. -/
private theorem laplacian_eq_zero_of_notMem_tsupport_aux {d : ℕ} (ψ : Space d → ℝ)
    {y : Space d} (hy : y ∉ tsupport ψ) : (Δ ψ) y = 0 := by
  have hz : iteratedFDeriv ℝ 2 ψ y = 0 := Function.notMem_support.mp
    (fun hmem ↦ hy (support_iteratedFDeriv_subset (𝕜 := ℝ) 2 hmem))
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hz,
    zero_apply, Finset.sum_const_zero]

/-- Integration by parts for a globally Lipschitz function against a compactly supported `C¹`
test function, in a fixed direction `v`. -/
theorem integral_fderiv_apply_mul_eq_neg_of_lipschitz {d : ℕ} {f ψ : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (v : Space d) :
    ∫ y, fderiv ℝ f y v * ψ y = -∫ y, f y * fderiv ℝ ψ y v := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero
  have h := hf.integral_lineDeriv_mul_eq hD hψc v (μ := volume)
  have hl : ∫ y, fderiv ℝ f y v * ψ y = ∫ y, lineDeriv ℝ f y v * ψ y := by
    apply integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with y hy
    rw [hy.lineDeriv_eq_fderiv]
  have hr : ∫ y, lineDeriv ℝ ψ y (-v) * f y = -∫ y, f y * fderiv ℝ ψ y v := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [(hψ.differentiable one_ne_zero y).lineDeriv_eq_fderiv, map_neg]
    ring
  rw [hl, h, hr]

/-- Green's identity for a globally Lipschitz function and a compactly supported `C²` test:
`∫ ⟨∇f, ∇ψ⟩ = -∫ f Δψ`. -/
theorem integral_inner_gradient_eq_neg_integral_mul_laplacian_of_lipschitz {d : ℕ}
    {f ψ : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ y, inner ℝ (gradient f y) (gradient ψ y) = -∫ y, f y * (Δ ψ) y := by
  let b := stdOrthonormalBasis ℝ (Space d)
  have hd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  have hdi : ∀ i, ContDiff ℝ 1 (fun y ↦ fderiv ℝ ψ y (b i)) := fun i ↦
    hd.clm_apply contDiff_const
  have hdc : ∀ i, HasCompactSupport (fun y ↦ fderiv ℝ ψ y (b i)) := fun i ↦
    hψc.fderiv_apply ℝ (b i)
  have hint1 : ∀ i, Integrable (fun y ↦ fderiv ℝ f y (b i) * fderiv ℝ ψ y (b i)) := by
    intro i
    refine ((hdi i).continuous.integrable_of_hasCompactSupport (hdc i)).bdd_mul
      (c := K * ‖b i‖) (measurable_fderiv_apply_const ℝ f (b i)).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ ?_))
    exact ((fderiv ℝ f y).le_opNorm (b i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
  have hint2 : ∀ i, Integrable
      (fun y ↦ f y * fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b i)) y (b i)) := by
    intro i
    have hcont : Continuous (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ ψ z (b i)) y (b i)) :=
      ((hdi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hf.continuous.mul hcont).integrable_of_hasCompactSupport
      ((hdc i).fderiv_apply ℝ (b i)).mul_left
  simp_rw [inner_gradient_eq_sum_fderiv b f ψ]
  rw [integral_finsetSum _ (fun i _ ↦ hint1 i)]
  simp_rw [integral_fderiv_apply_mul_eq_neg_of_lipschitz hf (hdi _) (hdc _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ ↦ hint2 i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [laplacian_eq_sum_fderiv b (hd.differentiable_one y), Finset.mul_sum]

/-- Squared-`L²` convergence on a finite measure space implies `L¹` convergence. -/
theorem tendsto_integral_abs_of_sq_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {h : ℕ → X → ℝ} (hh : ∀ j, MemLp (h j) 2 μ)
    (hlim : Tendsto (fun j ↦ ∫ x, h j x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x, |h j x| ∂μ) atTop (𝓝 0) := by
  have hbound : ∀ j, ∫ x, |h j x| ∂μ ≤ Real.sqrt (μ.real Set.univ * ∫ x, h j x ^ 2 ∂μ) := by
    intro j
    have hi : Integrable (fun x ↦ |h j x|) μ := ((hh j).integrable one_le_two).abs
    have hi2 : Integrable (fun x ↦ |h j x| ^ 2) μ := by
      simpa only [sq_abs] using (hh j).integrable_sq
    have hcs := sq_integral_le_measureReal_mul_integral_sq hi hi2
    simp only [sq_abs] at hcs
    rw [← Real.sqrt_sq (integral_nonneg (fun x ↦ abs_nonneg (h j x)))]
    exact Real.sqrt_le_sqrt hcs
  have hs : Tendsto (fun j ↦ Real.sqrt (μ.real Set.univ * ∫ x, h j x ^ 2 ∂μ)) atTop (𝓝 0) := by
    have h0 := (hlim.const_mul (μ.real Set.univ)).sqrt
    rwa [mul_zero, Real.sqrt_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) hbound

/-- Squared-`L²` convergence on a set of finite measure implies convergence of the integrals
against bounded weights vanishing off that set. -/
theorem tendsto_integral_mul_of_sq_tendsto {d : ℕ} {S : Set (Space d)}
    (hSf : volume S ≠ ⊤) {F : ℕ → Space d → ℝ} {g χ : Space d → ℝ}
    (hFg : ∀ j, MemLp (fun y ↦ F j y - g y) 2 (volume.restrict S))
    (hlim : Tendsto (fun j ↦ ∫ y in S, (F j y - g y) ^ 2) atTop (𝓝 0))
    {B : ℝ} (hχ : ∀ y, |χ y| ≤ B) (hχS : ∀ y ∉ S, χ y = 0)
    (hFi : ∀ j, Integrable (fun y ↦ F j y * χ y)) (hgi : Integrable (fun y ↦ g y * χ y)) :
    Tendsto (fun j ↦ ∫ y, F j y * χ y) atTop (𝓝 (∫ y, g y * χ y)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have hL1 := tendsto_integral_abs_of_sq_tendsto hFg hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ j, ‖(∫ y, F j y * χ y) - ∫ y, g y * χ y‖ ≤ B * ∫ y in S, |F j y - g y| := by
    intro j
    have hzero : ∀ y ∉ S, F j y * χ y - g y * χ y = 0 := fun y hy ↦ by
      rw [hχS y hy]
      ring
    rw [← integral_sub (hFi j) hgi, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      ← integral_const_mul]
    apply norm_integral_le_of_norm_le (((hFg j).integrable one_le_two).abs.const_mul B)
    apply Eventually.of_forall
    intro y
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hχ y) (abs_nonneg _)
  have h0 : Tendsto (fun j ↦ B * ∫ y in S, |F j y - g y|) atTop (𝓝 0) := by
    have h1 := hL1.const_mul B
    rwa [mul_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun _ ↦ norm_nonneg _) hle

/-- **Weak harmonicity passes to `L²` limits.** If Lipschitz functions `f j` converge to `g` in
`L²(B_r)` for every `r < R`, and their Dirichlet pairings with a compactly supported `C²` test
`ψ` supported in `B_R` tend to zero, then `∫ g Δψ = 0`. -/
theorem integral_mul_laplacian_eq_zero_of_sq_tendsto {d : ℕ} {x : Space d} {R : ℝ}
    {f : ℕ → Space d → ℝ} {g : Space d → ℝ} (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hg : ∀ r < R, MemLp g 2 (volume.restrict (ball x r)))
    (hlim : ∀ r < R, Tendsto (fun j ↦ ∫ y in ball x r, (f j y - g y) ^ 2) atTop (𝓝 0))
    {ψ : Space d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ ball x R)
    (hweak : Tendsto (fun j ↦ ∫ y, inner ℝ (gradient (f j) y) (gradient ψ y)) atTop (𝓝 0)) :
    ∫ y, g y * (Δ ψ) y = 0 := by
  choose K hK using hf
  obtain ⟨r, hrR, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψs
  have hΔc : Continuous (Δ ψ) := continuous_laplacian_aux hψ
  have hΔs : ∀ y ∉ ball x r, (Δ ψ) y = 0 := fun y hy ↦
    laplacian_eq_zero_of_notMem_tsupport_aux ψ (fun h ↦ hy (hsub h))
  have hΔcs : HasCompactSupport (Δ ψ) := by
    apply hψc.mono'
    intro y hy
    by_contra hn
    exact hy (laplacian_eq_zero_of_notMem_tsupport_aux ψ hn)
  obtain ⟨B, hB⟩ := hΔcs.exists_bound_of_continuous hΔc
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hFi : ∀ j, Integrable (fun y ↦ f j y * (Δ ψ) y) := fun j ↦
    ((hK j).continuous.mul hΔc).integrable_of_hasCompactSupport hΔcs.mul_left
  have hgi : Integrable (fun y ↦ g y * (Δ ψ) y) := by
    have hgr : IntegrableOn g (ball x r) := (hg r hrR).integrable one_le_two
    have hon : IntegrableOn (fun y ↦ g y * (Δ ψ) y) (ball x r) :=
      hgr.mul_bdd hΔc.aestronglyMeasurable (Eventually.of_forall hB)
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
    intro y hy
    by_contra hn
    exact hy (by simp only [hΔs y hn, mul_zero])
  have htend := tendsto_integral_mul_of_sq_tendsto measure_ball_lt_top.ne
    (fun j ↦ (memLp_two_ball_of_continuous (hK j).continuous x r).sub (hg r hrR))
    (hlim r hrR) (fun y ↦ by simpa only [Real.norm_eq_abs] using hB y) hΔs hFi hgi
  have heq : ∀ j, -∫ y, inner ℝ (gradient (f j) y) (gradient ψ y) = ∫ y, f j y * (Δ ψ) y := by
    intro j
    rw [integral_inner_gradient_eq_neg_integral_mul_laplacian_of_lipschitz (hK j) hψ hψc,
      neg_neg]
  have h2 : Tendsto (fun j ↦ ∫ y, f j y * (Δ ψ) y) atTop (𝓝 0) := by
    have h3 := hweak.neg
    rw [neg_zero] at h3
    exact h3.congr heq
  exact tendsto_nhds_unique htend h2

/-- A function that is square integrable on every ball `B_r`, `r < R`, is locally integrable on
`B_R`. -/
theorem locallyIntegrableOn_ball_of_memLp {d : ℕ} {x : Space d} {R : ℝ} {g : Space d → ℝ}
    (hg : ∀ r < R, MemLp g 2 (volume.restrict (ball x r))) :
    LocallyIntegrableOn g (ball x R) := by
  intro y hy
  have hyR : dist y x < R := hy
  have hr : (dist y x + R) / 2 < R := by linarith
  have : IsFiniteMeasure (volume.restrict (ball x ((dist y x + R) / 2))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  refine ⟨ball x ((dist y x + R) / 2), ?_, (hg _ hr).integrable one_le_two⟩
  apply mem_nhdsWithin_of_mem_nhds
  apply isOpen_ball.mem_nhds
  change dist y x < (dist y x + R) / 2
  linarith

/-- **Weak harmonicity of `L²` limits**, in the form required by Weyl's lemma: the limit is
locally integrable on `B_R` and annihilates the Laplacian of every smooth test compactly supported
in `B_R`. -/
theorem weakHarmonic_of_sq_tendsto {d : ℕ} {x : Space d} {R : ℝ}
    {f : ℕ → Space d → ℝ} {g : Space d → ℝ} (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hg : ∀ r < R, MemLp g 2 (volume.restrict (ball x r)))
    (hlim : ∀ r < R, Tendsto (fun j ↦ ∫ y in ball x r, (f j y - g y) ^ 2) atTop (𝓝 0))
    (hweak : ∀ ψ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball x R →
        Tendsto (fun j ↦ ∫ y, inner ℝ (gradient (f j) y) (gradient ψ y)) atTop (𝓝 0)) :
    LocallyIntegrableOn g (ball x R) ∧
      ∀ ψ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball x R → ∫ y, g y * (Δ ψ) y = 0 :=
  ⟨locallyIntegrableOn_ball_of_memLp hg, fun ψ hψ hψc hψs ↦
    integral_mul_laplacian_eq_zero_of_sq_tendsto hf hg hlim (hψ.of_le (by simp)) hψc hψs
      (hweak ψ hψ hψc hψs)⟩

/-! ### Lower semicontinuity of the Dirichlet energy -/

/-- The squared operator norm of a derivative is the sum of the squared directional derivatives
along an orthonormal basis. -/
private theorem norm_fderiv_sq_eq_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Space d)) (g : Space d → ℝ) (y : Space d) :
    ‖fderiv ℝ g y‖ ^ 2 = ∑ i, (fderiv ℝ g y (b i)) ^ 2 := by
  have h := inner_gradient_eq_sum_fderiv b g g y
  rw [real_inner_self_eq_norm_sq] at h
  have hn : ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [← hn, h]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A function continuous on an open set times a continuous cutoff supported inside it is
continuous. -/
private theorem continuous_mul_of_tsupport_subset_aux {d : ℕ} {a χ : Space d → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (ha : ContinuousOn a Ω) (hχ : Continuous χ)
    (hsub : tsupport χ ⊆ Ω) : Continuous (fun y ↦ a y * χ y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ Ω
  · exact (ha.continuousAt (hΩ.mem_nhds hy)).mul hχ.continuousAt
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    have hz := notMem_tsupport_iff_eventuallyEq.1 (fun hy' ↦ hy (hsub hy'))
    filter_upwards [hz] with z hz
    have hz' : χ z = 0 := hz
    rw [hz', mul_zero]

/-- Functions continuous on a closed ball are integrable on the open ball. -/
private theorem integrableOn_ball_of_continuousOn {d : ℕ} {F : Space d → ℝ} {x : Space d} {r : ℝ}
    (hF : ContinuousOn F (closedBall x r)) : IntegrableOn F (ball x r) :=
  (hF.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall

/-- A function continuous on `B_R` is approximated in `L²(B_r)`, `r < R`, by `C¹` functions whose
supports are compact subsets of `B_r`. -/
theorem exists_contDiff_tsupport_subset_ball_sq_integral_lt {d : ℕ} {x : Space d} {r R : ℝ}
    (hrR : r < R) {a : Space d → ℝ} (ha : ContinuousOn a (ball x R)) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : Space d → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball x r ∧
      ∫ y in ball x r, (a y - ψ y) ^ 2 < η := by
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · intro y hy
      simp [tsupport] at hy
    · rw [ball_eq_empty.2 hr, Measure.restrict_empty, integral_zero_measure]
      exact hη
  have hcb : closedBall x r ⊆ ball x R := closedBall_subset_ball hrR
  obtain ⟨A, hA⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn (ha.mono hcb)
  have hk2 : ∀ k : ℕ, (1 : ℝ) < (k : ℝ) + 2 := fun k ↦ by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  -- cutoffs equal to one on `B_{r - r/(k+2)}` and supported in `B_{r - r/(2(k+2))}`
  let χ : ℕ → ContDiffBump x := fun k ↦
    { rIn := r - r / ((k : ℝ) + 2)
      rOut := r - r / (2 * ((k : ℝ) + 2))
      rIn_pos := by
        have := div_lt_self hr (hk2 k)
        linarith
      rIn_lt_rOut := by
        have : r / (2 * ((k : ℝ) + 2)) < r / ((k : ℝ) + 2) :=
          div_lt_div_of_pos_left hr (by linarith [hk2 k]) (by linarith [hk2 k])
        linarith }
  have hχout : ∀ k, (χ k).rOut < r := fun k ↦ by
    have : 0 < r / (2 * ((k : ℝ) + 2)) := by
      have := hk2 k
      positivity
    change r - r / (2 * ((k : ℝ) + 2)) < r
    linarith
  have hcont : ∀ k, Continuous (fun y ↦ a y * χ k y) := fun k ↦
    continuous_mul_of_tsupport_subset_aux isOpen_ball ha (χ k).continuous
      (by rw [(χ k).tsupport_eq]; exact closedBall_subset_ball ((hχout k).trans hrR))
  have hex : ∀ k : ℕ, ∃ ψ : Space d → ℝ, ContDiff ℝ 1 ψ ∧
      (∀ y, |ψ y - a y * χ k y| < 1 / ((k : ℝ) + 1)) ∧
      Function.support ψ ⊆ Function.support (fun y ↦ a y * χ k y) := by
    intro k
    obtain ⟨ψ, hψ, happ, hsupp⟩ := (hcont k).exists_contDiff_approx 1
      (continuous_const (y := 1 / ((k : ℝ) + 1))) (fun _ ↦ by positivity)
    exact ⟨ψ, by simpa using hψ, fun y ↦ by simpa only [Real.dist_eq] using happ y, hsupp⟩
  choose ψ hψ happ hsupp using hex
  have hts : ∀ k, tsupport (ψ k) ⊆ closedBall x (χ k).rOut := by
    intro k
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    have h1 := hsupp k hy
    have h2 : y ∈ Function.support (χ k) := by
      intro h0
      apply h1
      simp only [h0, mul_zero]
    rw [(χ k).support_eq] at h2
    exact ball_subset_closedBall h2
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hbound : ∀ k, ∀ y ∈ ball x r, |a y - ψ k y| ≤ 2 * A + 1 := by
    intro k y hy
    have hay : |a y| ≤ A := by
      simpa only [Real.norm_eq_abs] using hA y (ball_subset_closedBall hy)
    have hχ0 : 0 ≤ χ k y := (χ k).nonneg
    have hχ1 : χ k y ≤ 1 := (χ k).le_one
    have hprod : |a y * χ k y| ≤ A := by
      rw [abs_mul, abs_of_nonneg hχ0]
      calc |a y| * χ k y ≤ |a y| * 1 := mul_le_mul_of_nonneg_left hχ1 (abs_nonneg _)
        _ ≤ A := by linarith
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    obtain ⟨h1a, h1b⟩ := abs_le.mp hay
    obtain ⟨h2a, h2b⟩ := abs_lt.mp (happ k y)
    obtain ⟨h3a, h3b⟩ := abs_le.mp hprod
    rw [abs_le]
    constructor <;> linarith
  have hpt : ∀ y ∈ ball x r, Tendsto (fun k ↦ (a y - ψ k y) ^ 2) atTop (𝓝 0) := by
    intro y hy
    have hy' : dist y x < r := hy
    have ht : Tendsto (fun k : ℕ ↦ r / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hev : ∀ᶠ k : ℕ in atTop, |ψ k y - a y| ≤ 1 / ((k : ℝ) + 1) := by
      filter_upwards [ht.eventually (ge_mem_nhds (sub_pos.2 hy'))] with k hk
      have hmem : y ∈ closedBall x (χ k).rIn := by
        change dist y x ≤ r - r / ((k : ℝ) + 2)
        linarith
      have h1 := happ k y
      rw [(χ k).one_of_mem_closedBall hmem, mul_one] at h1
      exact h1.le
    have hψt : Tendsto (fun k ↦ ψ k y) atTop (𝓝 (a y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall (fun k ↦ norm_nonneg _)) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [hev] with k hk
      rwa [Real.norm_eq_abs]
    have h2 := ((tendsto_const_nhds (x := a y)).sub hψt).pow 2
    rwa [sub_self, zero_pow two_ne_zero] at h2
  have hconv : Tendsto (fun k ↦ ∫ y in ball x r, (a y - ψ k y) ^ 2) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (ball x r))
      (F := fun k y ↦ (a y - ψ k y) ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * A + 1) ^ 2)
      (fun k ↦ (((ha.mono (ball_subset_ball hrR.le)).aestronglyMeasurable
        measurableSet_ball).sub (hψ k).continuous.aestronglyMeasurable).pow 2)
      (integrable_const _)
      (fun k ↦ by
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h1 := pow_le_pow_left₀ (abs_nonneg _) (hbound k y hy) 2
        rwa [sq_abs] at h1)
      (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        exact hpt y hy)
    simpa only [integral_zero] using h
  obtain ⟨k, hk⟩ := (hconv.eventually (gt_mem_nhds hη)).exists
  exact ⟨ψ k, hψ k, (isCompact_closedBall x _).of_isClosed_subset (isClosed_tsupport _) (hts k),
    (hts k).trans (closedBall_subset_ball (hχout k)), hk⟩

/-- Lower semicontinuity of the energy of a single directional derivative under `L²(B_r)`
convergence to a function that is `C¹` on a larger ball. -/
theorem eventually_integral_sq_fderiv_apply_le {d : ℕ} {x : Space d} {r R : ℝ} (hrR : r < R)
    {f : ℕ → Space d → ℝ} {g : Space d → ℝ} (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hg : ContDiffOn ℝ 1 g (ball x R))
    (hlim : Tendsto (fun j ↦ ∫ y in ball x r, (f j y - g y) ^ 2) atTop (𝓝 0))
    (v : Space d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, (∫ y in ball x r, (fderiv ℝ g y v) ^ 2) - ε ≤
      ∫ y in ball x r, (fderiv ℝ (f j) y v) ^ 2 := by
  choose K hK using hf
  have hcb : closedBall x r ⊆ ball x R := closedBall_subset_ball hrR
  have hBr : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x r)) := isFiniteMeasure_restrict.2 hBr
  have ha : ContinuousOn (fun y ↦ fderiv ℝ g y v) (ball x R) :=
    (hg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
  obtain ⟨ψ, hψ, hψc, hψs, hψa⟩ :=
    exists_contDiff_tsupport_subset_ball_sq_integral_lt hrR ha (half_pos hε)
  have hψa' : ∫ y in ball x r, (fderiv ℝ g y v - ψ y) ^ 2 < ε / 2 := hψa
  have hψcont : Continuous ψ := hψ.continuous
  have hψ0 : ∀ y ∉ ball x r, ψ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψs h))
  have hψ' : Continuous (fun y ↦ fderiv ℝ ψ y v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψ'c : HasCompactSupport (fun y ↦ fderiv ℝ ψ y v) := hψc.fderiv_apply ℝ v
  have hψ's : ∀ y ∉ ball x r, fderiv ℝ ψ y v = 0 := by
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψs h))]
    rfl
  obtain ⟨B, hB⟩ := hψ'c.exists_bound_of_continuous hψ'
  -- square integrability of `g` and of its directional derivative on `B_r`
  have hgL2 : MemLp g 2 (volume.restrict (ball x r)) := by
    obtain ⟨Ag, hAg⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
      (hg.continuousOn.mono hcb)
    refine MemLp.of_bound ((hg.continuousOn.mono (ball_subset_ball hrR.le)).aestronglyMeasurable
      measurableSet_ball) Ag ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hAg y (ball_subset_closedBall hy)
  have haL2 : MemLp (fun y ↦ fderiv ℝ g y v) 2 (volume.restrict (ball x r)) := by
    obtain ⟨Aa, hAa⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn (ha.mono hcb)
    refine MemLp.of_bound ((ha.mono (ball_subset_ball hrR.le)).aestronglyMeasurable
      measurableSet_ball) Aa ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hAa y (ball_subset_closedBall hy)
  have hgψ : Integrable (fun y ↦ g y * fderiv ℝ ψ y v) := by
    have hon : IntegrableOn (fun y ↦ g y * fderiv ℝ ψ y v) (ball x r) :=
      (hgL2.integrable one_le_two).mul_bdd hψ'.aestronglyMeasurable (Eventually.of_forall hB)
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
    intro y hy
    by_contra hn
    exact hy (by simp only [hψ's y hn, mul_zero])
  have hpair : Tendsto (fun j ↦ ∫ y, f j y * fderiv ℝ ψ y v) atTop
      (𝓝 (∫ y, g y * fderiv ℝ ψ y v)) :=
    tendsto_integral_mul_of_sq_tendsto hBr
      (fun j ↦ (memLp_two_ball_of_continuous (hK j).continuous x r).sub hgL2) hlim
      (fun y ↦ by simpa only [Real.norm_eq_abs] using hB y) hψ's
      (fun j ↦ ((hK j).continuous.mul hψ').integrable_of_hasCompactSupport hψ'c.mul_left) hgψ
  -- integration by parts for `g` and for the Lipschitz functions
  have hIBPg : ∫ y, g y * fderiv ℝ ψ y v = -∫ y, fderiv ℝ g y v * ψ y :=
    integral_mul_fderiv_eq_neg_of_hasCompactSupport isOpen_ball hg hψ hψc
      (hψs.trans (ball_subset_ball hrR.le)) v
  have hconv : Tendsto (fun j ↦ ∫ y, fderiv ℝ (f j) y v * ψ y) atTop
      (𝓝 (∫ y, fderiv ℝ g y v * ψ y)) := by
    have h1 := hpair.neg
    rw [hIBPg, neg_neg] at h1
    refine h1.congr (fun j ↦ ?_)
    rw [integral_fderiv_apply_mul_eq_neg_of_lipschitz (hK j) hψ hψc v]
  have hev : ∀ᶠ j in atTop,
      (∫ y, fderiv ℝ g y v * ψ y) - ε / 4 < ∫ y, fderiv ℝ (f j) y v * ψ y :=
    hconv.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev] with j hj
  have hDm : AEStronglyMeasurable (fun y ↦ fderiv ℝ (f j) y v) volume :=
    (measurable_fderiv_apply_const ℝ (f j) v).aestronglyMeasurable
  have hDb : ∀ y, ‖fderiv ℝ (f j) y v‖ ≤ K j * ‖v‖ := fun y ↦
    ((fderiv ℝ (f j) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hK j)) (norm_nonneg _))
  have hD2i : IntegrableOn (fun y ↦ (fderiv ℝ (f j) y v) ^ 2) (ball x r) := by
    refine Measure.integrableOn_of_bounded (M := ((K j : ℝ) * ‖v‖) ^ 2) hBr (hDm.pow 2)
      (Eventually.of_forall (fun y ↦ ?_))
    change ‖(fderiv ℝ (f j) y v) ^ 2‖ ≤ ((K j : ℝ) * ‖v‖) ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDb y) 2
  have hψ2i : IntegrableOn (fun y ↦ ψ y ^ 2) (ball x r) :=
    integrableOn_ball_of_continuous (hψcont.pow 2) x r
  have hDψi : IntegrableOn (fun y ↦ fderiv ℝ (f j) y v * ψ y) (ball x r) :=
    (integrableOn_ball_of_continuous hψcont x r).bdd_mul hDm.restrict
      (Eventually.of_forall hDb)
  have h2i : IntegrableOn (fun y ↦ 2 * (fderiv ℝ (f j) y v * ψ y)) (ball x r) :=
    hDψi.const_mul 2
  have hlow : ∫ y in ball x r, (2 * (fderiv ℝ (f j) y v * ψ y) - ψ y ^ 2) ≤
      ∫ y in ball x r, (fderiv ℝ (f j) y v) ^ 2 := by
    refine integral_mono (h2i.sub hψ2i) hD2i (fun y ↦ ?_)
    change 2 * (fderiv ℝ (f j) y v * ψ y) - ψ y ^ 2 ≤ (fderiv ℝ (f j) y v) ^ 2
    nlinarith [sq_nonneg (fderiv ℝ (f j) y v - ψ y)]
  rw [integral_sub h2i hψ2i, integral_const_mul] at hlow
  have hDψ_eq : ∫ y in ball x r, fderiv ℝ (f j) y v * ψ y = ∫ y, fderiv ℝ (f j) y v * ψ y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by rw [hψ0 y hy, mul_zero])
  have hψL2 := memLp_two_ball_of_continuous hψcont x r
  have ha2i : IntegrableOn (fun y ↦ (fderiv ℝ g y v) ^ 2) (ball x r) := haL2.integrable_sq
  have haψ2i : IntegrableOn (fun y ↦ (fderiv ℝ g y v - ψ y) ^ 2) (ball x r) :=
    (haL2.sub hψL2).integrable_sq
  have haψi : IntegrableOn (fun y ↦ fderiv ℝ g y v * ψ y) (ball x r) :=
    (haL2.integrable one_le_two).mul_bdd hψcont.aestronglyMeasurable.restrict
      (Eventually.of_forall (fun y ↦ (show ‖ψ y‖ ≤ _ from
        (hψc.exists_bound_of_continuous hψcont).choose_spec y)))
  have h2aψ : IntegrableOn (fun y ↦ 2 * (fderiv ℝ g y v * ψ y)) (ball x r) := haψi.const_mul 2
  have hid : (∫ y in ball x r, (fderiv ℝ g y v) ^ 2) -
      ∫ y in ball x r, (fderiv ℝ g y v - ψ y) ^ 2 =
      2 * (∫ y in ball x r, fderiv ℝ g y v * ψ y) - ∫ y in ball x r, ψ y ^ 2 := by
    rw [← integral_sub ha2i haψ2i, ← integral_const_mul, ← integral_sub h2aψ hψ2i]
    congr 1
    funext y
    ring
  have haψ_eq : ∫ y in ball x r, fderiv ℝ g y v * ψ y = ∫ y, fderiv ℝ g y v * ψ y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by rw [hψ0 y hy, mul_zero])
  linarith

/-- **Lower semicontinuity of the Dirichlet energy.** If Lipschitz functions converge in `L²(B_r)`
to a function that is `C¹` on `B_R ⊇ closure B_r`, then for every `ε > 0` eventually
`∫_{B_r} |∇g|² - ε ≤ ∫_{B_r} |∇f_j|²`. -/
theorem eventually_integral_norm_fderiv_sq_le {d : ℕ} {x : Space d} {r R : ℝ} (hrR : r < R)
    {f : ℕ → Space d → ℝ} {g : Space d → ℝ} (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hg : ContDiffOn ℝ 1 g (ball x R))
    (hlim : Tendsto (fun j ↦ ∫ y in ball x r, (f j y - g y) ^ 2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, (∫ y in ball x r, ‖fderiv ℝ g y‖ ^ 2) - ε ≤
      ∫ y in ball x r, ‖fderiv ℝ (f j) y‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  set ε' := ε / ((d : ℝ) + 1) with hε'_def
  have hε' : 0 < ε' := by positivity
  have hcomp : ∀ i, ∀ᶠ j in atTop, (∫ y in ball x r, (fderiv ℝ g y (b i)) ^ 2) - ε' ≤
      ∫ y in ball x r, (fderiv ℝ (f j) y (b i)) ^ 2 := fun i ↦
    eventually_integral_sq_fderiv_apply_le hrR hf hg hlim (b i) hε'
  filter_upwards [eventually_all.2 hcomp] with j hj
  obtain ⟨K, hK⟩ := hf j
  have hcb : closedBall x r ⊆ ball x R := closedBall_subset_ball hrR
  have hgi : ∀ i, IntegrableOn (fun y ↦ (fderiv ℝ g y (b i)) ^ 2) (ball x r) := fun i ↦
    integrableOn_ball_of_continuousOn
      ((((hg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply
        continuousOn_const).mono hcb).pow 2)
  have hfi : ∀ i, IntegrableOn (fun y ↦ (fderiv ℝ (f j) y (b i)) ^ 2) (ball x r) := by
    intro i
    refine Measure.integrableOn_of_bounded (M := ((K : ℝ) * ‖b i‖) ^ 2)
      measure_ball_lt_top.ne
      ((measurable_fderiv_apply_const ℝ (f j) (b i)).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ ?_))
    change ‖(fderiv ℝ (f j) y (b i)) ^ 2‖ ≤ ((K : ℝ) * ‖b i‖) ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (((fderiv ℝ (f j) y).le_opNorm (b i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _))) 2
  have hsumg : ∫ y in ball x r, ‖fderiv ℝ g y‖ ^ 2 =
      ∑ i, ∫ y in ball x r, (fderiv ℝ g y (b i)) ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ ↦ hgi i)]
    congr 1
    funext y
    exact norm_fderiv_sq_eq_sum b g y
  have hsumf : ∫ y in ball x r, ‖fderiv ℝ (f j) y‖ ^ 2 =
      ∑ i, ∫ y in ball x r, (fderiv ℝ (f j) y (b i)) ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ ↦ hfi i)]
    congr 1
    funext y
    exact norm_fderiv_sq_eq_sum b (f j) y
  rw [hsumg, hsumf]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hj i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hnε : (d : ℝ) * ε' ≤ ε := by
    rw [hε'_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Lower semicontinuity of the Dirichlet energy**, `liminf` form (the energies are assumed
bounded above, as they are in the Rellich setting). -/
theorem integral_norm_fderiv_sq_le_liminf {d : ℕ} {x : Space d} {r R : ℝ} (hrR : r < R)
    {f : ℕ → Space d → ℝ} {g : Space d → ℝ} (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hg : ContDiffOn ℝ 1 g (ball x R))
    (hlim : Tendsto (fun j ↦ ∫ y in ball x r, (f j y - g y) ^ 2) atTop (𝓝 0))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun j ↦ ∫ y in ball x r, ‖fderiv ℝ (f j) y‖ ^ 2)) :
    ∫ y in ball x r, ‖fderiv ℝ g y‖ ^ 2 ≤
      liminf (fun j ↦ ∫ y in ball x r, ‖fderiv ℝ (f j) y‖ ^ 2) atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := le_liminf_of_le hbdd.isCoboundedUnder_flip
    (eventually_integral_norm_fderiv_sq_le hrR hf hg hlim hε)
  linarith

/-! ### Averages -/

/-- Squared-`L²` convergence on a ball implies convergence of the averages over the ball. -/
theorem tendsto_setAverage_ball_of_sq_tendsto {d : ℕ} {x : Space d} {r : ℝ}
    {F : ℕ → Space d → ℝ} {g : Space d → ℝ} (hF : ∀ j, Continuous (F j))
    (hg : MemLp g 2 (volume.restrict (ball x r)))
    (hlim : Tendsto (fun j ↦ ∫ y in ball x r, (F j y - g y) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ⨍ y in ball x r, F j y) atTop (𝓝 (⨍ y in ball x r, g y)) := by
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hL1 := tendsto_integral_abs_of_sq_tendsto
    (fun j ↦ (memLp_two_ball_of_continuous (hF j) x r).sub hg) hlim
  have hgi : IntegrableOn g (ball x r) := hg.integrable one_le_two
  have hint : Tendsto (fun j ↦ ∫ y in ball x r, F j y) atTop (𝓝 (∫ y in ball x r, g y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun j ↦ ?_) hL1
    rw [← integral_sub (integrableOn_ball_of_continuous (hF j) x r) hgi, Real.norm_eq_abs]
    exact abs_integral_le_integral_abs
  simp_rw [setAverage_eq, smul_eq_mul]
  exact hint.const_mul _

/-- **Poincaré inequality with the average over a concentric sub-ball**: for `0 < s ≤ r`,
`∫_{B_r} |f - f_{B_s}|² ≤ 2 (1 + (r/s)^d) 2^(d+1) r² ∫_{B_r} |∇f|²`. -/
theorem poincare_ball_of_subball {d : ℕ} (x : Space d) {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    {f : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    ∫ y in ball x r, (f y - ⨍ z in ball x s, f z) ^ 2 ≤
      2 * (1 + (r / s) ^ d) * (2 ^ (d + 1) * r ^ 2 * ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2) := by
  have hr : 0 < r := hs.trans_le hsr
  set cr := ⨍ z in ball x r, f z with hcr
  set cs := ⨍ z in ball x s, f z with hcs
  set mr := volume.real (ball x r) with hmr
  set ms := volume.real (ball x s) with hms
  set Vr := ∫ y in ball x r, (f y - cr) ^ 2 with hVr
  have hP : Vr ≤ 2 ^ (d + 1) * r ^ 2 * ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2 :=
    poincare_ball x hr hf
  have hms0 : 0 < ms := measureReal_ball_pos x hs
  have hmsne : ms ≠ 0 := hms0.ne'
  have hsub : ball x s ⊆ ball x r := ball_subset_ball hsr
  have hratio : mr = (r / s) ^ d * ms := by
    rw [hmr, hms, measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
      Measure.addHaar_ball_of_pos volume x hs, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), div_pow]
    have hsd : s ^ d ≠ 0 := pow_ne_zero d hs.ne'
    field_simp
  have hfc : Continuous (fun y ↦ f y - cr) := hf.continuous.sub continuous_const
  have h1 : (∫ y in ball x s, (f y - cr)) ^ 2 ≤ ms * ∫ y in ball x s, (f y - cr) ^ 2 := by
    have : IsFiniteMeasure (volume.restrict (ball x s)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have h := sq_integral_le_measureReal_mul_integral_sq (μ := volume.restrict (ball x s))
      (integrableOn_ball_of_continuous hfc x s) (integrableOn_ball_of_continuous (hfc.pow 2) x s)
    rwa [measureReal_restrict_apply_univ] at h
  have h2 : ∫ y in ball x s, (f y - cr) ^ 2 ≤ Vr :=
    setIntegral_mono_set (integrableOn_ball_of_continuous (hfc.pow 2) x r)
      (Eventually.of_forall (fun _ ↦ sq_nonneg _)) (Eventually.of_forall hsub)
  have hcs_eq : cs - cr = ms⁻¹ * ∫ y in ball x s, (f y - cr) := by
    have hi1 : IntegrableOn f (ball x s) := integrableOn_ball_of_continuous hf.continuous x s
    have hi2 : IntegrableOn (fun _ : Space d ↦ cr) (ball x s) :=
      integrableOn_const measure_ball_lt_top.ne
    rw [integral_sub hi1 hi2, setIntegral_const, smul_eq_mul, hcs, setAverage_eq, smul_eq_mul,
      ← hms]
    field_simp
  have hdiff : (cs - cr) ^ 2 * ms ≤ Vr := by
    rw [hcs_eq]
    have hJ := h1.trans (mul_le_mul_of_nonneg_left h2 hms0.le)
    have e : (ms⁻¹ * ∫ y in ball x s, (f y - cr)) ^ 2 * ms =
        (∫ y in ball x s, (f y - cr)) ^ 2 / ms := by
      field_simp
    rw [e, div_le_iff₀ hms0]
    linarith
  have hpt : ∀ y, (f y - cs) ^ 2 ≤ 2 * (f y - cr) ^ 2 + 2 * (cr - cs) ^ 2 := fun y ↦ by
    nlinarith [sq_nonneg ((f y - cr) - (cr - cs))]
  have hi3 : IntegrableOn (fun y ↦ 2 * (f y - cr) ^ 2) (ball x r) :=
    (integrableOn_ball_of_continuous (hfc.pow 2) x r).const_mul 2
  have hi4 : IntegrableOn (fun _ : Space d ↦ 2 * (cr - cs) ^ 2) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hmain : ∫ y in ball x r, (f y - cs) ^ 2 ≤ 2 * Vr + 2 * mr * (cr - cs) ^ 2 := by
    have hL : IntegrableOn (fun y ↦ (f y - cs) ^ 2) (ball x r) :=
      integrableOn_ball_of_continuous ((hf.continuous.sub continuous_const).pow 2) x r
    have hR : IntegrableOn (fun y ↦ 2 * (f y - cr) ^ 2 + 2 * (cr - cs) ^ 2) (ball x r) :=
      hi3.add hi4
    have h : ∫ y in ball x r, (f y - cs) ^ 2 ≤
        ∫ y in ball x r, (2 * (f y - cr) ^ 2 + 2 * (cr - cs) ^ 2) :=
      integral_mono hL hR hpt
    rw [integral_add hi3 hi4, integral_const_mul, setIntegral_const, smul_eq_mul] at h
    linarith
  have hcr2 : (cr - cs) ^ 2 = (cs - cr) ^ 2 := by ring
  calc ∫ y in ball x r, (f y - cs) ^ 2 ≤ 2 * Vr + 2 * mr * (cr - cs) ^ 2 := hmain
    _ = 2 * Vr + 2 * (r / s) ^ d * ((cs - cr) ^ 2 * ms) := by
        rw [hratio, hcr2]
        ring
    _ ≤ 2 * Vr + 2 * (r / s) ^ d * Vr := by gcongr
    _ = 2 * (1 + (r / s) ^ d) * Vr := by ring
    _ ≤ 2 * (1 + (r / s) ^ d) * (2 ^ (d + 1) * r ^ 2 *
          ∫ y in ball x r, ‖fderiv ℝ f y‖ ^ 2) := by gcongr

/-! ### Packaged consequences -/

/-- A uniform bound on the Dirichlet energies passes to a `C¹` limit in `L²`. -/
theorem integral_norm_fderiv_sq_le_of_bound {d : ℕ} {x : Space d} {r R : ℝ} (hrR : r < R)
    {f : ℕ → Space d → ℝ} {g : Space d → ℝ} (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hg : ContDiffOn ℝ 1 g (ball x R))
    (hlim : Tendsto (fun j ↦ ∫ y in ball x r, (f j y - g y) ^ 2) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ j, ∫ y in ball x r, ‖fderiv ℝ (f j) y‖ ^ 2 ≤ M) :
    ∫ y in ball x r, ‖fderiv ℝ g y‖ ^ 2 ≤ M := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨j, hj⟩ := (eventually_integral_norm_fderiv_sq_le hrR hf hg hlim hε).exists
  linarith [hM j]

/-- **Rellich compactness with weak harmonicity of the limit.** A sequence of Lipschitz functions
with bounded `W^{1,2}(B_R)` energy whose Dirichlet pairings with every smooth test compactly
supported in `B_R` tend to zero has a subsequence converging in `L²(B_r)` for all `r < R` to a
measurable function `g` which is locally integrable on `B_R` and weakly harmonic there. -/
theorem exists_subseq_tendsto_weakHarmonic {d : ℕ} (x : Space d) (R M : ℝ)
    (f : ℕ → Space d → ℝ) (hf : ∀ j, ∃ K, LipschitzWith K (f j))
    (hM : ∀ j, ∫ y in ball x R, (f j y ^ 2 + ‖fderiv ℝ (f j) y‖ ^ 2) ≤ M)
    (hweak : ∀ ψ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball x R →
        Tendsto (fun j ↦ ∫ y, inner ℝ (gradient (f j) y) (gradient ψ y)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Space d → ℝ, Measurable g ∧
      (∀ r < R, MemLp g 2 (volume.restrict (ball x r))) ∧
      (∀ r < R, Tendsto (fun j ↦ ∫ y in ball x r, (f (φ j) y - g y) ^ 2) atTop (𝓝 0)) ∧
      LocallyIntegrableOn g (ball x R) ∧
      ∀ ψ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball x R → ∫ y, g y * (Δ ψ) y = 0 := by
  obtain ⟨φ, hφ, g, hgm, hgL2, hlim⟩ := exists_subseq_tendsto_sq_integral_ball x R M f hf hM
  have hw := weakHarmonic_of_sq_tendsto (f := fun j ↦ f (φ j)) (fun j ↦ hf (φ j)) hgL2 hlim
    (fun ψ hψ hψc hψs ↦ (hweak ψ hψ hψc hψs).comp hφ.tendsto_atTop)
  exact ⟨φ, hφ, g, hgm, hgL2, hlim, hw.1, hw.2⟩

end SerrinEpigraph
