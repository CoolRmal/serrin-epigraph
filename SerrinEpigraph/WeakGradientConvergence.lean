module

public import SerrinEpigraph.AlignedHeightDecomposition

/-!
# Weak convergence of gradients (input (E) of the aligned height decomposition)

Lipschitz functions `f_j` converging in `L²(B_R)` to a function `H` that is `C¹` and square
integrable on `B_R`, with bounded Dirichlet energies on `B_R`, have gradients converging weakly
against continuous vector fields supported in `B_r`, `r < R` (`weakGradientLimit`):

* for `C¹` test functions this is integration by parts on both sides
  (`integral_fderiv_apply_mul_eq_neg_of_lipschitz`,
  `integral_mul_fderiv_eq_neg_of_hasCompactSupport`) and the `L²` convergence
  (`tendsto_integral_mul_of_sq_tendsto`);
* a continuous test function is approximated in `L²` by `C¹` ones
  (`exists_contDiff_tsupport_subset_ball_sq_integral_lt`), with the error controlled by the
  Dirichlet bounds through `|ab| ≤ λ a²/2 + b²/(2λ)`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ}

theorem memLp_two_ball_of_lipschitz {f : Space m → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (R : ℝ) : MemLp f 2 (volume.restrict (ball (0 : Space m) R)) := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : Space m) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine MemLp.of_bound hf.continuous.aestronglyMeasurable (|f 0| + C * |R|) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  have h1 := hf.dist_le_mul y 0
  rw [Real.dist_eq, dist_zero_right] at h1
  have h2 : ‖y‖ ≤ |R| := by
    rw [mem_ball, dist_zero_right] at hy
    exact hy.le.trans (le_abs_self R)
  rw [Real.norm_eq_abs]
  calc |f y| ≤ |f 0| + |f y - f 0| := by
        have := abs_sub_abs_le_abs_sub (f y) (f 0)
        linarith
    _ ≤ |f 0| + C * |R| := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 C.2)

/-- `|∫_S a D - ∫_S b D| ≤ λ/2 ∫_S (a - b)² + (∫_S D²)/(2λ)`. -/
theorem abs_setIntegral_sub_mul_le {S : Set (Space m)} {a b D : Space m → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hab : IntegrableOn (fun y ↦ (a y - b y) ^ 2) S)
    (hD : IntegrableOn (fun y ↦ D y ^ 2) S) (haD : IntegrableOn (fun y ↦ a y * D y) S)
    (hbD : IntegrableOn (fun y ↦ b y * D y) S) :
    |(∫ y in S, a y * D y) - ∫ y in S, b y * D y| ≤
      lam / 2 * (∫ y in S, (a y - b y) ^ 2) + (∫ y in S, D y ^ 2) / (2 * lam) := by
  rw [← integral_sub haD hbD]
  have hR : IntegrableOn (fun y ↦ lam / 2 * (a y - b y) ^ 2 + D y ^ 2 / (2 * lam)) S :=
    (hab.const_mul _).add (hD.div_const _)
  calc |∫ y in S, (a y * D y - b y * D y)| ≤ ∫ y in S, |a y * D y - b y * D y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y in S, (lam / 2 * (a y - b y) ^ 2 + D y ^ 2 / (2 * lam)) := by
        refine integral_mono (haD.sub hbD).abs hR fun y ↦ ?_
        have h1 : |a y * D y - b y * D y| = |a y - b y| * |D y| := by
          rw [← sub_mul, abs_mul]
        rw [h1]
        have h2 : 0 ≤ (lam * |a y - b y| - |D y|) ^ 2 := sq_nonneg _
        have h3 : |a y - b y| * |D y| ≤
            lam / 2 * |a y - b y| ^ 2 + |D y| ^ 2 / (2 * lam) := by
          have e : (lam / 2 * |a y - b y| ^ 2 + |D y| ^ 2 / (2 * lam)) * (2 * lam) =
              lam ^ 2 * |a y - b y| ^ 2 + |D y| ^ 2 := by
            field_simp
          have key : |a y - b y| * |D y| * (2 * lam) ≤
              (lam / 2 * |a y - b y| ^ 2 + |D y| ^ 2 / (2 * lam)) * (2 * lam) := by
            rw [e]
            nlinarith [h2]
          exact le_of_mul_le_mul_right key (by positivity)
        simpa only [sq_abs] using h3
    _ = lam / 2 * (∫ y in S, (a y - b y) ^ 2) + (∫ y in S, D y ^ 2) / (2 * lam) := by
        rw [integral_add (hab.const_mul _) (hD.div_const _), integral_const_mul, integral_div]

/-- **One component of (E).** -/
theorem tendsto_integral_mul_fderiv_of_sq_tendsto {f : ℕ → Space m → ℝ} {H : Space m → ℝ}
    {K r R : ℝ} (hrR : r < R) (hLip : ∀ j, ∃ C, LipschitzWith C (f j))
    (hH : ContDiffOn ℝ 1 H (ball (0 : Space m) R))
    (hHL2 : MemLp H 2 (volume.restrict (ball (0 : Space m) R)))
    (hK : ∀ j, ∫ y in ball (0 : Space m) R, ‖fderiv ℝ (f j) y‖ ^ 2 ≤ K)
    (hlim : Tendsto (fun j ↦ ∫ y in ball (0 : Space m) R, (f j y - H y) ^ 2) atTop (𝓝 0))
    {χ : Space m → ℝ} (hχ : Continuous χ) (hχs : tsupport χ ⊆ ball (0 : Space m) r)
    (w : Space m) (hw : ‖w‖ ≤ 1) :
    Tendsto (fun j ↦ ∫ y, χ y * fderiv ℝ (f j) y w) atTop
      (𝓝 (∫ y, χ y * fderiv ℝ H y w)) := by
  set r₁ : ℝ := (r + R) / 2 with hr₁
  have hrr₁ : r < r₁ := by rw [hr₁]; linarith
  have hr₁R : r₁ < R := by rw [hr₁]; linarith
  set B₁ : Set (Space m) := ball (0 : Space m) r₁ with hB₁
  have hB₁R : B₁ ⊆ ball (0 : Space m) R := ball_subset_ball hr₁R.le
  have hcl : closedBall (0 : Space m) r₁ ⊆ ball (0 : Space m) R := closedBall_subset_ball hr₁R
  have hB₁f : volume B₁ ≠ ⊤ := measure_ball_lt_top.ne
  -- the derivative of `H` on `B̄_{r₁}`
  have hdHc : ContinuousOn (fun y ↦ fderiv ℝ H y w) (ball (0 : Space m) R) :=
    (hH.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
  have hdH2 : IntegrableOn (fun y ↦ (fderiv ℝ H y w) ^ 2) B₁ :=
    (((hdHc.mono hcl).pow 2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  set KH : ℝ := ∫ y in B₁, (fderiv ℝ H y w) ^ 2 with hKH
  have hKH0 : 0 ≤ KH := setIntegral_nonneg measurableSet_ball fun y _ ↦ sq_nonneg _
  -- the directional derivatives of the `f j`
  have hfdb : ∀ j, ∃ C : ℝ, ∀ y, |fderiv ℝ (f j) y w| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hLip j
    refine ⟨C, fun y ↦ ?_⟩
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (f j) y w‖ ≤ ‖fderiv ℝ (f j) y‖ * ‖w‖ := (fderiv ℝ (f j) y).le_opNorm w
      _ ≤ C * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hC) hw (norm_nonneg _) C.2
      _ = C := mul_one _
  have hfdm : ∀ j, Measurable (fun y ↦ fderiv ℝ (f j) y w) := fun j ↦
    measurable_fderiv_apply_const ℝ (f j) w
  have hfd : ∀ j, IntegrableOn (fun y ↦ (fderiv ℝ (f j) y w) ^ 2) B₁ ∧
      (∫ y in B₁, (fderiv ℝ (f j) y w) ^ 2) ≤ max K 0 := by
    intro j
    obtain ⟨C, hC⟩ := hLip j
    have hb : ∀ y, (fderiv ℝ (f j) y w) ^ 2 ≤ ‖fderiv ℝ (f j) y‖ ^ 2 := fun y ↦ by
      have h2 : |fderiv ℝ (f j) y w| ≤ ‖fderiv ℝ (f j) y‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖fderiv ℝ (f j) y w‖ ≤ ‖fderiv ℝ (f j) y‖ * ‖w‖ := (fderiv ℝ (f j) y).le_opNorm w
          _ ≤ ‖fderiv ℝ (f j) y‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
          _ = ‖fderiv ℝ (f j) y‖ := mul_one _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hint2 := integrableOn_fderiv_sq_of_lipschitz hC (r := r₁)
    have hint1 : IntegrableOn (fun y ↦ (fderiv ℝ (f j) y w) ^ 2) B₁ := by
      refine hint2.mono' ((hfdm j).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb y
    refine ⟨hint1, ?_⟩
    calc (∫ y in B₁, (fderiv ℝ (f j) y w) ^ 2) ≤ ∫ y in B₁, ‖fderiv ℝ (f j) y‖ ^ 2 :=
          setIntegral_mono_on hint1 hint2 measurableSet_ball fun y _ ↦ hb y
      _ ≤ ∫ y in ball (0 : Space m) R, ‖fderiv ℝ (f j) y‖ ^ 2 :=
          setIntegral_mono_set (integrableOn_fderiv_sq_of_lipschitz hC)
            (Eventually.of_forall fun y ↦ sq_nonneg _) (Eventually.of_forall hB₁R)
      _ ≤ max K 0 := (hK j).trans (le_max_left _ _)
  -- integrability of products with continuous functions on `B₁`
  have hprodf : ∀ (a : Space m → ℝ), Continuous a → ∀ j,
      IntegrableOn (fun y ↦ a y * fderiv ℝ (f j) y w) B₁ := by
    intro a ha j
    obtain ⟨C, hC⟩ := hfdb j
    obtain ⟨Ca, hCa⟩ := (isCompact_closedBall (0 : Space m) r₁).exists_bound_of_continuousOn
      ha.continuousOn
    refine Measure.integrableOn_of_bounded (M := Ca * C) hB₁f
      (ha.aestronglyMeasurable.mul (hfdm j).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [norm_mul, Real.norm_eq_abs (fderiv ℝ (f j) y w)]
    exact mul_le_mul (hCa y (ball_subset_closedBall hy)) (hC y) (abs_nonneg _)
      ((norm_nonneg _).trans (hCa y (ball_subset_closedBall hy)))
  have hprodH : ∀ (a : Space m → ℝ), Continuous a →
      IntegrableOn (fun y ↦ a y * fderiv ℝ H y w) B₁ := fun a ha ↦
    ((ha.continuousOn.mul (hdHc.mono hcl)).integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  -- step 1: `C¹` test functions supported in `B₁`
  have hsmooth : ∀ ψ : Space m → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ B₁ →
      Tendsto (fun j ↦ ∫ y, ψ y * fderiv ℝ (f j) y w) atTop
        (𝓝 (∫ y, ψ y * fderiv ℝ H y w)) := by
    intro ψ hψ hcψ hψs
    have hdψ : Continuous (fun y ↦ fderiv ℝ ψ y w) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hsuppψ : ∀ y, y ∉ tsupport ψ → fderiv ℝ ψ y w = 0 := fun y hn ↦ by
      simp [fderiv_of_notMem_tsupport ℝ hn]
    have hcdψ : HasCompactSupport (fun y ↦ fderiv ℝ ψ y w) :=
      hcψ.mono' (fun y hy ↦ by
        by_contra hn
        exact hy (hsuppψ y hn))
    obtain ⟨Bψ, hBψ⟩ := hdψ.bounded_above_of_compact_support hcdψ
    have hzero : ∀ y ∉ ball (0 : Space m) R, fderiv ℝ ψ y w = 0 := fun y hy ↦
      hsuppψ y (fun h' ↦ hy (hB₁R (hψs h')))
    have hHψ : Integrable (fun y ↦ H y * fderiv ℝ ψ y w) := by
      have h1 : IntegrableOn (fun y ↦ H y * fderiv ℝ ψ y w) (tsupport ψ) :=
        (((hH.mono (hψs.trans hB₁R)).continuousOn).mul hdψ.continuousOn).integrableOn_compact
          hcψ.isCompact
      refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
      intro y hy
      by_contra hn
      exact hy (by simp [hsuppψ y hn])
    have hlim' := tendsto_integral_mul_of_sq_tendsto (S := ball (0 : Space m) R)
      measure_ball_lt_top.ne (F := f) (g := H) (χ := fun y ↦ fderiv ℝ ψ y w)
      (fun j ↦ by
        obtain ⟨C, hC⟩ := hLip j
        exact (memLp_two_ball_of_lipschitz hC R).sub hHL2) hlim (B := Bψ)
      (fun y ↦ by rw [← Real.norm_eq_abs]; exact hBψ y) hzero
      (fun j ↦ by
        obtain ⟨C, hC⟩ := hLip j
        exact (hC.continuous.mul hdψ).integrable_of_hasCompactSupport hcdψ.mul_left) hHψ
    have e1 : ∀ j, (∫ y, ψ y * fderiv ℝ (f j) y w) = -∫ y, f j y * fderiv ℝ ψ y w := by
      intro j
      obtain ⟨C, hC⟩ := hLip j
      rw [← integral_fderiv_apply_mul_eq_neg_of_lipschitz hC hψ hcψ w]
      exact integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
    have e2 : (∫ y, ψ y * fderiv ℝ H y w) = -∫ y, H y * fderiv ℝ ψ y w := by
      rw [integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := volume) isOpen_ball hH hψ hcψ
        (hψs.trans hB₁R) w, neg_neg]
      exact integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
    rw [e2]
    exact hlim'.neg.congr fun j ↦ (e1 j).symm
  -- step 2: approximation of `χ` in `L²(B₁)`
  have hχB : ∀ y ∉ B₁, χ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (ball_subset_ball hrr₁.le (hχs h')))
  rw [Metric.tendsto_atTop]
  intro ε hε
  set A : ℝ := max K 0 + KH with hA
  have hA0 : 0 ≤ A := add_nonneg (le_max_right _ _) hKH0
  set lam : ℝ := 3 * (A + 1) / ε with hlam
  have hlam0 : 0 < lam := div_pos (by linarith) hε
  have hAlam : A / (2 * lam) < ε / 3 := by
    rw [hlam, div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  set η : ℝ := ε / (3 * lam) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ψ, hψ, hcψ, hψs, hψη⟩ := exists_contDiff_tsupport_subset_ball_sq_integral_lt
    (x := (0 : Space m)) hr₁R hχ.continuousOn hη0
  have hψc : Continuous ψ := hψ.continuous
  have hψB : ∀ y ∉ B₁, ψ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hψs h'))
  have hdiff2 : IntegrableOn (fun y ↦ (χ y - ψ y) ^ 2) B₁ :=
    (((hχ.sub hψc).pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hsmooth ψ hψ hcψ hψs) (ε / 3) (by positivity)
  refine ⟨N, fun j hj ↦ ?_⟩
  have hNj := hN j hj
  have eB : ∀ (a D : Space m → ℝ), (∀ y ∉ B₁, a y = 0) →
      (∫ y, a y * D y) = ∫ y in B₁, a y * D y := fun a D ha ↦
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [ha y hy, zero_mul]).symm
  rw [Real.dist_eq, eB χ _ hχB, eB χ _ hχB]
  rw [Real.dist_eq, eB ψ _ hψB, eB ψ _ hψB] at hNj
  have b1 := abs_setIntegral_sub_mul_le hlam0 hdiff2 (hfd j).1 (hprodf χ hχ j) (hprodf ψ hψc j)
  have b2 := abs_setIntegral_sub_mul_le hlam0 hdiff2 hdH2 (hprodH χ hχ) (hprodH ψ hψc)
  have hη' : lam / 2 * (∫ y in B₁, (χ y - ψ y) ^ 2) ≤ lam / 2 * η :=
    mul_le_mul_of_nonneg_left hψη.le (by positivity)
  have hf2 := (hfd j).2
  have hlη : lam / 2 * η + lam / 2 * η = ε / 3 := by
    rw [hη]
    field_simp
    ring
  have hdivs : (∫ y in B₁, (fderiv ℝ (f j) y w) ^ 2) / (2 * lam) + KH / (2 * lam) ≤
      A / (2 * lam) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by rw [hA]; linarith) (by positivity)
  set A1 := ∫ y in B₁, χ y * fderiv ℝ (f j) y w
  set A2 := ∫ y in B₁, ψ y * fderiv ℝ (f j) y w
  set A3 := ∫ y in B₁, χ y * fderiv ℝ H y w
  set A4 := ∫ y in B₁, ψ y * fderiv ℝ H y w
  calc |A1 - A3| ≤ |A1 - A2| + |A2 - A4| + |A3 - A4| := by
        have h1 := abs_sub_le A1 A2 A3
        have h2 := abs_sub_le A2 A4 A3
        rw [abs_sub_comm A4 A3] at h2
        linarith
    _ < ε := by
        have : |A2 - A4| < ε / 3 := hNj
        linarith

/-- **(E) Weak convergence of gradients.** -/
theorem weakGradientLimit (m : ℕ) : WeakGradientLimit m := by
  intro f H K r R hrR hLip hH hHL2 hK hlim ζ hζ hζs
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  have hcomp : ∀ (F : Space m → ℝ) (y : Space m),
      inner ℝ (ζ y) (gradient F y) = ∑ i, inner ℝ (ζ y) (b i) * fderiv ℝ F y (b i) := by
    intro F y
    rw [← b.sum_inner_mul_inner (ζ y) (gradient F y)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm (gradient F y) (b i), inner_gradient_left]
  have hχi : ∀ i, Continuous (fun y ↦ inner ℝ (ζ y) (b i)) := fun i ↦
    hζ.inner continuous_const
  have hχis : ∀ i, tsupport (fun y ↦ inner ℝ (ζ y) (b i)) ⊆ ball (0 : Space m) r := fun i ↦
    (closure_minimal (fun y (hy : y ∈ Function.support (fun y ↦ inner ℝ (ζ y) (b i))) ↦
      subset_tsupport ζ (fun h0 ↦ (Function.mem_support.mp hy) (by simp [h0])))
      (isClosed_tsupport ζ)).trans hζs
  have hcχi : ∀ i, HasCompactSupport (fun y ↦ inner ℝ (ζ y) (b i)) := fun i ↦
    isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (isBounded_ball.subset (hχis i))
  have hbi : ∀ i, ‖b i‖ ≤ 1 := fun i ↦ by simp [b]
  have hdHc : ContinuousOn (fderiv ℝ H) (ball (0 : Space m) R) :=
    hH.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hintf : ∀ j i, Integrable (fun y ↦ inner ℝ (ζ y) (b i) * fderiv ℝ (f j) y (b i)) := by
    intro j i
    obtain ⟨C, hC⟩ := hLip j
    obtain ⟨Ca, hCa⟩ := (hχi i).bounded_above_of_compact_support (hcχi i)
    have h1 : IntegrableOn (fun y ↦ inner ℝ (ζ y) (b i) * fderiv ℝ (f j) y (b i))
        (tsupport (fun y ↦ inner ℝ (ζ y) (b i))) := by
      refine Measure.integrableOn_of_bounded (M := Ca * (C * 1))
        (hcχi i).isCompact.measure_lt_top.ne
        ((hχi i).aestronglyMeasurable.mul
          (measurable_fderiv_apply_const ℝ (f j) (b i)).aestronglyMeasurable)
        (Eventually.of_forall fun y ↦ ?_)
      rw [norm_mul]
      refine mul_le_mul (hCa y) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hCa y))
      exact ((fderiv ℝ (f j) y).le_opNorm (b i)).trans
        (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hC) (hbi i) (norm_nonneg _) C.2)
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
    intro y hy
    by_contra hn
    exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
  have hintH : ∀ i, Integrable (fun y ↦ inner ℝ (ζ y) (b i) * fderiv ℝ H y (b i)) := by
    intro i
    have h1 : IntegrableOn (fun y ↦ inner ℝ (ζ y) (b i) * fderiv ℝ H y (b i))
        (tsupport (fun y ↦ inner ℝ (ζ y) (b i))) :=
      ((hχi i).continuousOn.mul (((hdHc.mono ((hχis i).trans
        (ball_subset_ball hrR.le)))).clm_apply continuousOn_const)).integrableOn_compact
          (hcχi i).isCompact
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
    intro y hy
    by_contra hn
    exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
  have e : ∀ F : Space m → ℝ,
      (∀ i, Integrable (fun y ↦ inner ℝ (ζ y) (b i) * fderiv ℝ F y (b i))) →
      (∫ y, inner ℝ (ζ y) (gradient F y)) =
        ∑ i, ∫ y, inner ℝ (ζ y) (b i) * fderiv ℝ F y (b i) := by
    intro F hF
    rw [← integral_finsetSum _ fun i _ ↦ hF i]
    exact integral_congr_ae (Eventually.of_forall fun y ↦ hcomp F y)
  rw [e H hintH]
  refine (tendsto_finsetSum _ fun i _ ↦ tendsto_integral_mul_fderiv_of_sq_tendsto hrR hLip hH
    hHL2 hK hlim (hχi i) (hχis i) (b i) (hbi i)).congr fun j ↦ (e (f j) (hintf j)).symm

variable {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **The aligned harmonic layer data from (A), (B), (C)** ((E) is `weakGradientLimit`). -/
theorem RigidityHypotheses.exists_hasAlignedHarmonicLayerData_of_heightInputs
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0} (hρ : 3 / 4 < ρ)
    (hA : HasAlignedHeightCompactness g u ℓ r₀ b ρ τ s₁ s₂ L c K)
    (hB : HasAlignedHeightMoments g u ℓ r₀ b ρ τ s₁ s₂ L c K)
    (hC : HasAlignedFluxIdentification g u (phasePrimitive f 1) ℓ r₀ b ρ τ s₁ s₂ L c K) :
    ∃ M : ℝ, 0 ≤ M ∧ HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M :=
  hr.exists_hasAlignedHarmonicLayerData_of_inputs h hsharp hρ hA hB hC (weakGradientLimit m)

end SerrinEpigraph
