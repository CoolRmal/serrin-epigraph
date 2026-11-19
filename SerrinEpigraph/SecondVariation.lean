module

public import SerrinEpigraph.SmoothBoundaryChart

/-!
# Second variation of perimeter on a smooth chart and the stability inequality (GR1)

Let `E` minimize perimeter in `Ω`, let `(μ, ν)` be a perimeter measure with polar vector on `Ω`
(`IsPerimeterPolarOn`), and let `(E, U, F)` be a smooth boundary chart with `U ⊆ Ω`. We deform `E`
by the normal variation `Φ_t = id + t X`, `X = ζ ν`, and use the BV9 change of variables
`P(Φ_t E, Ω) = ∫ ‖cofactorMap (t DX) ν‖ dμ`, where `cofactorMap T = det (1 + T) ((1 + T)⁻¹)ᵀ`.

## Main results
* `exists_det_one_add_smul_expansion`:
  `det (1 + tA) = 1 + t tr A + t² ((tr A)² - tr A²) / 2 + O(|t|³)` uniformly for `‖A‖ ≤ M`
  (via Jacobi's formula `hasDerivAt_det_one_add_smul_of_norm_lt` and the mean value theorem).
* `exists_norm_sq_cofactorMap_expansion`:
  `‖cofactorMap (tA) v‖² = 1 + 2t β + t² γ + O(|t|³)` uniformly for `‖A‖ ≤ M`, `‖v‖ = 1`,
  with `β = firstVariationCoeff A v = tr A - ⟪A v, v⟫` and `γ = secondVariationCoeff A v`.
* `IsPerimeterPolarOn.exists_integral_norm_le_cofactorMap`: minimality against the deformations.
* `IsSmoothBoundaryChart.firstVariationCoeff_fderiv_smul_chartNormal` (`β = ζ H`) and
  `IsSmoothBoundaryChart.secondVariationCoeff_fderiv_smul_chartNormal`
  (`γ = |δζ|² - ζ² |A|²` where `H = 0`).
* `IsSmoothBoundaryChart.stability_inequality` (GR1.1): `∫_M ζ² |A|² dμ ≤ ∫_M |δζ|² dμ` for every
  `C²` function `ζ` compactly supported in the chart.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff CompactlySupported ENNReal

namespace SerrinEpigraph

/-! ### Elementary estimates -/

section Elementary

variable {d : ℕ}

/-- `|tr T| ≤ d ‖T‖`. -/
theorem abs_trace_clm_le (T : Space d →L[ℝ] Space d) :
    |LinearMap.trace ℝ (Space d) T.toLinearMap| ≤ d * ‖T‖ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc |∑ i, inner ℝ (b i) (T.toLinearMap (b i))|
      ≤ ∑ i, |inner ℝ (b i) (T.toLinearMap (b i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖T‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hb : ‖b i‖ = 1 := b.orthonormal.1 i
        change |inner ℝ (b i) (T (b i))| ≤ ‖T‖
        calc |inner ℝ (b i) (T (b i))| ≤ ‖b i‖ * ‖T (b i)‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖b i‖ * (‖T‖ * ‖b i‖) :=
              mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
          _ = ‖T‖ := by rw [hb]; ring
    _ = d * ‖T‖ := by simp

theorem trace_clm_sub (S T : Space d →L[ℝ] Space d) :
    LinearMap.trace ℝ (Space d) (S - T).toLinearMap =
      LinearMap.trace ℝ (Space d) S.toLinearMap - LinearMap.trace ℝ (Space d) T.toLinearMap := by
  have h1 : (S - T).toLinearMap = S.toLinearMap - T.toLinearMap := rfl
  rw [h1, map_sub]

/-- Mean value estimate: a derivative bounded by `K |s|ⁿ` on `[-|t|, |t|]` gives an
increment bounded by `K |t|ⁿ⁺¹`. -/
theorem abs_sub_le_of_hasDerivAt_le {f f' : ℝ → ℝ} {t K : ℝ} (n : ℕ) (hK : 0 ≤ K)
    (hd : ∀ s, |s| ≤ |t| → HasDerivAt f (f' s) s)
    (hb : ∀ s, |s| ≤ |t| → |f' s| ≤ K * |s| ^ n) :
    |f t - f 0| ≤ K * |t| ^ (n + 1) := by
  have hmem : ∀ s, s ∈ Icc (-|t|) |t| ↔ |s| ≤ |t| := fun s ↦ abs_le.symm
  have h := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f)
    (f' := f') (C := K * |t| ^ n)
    (fun s hs ↦ (hd s ((hmem s).mp hs)).hasDerivWithinAt)
    (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      exact (hb s ((hmem s).mp hs)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg s) ((hmem s).mp hs) n) hK))
    ((hmem 0).mpr (by simp)) ((hmem t).mpr le_rfl)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
  calc |f t - f 0| ≤ K * |t| ^ n * |t| := h
    _ = K * |t| ^ (n + 1) := by ring

theorem isUnit_one_add_of_norm_lt_one {T : Space d →L[ℝ] Space d} (hT : ‖T‖ < 1) :
    IsUnit ((1 : Space d →L[ℝ] Space d) + T) := by
  have h : ‖-T‖ < 1 := by rwa [norm_neg]
  simpa [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one h

theorem inverse_one_add_eq {T : Space d →L[ℝ] Space d} (hT : ‖T‖ < 1) :
    Ring.inverse ((1 : Space d →L[ℝ] Space d) + T) =
      1 - T * Ring.inverse ((1 : Space d →L[ℝ] Space d) + T) := by
  have h := Ring.mul_inverse_cancel _ (isUnit_one_add_of_norm_lt_one hT)
  rw [add_mul, one_mul] at h
  exact eq_sub_of_add_eq h

theorem norm_inverse_one_add_le {T : Space d →L[ℝ] Space d} (hT : ‖T‖ ≤ 1 / 2) :
    ‖Ring.inverse ((1 : Space d →L[ℝ] Space d) + T)‖ ≤ 2 := by
  have hT1 : ‖T‖ < 1 := by linarith
  set R := Ring.inverse ((1 : Space d →L[ℝ] Space d) + T)
  have h := inverse_one_add_eq hT1
  have h1 : ‖(1 : Space d →L[ℝ] Space d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h2 : ‖R‖ ≤ 1 + ‖T‖ * ‖R‖ := by
    calc ‖R‖ = ‖1 - T * R‖ := congrArg norm h
      _ ≤ ‖(1 : Space d →L[ℝ] Space d)‖ + ‖T * R‖ := norm_sub_le _ _
      _ ≤ 1 + ‖T‖ * ‖R‖ := add_le_add h1 (norm_mul_le _ _)
  nlinarith [norm_nonneg R, norm_nonneg T]

theorem clm_mul_smul_eq (A B : Space d →L[ℝ] Space d) (c : ℝ) : A * (c • B) = c • (A * B) := by
  ext1 w
  simp

theorem clm_smul_mul_eq (A B : Space d →L[ℝ] Space d) (c : ℝ) : (c • A) * B = c • (A * B) := by
  ext1 w
  simp

theorem inverse_expand_two {A R : Space d →L[ℝ] Space d} {s : ℝ} (hR : R = 1 - s • (A * R)) :
    R = 1 - s • A + s ^ 2 • (A * A * R) := by
  have h2 : A * R = A - s • (A * A * R) := by
    conv_lhs => rw [hR]
    rw [mul_sub, mul_one, clm_mul_smul_eq, ← mul_assoc]
  calc R = 1 - s • (A * R) := hR
    _ = 1 - s • (A - s • (A * A * R)) := by rw [h2]
    _ = _ := by module

theorem inverse_expand_three {A R : Space d →L[ℝ] Space d} {s : ℝ} (hR : R = 1 - s • (A * R)) :
    R = 1 - s • A + s ^ 2 • (A * A) - s ^ 3 • (A * A * A * R) := by
  have h3 : A * A * R = A * A - s • (A * A * A * R) := by
    conv_lhs => rw [hR]
    rw [mul_sub, mul_one, clm_mul_smul_eq, ← mul_assoc]
  calc R = 1 - s • A + s ^ 2 • (A * A * R) := inverse_expand_two hR
    _ = 1 - s • A + s ^ 2 • (A * A - s • (A * A * A * R)) := by rw [h3]
    _ = _ := by module

/-- Jacobi's formula along a line, away from the origin:
`d/dt det (1 + t A) = det (1 + s A) tr ((1 + s A)⁻¹ A)` at `t = s`. -/
theorem hasDerivAt_det_one_add_smul_of_norm_lt (A : Space d →L[ℝ] Space d) {s : ℝ}
    (hs : ‖s • A‖ < 1) :
    HasDerivAt (fun t : ℝ ↦ LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap)
      (LinearMap.det ((1 : Space d →L[ℝ] Space d) + s • A).toLinearMap *
        LinearMap.trace ℝ (Space d)
          (Ring.inverse ((1 : Space d →L[ℝ] Space d) + s • A) * A).toLinearMap) s := by
  set R := Ring.inverse ((1 : Space d →L[ℝ] Space d) + s • A)
  have hmul : ((1 : Space d →L[ℝ] Space d) + s • A) * R = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_add_of_norm_lt_one hs)
  have hfac (h : ℝ) : (1 : Space d →L[ℝ] Space d) + (s + h) • A =
      ((1 : Space d →L[ℝ] Space d) + s • A) * (1 + h • (R * A)) := by
    rw [mul_add, mul_one, clm_mul_smul_eq, ← mul_assoc, hmul, one_mul]
    module
  have hdet (h : ℝ) :
      LinearMap.det ((1 : Space d →L[ℝ] Space d) + (s + h) • A).toLinearMap =
        LinearMap.det ((1 : Space d →L[ℝ] Space d) + s • A).toLinearMap *
          LinearMap.det ((1 : Space d →L[ℝ] Space d) + h • (R * A)).toLinearMap := by
    rw [hfac h]
    exact map_mul LinearMap.det _ _
  have hd0 := (hasDerivAt_det_one_add_smul (R * A)).const_mul
    (LinearMap.det ((1 : Space d →L[ℝ] Space d) + s • A).toLinearMap)
  have hd1 : HasDerivAt
      (fun h : ℝ ↦ LinearMap.det ((1 : Space d →L[ℝ] Space d) + (s + h) • A).toLinearMap)
      (LinearMap.det ((1 : Space d →L[ℝ] Space d) + s • A).toLinearMap *
        LinearMap.trace ℝ (Space d) (R * A).toLinearMap) 0 := by
    rw [funext hdet]
    exact hd0
  have hd2 := HasDerivAt.comp_const_add (-s) s (by rw [neg_add_cancel]; exact hd1)
  simp only [add_neg_cancel_left] at hd2
  exact hd2

/-- Second-order expansion of `det (1 + t A)` with a cubic remainder, uniformly for `‖A‖ ≤ M`. -/
theorem exists_det_one_add_smul_expansion (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Space d →L[ℝ] Space d, ‖A‖ ≤ M → ∀ t : ℝ, |t| ≤ 1 / (2 * (M + 1)) →
      |LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap -
        (1 + t * LinearMap.trace ℝ (Space d) A.toLinearMap +
          t ^ 2 * ((LinearMap.trace ℝ (Space d) A.toLinearMap) ^ 2 -
            LinearMap.trace ℝ (Space d) (A * A).toLinearMap) / 2)| ≤ C * |t| ^ 3 := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (1 : Space d →L[ℝ] Space d) (1 / 2)).exists_bound_of_continuousOn
    ((contDiff_clm_det (d := d) (n := 0)).continuous.continuousOn)
  set K := max K₀ 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  set D : ℝ := (d : ℝ) with hDdef
  have hD : 0 ≤ D := Nat.cast_nonneg d
  set C₀ : ℝ := K * (D * (2 * M)) with hC₀def
  set C₁ : ℝ := C₀ * (D * (2 * M)) + D * (2 * M ^ 2) with hC₁def
  set C₂ : ℝ := C₁ * (D * (2 * M)) + D * (2 * M ^ 3) + D * M * (D * M ^ 2) +
    D * M * (D * (2 * M ^ 3)) with hC₂def
  have hC₀ : 0 ≤ C₀ := by positivity
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨C₂, hC₂, fun A hA t ht ↦ ?_⟩
  set t₀ : ℝ := 1 / (2 * (M + 1)) with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  have ht₀1 : t₀ ≤ 1 := by
    rw [ht₀def, div_le_one (by positivity)]
    linarith
  set a := LinearMap.trace ℝ (Space d) A.toLinearMap with hadef
  set c := LinearMap.trace ℝ (Space d) (A * A).toLinearMap with hcdef
  have hAA : ‖A * A‖ ≤ M ^ 2 := (norm_mul_le A A).trans (by nlinarith [norm_nonneg A])
  have ha : |a| ≤ D * M := (abs_trace_clm_le A).trans (mul_le_mul_of_nonneg_left hA hD)
  have hc : |c| ≤ D * M ^ 2 := (abs_trace_clm_le _).trans (mul_le_mul_of_nonneg_left hAA hD)
  let φ : ℝ → ℝ := fun s ↦ LinearMap.det ((1 : Space d →L[ℝ] Space d) + s • A).toLinearMap
  let R : ℝ → Space d →L[ℝ] Space d := fun s ↦ Ring.inverse ((1 : Space d →L[ℝ] Space d) + s • A)
  let τ : ℝ → ℝ := fun s ↦ LinearMap.trace ℝ (Space d) (R s * A).toLinearMap
  have hsA (s : ℝ) (hs : |s| ≤ t₀) : ‖s • A‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |s| * ‖A‖ ≤ t₀ * M := mul_le_mul hs hA (norm_nonneg _) ht₀.le
      _ ≤ 1 / 2 := by
        rw [ht₀def, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hderiv (s : ℝ) (hs : |s| ≤ t₀) : HasDerivAt φ (φ s * τ s) s :=
    hasDerivAt_det_one_add_smul_of_norm_lt A ((hsA s hs).trans_lt (by norm_num))
  have hφb (s : ℝ) (hs : |s| ≤ t₀) : |φ s| ≤ K := by
    have hmem : (1 : Space d →L[ℝ] Space d) + s • A ∈
        closedBall (1 : Space d →L[ℝ] Space d) (1 / 2) := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hsA s hs
    have h1 := hK₀ _ hmem
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  have hRb (s : ℝ) (hs : |s| ≤ t₀) : ‖R s‖ ≤ 2 := norm_inverse_one_add_le (hsA s hs)
  have hReq (s : ℝ) (hs : |s| ≤ t₀) : R s = 1 - s • (A * R s) := by
    have h1 := inverse_one_add_eq ((hsA s hs).trans_lt (by norm_num))
    rw [clm_smul_mul_eq] at h1
    exact h1
  have hτb (s : ℝ) (hs : |s| ≤ t₀) : |τ s| ≤ D * (2 * M) := by
    refine (abs_trace_clm_le _).trans (mul_le_mul_of_nonneg_left ?_ hD)
    calc ‖R s * A‖ ≤ ‖R s‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ 2 * M := mul_le_mul (hRb s hs) hA (norm_nonneg _) (by norm_num)
  have hτa (s : ℝ) (hs : |s| ≤ t₀) : |τ s - a| ≤ D * (2 * M ^ 2) * |s| := by
    have heq : R s * A - A = -(s • (A * R s * A)) := by
      conv_lhs => rw [hReq s hs]
      rw [sub_mul, one_mul, clm_smul_mul_eq]
      abel
    have htr : τ s - a = LinearMap.trace ℝ (Space d) (R s * A - A).toLinearMap :=
      (trace_clm_sub _ _).symm
    rw [htr, heq]
    refine (abs_trace_clm_le _).trans ?_
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    have h1 : ‖A * R s * A‖ ≤ 2 * M ^ 2 := by
      calc ‖A * R s * A‖ ≤ ‖A * R s‖ * ‖A‖ := norm_mul_le _ _
        _ ≤ ‖A‖ * ‖R s‖ * ‖A‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ M * 2 * M := by
          have hR' := hRb s hs
          gcongr
        _ = 2 * M ^ 2 := by ring
    have h2 : |s| * ‖A * R s * A‖ ≤ |s| * (2 * M ^ 2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg s)
    nlinarith [abs_nonneg s]
  have hτexp (s : ℝ) (hs : |s| ≤ t₀) : τ s = a - s * c +
      s ^ 2 * LinearMap.trace ℝ (Space d) (A * A * R s * A).toLinearMap := by
    have h2 := inverse_expand_two (hReq s hs)
    have heq : R s * A = A - s • (A * A) + s ^ 2 • (A * A * R s * A) := by
      conv_lhs => rw [h2]
      rw [add_mul, sub_mul, one_mul, clm_smul_mul_eq, clm_smul_mul_eq]
    show LinearMap.trace ℝ (Space d) (R s * A).toLinearMap = _
    rw [heq, trace_clm_add, trace_clm_sub, trace_clm_smul, trace_clm_smul]
  have hρ (s : ℝ) (hs : |s| ≤ t₀) :
      |LinearMap.trace ℝ (Space d) (A * A * R s * A).toLinearMap| ≤ D * (2 * M ^ 3) := by
    refine (abs_trace_clm_le _).trans (mul_le_mul_of_nonneg_left ?_ hD)
    calc ‖A * A * R s * A‖ ≤ ‖A * A * R s‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ ‖A * A‖ * ‖R s‖ * ‖A‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ M ^ 2 * 2 * M := by
        have hR' := hRb s hs
        gcongr
      _ = 2 * M ^ 3 := by ring
  have hφ0 : φ 0 = 1 := by simp [φ]
  -- step 1: `|φ t - 1| ≤ C₀ |t|`
  have hstep1 (t' : ℝ) (ht' : |t'| ≤ t₀) : |φ t' - 1| ≤ C₀ * |t'| := by
    have h := abs_sub_le_of_hasDerivAt_le (f := φ) (f' := fun s ↦ φ s * τ s) (t := t') 0 hC₀
      (fun s hs ↦ hderiv s (hs.trans ht'))
      (fun s hs ↦ by
        rw [pow_zero, mul_one, abs_mul, hC₀def]
        exact mul_le_mul (hφb s (hs.trans ht')) (hτb s (hs.trans ht')) (abs_nonneg _) hK)
    rwa [hφ0, zero_add, pow_one] at h
  -- step 2: `|φ t - 1 - t a| ≤ C₁ |t|²`
  have hstep2 (t' : ℝ) (ht' : |t'| ≤ t₀) : |φ t' - 1 - t' * a| ≤ C₁ * |t'| ^ 2 := by
    have h := abs_sub_le_of_hasDerivAt_le (f := fun s ↦ φ s - 1 - s * a)
      (f' := fun s ↦ φ s * τ s - a) (t := t') 1 hC₁
      (fun s hs ↦ ((hderiv s (hs.trans ht')).sub_const 1).sub (hasDerivAt_mul_const a))
      (fun s hs ↦ by
        have hs' := hs.trans ht'
        have h1 := hstep1 s hs'
        have h2 := hτb s hs'
        have h3 := hτa s hs'
        have heq : φ s * τ s - a = (φ s - 1) * τ s + (τ s - a) := by ring
        rw [heq, pow_one]
        calc |(φ s - 1) * τ s + (τ s - a)| ≤ |φ s - 1| * |τ s| + |τ s - a| := by
              rw [← abs_mul]
              exact abs_add_le _ _
          _ ≤ C₀ * |s| * (D * (2 * M)) + D * (2 * M ^ 2) * |s| := by
              gcongr
          _ = C₁ * |s| := by rw [hC₁def]; ring)
    simp only [hφ0, zero_mul, sub_zero, sub_self] at h
    simpa using h
  -- step 3: the cubic remainder
  have h := abs_sub_le_of_hasDerivAt_le (f := fun s ↦ φ s - 1 - s * a - s ^ 2 * (a ^ 2 - c) / 2)
    (f' := fun s ↦ φ s * τ s - a - s * (a ^ 2 - c)) (t := t) 2 hC₂
    (fun s hs ↦ by
      have h1 := ((hderiv s (hs.trans ht)).sub_const 1).sub (hasDerivAt_mul_const a)
      have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 * (a ^ 2 - c) / 2) (s * (a ^ 2 - c)) s := by
        have := ((hasDerivAt_pow 2 s).mul_const (a ^ 2 - c)).div_const 2
        convert this using 1
        push_cast
        ring
      exact h1.sub h2)
    (fun s hs ↦ by
      have hs' := hs.trans ht
      have hs1 : |s| ≤ 1 := hs'.trans ht₀1
      set ρ := LinearMap.trace ℝ (Space d) (A * A * R s * A).toLinearMap with hρdef
      have heq : φ s * τ s - a - s * (a ^ 2 - c) =
          (φ s - 1 - s * a) * τ s + s ^ 2 * (ρ - a * c) + s ^ 3 * (a * ρ) := by
        rw [hτexp s hs']
        ring
      rw [heq]
      have h1 := hstep2 s hs'
      have h2 := hτb s hs'
      have h3 := hρ s hs'
      have hs3 : |s| ^ 3 ≤ |s| ^ 2 := by
        have : |s| ^ 3 = |s| ^ 2 * |s| := by ring
        rw [this]
        exact mul_le_of_le_one_right (by positivity) hs1
      have hac : |a * c| ≤ D * M * (D * M ^ 2) := by
        rw [abs_mul]
        exact mul_le_mul ha hc (abs_nonneg _) (by positivity)
      have haρ : |a * ρ| ≤ D * M * (D * (2 * M ^ 3)) := by
        rw [abs_mul]
        exact mul_le_mul ha h3 (abs_nonneg _) (by positivity)
      have hsub : |ρ - a * c| ≤ D * (2 * M ^ 3) + D * M * (D * M ^ 2) :=
        (abs_sub _ _).trans (add_le_add h3 hac)
      calc |(φ s - 1 - s * a) * τ s + s ^ 2 * (ρ - a * c) + s ^ 3 * (a * ρ)|
          ≤ |(φ s - 1 - s * a) * τ s| + |s ^ 2 * (ρ - a * c)| + |s ^ 3 * (a * ρ)| :=
            abs_add_three _ _ _
        _ = |φ s - 1 - s * a| * |τ s| + |s| ^ 2 * |ρ - a * c| + |s| ^ 3 * |a * ρ| := by
            rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
        _ ≤ C₁ * |s| ^ 2 * (D * (2 * M)) + |s| ^ 2 * (D * (2 * M ^ 3) + D * M * (D * M ^ 2)) +
              |s| ^ 2 * (D * M * (D * (2 * M ^ 3))) := by
            gcongr
        _ = C₂ * |s| ^ 2 := by rw [hC₂def]; ring)
  simp only [hφ0, zero_mul, sub_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at h
  have hgoal : LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap -
      (1 + t * a + t ^ 2 * (a ^ 2 - c) / 2) = φ t - 1 - t * a - t ^ 2 * (a ^ 2 - c) / 2 := by
    simp only [φ]
    ring
  rw [hgoal]
  simpa using h

theorem norm_sq_add_two_eq (v a₁ a₂ : Space d) (t : ℝ) :
    ‖v + t • a₁ + t ^ 2 • a₂‖ ^ 2 =
      ‖v‖ ^ 2 + 2 * t * inner ℝ v a₁ + t ^ 2 * (‖a₁‖ ^ 2 + 2 * inner ℝ v a₂) +
        (2 * t ^ 3 * inner ℝ a₁ a₂ + t ^ 4 * ‖a₂‖ ^ 2) := by
  have h1 : ‖t • a₁‖ ^ 2 = t ^ 2 * ‖a₁‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h2 : ‖t ^ 2 • a₂‖ ^ 2 = t ^ 4 * ‖a₂‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (sq_nonneg t)]
    ring
  rw [norm_add_sq_real, norm_add_sq_real, h1, h2]
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Uniform cubic control of `‖v + t a₁ + t² a₂ + e‖²` around its second-order Taylor
polynomial, for a unit vector `v`. -/
theorem abs_norm_sq_expansion_le {v a₁ a₂ e : Space d} {t B K : ℝ} (hv : ‖v‖ = 1)
    (ht : |t| ≤ 1) (hB : 0 ≤ B) (ha₁ : ‖a₁‖ ≤ B) (ha₂ : ‖a₂‖ ≤ B)
    (he : ‖e‖ ≤ K * |t| ^ 3) :
    |‖v + t • a₁ + t ^ 2 • a₂ + e‖ ^ 2 -
        (1 + 2 * t * inner ℝ v a₁ + t ^ 2 * (‖a₁‖ ^ 2 + 2 * inner ℝ v a₂))| ≤
      (3 * B ^ 2 + 2 * (1 + 2 * B) * K + K ^ 2) * |t| ^ 3 := by
  set p := v + t • a₁ + t ^ 2 • a₂ with hp
  have hexp : ‖p + e‖ ^ 2 - (1 + 2 * t * inner ℝ v a₁ + t ^ 2 * (‖a₁‖ ^ 2 + 2 * inner ℝ v a₂)) =
      2 * t ^ 3 * inner ℝ a₁ a₂ + t ^ 4 * ‖a₂‖ ^ 2 + 2 * inner ℝ p e + ‖e‖ ^ 2 := by
    rw [norm_add_sq_real, hp, norm_sq_add_two_eq, hv]
    ring
  rw [hexp]
  have hta : 0 ≤ |t| := abs_nonneg t
  have ht4 : |t| ^ 4 ≤ |t| ^ 3 := by
    have : |t| ^ 4 = |t| ^ 3 * |t| := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ht
  have ht6 : |t| ^ 6 ≤ |t| ^ 3 := by
    have : |t| ^ 6 = |t| ^ 3 * |t| ^ 3 := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hta ht)
  have hp_le : ‖p‖ ≤ 1 + 2 * B := by
    calc ‖p‖ ≤ ‖v + t • a₁‖ + ‖t ^ 2 • a₂‖ := norm_add_le _ _
      _ ≤ ‖v‖ + ‖t • a₁‖ + ‖t ^ 2 • a₂‖ := by gcongr; exact norm_add_le _ _
      _ = 1 + |t| * ‖a₁‖ + |t| ^ 2 * ‖a₂‖ := by
          rw [hv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
      _ ≤ 1 + 1 * B + 1 * B := by
          gcongr
          exact pow_le_one₀ hta ht
      _ = 1 + 2 * B := by ring
  have h1 : |2 * t ^ 3 * inner ℝ a₁ a₂| ≤ 2 * B ^ 2 * |t| ^ 3 := by
    rw [abs_mul, abs_mul, abs_pow, abs_two]
    have := abs_real_inner_le_norm a₁ a₂
    have h' : ‖a₁‖ * ‖a₂‖ ≤ B * B := mul_le_mul ha₁ ha₂ (norm_nonneg _) hB
    nlinarith [pow_nonneg hta 3]
  have h2 : |t ^ 4 * ‖a₂‖ ^ 2| ≤ B ^ 2 * |t| ^ 3 := by
    rw [abs_mul, abs_pow, abs_pow, abs_norm]
    have h' : ‖a₂‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha₂ 2
    nlinarith [pow_nonneg hta 3, pow_nonneg hta 4, sq_nonneg ‖a₂‖]
  have h3 : |2 * inner ℝ p e| ≤ 2 * (1 + 2 * B) * K * |t| ^ 3 := by
    rw [abs_mul, abs_two]
    have := abs_real_inner_le_norm p e
    have h' : ‖p‖ * ‖e‖ ≤ (1 + 2 * B) * (K * |t| ^ 3) :=
      mul_le_mul hp_le he (norm_nonneg _) (by positivity)
    nlinarith
  have h4 : |‖e‖ ^ 2| ≤ K ^ 2 * |t| ^ 3 := by
    rw [abs_pow, abs_norm]
    have h' : ‖e‖ ^ 2 ≤ (K * |t| ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    have h'' : (K * |t| ^ 3) ^ 2 = K ^ 2 * |t| ^ 6 := by ring
    nlinarith [sq_nonneg K]
  calc |2 * t ^ 3 * inner ℝ a₁ a₂ + t ^ 4 * ‖a₂‖ ^ 2 + 2 * inner ℝ p e + ‖e‖ ^ 2|
      ≤ |2 * t ^ 3 * inner ℝ a₁ a₂ + t ^ 4 * ‖a₂‖ ^ 2 + 2 * inner ℝ p e| + |‖e‖ ^ 2| :=
        abs_add_le _ _
    _ ≤ |2 * t ^ 3 * inner ℝ a₁ a₂| + |t ^ 4 * ‖a₂‖ ^ 2| + |2 * inner ℝ p e| + |‖e‖ ^ 2| := by
        gcongr
        exact abs_add_three _ _ _
    _ ≤ 2 * B ^ 2 * |t| ^ 3 + B ^ 2 * |t| ^ 3 + 2 * (1 + 2 * B) * K * |t| ^ 3 +
          K ^ 2 * |t| ^ 3 := by gcongr
    _ = (3 * B ^ 2 + 2 * (1 + 2 * B) * K + K ^ 2) * |t| ^ 3 := by ring

end Elementary

/-! ### The cofactor field and its second-order expansion -/

section Cofactor

variable {d : ℕ}

/-- The cofactor field `det (1 + T) • ((1 + T)⁻¹)ᵀ`; for `T = t DX` it transforms the perimeter
integrand under the deformation `x ↦ x + t X x`. -/
def cofactorMap (T : Space d →L[ℝ] Space d) : Space d →L[ℝ] Space d :=
  LinearMap.det ((1 : Space d →L[ℝ] Space d) + T).toLinearMap •
    (Ring.inverse ((1 : Space d →L[ℝ] Space d) + T)).adjoint

/-- First-order coefficient `tr A - ⟪A v, v⟫` of `t ↦ ‖cofactorMap (t A) v‖`. -/
def firstVariationCoeff (A : Space d →L[ℝ] Space d) (v : Space d) : ℝ :=
  LinearMap.trace ℝ (Space d) A.toLinearMap - inner ℝ (A v) v

/-- Second-order coefficient of `t ↦ ‖cofactorMap (t A) v‖²`:
`2 (tr A)² - tr (A²) + ‖Aᵀ v‖² + 2 ⟪A² v, v⟫ - 4 tr A ⟪A v, v⟫`. -/
def secondVariationCoeff (A : Space d →L[ℝ] Space d) (v : Space d) : ℝ :=
  2 * LinearMap.trace ℝ (Space d) A.toLinearMap ^ 2 -
    LinearMap.trace ℝ (Space d) (A * A).toLinearMap + ‖A.adjoint v‖ ^ 2 +
      2 * inner ℝ (A (A v)) v - 4 * LinearMap.trace ℝ (Space d) A.toLinearMap * inner ℝ (A v) v

theorem cofactorMap_zero : cofactorMap (0 : Space d →L[ℝ] Space d) = 1 := by
  have h1 : (1 : Space d →L[ℝ] Space d).adjoint = 1 :=
    ((ContinuousLinearMap.eq_adjoint_iff 1 1).mpr fun _ _ ↦ rfl).symm
  simp [cofactorMap, h1]

theorem cofactorMap_apply (T : Space d →L[ℝ] Space d) (v : Space d) :
    cofactorMap T v = LinearMap.det ((1 : Space d →L[ℝ] Space d) + T).toLinearMap •
      (Ring.inverse ((1 : Space d →L[ℝ] Space d) + T)).adjoint v := rfl

/-- **Second-order expansion of the area density.** Uniformly for `‖A‖ ≤ M`, unit `v`, and small
`|t|`, `‖cofactor(1 + tA) v‖² = 1 + 2 t β + t² γ + O(|t|³)` with `β = firstVariationCoeff A v`
and `γ = secondVariationCoeff A v`. -/
theorem exists_norm_sq_cofactorMap_expansion (M : ℝ) (hM : 0 ≤ M) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Space d →L[ℝ] Space d, ‖A‖ ≤ M →
      ∀ v : Space d, ‖v‖ = 1 → ∀ t : ℝ, |t| ≤ t₁ →
        |‖cofactorMap (t • A) v‖ ^ 2 -
          (1 + 2 * t * firstVariationCoeff A v + t ^ 2 * secondVariationCoeff A v)| ≤
            C * |t| ^ 3 := by
  obtain ⟨Cd, hCd, hdet⟩ := exists_det_one_add_smul_expansion (d := d) M hM
  set D : ℝ := (d : ℝ) with hDdef
  have hD : 0 ≤ D := Nat.cast_nonneg d
  set S : ℝ := (D ^ 2 * M ^ 2 + D * M ^ 2) / 2 with hSdef
  have hS : 0 ≤ S := by positivity
  set B : ℝ := D * M + M + (S + D * M * M + M ^ 2) with hBdef
  have hB : 0 ≤ B := by positivity
  set KE : ℝ := D * M * M ^ 2 + S * M + S * M ^ 2 + (1 + D * M + S) * (2 * M ^ 3) + Cd * 2
    with hKEdef
  have hKE : 0 ≤ KE := by positivity
  set t₀ : ℝ := 1 / (2 * (M + 1)) with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  have ht₀1 : t₀ ≤ 1 := by
    rw [ht₀def, div_le_one (by positivity)]
    linarith
  refine ⟨t₀, ht₀, 3 * B ^ 2 + 2 * (1 + 2 * B) * KE + KE ^ 2, by positivity,
    fun A hA v hv t ht ↦ ?_⟩
  have ht1 : |t| ≤ 1 := ht.trans ht₀1
  have hta : 0 ≤ |t| := abs_nonneg t
  have htA : ‖t • A‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖A‖ ≤ t₀ * M := mul_le_mul ht hA (norm_nonneg _) ht₀.le
      _ ≤ 1 / 2 := by
        rw [ht₀def, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  set a := LinearMap.trace ℝ (Space d) A.toLinearMap with hadef
  set c := LinearMap.trace ℝ (Space d) (A * A).toLinearMap with hcdef
  have hAA : ‖A * A‖ ≤ M ^ 2 := (norm_mul_le A A).trans (by nlinarith [norm_nonneg A])
  have ha : |a| ≤ D * M := (abs_trace_clm_le A).trans (mul_le_mul_of_nonneg_left hA hD)
  have hc : |c| ≤ D * M ^ 2 := (abs_trace_clm_le _).trans (mul_le_mul_of_nonneg_left hAA hD)
  set σ : ℝ := (a ^ 2 - c) / 2 with hσdef
  have hσ : |σ| ≤ S := by
    rw [hσdef, hSdef, abs_div, abs_two]
    have h1 : |a ^ 2 - c| ≤ a ^ 2 + |c| := by
      calc |a ^ 2 - c| ≤ |a ^ 2| + |c| := abs_sub _ _
        _ = a ^ 2 + |c| := by rw [abs_pow, sq_abs]
    have h2 : a ^ 2 ≤ (D * M) ^ 2 := by
      rw [← sq_abs a]
      exact pow_le_pow_left₀ (abs_nonneg a) ha 2
    have h3 : |a ^ 2 - c| ≤ D ^ 2 * M ^ 2 + D * M ^ 2 := by nlinarith
    linarith
  set R := Ring.inverse ((1 : Space d →L[ℝ] Space d) + t • A) with hRdef
  have hRb : ‖R‖ ≤ 2 := norm_inverse_one_add_le htA
  have hReq : R = 1 - t • (A * R) := by
    have h1 := inverse_one_add_eq (htA.trans_lt (by norm_num))
    rw [clm_smul_mul_eq] at h1
    exact h1
  have hexp3 := inverse_expand_three hReq
  have hadj_norm (T : Space d →L[ℝ] Space d) : ‖T.adjoint v‖ ≤ ‖T‖ := by
    calc ‖T.adjoint v‖ ≤ ‖T.adjoint‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖T‖ := by rw [hv, mul_one, LinearIsometryEquiv.norm_map]
  set x₁ := A.adjoint v with hx₁def
  set x₂ := (A * A).adjoint v with hx₂def
  set e := (A * A * A * R).adjoint v with hedef
  set u := R.adjoint v with hudef
  have hx₁ : ‖x₁‖ ≤ M := (hadj_norm A).trans hA
  have hx₂ : ‖x₂‖ ≤ M ^ 2 := (hadj_norm _).trans hAA
  have he : ‖e‖ ≤ 2 * M ^ 3 := by
    refine (hadj_norm _).trans ?_
    calc ‖A * A * A * R‖ ≤ ‖A * A * A‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ ‖A * A‖ * ‖A‖ * ‖R‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ M ^ 2 * M * 2 := by gcongr
      _ = 2 * M ^ 3 := by ring
  have hu : ‖u‖ ≤ 2 := (hadj_norm R).trans hRb
  have hu_eq : u = v - t • x₁ + t ^ 2 • x₂ - t ^ 3 • e := by
    apply ext_inner_left ℝ
    intro w
    rw [hudef, ContinuousLinearMap.adjoint_inner_right]
    simp only [hx₁def, hx₂def, hedef, inner_sub_right, inner_add_right, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
    conv_lhs => rw [hexp3]
    simp only [FunLike.coe_sub, FunLike.coe_add, FunLike.coe_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, inner_sub_left, inner_add_left, real_inner_smul_left]
    rfl
  set φ := LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap with hφdef
  set h₂ := φ - (1 + t * a + t ^ 2 * σ) with hh₂def
  have hh₂ : |h₂| ≤ Cd * |t| ^ 3 := by
    have h1 := hdet A hA t ht
    have h2 : t ^ 2 * (a ^ 2 - c) / 2 = t ^ 2 * σ := by rw [hσdef]; ring
    rw [h2] at h1
    exact h1
  have hw : cofactorMap (t • A) v = φ • u := rfl
  have hwE : φ • u = v + t • (a • v - x₁) + t ^ 2 • (σ • v - a • x₁ + x₂) +
      (t ^ 3 • (a • x₂ - σ • x₁) + t ^ 4 • (σ • x₂) -
        t ^ 3 • ((1 + t * a + t ^ 2 * σ) • e) + h₂ • u) := by
    rw [hh₂def, hu_eq]
    module
  have hP₁ : |1 + t * a + t ^ 2 * σ| ≤ 1 + D * M + S := by
    calc |1 + t * a + t ^ 2 * σ| ≤ |1 + t * a| + |t ^ 2 * σ| := abs_add_le _ _
      _ ≤ |(1 : ℝ)| + |t * a| + |t ^ 2 * σ| := by gcongr; exact abs_add_le _ _
      _ = 1 + |t| * |a| + |t| ^ 2 * |σ| := by rw [abs_one, abs_mul, abs_mul, abs_pow]
      _ ≤ 1 + 1 * (D * M) + 1 * S := by
          gcongr
          exact pow_le_one₀ hta ht1
      _ = 1 + D * M + S := by ring
  have ht4 : |t| ^ 4 ≤ |t| ^ 3 := by
    have : |t| ^ 4 = |t| ^ 3 * |t| := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ht1
  have hE : ‖t ^ 3 • (a • x₂ - σ • x₁) + t ^ 4 • (σ • x₂) -
      t ^ 3 • ((1 + t * a + t ^ 2 * σ) • e) + h₂ • u‖ ≤ KE * |t| ^ 3 := by
    have e1 : ‖t ^ 3 • (a • x₂ - σ • x₁)‖ ≤ |t| ^ 3 * (D * M * M ^ 2 + S * M) := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      gcongr
      calc ‖a • x₂ - σ • x₁‖ ≤ ‖a • x₂‖ + ‖σ • x₁‖ := norm_sub_le _ _
        _ = |a| * ‖x₂‖ + |σ| * ‖x₁‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
            Real.norm_eq_abs]
        _ ≤ D * M * M ^ 2 + S * M := by gcongr
    have e2 : ‖t ^ 4 • (σ • x₂)‖ ≤ |t| ^ 3 * (S * M ^ 2) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
      have h1 : |σ| * ‖x₂‖ ≤ S * M ^ 2 := by gcongr
      exact mul_le_mul ht4 h1 (by positivity) (by positivity)
    have e3 : ‖t ^ 3 • ((1 + t * a + t ^ 2 * σ) • e)‖ ≤
        |t| ^ 3 * ((1 + D * M + S) * (2 * M ^ 3)) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
      gcongr
    have e4 : ‖h₂ • u‖ ≤ |t| ^ 3 * (Cd * 2) := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |h₂| * ‖u‖ ≤ Cd * |t| ^ 3 * 2 := by gcongr
        _ = |t| ^ 3 * (Cd * 2) := by ring
    calc ‖t ^ 3 • (a • x₂ - σ • x₁) + t ^ 4 • (σ • x₂) -
          t ^ 3 • ((1 + t * a + t ^ 2 * σ) • e) + h₂ • u‖
        ≤ ‖t ^ 3 • (a • x₂ - σ • x₁) + t ^ 4 • (σ • x₂) -
            t ^ 3 • ((1 + t * a + t ^ 2 * σ) • e)‖ + ‖h₂ • u‖ := norm_add_le _ _
      _ ≤ ‖t ^ 3 • (a • x₂ - σ • x₁)‖ + ‖t ^ 4 • (σ • x₂)‖ +
            ‖t ^ 3 • ((1 + t * a + t ^ 2 * σ) • e)‖ + ‖h₂ • u‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ |t| ^ 3 * (D * M * M ^ 2 + S * M) + |t| ^ 3 * (S * M ^ 2) +
            |t| ^ 3 * ((1 + D * M + S) * (2 * M ^ 3)) + |t| ^ 3 * (Cd * 2) := by gcongr
      _ = KE * |t| ^ 3 := by rw [hKEdef]; ring
  have ha₁ : ‖a • v - x₁‖ ≤ B := by
    calc ‖a • v - x₁‖ ≤ ‖a • v‖ + ‖x₁‖ := norm_sub_le _ _
      _ = |a| + ‖x₁‖ := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
      _ ≤ D * M + M := by gcongr
      _ ≤ B := by
        rw [hBdef]
        exact le_add_of_nonneg_right (by positivity)
  have ha₂ : ‖σ • v - a • x₁ + x₂‖ ≤ B := by
    calc ‖σ • v - a • x₁ + x₂‖ ≤ ‖σ • v - a • x₁‖ + ‖x₂‖ := norm_add_le _ _
      _ ≤ ‖σ • v‖ + ‖a • x₁‖ + ‖x₂‖ := by gcongr; exact norm_sub_le _ _
      _ = |σ| + |a| * ‖x₁‖ + ‖x₂‖ := by
          rw [norm_smul, norm_smul, hv, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ S + D * M * M + M ^ 2 := by gcongr
      _ ≤ B := by
        rw [hBdef]
        exact le_add_of_nonneg_left (by positivity)
  have key := abs_norm_sq_expansion_le hv ht1 hB ha₁ ha₂ hE
  have hβ : inner ℝ v (a • v - x₁) = firstVariationCoeff A v := by
    rw [firstVariationCoeff, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv,
      hx₁def, ContinuousLinearMap.adjoint_inner_right]
    ring
  have hγ : ‖a • v - x₁‖ ^ 2 + 2 * inner ℝ v (σ • v - a • x₁ + x₂) =
      secondVariationCoeff A v := by
    have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
    have hvx₁ : inner ℝ v x₁ = inner ℝ (A v) v := by
      rw [hx₁def, ContinuousLinearMap.adjoint_inner_right]
    have hvx₂ : inner ℝ v x₂ = inner ℝ (A (A v)) v := by
      rw [hx₂def, ContinuousLinearMap.adjoint_inner_right]
      rfl
    rw [secondVariationCoeff, norm_sub_sq_real, norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs,
      real_inner_smul_left, inner_add_right, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right, hvv, hvx₁, hvx₂, ← hx₁def, ← hadef, ← hcdef]
    rw [hσdef]
    ring
  rw [hw, hwE, ← hβ, ← hγ]
  exact key

end Cofactor

/-! ### Perimeter of the deformed sets -/

/-- **Second-variation competitors.** If `E` minimizes perimeter in `Ω` and `X` is a compactly
supported `C²` field in `Ω`, then for all small `|t|` the deformed set `(id + t X)(E)` has
perimeter `∫ ‖cofactorMap (t DX) ν‖ dμ`, which by minimality is at least `∫ ‖ν‖ dμ = P(E, Ω)`. -/
theorem IsPerimeterPolarOn.exists_integral_norm_le_cofactorMap {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (hp : IsPerimeterPolarOn b E Ω μ ν) (hE : MeasurableSet E)
    (hmin : IsPerimeterMinimizingIn b E Ω) {X : Space d → Space d} (hX : ContDiff ℝ 2 X)
    (hXc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∫ x, ‖ν x‖ ∂μ.restrict Ω ≤ ∫ x, ‖cofactorMap (t • fderiv ℝ X x) (ν x)‖ ∂μ.restrict Ω := by
  obtain ⟨δ, Ψ, hδ_pos, hdiff_family⟩ := exists_perturbation_diffeomorph hX hXc
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  have hΩ := hp.isOpen
  refine ⟨δ, hδ_pos, fun t ht ↦ ?_⟩
  obtain ⟨hΦt, hΨt, hΨΦ, hΦΨ, hΦid, hΨid, hdet_pos⟩ := hdiff_family t ht
  let Φt : Space d → Space d := fun x ↦ x + t • X x
  have hΦ_Ω : Φt '' Ω = Ω := by
    ext y
    constructor
    · rintro ⟨x, hxΩ, rfl⟩
      by_contra hyΩ
      have hyX : Φt x ∉ tsupport X := fun hh ↦ hyΩ (hXΩ hh)
      have hfix := hΨid (Φt x) hyX
      rw [hΨΦ x] at hfix
      exact hyΩ (hfix ▸ hxΩ)
    · intro hyΩ
      refine ⟨Ψ t y, ?_, hΦΨ y⟩
      by_contra hxΩ
      have hxX : Ψ t y ∉ tsupport X := fun hh ↦ hxΩ (hXΩ hh)
      have hfix : Ψ t y + t • X (Ψ t y) = Ψ t y := hΦid (Ψ t y) hxX
      rw [hΦΨ y] at hfix
      exact hxΩ (hfix ▸ hyΩ)
  have hDt_eq : Φt '' E = Ψ t ⁻¹' E := by
    ext y
    simp only [mem_image, mem_preimage]
    exact ⟨fun ⟨x, hxE, hxy⟩ ↦ hxy ▸ (hΨΦ x).symm ▸ hxE,
      fun hyE ↦ ⟨Ψ t y, hyE, hΦΨ y⟩⟩
  have hDt_meas : MeasurableSet (Φt '' E) := by
    rw [hDt_eq]
    exact hE.preimage hΨt.continuous.measurable
  have hcomp_t : variationalPerimeter b E Ω ≤ variationalPerimeter b (Φt '' E) Ω := by
    apply hmin (Φt '' E) hDt_meas
    refine ⟨tsupport X, hXc, hXΩ, Eventually.of_forall fun x hxX ↦ ?_⟩
    rw [hDt_eq, mem_preimage, hΨid x hxX]
  have hPV_t : variationalPerimeter b (Φt '' E) Ω =
      ENNReal.ofReal (∫ x, ‖cofactorMap (t • fderiv ℝ X x) (ν x)‖ ∂(μ.restrict Ω)) := by
    have hΦt' : ContDiff ℝ 2 Φt := hΦt
    conv_lhs => rw [← hΦ_Ω]
    rw [variationalPerimeter_image_diffeomorph_of_eq_id_compl b hΩ Subset.rfl hXc
      hΦt' hΨt hΨΦ hΦΨ hΦid μ hp.integrable hp.norm_eq_one hp.pairing_eq]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    have hdfΦ : fderiv ℝ Φt x = (1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x :=
      ((hasFDerivAt_id x).add
        (((hX1.differentiable one_ne_zero x).hasFDerivAt).const_smul t)).fderiv
    have h1 : (fderiv ℝ (Ψ t) (Φt x)).comp (fderiv ℝ Φt x) = 1 := by
      have hd := ((hΨt.differentiable (by norm_num) (Φt x)).hasFDerivAt.comp x
        (hΦt'.differentiable (by norm_num) x).hasFDerivAt).fderiv
      have hid : fderiv ℝ (Ψ t ∘ Φt) x = 1 := by
        rw [show Ψ t ∘ Φt = id from funext hΨΦ]
        exact (hasFDerivAt_id x).fderiv
      exact hd.symm.trans hid
    have h2 : (fderiv ℝ Φt x).comp (fderiv ℝ (Ψ t) (Φt x)) = 1 := by
      have hd := ((hΦt'.differentiable (by norm_num) (Ψ t (Φt x))).hasFDerivAt.comp (Φt x)
        (hΨt.differentiable (by norm_num) (Φt x)).hasFDerivAt).fderiv
      have hid : fderiv ℝ (Φt ∘ Ψ t) (Φt x) = 1 := by
        rw [show Φt ∘ Ψ t = id from funext hΦΨ]
        exact (hasFDerivAt_id (Φt x)).fderiv
      have hΨΦx : Ψ t (Φt x) = x := hΨΦ x
      rw [hΨΦx] at hd
      exact hd.symm.trans hid
    let u_tx : (Space d →L[ℝ] Space d)ˣ := ⟨fderiv ℝ Φt x, fderiv ℝ (Ψ t) (Φt x), h2, h1⟩
    have hinv_eq : Ring.inverse ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x) =
        fderiv ℝ (Ψ t) (Φt x) := by
      rw [← hdfΦ]
      exact Ring.inverse_unit u_tx
    have hdet_abs : |LinearMap.det (fderiv ℝ Φt x).toLinearMap| =
        LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x).toLinearMap := by
      have hpos : 0 < LinearMap.det (fderiv ℝ Φt x).toLinearMap := hdet_pos x
      rw [abs_of_pos hpos, hdfΦ]
    dsimp only
    rw [hdet_abs, ← hinv_eq, cofactorMap_apply]
  have hPV_0 : variationalPerimeter b E Ω = ENNReal.ofReal (∫ x, ‖ν x‖ ∂(μ.restrict Ω)) := by
    have h0_eq : variationalPerimeter b ((id : Space d → Space d) '' E)
        ((id : Space d → Space d) '' Ω) =
        ENNReal.ofReal (∫ x in Ω, ‖|LinearMap.det (fderiv ℝ id x).toLinearMap| •
          ((fderiv ℝ id (id x)).adjoint (ν x))‖ ∂μ) :=
      variationalPerimeter_image_diffeomorph_of_eq_id_compl b hΩ Subset.rfl isCompact_empty
        contDiff_id contDiff_id (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) μ hp.integrable
        hp.norm_eq_one hp.pairing_eq
    rw [Set.image_id, Set.image_id] at h0_eq
    rw [h0_eq]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    have hid_fderiv : fderiv ℝ (id : Space d → Space d) x =
        ContinuousLinearMap.id ℝ (Space d) := (hasFDerivAt_id x).fderiv
    have hid_fderiv2 : fderiv ℝ (id : Space d → Space d) (id x) =
        ContinuousLinearMap.id ℝ (Space d) := (hasFDerivAt_id (id x)).fderiv
    have hdet1 : LinearMap.det (ContinuousLinearMap.id ℝ (Space d)).toLinearMap = 1 :=
      LinearMap.det_id
    dsimp only
    rw [hid_fderiv, hid_fderiv2, hdet1, abs_one, ContinuousLinearMap.adjoint_id,
      one_smul, ContinuousLinearMap.id_apply]
  rw [hPV_0, hPV_t] at hcomp_t
  exact (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg fun x ↦ norm_nonneg _)).mp hcomp_t

/-! ### Normal variations on a chart -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E U Ω : Set (Space d)}
  {F : Space d → ℝ} {μ : Measure (Space d)} {ν : Space d → Space d} {y : Space d}

/-- For the normal variation `X = ζ ν`, the first-order coefficient is `ζ H`. -/
theorem firstVariationCoeff_fderiv_smul_chartNormal (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) {ζ : Space d → ℝ} (hζ : DifferentiableAt ℝ ζ y) :
    firstVariationCoeff (fderiv ℝ (fun x ↦ ζ x • chartNormal F x) y) (chartNormal F y) =
      ζ y * meanCurvature F y := by
  rw [firstVariationCoeff, real_inner_comm, ← h.tangentialDivergence_smul_chartNormal hy hζ]
  rfl

/-- For the normal variation `X = ζ ν` at a point of vanishing mean curvature, the second-order
coefficient is `|δζ|² - ζ² |A|²`. -/
theorem secondVariationCoeff_fderiv_smul_chartNormal (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) {ζ : Space d → ℝ} (hζ : DifferentiableAt ℝ ζ y)
    (hH : meanCurvature F y = 0) :
    secondVariationCoeff (fderiv ℝ (fun x ↦ ζ x • chartNormal F x) y) (chartNormal F y) =
      ‖tangentialGradient F ζ y‖ ^ 2 - ζ y ^ 2 * sqNormSecondFundamentalForm F y := by
  have hne := h.gradient_ne_zero y hy
  have hA : fderiv ℝ (fun x ↦ ζ x • chartNormal F x) y =
      ζ y • fderiv ℝ (chartNormal F) y + (fderiv ℝ ζ y).smulRight (chartNormal F y) :=
    (hζ.hasFDerivAt.smul (h.differentiableAt_chartNormal hy).hasFDerivAt).fderiv
  have htrBB : LinearMap.trace ℝ (Space d)
      (fderiv ℝ (chartNormal F) y * fderiv ℝ (chartNormal F) y).toLinearMap =
        sqNormSecondFundamentalForm F y :=
    (h.sqNormSecondFundamentalForm_eq_trace_sq hy).symm
  rw [hA]
  set v := chartNormal F y with hvdef
  set B := fderiv ℝ (chartNormal F) y with hBdef
  set φ := fderiv ℝ ζ y with hφdef
  set z := ζ y with hzdef
  have hvv : inner ℝ v v = 1 := inner_chartNormal_self hne
  have hvB (w : Space d) : inner ℝ v (B w) = 0 := h.inner_chartNormal_fderiv_chartNormal hy w
  have hBv (w : Space d) : inner ℝ (B w) v = 0 := by
    rw [real_inner_comm]
    exact hvB w
  have htrB : LinearMap.trace ℝ (Space d) B.toLinearMap = 0 := hH
  set A := z • B + φ.smulRight v with hAdef
  have hAw (w : Space d) : A w = z • B w + φ w • v := rfl
  have htrA : LinearMap.trace ℝ (Space d) A.toLinearMap = φ v := by
    rw [hAdef, trace_clm_add, trace_clm_smul, trace_clm_smulRight, htrB, mul_zero, zero_add]
  have hAv_v : inner ℝ (A v) v = φ v := by
    rw [hAw, inner_add_left, real_inner_smul_left, real_inner_smul_left, hBv, hvv]
    ring
  have hAadj : A.adjoint v = gradient ζ y := by
    apply ext_inner_right ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, hAw, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hvB, hvv, inner_gradient_left]
    ring
  have hAAv_v : inner ℝ (A (A v)) v = z * φ (B v) + φ v ^ 2 := by
    rw [hAw (A v), inner_add_left, real_inner_smul_left, real_inner_smul_left, hBv, hvv, hAw v,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hAA : A * A = (z ^ 2) • (B * B) + z • φ.smulRight (B v) +
      z • (φ.comp B).smulRight v + (φ v) • φ.smulRight v := by
    ext1 w
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hAw, map_add,
      map_smul, FunLike.coe_add,
      FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    module
  have htrAA : LinearMap.trace ℝ (Space d) (A * A).toLinearMap =
      z ^ 2 * sqNormSecondFundamentalForm F y + 2 * z * φ (B v) + φ v ^ 2 := by
    rw [hAA, trace_clm_add, trace_clm_add, trace_clm_add, trace_clm_smul, trace_clm_smul,
      trace_clm_smul, trace_clm_smul, trace_clm_smulRight, trace_clm_smulRight,
      trace_clm_smulRight, htrBB, ContinuousLinearMap.comp_apply]
    ring
  have hvg : inner ℝ v (gradient ζ y) = φ v := by
    rw [real_inner_comm, inner_gradient_left]
  rw [secondVariationCoeff, htrA, hAv_v, hAadj, hAAv_v, htrAA, tangentialGradient,
    norm_sq_tangentialProj hne, ← hvdef, hvg]
  ring

theorem continuousOn_tangentialProj_apply (h : IsSmoothBoundaryChart E U F)
    {w : Space d → Space d} (hw : ContinuousOn w U) :
    ContinuousOn (fun x ↦ tangentialProj F x (w x)) U := by
  have hN : ContinuousOn (chartNormal F) U := h.contDiffOn_chartNormal.continuousOn
  have hfun : (fun x ↦ tangentialProj F x (w x)) =
      fun x ↦ w x - inner ℝ (chartNormal F x) (w x) • chartNormal F x :=
    funext fun x ↦ tangentialProj_apply F x (w x)
  rw [hfun]
  exact hw.sub ((hN.inner (𝕜 := ℝ) hw).smul hN)

theorem continuousOn_sqNormSecondFundamentalForm (h : IsSmoothBoundaryChart E U F) :
    ContinuousOn (sqNormSecondFundamentalForm F) U := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hfun : sqNormSecondFundamentalForm F =
      fun x ↦ ∑ i, ‖secondFundamentalForm F x (e i)‖ ^ 2 :=
    funext fun x ↦ sqNormSecondFundamentalForm_eq_sum e F x
  rw [hfun]
  have hD : ContinuousOn (fderiv ℝ (chartNormal F)) U :=
    h.contDiffOn_chartNormal.continuousOn_fderiv_of_isOpen h.isOpen (by simp)
  refine continuousOn_finsetSum _ fun i _ ↦ ?_
  have h1 : ContinuousOn (fun x ↦ tangentialProj F x (e i)) U :=
    h.continuousOn_tangentialProj_apply continuousOn_const
  have h2 : ContinuousOn (fun x ↦ fderiv ℝ (chartNormal F) x (tangentialProj F x (e i))) U :=
    hD.clm_apply h1
  have h3 := h.continuousOn_tangentialProj_apply h2
  exact (h3.norm).pow 2

theorem continuousOn_tangentialGradient (h : IsSmoothBoundaryChart E U F) {f : Space d → ℝ}
    (hf : ContDiff ℝ 1 f) : ContinuousOn (tangentialGradient F f) U :=
  h.continuousOn_tangentialProj_apply
    ((toDual ℝ (Space d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)).continuousOn

/-- **GR1: the stability inequality.** Let `E` minimize perimeter in `Ω`, let `(μ, ν)` be a
perimeter measure with polar vector on `Ω`, and let `(E, U, F)` be a smooth boundary chart with
`U ⊆ Ω`. Then for every `C²` function `ζ` compactly supported in `U`,
`∫_M ζ² |A|² dμ ≤ ∫_M |δζ|² dμ`. -/
theorem stability_inequality (h : IsSmoothBoundaryChart E U F) (hE : MeasurableSet E)
    (hp : IsPerimeterPolarOn b E Ω μ ν) (hmin : IsPerimeterMinimizingIn b E Ω) (hUΩ : U ⊆ Ω)
    {ζ : Space d → ℝ} (hζ : ContDiff ℝ 2 ζ) (hζc : HasCompactSupport ζ)
    (hζU : tsupport ζ ⊆ U) :
    ∫ x in U, ζ x ^ 2 * sqNormSecondFundamentalForm F x ∂μ ≤
      ∫ x in U, ‖tangentialGradient F ζ x‖ ^ 2 ∂μ := by
  have hfinΩ := hp.isFiniteMeasure
  have hfinU := isFiniteMeasure_restrict hp hUΩ
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by norm_num)
  -- the normal variation field `X = ζ ν`
  set X : Space d → Space d := fun x ↦ ζ x • chartNormal F x with hXdef
  have hX : ContDiff ℝ 2 X :=
    contDiff_smul_of_tsupport_subset_of_contDiffOn h.isOpen
      (h.contDiffOn_chartNormal.of_le (by simp)) hζ hζU
  have hXc : HasCompactSupport X := hasCompactSupport_smul_left' hζc _
  have hXU : tsupport X ⊆ U := (tsupport_smul_subset_left' _ _).trans hζU
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  -- a uniform bound on `DX`
  obtain ⟨M₀, hM₀⟩ :=
    hXc.exists_bound_of_continuousOn (hX1.continuous_fderiv one_ne_zero).continuousOn
  set M := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hDX (x : Space d) : ‖fderiv ℝ X x‖ ≤ M := by
    by_cases hx : x ∈ tsupport X
    · exact (hM₀ x hx).trans (le_max_left _ _)
    · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact hM
  obtain ⟨t₁, ht₁, C, hC, hexp⟩ := exists_norm_sq_cofactorMap_expansion (d := d) M hM
  obtain ⟨δ, hδ, hcomp⟩ := hp.exists_integral_norm_le_cofactorMap hE hmin hX hXc
    (hXU.trans hUΩ)
  -- the second variation density
  set Γ : Space d → ℝ := fun x ↦
    ‖tangentialGradient F ζ x‖ ^ 2 - ζ x ^ 2 * sqNormSecondFundamentalForm F x with hΓdef
  have hδζ0 (x : Space d) (hx : x ∉ tsupport ζ) : tangentialGradient F ζ x = 0 := by
    simp [tangentialGradient, gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hΓ0 (x : Space d) (hx : x ∉ tsupport ζ) : Γ x = 0 := by
    simp [hΓdef, hδζ0 x hx, image_eq_zero_of_notMem_tsupport hx]
  have hcont1 : Continuous fun x ↦ ‖tangentialGradient F ζ x‖ ^ 2 := by
    apply continuous_of_continuousOn_of_eq_zero h.isOpen (isClosed_tsupport ζ) hζU
    · exact ((h.continuousOn_tangentialGradient hζ1).norm).pow 2
    · intro x hx
      simp [hδζ0 x hx]
  have hcont2 : Continuous fun x ↦ ζ x ^ 2 * sqNormSecondFundamentalForm F x := by
    apply continuous_of_continuousOn_of_eq_zero h.isOpen (isClosed_tsupport ζ) hζU
    · exact (hζ.continuous.continuousOn.pow 2).mul h.continuousOn_sqNormSecondFundamentalForm
    · intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hsupp (g : Space d → ℝ) (hg : ∀ x, x ∉ tsupport ζ → g x = 0) : HasCompactSupport g := by
    apply hζc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport ζ)
    intro x hx
    by_contra hxζ
    exact hx (hg x hxζ)
  have hc1 : HasCompactSupport fun x ↦ ‖tangentialGradient F ζ x‖ ^ 2 :=
    hsupp _ fun x hx ↦ by simp [hδζ0 x hx]
  have hc2 : HasCompactSupport fun x ↦ ζ x ^ 2 * sqNormSecondFundamentalForm F x :=
    hsupp _ fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have hΓcont : Continuous Γ := hcont1.sub hcont2
  have hΓint : Integrable Γ (μ.restrict Ω) :=
    hΓcont.integrable_of_hasCompactSupport (hsupp Γ hΓ0)
  -- pointwise second-order upper bound for the deformed area density
  have hpt : ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ᵐ x ∂μ.restrict Ω,
      ‖cofactorMap (t • fderiv ℝ X x) (ν x)‖ ≤ 1 + t ^ 2 / 2 * Γ x + C / 2 * t ^ 3 := by
    intro t ht0 htt₁
    have hae2 : ∀ᵐ x ∂μ.restrict Ω, x ∈ U → F x = 0 ∧ ν x = chartNormal F x := by
      have h3 : ∀ᵐ x ∂μ.restrict U, F x = 0 ∧ ν x = chartNormal F x :=
        (h.ae_restrict_eq_zero hp hUΩ).and (h.ae_restrict_eq_chartNormal hp hUΩ)
      rw [ae_restrict_iff' h.isOpen.measurableSet] at h3
      exact ae_restrict_of_ae h3
    filter_upwards [hp.norm_eq_one, hae2] with x hx1 hx2
    by_cases hxζ : x ∈ tsupport ζ
    · have hxU := hζU hxζ
      obtain ⟨hF0, hνx⟩ := hx2 hxU
      have hH := h.meanCurvature_eq_zero hE hp hmin hUΩ hxU hF0
      have hζd : DifferentiableAt ℝ ζ x := hζ1.differentiable one_ne_zero x
      have hβ := h.firstVariationCoeff_fderiv_smul_chartNormal hxU hζd
      have hγ := h.secondVariationCoeff_fderiv_smul_chartNormal hxU hζd hH
      rw [hH, mul_zero] at hβ
      have hv1 : ‖chartNormal F x‖ = 1 := norm_chartNormal (h.gradient_ne_zero x hxU)
      have hb := hexp (fderiv ℝ X x) (hDX x) (chartNormal F x) hv1 t
        (by rw [abs_of_pos ht0]; exact htt₁)
      rw [hβ, hγ, abs_of_pos ht0] at hb
      rw [hνx]
      have hw2 := (abs_le.mp hb).2
      have hΓx : Γ x = ‖tangentialGradient F ζ x‖ ^ 2 -
          ζ x ^ 2 * sqNormSecondFundamentalForm F x := rfl
      rw [hΓx]
      nlinarith [sq_nonneg (‖cofactorMap (t • fderiv ℝ X x) (chartNormal F x)‖ - 1)]
    · have hDX0 : fderiv ℝ X x = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hh ↦ hxζ (tsupport_smul_subset_left' _ _ hh))
      have h0 : t • (0 : Space d →L[ℝ] Space d) = 0 := by
        ext1 w
        simp
      rw [hDX0, h0, cofactorMap_zero, one_apply_eq_self, hx1, hΓ0 x hxζ]
      have : 0 ≤ C / 2 * t ^ 3 := by positivity
      linarith
  -- integrate the pointwise bound against minimality
  set m : ℝ := (μ.restrict Ω).real univ with hmdef
  set I : ℝ := ∫ x, Γ x ∂μ.restrict Ω with hIdef
  have hν1 : ∫ x, ‖ν x‖ ∂μ.restrict Ω = m := by
    rw [integral_congr_ae hp.norm_eq_one, integral_const, smul_eq_mul, mul_one]
  have hstep : ∀ t : ℝ, 0 < t → t < min δ t₁ → 0 ≤ I + C * t * m := by
    intro t ht0 htlt
    have htδ : |t| < δ := by
      rw [abs_of_pos ht0]
      exact htlt.trans_le (min_le_left _ _)
    have htt₁ : t ≤ t₁ := htlt.le.trans (min_le_right _ _)
    have h1 := hcomp t htδ
    have hf1 : Integrable (fun x ↦ 1 + t ^ 2 / 2 * Γ x) (μ.restrict Ω) :=
      (integrable_const _).add (hΓint.const_mul _)
    have hupper : Integrable (fun x ↦ 1 + t ^ 2 / 2 * Γ x + C / 2 * t ^ 3) (μ.restrict Ω) :=
      hf1.add (integrable_const _)
    have h2 : ∫ x, ‖cofactorMap (t • fderiv ℝ X x) (ν x)‖ ∂μ.restrict Ω ≤
        ∫ x, (1 + t ^ 2 / 2 * Γ x + C / 2 * t ^ 3) ∂μ.restrict Ω :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _) hupper
        (hpt t ht0 htt₁)
    have h3 : ∫ x, (1 + t ^ 2 / 2 * Γ x + C / 2 * t ^ 3) ∂μ.restrict Ω =
        m + t ^ 2 / 2 * I + C / 2 * t ^ 3 * m := by
      rw [integral_add hf1 (integrable_const _),
        integral_add (integrable_const _) (hΓint.const_mul _), integral_const, integral_const,
        integral_const_mul, smul_eq_mul, smul_eq_mul, mul_one]
      ring
    have ht2 : 0 < t ^ 2 / 2 := by positivity
    have h4 : t ^ 2 / 2 * 0 ≤ t ^ 2 / 2 * (I + C * t * m) := by
      have : t ^ 2 / 2 * (I + C * t * m) = t ^ 2 / 2 * I + C / 2 * t ^ 3 * m := by ring
      rw [this, mul_zero]
      linarith
    exact le_of_mul_le_mul_left h4 ht2
  have hI : 0 ≤ I := by
    have hlim : Tendsto (fun t : ℝ ↦ I + C * t * m) (𝓝[>] 0) (𝓝 (I + C * 0 * m)) :=
      ((continuous_const.add ((continuous_const.mul continuous_id).mul continuous_const)).tendsto
        0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ I + C * t * m := by
      filter_upwards [Ioo_mem_nhdsGT (lt_min hδ ht₁)] with t ht
      exact hstep t ht.1 ht.2
    have := ge_of_tendsto hlim hev
    simpa using this
  -- rewrite `I` as the difference of the two integrals over the chart
  have hΓU : I = ∫ x in U, Γ x ∂μ := by
    rw [hIdef, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (fun x hx ↦ hΓ0 x (fun hh ↦ hx (hζU hh))), Measure.restrict_restrict' hp.isOpen.measurableSet,
      inter_eq_left.mpr hUΩ]
  have hint1 : Integrable (fun x ↦ ‖tangentialGradient F ζ x‖ ^ 2) (μ.restrict U) :=
    hcont1.integrable_of_hasCompactSupport hc1
  have hint2 : Integrable (fun x ↦ ζ x ^ 2 * sqNormSecondFundamentalForm F x) (μ.restrict U) :=
    hcont2.integrable_of_hasCompactSupport hc2
  have hsplit : ∫ x in U, Γ x ∂μ = ∫ x in U, ‖tangentialGradient F ζ x‖ ^ 2 ∂μ -
      ∫ x in U, ζ x ^ 2 * sqNormSecondFundamentalForm F x ∂μ := integral_sub hint1 hint2
  rw [hΓU, hsplit] at hI
  linarith

end IsSmoothBoundaryChart

end SerrinEpigraph
