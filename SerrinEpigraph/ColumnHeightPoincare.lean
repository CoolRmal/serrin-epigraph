module

public import SerrinEpigraph.PerimeterRotation

/-!
# BV Poincaré inequality for the column signed height (`GR9`, `GR10`)

For a set `E` whose boundary in the cylinder `U × (-H', H')` is trapped in the slab `|t| ≤ H`, the
signed height `g = columnSignedHeight E H` is a bounded function of bounded variation on `U` with
`Dg = -π_# (ν_h μ)` (`BVColumnGraph`, `BV13.3`). This module proves the `L¹` Poincaré inequality on
horizontal balls
`∫_{B_r(y₀)} |g - g_{B_r(y₀)}| ≤ 2^(m+1) r ∫_{π⁻¹ B_R(y₀)} |ν_h| dμ` (`r < R`),
by smoothing `g` with the averaging kernels of `Mollification`, bounding the gradient mass of the
smoothed heights through the horizontal moment formula, applying the `C¹` Poincaré inequality on
balls (`integral_ball_norm_sub_le_gradient`), and passing to the limit.
Together with the Cauchy–Schwarz bound `∫_{π⁻¹A} |ν_h| dμ ≤ √(2 ε(A)(|A| + ε(A)))`
(`integral_norm_horizontal_normal_le`, `GR9.1`) this controls oscillations of `g` by the excess.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported

namespace SerrinEpigraph

/-! ### 1. The `L¹` Poincaré inequality on balls for `C¹` functions -/

/-- Double-integral `L¹` Poincaré inequality on any ball of `Space d` for `C¹` functions. -/
theorem integral_ball_norm_sub_le_gradient {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (y₀ : Space d) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball y₀ r, ∫ y in ball y₀ r, ‖v x - v y‖) ≤
      2 ^ (d + 1) * r * volume.real (ball y₀ r) * ∫ z in ball y₀ r, ‖gradient v z‖ := by
  let B₁ : Set (Space d) := ball y₀ r
  let μB : Measure (Space d) := volume.restrict B₁
  let I_half : Set ℝ := Icc (0 : ℝ) (1 / 2)
  let μT : Measure ℝ := volume.restrict I_half
  let : IsFiniteMeasure μB := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact measure_ball_lt_top⟩
  let : IsFiniteMeasure μT := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hG_cont : Continuous (fun z ↦ ‖gradient v z‖) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (hv.continuous_fderiv one_ne_zero).norm
  have hGi_B : IntegrableOn (fun z ↦ ‖gradient v z‖) B₁ volume :=
    (hG_cont.continuousOn.integrableOn_compact (isCompact_closedBall y₀ r)).mono_set
      ball_subset_closedBall
  let g : Space d → ℝ := B₁.indicator (fun z ↦ ‖gradient v z‖)
  have hgi : Integrable g volume := hGi_B.integrable_indicator measurableSet_ball
  let H : Space d × Space d → ℝ → ℝ :=
    fun p t ↦ ‖gradient v ((1 - t) • p.1 + t • p.2)‖
  have hH_cont : Continuous (Function.uncurry H) :=
    hG_cont.comp (((continuous_const.sub continuous_snd).smul
      (continuous_fst.comp continuous_fst)).add
      (continuous_snd.smul (continuous_snd.comp continuous_fst)))
  have hHi : Integrable (Function.uncurry H) ((μB.prod μB).prod μT) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    refine (hH_cont.continuousOn.integrableOn_compact
      (((isCompact_closedBall y₀ r).prod
        (isCompact_closedBall y₀ r)).prod
          (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2)))).mono_set ?_
    exact Set.prod_mono (Set.prod_mono ball_subset_closedBall ball_subset_closedBall) Subset.rfl
  let Φ : Space d × Space d → ℝ := fun p ↦ ∫ t in I_half, H p t
  have hΦ_cont : Continuous Φ :=
    continuous_parametric_integral_of_continuous (μ := volume) hH_cont isCompact_Icc
  have hΦ_int : Integrable Φ (μB.prod μB) := by
    rw [Measure.prod_restrict]
    exact (hΦ_cont.continuousOn.integrableOn_compact
      ((isCompact_closedBall y₀ r).prod (isCompact_closedBall y₀ r))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  let Φ_swap : Space d × Space d → ℝ := fun p ↦ Φ (p.2, p.1)
  have hΦ_swap_cont : Continuous Φ_swap := hΦ_cont.comp continuous_swap
  have hΦ_swap_int : Integrable Φ_swap (μB.prod μB) := by
    rw [Measure.prod_restrict]
    exact (hΦ_swap_cont.continuousOn.integrableOn_compact
      ((isCompact_closedBall y₀ r).prod (isCompact_closedBall y₀ r))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  have hdiff_cont : Continuous (fun p : Space d × Space d ↦ ‖v p.1 - v p.2‖) :=
    ((hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)).norm
  have hdiff_int : Integrable (fun p : Space d × Space d ↦ ‖v p.1 - v p.2‖)
      (μB.prod μB) := by
    rw [Measure.prod_restrict]
    exact (hdiff_cont.continuousOn.integrableOn_compact
      ((isCompact_closedBall y₀ r).prod (isCompact_closedBall y₀ r))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  have hpoint (p : Space d × Space d) (hp : p ∈ B₁ ×ˢ B₁) :
      ‖v p.1 - v p.2‖ ≤ 2 * r * (Φ p + Φ_swap p) := by
    have hx : dist p.1 y₀ < r := hp.1
    have hy : dist p.2 y₀ < r := hp.2
    have hdist : ‖p.2 - p.1‖ ≤ 2 * r := by
      rw [← dist_eq_norm]
      have htri := dist_triangle_right p.2 p.1 y₀
      linarith
    have hseg := norm_sub_le_integral_segment_gradient hv p.1 (p.2 - p.1)
    have hadd : p.1 + (p.2 - p.1) = p.2 := add_sub_cancel p.1 p.2
    rw [hadd, norm_sub_rev] at hseg
    have hgamma (t : ℝ) : p.1 + t • (p.2 - p.1) = (1 - t) • p.1 + t • p.2 := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    simp_rw [hgamma] at hseg
    have hc_seg : Continuous (fun t : ℝ ↦ H p t) :=
      hG_cont.comp (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const))
    have hnonneg_int : 0 ≤ ∫ t in (0 : ℝ)..1, H p t :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ norm_nonneg _
    have hsplit : (∫ t in (0 : ℝ)..1, H p t) = Φ p + Φ_swap p := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hc_seg.intervalIntegrable 0 (1 / 2))
        (hc_seg.intervalIntegrable (1 / 2) 1)]
      congr 1
      · rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      · have hsub_var := intervalIntegral.integral_comp_sub_left
          (fun s : ℝ ↦ ‖gradient v (s • p.1 + (1 - s) • p.2)‖) (1 : ℝ) (a := (1 / 2 : ℝ)) (b := 1)
        simp only [sub_self] at hsub_var
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at hsub_var
        have hlhs_eq : (∫ t in (1 / 2 : ℝ)..1, H p t) =
            ∫ t in (1 / 2 : ℝ)..1, ‖gradient v ((1 - t) • p.1 + (1 - (1 - t)) • p.2)‖ := by
          congr 1 with t
          simp [H]
        rw [hlhs_eq, hsub_var, intervalIntegral.integral_of_le (by norm_num),
          ← integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_fun measurableSet_Icc fun s _ ↦ ?_
        dsimp [Φ_swap, Φ, H]
        have hcomm : s • p.1 + (1 - s) • p.2 = (1 - s) • p.2 + s • p.1 := add_comm _ _
        rw [hcomm]
    calc
      ‖v p.1 - v p.2‖ ≤ ‖p.2 - p.1‖ * ∫ t in (0 : ℝ)..1, H p t := hseg
      _ ≤ 2 * r * ∫ t in (0 : ℝ)..1, H p t := mul_le_mul_of_nonneg_right hdist hnonneg_int
      _ = 2 * r * (Φ p + Φ_swap p) := by rw [hsplit]
  have hprod_le : (∫ p, ‖v p.1 - v p.2‖ ∂(μB.prod μB)) ≤
      2 * r * ((∫ p, Φ p ∂(μB.prod μB)) + ∫ p, Φ_swap p ∂(μB.prod μB)) := by
    have hae : (fun p ↦ ‖v p.1 - v p.2‖) ≤ᵐ[μB.prod μB] fun p ↦ 2 * r * (Φ p + Φ_swap p) := by
      change ∀ᵐ p ∂(μB.prod μB), ‖v p.1 - v p.2‖ ≤ 2 * r * (Φ p + Φ_swap p)
      rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_ball.prod measurableSet_ball)]
      exact Eventually.of_forall hpoint
    have h1 := integral_mono_ae hdiff_int ((hΦ_int.add hΦ_swap_int).const_mul (2 * r)) hae
    change (∫ p, ‖v p.1 - v p.2‖ ∂(μB.prod μB)) ≤
      ∫ p, 2 * r * (Φ p + Φ_swap p) ∂(μB.prod μB) at h1
    rwa [integral_const_mul, integral_add hΦ_int hΦ_swap_int] at h1
  have hswap_eq : (∫ p, Φ_swap p ∂(μB.prod μB)) = ∫ p, Φ p ∂(μB.prod μB) := by
    rw [integral_prod _ hΦ_swap_int, integral_integral_swap hΦ_swap_int]
    change (∫ y, ∫ x, Φ (y, x) ∂μB ∂μB) = _
    rw [← integral_prod _ hΦ_int]
  have hslice (t : ℝ) (ht : t ∈ I_half) :
      (∫ p, H p t ∂(μB.prod μB)) ≤
        2 ^ d * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖ := by
    have ht0 : 0 ≤ t := ht.1
    have ht_half : t ≤ 1 / 2 := ht.2
    let s : ℝ := 1 - t
    have hs_half : 1 / 2 ≤ s := by dsimp [s]; linarith
    have hs_pos : 0 < s := by linarith
    have hHt_int : Integrable (fun p : Space d × Space d ↦ H p t) (μB.prod μB) := by
      rw [Measure.prod_restrict]
      have hc : Continuous (fun p : Space d × Space d ↦ H p t) :=
        hG_cont.comp ((continuous_fst.const_smul (1 - t)).add (continuous_snd.const_smul t))
      exact (hc.continuousOn.integrableOn_compact
        ((isCompact_closedBall y₀ r).prod (isCompact_closedBall y₀ r))).mono_set
        (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
    have hinner (y : Space d) (hy : y ∈ B₁) :
        (∫ x in B₁, H (x, y) t) ≤ 2 ^ d * ∫ z in B₁, ‖gradient v z‖ := by
      have hconv (x : Space d) (hx : x ∈ B₁) : H (x, y) t = g (t • y + s • x) := by
        have hmem : (1 - t) • x + t • y ∈ B₁ :=
          (convex_ball y₀ r) hx hy hs_pos.le ht0 (by ring)
        have hmem' : t • y + s • x ∈ B₁ := by
          dsimp [s]
          rwa [add_comm (t • y) ((1 - t) • x)]
        dsimp [H, g, s]
        rw [add_comm ((1 - t) • x) (t • y), indicator_of_mem hmem']
      have heq_set : (∫ x in B₁, H (x, y) t) = ∫ x in B₁, g (t • y + s • x) :=
        setIntegral_congr_fun measurableSet_ball hconv
      have hgi_shift : Integrable (fun u ↦ g (t • y + u)) volume :=
        (measurePreserving_add_left volume (t • y)).integrable_comp_of_integrable hgi
      have hgi_comp : Integrable (fun x ↦ g (t • y + s • x)) volume :=
        hgi_shift.comp_smul hs_pos.ne'
      have hle_univ : (∫ x in B₁, g (t • y + s • x)) ≤ ∫ x, g (t • y + s • x) :=
        setIntegral_le_integral hgi_comp (Eventually.of_forall fun x ↦ by
          dsimp [g]
          by_cases h : t • y + s • x ∈ B₁ <;> simp [h])
      have hdil := Measure.integral_comp_smul (μ := volume)
        (f := fun u : Space d ↦ g (t • y + u)) s
      simp only [Space, finrank_euclideanSpace_fin, abs_inv, abs_pow,
        abs_of_pos hs_pos, smul_eq_mul] at hdil
      have htrans : (∫ u : Space d, g (t • y + u)) = ∫ z in B₁, ‖gradient v z‖ := by
        rw [integral_add_left_eq_self g (t • y), integral_indicator measurableSet_ball]
      have hscale_le : (s ^ d)⁻¹ ≤ (2 : ℝ) ^ d := by
        have hpow_le : ((1 : ℝ) / 2) ^ d ≤ s ^ d :=
          pow_le_pow_left₀ (by positivity) hs_half d
        have hinv := inv_anti₀ (by positivity) hpow_le
        have h2 : (((1 : ℝ) / 2) ^ d)⁻¹ = (2 : ℝ) ^ d := by
          rw [one_div, inv_pow, inv_inv]
        rwa [h2] at hinv
      have hgrad_nonneg : 0 ≤ ∫ z in B₁, ‖gradient v z‖ :=
        integral_nonneg fun _ ↦ norm_nonneg _
      rw [heq_set]
      refine hle_univ.trans ?_
      rw [hdil, htrans]
      exact mul_le_mul_of_nonneg_right hscale_le hgrad_nonneg
    rw [integral_prod _ hHt_int, integral_integral_swap hHt_int]
    have hmono := setIntegral_mono_on hHt_int.integral_prod_right
      (integrableOn_const (μ := volume) (s := B₁) (C := 2 ^ d * ∫ z in B₁, ‖gradient v z‖)
        measure_ball_ne_top)
      measurableSet_ball hinner
    simpa only [setIntegral_const, smul_eq_mul, mul_comm (volume.real B₁), mul_assoc] using hmono
  have hΦ_bound : (∫ p, Φ p ∂(μB.prod μB)) ≤
      (1 / 2 : ℝ) * (2 ^ d * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖) := by
    change (∫ p, (∫ t, H p t ∂μT) ∂(μB.prod μB)) ≤ _
    rw [integral_integral_swap hHi]
    have hmono := setIntegral_mono_on hHi.integral_prod_right
      (integrableOn_const (μ := volume) (s := I_half)
        (C := 2 ^ d * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Icc hslice
    simpa only [μT, I_half, setIntegral_const, Real.volume_real_Icc, sub_zero,
      max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul,
      Function.uncurry_apply_pair] using hmono
  rw [← integral_prod _ hdiff_int]
  calc
    (∫ p, ‖v p.1 - v p.2‖ ∂(μB.prod μB)) ≤ 4 * r * ∫ p, Φ p ∂(μB.prod μB) := by
      refine hprod_le.trans (le_of_eq ?_)
      rw [hswap_eq]
      ring
    _ ≤ 4 * r * ((1 / 2 : ℝ) * (2 ^ d * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖)) :=
      mul_le_mul_of_nonneg_left hΦ_bound (by positivity)
    _ = 2 ^ (d + 1) * r * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖ := by
      rw [pow_succ]
      ring

/-- Jensen's step: the mean oscillation on a set is at most the normalized double integral of the
pairwise differences. -/
theorem integral_abs_sub_setAverage_le {d : ℕ} {v : Space d → ℝ} {B : Set (Space d)}
    (hBfin : volume B ≠ ⊤)
    (hint : Integrable (fun p : Space d × Space d ↦ |v p.1 - v p.2|)
      ((volume.restrict B).prod (volume.restrict B)))
    (hv : IntegrableOn v B) :
    ∫ x in B, |v x - ⨍ y in B, v y| ≤
      (volume.real B)⁻¹ * ∫ x in B, ∫ y in B, |v x - v y| := by
  have : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact lt_top_iff_ne_top.mpr hBfin⟩
  by_cases hB0 : volume.real B = 0
  · have hB0' : volume B = 0 := (measureReal_eq_zero_iff hBfin).mp hB0
    simp [Measure.restrict_eq_zero.mpr hB0']
  have hBpos : 0 < volume.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hB0)
  have hrow := hint.integral_prod_left
  have hpt : ∀ x, |v x - ⨍ y in B, v y| ≤ (volume.real B)⁻¹ * ∫ y in B, |v x - v y| := by
    intro x
    have hc : IntegrableOn (fun _ : Space d ↦ v x) B := integrableOn_const hBfin
    have heq : v x - ⨍ y in B, v y = (volume.real B)⁻¹ * ∫ y in B, (v x - v y) := by
      rw [integral_sub hc hv, setIntegral_const, setAverage_eq, smul_eq_mul, smul_eq_mul]
      field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (inv_nonneg.mpr hBpos.le)
  have hleft : IntegrableOn (fun x ↦ |v x - ⨍ y in B, v y|) B :=
    (hv.sub (integrableOn_const hBfin)).abs
  calc
    ∫ x in B, |v x - ⨍ y in B, v y| ≤ ∫ x in B, (volume.real B)⁻¹ * ∫ y in B, |v x - v y| :=
      integral_mono hleft (hrow.const_mul _) hpt
    _ = (volume.real B)⁻¹ * ∫ x in B, ∫ y in B, |v x - v y| := integral_const_mul _ _

/-- The mean oscillation of a `C¹` function on a ball is controlled by its gradient mass. -/
theorem integral_abs_sub_ball_average_le {d : ℕ} {v : Space d → ℝ} (hv : ContDiff ℝ 1 v)
    (y₀ : Space d) {r : ℝ} (hr : 0 < r) :
    ∫ x in ball y₀ r, |v x - ⨍ y in ball y₀ r, v y| ≤
      2 ^ (d + 1) * r * ∫ z in ball y₀ r, ‖gradient v z‖ := by
  have hBpos : 0 < volume.real (ball y₀ r) :=
    ENNReal.toReal_pos (measure_ball_pos volume y₀ hr).ne' measure_ball_ne_top
  have hcont : Continuous (fun p : Space d × Space d ↦ |v p.1 - v p.2|) :=
    ((hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)).abs
  have hint : Integrable (fun p : Space d × Space d ↦ |v p.1 - v p.2|)
      ((volume.restrict (ball y₀ r)).prod (volume.restrict (ball y₀ r))) := by
    rw [Measure.prod_restrict]
    exact (hcont.continuousOn.integrableOn_compact
      ((isCompact_closedBall y₀ r).prod (isCompact_closedBall y₀ r))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  have hvB : IntegrableOn v (ball y₀ r) :=
    (hv.continuous.continuousOn.integrableOn_compact (isCompact_closedBall y₀ r)).mono_set
      ball_subset_closedBall
  have hJ := integral_abs_sub_setAverage_le measure_ball_ne_top hint hvB
  have hP := integral_ball_norm_sub_le_gradient hv y₀ hr
  simp only [Real.norm_eq_abs] at hP
  calc
    _ ≤ (volume.real (ball y₀ r))⁻¹ * ∫ x in ball y₀ r, ∫ y in ball y₀ r, |v x - v y| := hJ
    _ ≤ (volume.real (ball y₀ r))⁻¹ * (2 ^ (d + 1) * r * volume.real (ball y₀ r) *
          ∫ z in ball y₀ r, ‖gradient v z‖) :=
      mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hBpos.le)
    _ = 2 ^ (d + 1) * r * ∫ z in ball y₀ r, ‖gradient v z‖ := by
      field_simp

/-! ### 2. Horizontal normal mass and the excess (`GR9.1`) -/

/-- Cauchy–Schwarz bound for the horizontal normal mass over a column set (`GR9.1`):
`∫_{π⁻¹A} |ν_h| dμ ≤ √(2 ε(A) (|A| + ε(A)))`, where `ε = projectedExcessMeasure μ ν`. -/
theorem integral_norm_horizontal_normal_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    ∫ x in horizontal ⁻¹' A, ‖horizontal (ν x)‖ ∂μ ≤
      Real.sqrt (2 * (projectedExcessMeasure μ ν).real A *
        (volume.real A + (projectedExcessMeasure μ ν).real A)) := by
  have := hrep.isFiniteMeasure
  have hν := hrep.integrable
  have hνunit := hrep.norm_eq_one
  let S : Set (Space (m + 1)) := horizontal ⁻¹' A
  have hS : MeasurableSet S := hA.preimage continuous_horizontal.measurable
  have hνh_aesm : AEStronglyMeasurable (fun x ↦ ‖horizontal (ν x)‖) (μ.restrict S) :=
    (horizontalContinuousLinearMap.continuous.comp_aestronglyMeasurable
      hν.aestronglyMeasurable.restrict).norm
  have hνh_sq_int : Integrable (fun x ↦ ‖horizontal (ν x)‖ ^ 2) (μ.restrict S) := by
    refine Integrable.of_bound ((continuous_pow 2).comp_aestronglyMeasurable hνh_aesm) 1 ?_
    filter_upwards [ae_restrict_of_ae hνunit] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hsq : ‖horizontal (ν x)‖ ^ 2 + (inner ℝ (ν x) (verticalDirection m)) ^ 2 = 1 := by
      have h1 : ‖ν x‖ ^ 2 = 1 := by rw [hx, one_pow]
      nth_rw 1 [← point_horizontal_last (ν x)] at h1
      rw [← real_inner_self_eq_norm_sq (point _ _), inner_point_point,
        real_inner_self_eq_norm_sq, ← inner_verticalDirection_right (ν x)] at h1
      linarith
    nlinarith [sq_nonneg (inner ℝ (ν x) (verticalDirection m))]
  have h1_sq_int : Integrable (fun _ : Space (m + 1) ↦ (1 : ℝ) ^ 2) (μ.restrict S) :=
    integrable_const _
  have hcs := abs_integral_mul_le_sqrt hνh_sq_int h1_sq_int
  simp only [mul_one] at hcs
  have hpos_int : 0 ≤ ∫ x in S, ‖horizontal (ν x)‖ ∂μ :=
    integral_nonneg fun x ↦ norm_nonneg _
  rw [abs_of_nonneg hpos_int] at hcs
  let w : Space (m + 1) → ℝ := fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)
  have hw_aesm : AEStronglyMeasurable w μ :=
    aestronglyMeasurable_const.sub (hν.aestronglyMeasurable.inner aestronglyMeasurable_const)
  have hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x := by
    filter_upwards [hνunit] with x hx
    have hc := real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hc
    dsimp [w]
    linarith
  have hw_int : Integrable w (μ.restrict S) := by
    refine Integrable.of_bound hw_aesm.restrict 2 ?_
    filter_upwards [ae_restrict_of_ae hνunit] with x hx
    have hc := abs_real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hc
    rw [Real.norm_eq_abs, abs_le]
    dsimp [w]
    exact ⟨by linarith [(abs_le.mp hc).2], by linarith [(abs_le.mp hc).1]⟩
  have hfirst : (∫ x in S, ‖horizontal (ν x)‖ ^ 2 ∂μ) ≤
      2 * (projectedExcessMeasure μ ν).real A := by
    have hle : (∫ x in S, ‖horizontal (ν x)‖ ^ 2 ∂μ) ≤ ∫ x in S, 2 * w x ∂μ := by
      refine integral_mono_ae hνh_sq_int (hw_int.const_mul 2) ?_
      filter_upwards [ae_restrict_of_ae hνunit] with x hx
      exact norm_horizontal_sq_le_two_mul_one_sub_vertical hx
    rw [integral_const_mul] at hle
    have hexc_eq : (projectedExcessMeasure μ ν).real A = ∫ x in S, w x ∂μ := by
      unfold projectedExcessMeasure Measure.real
      rw [Measure.map_apply continuous_horizontal.measurable hA,
        withDensity_apply _ hS]
      have hlint : (∫⁻ x in S, ENNReal.ofReal (w x) ∂μ) =
          ENNReal.ofReal (∫ x in S, w x ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hw_int (ae_restrict_of_ae hw_nonneg)
      rw [hlint, ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hw_nonneg))]
    rwa [← hexc_eq] at hle
  have hsecond : (∫ _ in S, (1 : ℝ) ^ 2 ∂μ) =
      volume.real A + (projectedExcessMeasure μ ν).real A := by
    simp only [one_pow, integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one]
    have hmapA : (μ S).toReal = (projectedPerimeterMeasure μ).real A := by
      unfold projectedPerimeterMeasure Measure.real
      rw [Measure.map_apply continuous_horizontal.measurable hA]
    rw [hmapA]
    exact projectedPerimeterMeasure_real_apply_eq b hE hU hH hHH' μ hrep.measure_compl
      hrep.measure_open hν hνunit hrep.dist hbot htop hA hAU
  have hnonneg₁ : 0 ≤ 2 * (projectedExcessMeasure μ ν).real A := by positivity
  calc
    ∫ x in S, ‖horizontal (ν x)‖ ∂μ
        ≤ Real.sqrt (∫ x in S, ‖horizontal (ν x)‖ ^ 2 ∂μ) *
          Real.sqrt (∫ _ in S, (1 : ℝ) ^ 2 ∂μ) := hcs
    _ ≤ Real.sqrt (2 * (projectedExcessMeasure μ ν).real A) *
          Real.sqrt (volume.real A + (projectedExcessMeasure μ ν).real A) :=
      mul_le_mul (Real.sqrt_le_sqrt hfirst) (by rw [hsecond])
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * (projectedExcessMeasure μ ν).real A *
          (volume.real A + (projectedExcessMeasure μ ν).real A)) :=
      (Real.sqrt_mul hnonneg₁ _).symm

/-! ### 3. Divergence pairings of the signed height -/

/-- A unit horizontal test field supported in `S ⊆ U` pairs with the signed height to at most the
horizontal normal mass over the columns above `S`. -/
theorem abs_integral_columnSignedHeight_fieldDivergence_le_mass {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    (bm : OrthonormalBasis (Fin m) ℝ (Space m))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {S : Set (Space m)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    {G : Space m → Space m} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (hGs : tsupport G ⊆ S) (hGunit : ∀ y, ‖G y‖ ≤ 1) :
    |∫ y, columnSignedHeight E H y * fieldDivergence bm G y| ≤
      ∫ x in horizontal ⁻¹' S, ‖horizontal (ν x)‖ ∂μ := by
  have := hrep.isFiniteMeasure
  have hν := hrep.integrable
  rw [integral_columnSignedHeight_fieldDivergence_eq b bm hE hU hH hHH' μ hrep.measure_compl
    hrep.measure_open hν hrep.dist hbot htop hG hGc (hGs.trans hSU)]
  have hSm : MeasurableSet (horizontal ⁻¹' S : Set (Space (m + 1))) :=
    hS.preimage continuous_horizontal.measurable
  have hnorm_int : Integrable (fun x ↦ ‖horizontal (ν x)‖) μ :=
    (horizontalContinuousLinearMap.integrable_comp hν).norm
  rw [← integral_indicator hSm, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hnorm_int.indicator hSm) (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ horizontal ⁻¹' S
  · rw [indicator_of_mem hx]
    calc
      ‖inner ℝ (horizontal (ν x)) (G (horizontal x))‖
          ≤ ‖horizontal (ν x)‖ * ‖G (horizontal x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖horizontal (ν x)‖ * 1 := mul_le_mul_of_nonneg_left (hGunit _) (norm_nonneg _)
      _ = ‖horizontal (ν x)‖ := mul_one _
  · rw [indicator_of_notMem hx]
    have hG0 : G (horizontal x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦ hx (hGs hmem)
    rw [hG0, inner_zero_right, norm_zero]

/-! ### 4. Smoothed signed heights -/

theorem abs_columnSignedHeight_le {m : ℕ} (E : Set (Space (m + 1))) {H : ℝ} (hH : 0 ≤ H)
    (y : Space m) : |columnSignedHeight E H y| ≤ H :=
  abs_le.mpr (columnSignedHeight_mem_Icc E hH y)

theorem locallyIntegrable_columnSignedHeight {m : ℕ} {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {H : ℝ} (hH : 0 ≤ H) :
    LocallyIntegrable (columnSignedHeight E H) volume := by
  refine (continuous_const (y := H)).locallyIntegrable.mono
    (measurable_columnSignedHeight hE H).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hH]
  exact abs_columnSignedHeight_le E hH y

/-- Averaging preserves a uniform bound. -/
theorem abs_mollify_le {d : ℕ} {v : Space d → ℝ} {C : ℝ} (hC : ∀ x, |v x| ≤ C) (n : ℕ)
    (x : Space d) : |mollify v n x| ≤ C := by
  unfold mollify
  rw [convolution_def, ← Real.norm_eq_abs]
  have hK := (averagingBump d n).integrable_normed (μ := volume)
  refine (norm_integral_le_of_norm_le (hK.mul_const C) (Eventually.of_forall fun t ↦ ?_)).trans
    (le_of_eq ?_)
  · rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul,
      Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC _) ((averagingBump d n).nonneg_normed t)
  · rw [integral_mul_const, (averagingBump d n).integral_normed, one_mul]

/-- A uniform bound passes to averages over sets of finite measure. -/
theorem abs_setAverage_le_of_abs_le {d : ℕ} {v : Space d → ℝ} {B : Set (Space d)}
    (hB : volume B < ⊤) {C : ℝ} (hC : ∀ x, |v x| ≤ C) : |⨍ x in B, v x| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [setAverage_eq, smul_eq_mul, abs_mul]
  by_cases h0 : volume.real B = 0
  · simp [h0, hC0]
  · have hpos : 0 < volume.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
    have hint := norm_setIntegral_le_of_norm_le_const hB
      (fun x _ ↦ (show ‖v x‖ ≤ C by rw [Real.norm_eq_abs]; exact hC x))
    rw [Real.norm_eq_abs] at hint
    rw [abs_of_pos (inv_pos.mpr hpos)]
    calc
      (volume.real B)⁻¹ * |∫ x in B, v x| ≤ (volume.real B)⁻¹ * (C * volume.real B) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
      _ = C := by field_simp

/-- **Gradient mass of the smoothed heights.** If the averaging radius is at most `R - r`, the
gradient mass of the smoothed signed height on `B_r(y₀)` is at most the horizontal normal mass
over the columns above `B_R(y₀)`. -/
theorem integral_norm_gradient_mollify_columnSignedHeight_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {y₀ : Space m} {r R : ℝ} (hball : ball y₀ R ⊆ U) {n : ℕ}
    (hn : (averagingBump m n).rOut ≤ R - r) :
    ∫ y in ball y₀ r, ‖gradient (mollify (columnSignedHeight E H) n) y‖ ≤
      ∫ x in horizontal ⁻¹' ball y₀ R, ‖horizontal (ν x)‖ ∂μ := by
  set g := columnSignedHeight E H with hg_def
  let bm : OrthonormalBasis (Fin m) ℝ (Space m) := EuclideanSpace.basisFun (Fin m) ℝ
  have hgm : Measurable g := measurable_columnSignedHeight hE H
  have hgb : ∀ y, ‖g y‖ ≤ H := fun y ↦ by
    rw [Real.norm_eq_abs]
    exact abs_columnSignedHeight_le E hH.le y
  have hgli := locallyIntegrable_columnSignedHeight hE hH.le
  have hv : ContDiff ℝ 1 (mollify g n) :=
    (mollify_contDiff_of_locallyIntegrable hgli n).of_le (by simp)
  set I := ∫ x in horizontal ⁻¹' ball y₀ R, ‖horizontal (ν x)‖ ∂μ with hI_def
  have hI0 : 0 ≤ I := integral_nonneg fun x ↦ norm_nonneg _
  have htest : ∀ F : Space m → Space m, ContDiff ℝ 1 F → HasCompactSupport F →
      tsupport F ⊆ ball y₀ r → (∀ x, ‖F x‖ ≤ 1) →
      ‖∫ x, mollify g n x * fieldDivergence bm F x‖ ≤ I := by
    intro F hF hFc hFs hFu
    have hψ := fieldDivergence_continuous bm hF
    have hψc := hasCompactSupport_fieldDivergence bm hFc
    rw [integral_mollify_mul_eq_average_tests hgm hgb hψ hψc n]
    set K := (averagingBump m n).normed volume with hK_def
    have hJ : ∀ y, ‖K y * ∫ x, g x * fieldDivergence bm F (x + y)‖ ≤ K y * I := by
      intro y
      by_cases hy : K y = 0
      · rw [hy, zero_mul, norm_zero, zero_mul]
      · have hyb : ‖y‖ < (averagingBump m n).rOut := by
          have hsupp : y ∈ Function.support K := hy
          rw [hK_def, (averagingBump m n).support_normed_eq] at hsupp
          simpa using hsupp
        let Fy : Space m → Space m := fun x ↦ F (x + y)
        have hFy : ContDiff ℝ 1 Fy := hF.comp (contDiff_id.add contDiff_const)
        have hFys : tsupport Fy ⊆ ball y₀ R := by
          intro x hx
          have hxy : x + y ∈ tsupport F :=
            tsupport_comp_subset_preimage F (continuous_id.add continuous_const) hx
          have hxr := hFs hxy
          rw [mem_ball] at hxr ⊢
          have hd : dist x (x + y) = ‖y‖ := by
            rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
          calc
            dist x y₀ ≤ dist x (x + y) + dist (x + y) y₀ := dist_triangle _ _ _
            _ < R := by rw [hd]; linarith
        have hFyc : HasCompactSupport Fy :=
          (isCompact_closedBall y₀ R).of_isClosed_subset (isClosed_tsupport _)
            (hFys.trans ball_subset_closedBall)
        have hpair := abs_integral_columnSignedHeight_fieldDivergence_le_mass bm hE hU hH hHH'
          hrep hbot htop measurableSet_ball hball hFy hFyc hFys (fun x ↦ hFu _)
        have htr : ∫ x, g x * fieldDivergence bm F (x + y) =
            ∫ x, g x * fieldDivergence bm Fy x := by
          congr 1
          funext x
          rw [fieldDivergence_translate bm hF y x]
        rw [norm_mul, Real.norm_of_nonneg ((averagingBump m n).nonneg_normed y), htr,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hpair ((averagingBump m n).nonneg_normed y)
    have hKint : Integrable K volume := (averagingBump m n).integrable_normed
    calc
      ‖∫ y, K y * ∫ x, g x * fieldDivergence bm F (x + y)‖
          ≤ ∫ y, ‖K y * ∫ x, g x * fieldDivergence bm F (x + y)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y, K y * I :=
        integral_mono_of_nonneg (Eventually.of_forall fun y ↦ norm_nonneg _)
          (hKint.mul_const I) (Eventually.of_forall hJ)
      _ = I := by rw [integral_mul_const, (averagingBump m n).integral_normed, one_mul]
  have he := lintegral_gradient_le_of_divergence_bound bm hv isOpen_ball htest
  have hgc : Continuous (gradient (mollify g n)) :=
    (toDual ℝ (Space m)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hi : IntegrableOn (fun x ↦ ‖gradient (mollify g n) x‖) (ball y₀ r) :=
    (hgc.norm.continuousOn.integrableOn_compact (isCompact_closedBall y₀ r)).mono_set
      ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall
    (fun x ↦ norm_nonneg _))] at he
  exact (ENNReal.ofReal_le_ofReal_iff hI0).mp he

/-! ### 5. The BV Poincaré inequality for the signed height -/

/-- **BV Poincaré inequality for the column signed height.** For `r < R` with `B_R(y₀) ⊆ U`,
`∫_{B_r(y₀)} |g - g_{B_r(y₀)}| ≤ 2^(m+1) r ∫_{π⁻¹ B_R(y₀)} |ν_h| dμ`. -/
theorem integral_abs_columnSignedHeight_sub_average_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {y₀ : Space m} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hball : ball y₀ R ⊆ U) :
    ∫ y in ball y₀ r, |columnSignedHeight E H y - ⨍ z in ball y₀ r, columnSignedHeight E H z| ≤
      2 ^ (m + 1) * r * ∫ x in horizontal ⁻¹' ball y₀ R, ‖horizontal (ν x)‖ ∂μ := by
  set g := columnSignedHeight E H with hg_def
  set I := ∫ x in horizontal ⁻¹' ball y₀ R, ‖horizontal (ν x)‖ ∂μ with hI_def
  set B := ball y₀ r with hB_def
  have hgm : Measurable g := measurable_columnSignedHeight hE H
  have hgb : ∀ y, |g y| ≤ H := abs_columnSignedHeight_le E hH.le
  have hgli := locallyIntegrable_columnSignedHeight hE hH.le
  have hcont : ∀ n, Continuous (mollify g n) := fun n ↦
    (mollify_contDiff_of_locallyIntegrable hgli n).continuous
  have hev : ∀ᶠ n in atTop,
      ∫ y in B, |mollify g n y - ⨍ z in B, mollify g n z| ≤ 2 ^ (m + 1) * r * I := by
    have hsmall : ∀ᶠ n : ℕ in atTop, (averagingBump m n).rOut ≤ R - r :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iic_mem_nhds (sub_pos.mpr hrR))
    filter_upwards [hsmall] with n hn
    have hv : ContDiff ℝ 1 (mollify g n) :=
      (mollify_contDiff_of_locallyIntegrable hgli n).of_le (by simp)
    calc
      ∫ y in B, |mollify g n y - ⨍ z in B, mollify g n z|
          ≤ 2 ^ (m + 1) * r * ∫ y in B, ‖gradient (mollify g n) y‖ :=
        integral_abs_sub_ball_average_le hv y₀ hr
      _ ≤ 2 ^ (m + 1) * r * I :=
        mul_le_mul_of_nonneg_left (integral_norm_gradient_mollify_columnSignedHeight_le hE hU
          hH hHH' hrep hbot htop hball hn) (by positivity)
  have hfinB : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact measure_ball_lt_top⟩
  have hae : ∀ᵐ y ∂volume, Tendsto (fun n ↦ mollify g n y) atTop (𝓝 (g y)) :=
    mollify_tendsto_ae_of_locallyIntegrable hgli
  have hbdn : ∀ n y, |mollify g n y| ≤ H := fun n y ↦ abs_mollify_le hgb n y
  have havg : Tendsto (fun n ↦ ⨍ z in B, mollify g n z) atTop (𝓝 (⨍ z in B, g z)) := by
    simp only [setAverage_eq]
    refine Tendsto.const_smul ?_ _
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ H)
      (fun n ↦ (hcont n).aestronglyMeasurable) (integrable_const H)
      (fun n ↦ Eventually.of_forall fun y ↦ ?_) (ae_restrict_of_ae hae)
    rw [Real.norm_eq_abs]
    exact hbdn n y
  have hlim : Tendsto (fun n ↦ ∫ y in B, |mollify g n y - ⨍ z in B, mollify g n z|) atTop
      (𝓝 (∫ y in B, |g y - ⨍ z in B, g z|)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * H)
      (fun n ↦ ((hcont n).sub continuous_const).abs.aestronglyMeasurable) (integrable_const _)
      (fun n ↦ Eventually.of_forall fun y ↦ ?_) ?_
    · rw [Real.norm_eq_abs, abs_abs]
      have h1 := hbdn n y
      have h2 : |⨍ z in B, mollify g n z| ≤ H :=
        abs_setAverage_le_of_abs_le measure_ball_lt_top (hbdn n)
      calc
        |mollify g n y - ⨍ z in B, mollify g n z|
            ≤ |mollify g n y| + |⨍ z in B, mollify g n z| := abs_sub _ _
        _ ≤ 2 * H := by linarith
    · filter_upwards [ae_restrict_of_ae hae] with y hy
      exact ((hy.sub havg).abs)
  exact le_of_tendsto hlim hev

end SerrinEpigraph
