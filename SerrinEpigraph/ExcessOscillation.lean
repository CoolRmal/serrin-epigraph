module

public import SerrinEpigraph.ExcessGoodSet

/-!
# Oscillation of the signed height under small excess density (`GR9`)

We bundle the standing hypotheses of `GR9–GR10` into `SlabTrappedRepresentation` and prove the
pointwise oscillation estimates for the signed height `g = columnSignedHeight E H`:

* `SlabTrappedRepresentation.integral_abs_sub_average_le_of_excess`: if the excess density on
  `B_{2r}(y)` is at most `κ`, then `∫_{B_r(y)} |g - g_{B_r(y)}| ≤ 2^(2m+1) √(2κ(1+κ)) r |B_r|`
  (BV Poincaré plus `GR9.1`).
* `SlabTrappedRepresentation.abs_sub_average_le_of_excess` (dyadic telescoping): at a Lebesgue
  point `y` of `g` at which the excess density of all balls `B_{2s}(y)`, `s ≤ r`, is at most `κ`,
  `|g(y) - g_{B_r(y)}| ≤ 2^(3m+2) √(2κ(1+κ)) r`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported

namespace SerrinEpigraph

/-! ### 1. Standing hypotheses -/

/-- Standing hypotheses of `GR9–GR10`: `E` is measurable, `(μ, ν)` represents the perimeter of
`E` in the cylinder `U × (-H', H')`, and the boundary is trapped in the slab `|t| ≤ H` (empty phase
below, full phase above). -/
structure SlabTrappedRepresentation {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (E : Set (Space (m + 1)))
    (U : Set (Space m)) (H H' : ℝ) (μ : Measure (Space (m + 1)))
    (ν : Space (m + 1) → Space (m + 1)) : Prop where
  measurableSet : MeasurableSet E
  isOpen : IsOpen U
  pos : 0 < H
  lt : H < H'
  rep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν
  bot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E
  top : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

theorem isFiniteMeasure (hS : SlabTrappedRepresentation b E U H H' μ ν) : IsFiniteMeasure μ :=
  hS.rep.isFiniteMeasure

theorem isFiniteMeasure_excess (hS : SlabTrappedRepresentation b E U H H' μ ν) :
    IsFiniteMeasure (projectedExcessMeasure μ ν) := by
  have := hS.isFiniteMeasure
  exact isFiniteMeasure_projectedExcessMeasure μ hS.rep.integrable

end SlabTrappedRepresentation

/-! ### 2. Ball volumes -/

theorem volume_ball_of_pos {d : ℕ} (y : Space d) {r : ℝ} (hr : 0 < r) :
    volume (ball y r) = ENNReal.ofReal (r ^ d) * volume (ball (0 : Space d) 1) := by
  rw [Measure.addHaar_ball_of_pos volume y hr, finrank_euclideanSpace_fin]

theorem volume_closedBall_eq_ball {d : ℕ} (y : Space d) {r : ℝ} (hr : 0 < r) :
    volume (closedBall y r) = volume (ball y r) := by
  rw [Measure.addHaar_closedBall volume y hr.le, volume_ball_of_pos y hr,
    finrank_euclideanSpace_fin]

theorem volume_real_ball_of_pos {d : ℕ} (y : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball y r) = r ^ d * volume.real (ball (0 : Space d) 1) := by
  rw [Measure.real, volume_ball_of_pos y hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem volume_real_ball_pos {d : ℕ} (y : Space d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball y r) :=
  ENNReal.toReal_pos (measure_ball_pos volume y hr).ne' measure_ball_ne_top

theorem volume_real_ball_mul {d : ℕ} (y z : Space d) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    volume.real (ball y (c * r)) = c ^ d * volume.real (ball z r) := by
  rw [volume_real_ball_of_pos y (mul_pos hc hr), volume_real_ball_of_pos z hr, mul_pow]
  ring

/-! ### 3. Elementary average estimates -/

/-- Comparing a constant with the average over a subset. -/
theorem abs_sub_setAverage_le_of_subset {d : ℕ} {v : Space d → ℝ} {B B' : Set (Space d)}
    (hB'B : B' ⊆ B) (hB' : 0 < volume.real B') (hBfin : volume B ≠ ⊤)
    (hv : IntegrableOn v B) (a : ℝ) :
    |a - ⨍ z in B', v z| ≤ (volume.real B')⁻¹ * ∫ z in B, |v z - a| := by
  have hB'fin : volume B' ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hB'B)
  have hvB' : IntegrableOn v B' := hv.mono_set hB'B
  have hc : IntegrableOn (fun _ : Space d ↦ a) B' := integrableOn_const hB'fin
  have heq : a - ⨍ z in B', v z = (volume.real B')⁻¹ * ∫ z in B', (a - v z) := by
    rw [integral_sub hc hvB', setIntegral_const, setAverage_eq, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hB')]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hB'.le)
  calc
    |∫ z in B', (a - v z)| ≤ ∫ z in B', |a - v z| := abs_integral_le_integral_abs
    _ = ∫ z in B', |v z - a| := by
      congr 1
      funext z
      exact abs_sub_comm _ _
    _ ≤ ∫ z in B, |v z - a| :=
      setIntegral_mono_set (hv.sub (integrableOn_const hBfin)).abs
        (Eventually.of_forall fun z ↦ abs_nonneg _) hB'B.eventuallyLE

theorem integrableOn_columnSignedHeight_ball {m : ℕ} {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {H : ℝ} (hH : 0 ≤ H) (y : Space m) (r : ℝ) :
    IntegrableOn (columnSignedHeight E H) (ball y r) :=
  ((locallyIntegrable_columnSignedHeight hE hH).integrableOn_isCompact
    (isCompact_closedBall y r)).mono_set ball_subset_closedBall

/-! ### 4. Oscillation estimates -/

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **Mean oscillation under small excess density.** If the excess density on `B_{2r}(y)` is at
most `κ`, then `∫_{B_r(y)} |g - g_{B_r(y)}| ≤ 2^(2m+1) √(2κ(1+κ)) r |B_r(y)|`. -/
theorem integral_abs_sub_average_le_of_excess
    (hS : SlabTrappedRepresentation b E U H H' μ ν) {y : Space m} {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 ≤ κ) (hball : ball y (2 * r) ⊆ U)
    (hexc : projectedExcessMeasure μ ν (ball y (2 * r)) ≤
      ENNReal.ofReal κ * volume (ball y (2 * r))) :
    ∫ z in ball y r, |columnSignedHeight E H z - ⨍ w in ball y r, columnSignedHeight E H w| ≤
      2 ^ (2 * m + 1) * Real.sqrt (2 * κ * (1 + κ)) * r * volume.real (ball y r) := by
  have := hS.isFiniteMeasure_excess
  have hP := integral_abs_columnSignedHeight_sub_average_le hS.measurableSet hS.isOpen hS.pos
    hS.lt hS.rep hS.bot hS.top hr (by linarith : r < 2 * r) hball
  have hM := integral_norm_horizontal_normal_le hS.measurableSet hS.isOpen hS.pos hS.lt hS.rep
    hS.bot hS.top measurableSet_ball hball
  set V := volume.real (ball y (2 * r)) with hV_def
  set e := (projectedExcessMeasure μ ν).real (ball y (2 * r)) with he_def
  have he : e ≤ κ * V := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top)
      hexc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] at h
  have he0 : 0 ≤ e := measureReal_nonneg
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hV : V = 2 ^ m * volume.real (ball y r) := volume_real_ball_mul y y hr two_pos
  have hsq : Real.sqrt (2 * e * (V + e)) ≤ V * Real.sqrt (2 * κ * (1 + κ)) := by
    have h1 : e * (V + e) ≤ (κ * V) * (V + κ * V) :=
      mul_le_mul he (by linarith) (by positivity) (by positivity)
    have h2 : 2 * e * (V + e) ≤ V ^ 2 * (2 * κ * (1 + κ)) := by nlinarith
    calc
      Real.sqrt (2 * e * (V + e)) ≤ Real.sqrt (V ^ 2 * (2 * κ * (1 + κ))) := Real.sqrt_le_sqrt h2
      _ = V * Real.sqrt (2 * κ * (1 + κ)) := by
        rw [Real.sqrt_mul (sq_nonneg V), Real.sqrt_sq hV0]
  calc
    _ ≤ 2 ^ (m + 1) * r * ∫ x in horizontal ⁻¹' ball y (2 * r), ‖horizontal (ν x)‖ ∂μ := hP
    _ ≤ 2 ^ (m + 1) * r * Real.sqrt (2 * e * (V + e)) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ 2 ^ (m + 1) * r * (V * Real.sqrt (2 * κ * (1 + κ))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 ^ (2 * m + 1) * Real.sqrt (2 * κ * (1 + κ)) * r * volume.real (ball y r) := by
      rw [hV, show 2 * m + 1 = (m + 1) + m by ring, pow_add]
      ring

/-- **Telescoping at Lebesgue points.** If `y` is a Lebesgue point of the signed height (averages
over shrinking balls converge to `g(y)`) and all balls `B_{2s}(y)`, `0 < s ≤ r`, have excess
density at most `κ`, then `|g(y) - g_{B_r(y)}| ≤ 2^(3m+2) √(2κ(1+κ)) r`. -/
theorem abs_sub_average_le_of_excess
    (hS : SlabTrappedRepresentation b E U H H' μ ν) {y : Space m} {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 ≤ κ) (hball : ball y (2 * r) ⊆ U)
    (hexc : ∀ s, 0 < s → s ≤ r → projectedExcessMeasure μ ν (ball y (2 * s)) ≤
      ENNReal.ofReal κ * volume (ball y (2 * s)))
    (hleb : Tendsto (fun ρ ↦ ⨍ z in ball y ρ, columnSignedHeight E H z) (𝓝[>] 0)
      (𝓝 (columnSignedHeight E H y))) :
    |columnSignedHeight E H y - ⨍ z in ball y r, columnSignedHeight E H z| ≤
      2 ^ (3 * m + 2) * Real.sqrt (2 * κ * (1 + κ)) * r := by
  set g := columnSignedHeight E H with hg_def
  set A := 2 ^ (2 * m + 1) * Real.sqrt (2 * κ * (1 + κ)) with hA_def
  have hA0 : 0 ≤ A := by positivity
  set ρ : ℕ → ℝ := fun k ↦ r * (1 / 2) ^ k with hρ_def
  set a : ℕ → ℝ := fun k ↦ ⨍ z in ball y (ρ k), g z with ha_def
  have hρpos : ∀ k, 0 < ρ k := fun k ↦ by positivity
  have hρle : ∀ k, ρ k ≤ r := fun k ↦ by
    have h1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : r * (1 / 2) ^ k ≤ r * 1 := mul_le_mul_of_nonneg_left h1 hr.le
    simpa [hρ_def] using this
  have hρsucc : ∀ k, ρ k = 2 * ρ (k + 1) := fun k ↦ by
    simp only [hρ_def, pow_succ]
    ring
  have hstep : ∀ k, |a k - a (k + 1)| ≤ 2 ^ m * A * ρ k := by
    intro k
    have hsub : ball y (ρ (k + 1)) ⊆ ball y (ρ k) :=
      ball_subset_ball (by rw [hρsucc k]; linarith [hρpos (k + 1)])
    have hint := integrableOn_columnSignedHeight_ball hS.measurableSet hS.pos.le y (ρ k)
    have h1 := abs_sub_setAverage_le_of_subset hsub (volume_real_ball_pos y (hρpos (k + 1)))
      measure_ball_ne_top hint (a k)
    have hballk : ball y (2 * ρ k) ⊆ U :=
      (ball_subset_ball (by linarith [hρle k])).trans hball
    have h2 := hS.integral_abs_sub_average_le_of_excess (hρpos k) hκ hballk
      (hexc (ρ k) (hρpos k) (hρle k))
    have hvol : volume.real (ball y (ρ k)) = 2 ^ m * volume.real (ball y (ρ (k + 1))) := by
      rw [hρsucc k]
      exact volume_real_ball_mul y y (hρpos (k + 1)) two_pos
    have hpos := volume_real_ball_pos y (hρpos (k + 1))
    calc
      |a k - a (k + 1)| ≤ (volume.real (ball y (ρ (k + 1))))⁻¹ *
          ∫ z in ball y (ρ k), |g z - a k| := h1
      _ ≤ (volume.real (ball y (ρ (k + 1))))⁻¹ * (A * ρ k * volume.real (ball y (ρ k))) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hpos.le)
      _ = 2 ^ m * A * ρ k := by
        rw [hvol]
        field_simp
  have hsum : ∀ n, |a 0 - a n| ≤ 2 ^ m * A * r * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        |a 0 - a (n + 1)| ≤ |a 0 - a n| + |a n - a (n + 1)| := abs_sub_le _ _ _
        _ ≤ 2 ^ m * A * r * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k + 2 ^ m * A * ρ n :=
          add_le_add ih (hstep n)
        _ = 2 ^ m * A * r * (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k + (1 / 2) ^ n) := by
          simp only [hρ_def]
          ring
  have hbound : ∀ n, |a 0 - a n| ≤ 2 ^ m * A * r * 2 := fun n ↦
    (hsum n).trans (mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by positivity))
  have hρlim : Tendsto ρ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall hρpos)
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
    simpa [hρ_def] using this
  have hlim : Tendsto a atTop (𝓝 (g y)) := hleb.comp hρlim
  have hfin := le_of_tendsto ((tendsto_const_nhds (x := a 0)).sub hlim).abs
    (Eventually.of_forall hbound)
  have ha0 : a 0 = ⨍ z in ball y r, g z := by simp [ha_def, hρ_def]
  rw [ha0, abs_sub_comm] at hfin
  calc
    |g y - ⨍ z in ball y r, g z| ≤ 2 ^ m * A * r * 2 := hfin
    _ = 2 ^ (3 * m + 2) * Real.sqrt (2 * κ * (1 + κ)) * r := by
      rw [hA_def, show 3 * m + 2 = m + (2 * m + 1) + 1 by ring, pow_add, pow_add]
      ring

end SlabTrappedRepresentation

end SerrinEpigraph
