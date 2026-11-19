module

public import SerrinEpigraph.ExcessOscillation
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Lipschitz approximation of the signed height (`GR9`)

Normalized setting of `GR9`: the cylinder base contains `B_2`, the total excess is
`e = ε(B_2)`, and the threshold `κ = λ²` satisfies `e ≤ κ ≤ 1`. The good set is
`G = excessGoodSet ε B_{3/2} (1/4) κ`.

* `SlabTrappedRepresentation.abs_sub_le_of_mem_goodLebesgue`: the signed height is
  `C √κ`-Lipschitz on the good Lebesgue points (`GR9`, BV Poincaré on balls and on `B_{7/4}`).
* `SlabTrappedRepresentation.exists_lipschitz_approx` (`GR9`, McShane extension): there is a
  `C √κ`-Lipschitz function `f` with `|f| ≤ H` that coincides almost everywhere on `G` with the
  signed height.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported NNReal

namespace SerrinEpigraph

/-! ### 1. Lebesgue points along open balls -/

theorem ae_eq_ball_closedBall {d : ℕ} (y : Space d) {r : ℝ} (hr : 0 < r) :
    (ball y r : Set (Space d)) =ᵐ[volume] closedBall y r := by
  refine ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
    measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  rw [volume_closedBall_eq_ball y hr]

theorem setAverage_closedBall_eq_ball {d : ℕ} (v : Space d → ℝ) (y : Space d) {r : ℝ}
    (hr : 0 < r) : ⨍ z in closedBall y r, v z = ⨍ z in ball y r, v z := by
  rw [setAverage_eq, setAverage_eq, setIntegral_congr_set (ae_eq_ball_closedBall y hr).symm,
    Measure.real, Measure.real, volume_closedBall_eq_ball y hr]

/-- Almost every point is a Lebesgue point along shrinking open balls. -/
theorem ae_tendsto_average_ball {d : ℕ} {v : Space d → ℝ} (hv : LocallyIntegrable v volume) :
    ∀ᵐ y ∂volume, Tendsto (fun ρ ↦ ⨍ z in ball y ρ, v z) (𝓝[>] 0) (𝓝 (v y)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Space d))).ae_tendsto_average hv]
    with y hy
  have hc := hy.comp (Besicovitch.tendsto_filterAt volume y)
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact setAverage_closedBall_eq_ball v y hρ

/-- Good points have small excess density on open balls of radius below `s₀`. -/
theorem excess_ball_le_of_mem_excessGoodSet {m : ℕ} {ε : Measure (Space m)}
    {A : Set (Space m)} {s₀ κ : ℝ} {y : Space m} (hy : y ∈ excessGoodSet ε A s₀ κ)
    {s : ℝ} (hs : 0 < s) (hss₀ : s < s₀) :
    ε (ball y s) ≤ ENNReal.ofReal κ * volume (ball y s) := by
  calc
    ε (ball y s) ≤ ε (closedBall y s) := measure_mono ball_subset_closedBall
    _ ≤ ENNReal.ofReal κ * volume (closedBall y s) := hy.2 s hs hss₀
    _ = ENNReal.ofReal κ * volume (ball y s) := by rw [volume_closedBall_eq_ball y hs]

/-! ### 2. Comparison of averages -/

/-- Averages over a sub-ball deviate from the average over the ball by at most the normalized
mean oscillation. -/
theorem abs_setAverage_sub_setAverage_le {d : ℕ} {v : Space d → ℝ} {y z : Space d}
    {r ρ : ℝ} (hρ : 0 < ρ) (hsub : ball z ρ ⊆ ball y r) (hv : IntegrableOn v (ball y r)) :
    |(⨍ w in ball y r, v w) - ⨍ w in ball z ρ, v w| ≤
      (volume.real (ball z ρ))⁻¹ * ∫ w in ball y r, |v w - ⨍ u in ball y r, v u| :=
  abs_sub_setAverage_le_of_subset hsub (volume_real_ball_pos z hρ) measure_ball_ne_top hv _

/-! ### 3. The Lipschitz constant -/

/-- The dimensional constant of the far-point comparison in `GR9`. -/
def lipschitzApproxFarConst (m : ℕ) : ℝ :=
  2 * (2 ^ (3 * m + 2) * 2 / 16) +
    2 * ((volume.real (ball (0 : Space m) 1))⁻¹ * 16 ^ m * (2 ^ (m + 1) * (7 / 4) *
      Real.sqrt (2 * (2 ^ m * volume.real (ball (0 : Space m) 1) + 1))))

/-- The Lipschitz constant (divided by `√κ`) of the approximation in `GR9`. -/
def lipschitzApproxConst (m : ℕ) : ℝ :=
  max (2 ^ (3 * m + 4) * 2) (16 * lipschitzApproxFarConst m)

theorem lipschitzApproxFarConst_nonneg (m : ℕ) : 0 ≤ lipschitzApproxFarConst m := by
  unfold lipschitzApproxFarConst
  have : 0 ≤ (volume.real (ball (0 : Space m) 1))⁻¹ := inv_nonneg.mpr measureReal_nonneg
  positivity

theorem lipschitzApproxConst_nonneg (m : ℕ) : 0 ≤ lipschitzApproxConst m :=
  le_max_of_le_left (by positivity)

theorem sqrt_two_mul_one_add_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    Real.sqrt (2 * κ * (1 + κ)) ≤ 2 * Real.sqrt κ := by
  rw [show 2 * Real.sqrt κ = Real.sqrt (4 * κ) by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-! ### 4. Good Lebesgue points and the Lipschitz estimate -/

/-- The good set of the normalized `GR9` setting. -/
abbrev normalizedGoodSet {m : ℕ} (ε : Measure (Space m)) (κ : ℝ) : Set (Space m) :=
  excessGoodSet ε (ball 0 (3 / 2)) (1 / 4) κ

/-- Good points that are Lebesgue points of the signed height along open balls. -/
def goodLebesgueSet {m : ℕ} (E : Set (Space (m + 1))) (H : ℝ) (ε : Measure (Space m))
    (κ : ℝ) : Set (Space m) :=
  {y ∈ normalizedGoodSet ε κ | Tendsto (fun ρ ↦ ⨍ z in ball y ρ, columnSignedHeight E H z)
    (𝓝[>] 0) (𝓝 (columnSignedHeight E H y))}

theorem goodLebesgueSet_subset {m : ℕ} (E : Set (Space (m + 1))) (H : ℝ)
    (ε : Measure (Space m)) (κ : ℝ) : goodLebesgueSet E H ε κ ⊆ normalizedGoodSet ε κ :=
  fun _ hy ↦ hy.1

/-- Almost every good point is a good Lebesgue point. -/
theorem ae_mem_goodLebesgueSet {m : ℕ} {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {H : ℝ} (hH : 0 ≤ H) (ε : Measure (Space m)) (κ : ℝ) :
    ∀ᵐ y ∂volume, y ∈ normalizedGoodSet ε κ → y ∈ goodLebesgueSet E H ε κ := by
  filter_upwards [ae_tendsto_average_ball (locallyIntegrable_columnSignedHeight hE hH)] with y hy
    hyG
  exact ⟨hyG, hy⟩

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

theorem ball_subset_of_mem_normalizedGoodSet {p : Space m} {ε : Measure (Space m)} {κ : ℝ}
    (hp : p ∈ normalizedGoodSet ε κ) {r : ℝ} (hr : r ≤ 1 / 4) :
    ball p r ⊆ ball (0 : Space m) (7 / 4) := by
  intro w hw
  have hp0 : dist p 0 < 3 / 2 := hp.1
  rw [mem_ball] at hw ⊢
  calc
    dist w 0 ≤ dist w p + dist p 0 := dist_triangle _ _ _
    _ < 7 / 4 := by linarith

/-- Mean oscillation at good points. -/
theorem integral_abs_sub_average_le_of_mem_normalizedGoodSet
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} (hκ : 0 ≤ κ) {p : Space m} (hp : p ∈ normalizedGoodSet (projectedExcessMeasure μ ν) κ)
    {r : ℝ} (hr : 0 < r) (hr8 : r < 1 / 8) :
    ∫ z in ball p r, |columnSignedHeight E H z - ⨍ w in ball p r, columnSignedHeight E H w| ≤
      2 ^ (2 * m + 1) * Real.sqrt (2 * κ * (1 + κ)) * r * volume.real (ball p r) := by
  have hball : ball p (2 * r) ⊆ U :=
    ((ball_subset_of_mem_normalizedGoodSet hp (by linarith)).trans
      (ball_subset_ball (by norm_num))).trans hU2
  exact hS.integral_abs_sub_average_le_of_excess hr hκ hball
    (excess_ball_le_of_mem_excessGoodSet hp (by positivity) (by linarith))

/-- Distance from the value at a good Lebesgue point to small-ball averages. -/
theorem abs_sub_average_le_of_mem_goodLebesgueSet
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} (hκ : 0 ≤ κ) {p : Space m}
    (hp : p ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ)
    {r : ℝ} (hr : 0 < r) (hr8 : r < 1 / 8) :
    |columnSignedHeight E H p - ⨍ z in ball p r, columnSignedHeight E H z| ≤
      2 ^ (3 * m + 2) * Real.sqrt (2 * κ * (1 + κ)) * r := by
  have hball : ball p (2 * r) ⊆ U :=
    ((ball_subset_of_mem_normalizedGoodSet hp.1 (by linarith)).trans
      (ball_subset_ball (by norm_num))).trans hU2
  refine hS.abs_sub_average_le_of_excess hr hκ hball (fun s hs hsr ↦ ?_) hp.2
  exact excess_ball_le_of_mem_excessGoodSet hp.1 (by positivity) (by linarith)

/-- **Lipschitz estimate on good Lebesgue points** (`GR9`): if `e = ε(B_2) ≤ κ ≤ 1`, the signed
height is `C √κ`-Lipschitz on the good Lebesgue points, with `C = lipschitzApproxConst m`. -/
theorem abs_sub_le_of_mem_goodLebesgueSet
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (he : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ κ) {y z : Space m}
    (hy : y ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ)
    (hz : z ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ) :
    |columnSignedHeight E H y - columnSignedHeight E H z| ≤
      lipschitzApproxConst m * Real.sqrt κ * dist y z := by
  set g := columnSignedHeight E H with hg_def
  have := hS.isFiniteMeasure_excess
  set A := Real.sqrt (2 * κ * (1 + κ)) with hA_def
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA : A ≤ 2 * Real.sqrt κ := sqrt_two_mul_one_add_le hκ0 hκ1
  have hsk : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  have hint : ∀ (p : Space m) (r : ℝ), IntegrableOn g (ball p r) := fun p r ↦
    integrableOn_columnSignedHeight_ball hS.measurableSet hS.pos.le p r
  have hd0 : 0 ≤ dist y z := dist_nonneg
  rcases lt_or_ge (dist y z) (1 / 16) with hnear | hfar
  · rcases eq_or_lt_of_le hd0 with h0 | hρ
    · rw [← h0, dist_eq_zero.mp h0.symm]
      simp
    set ρ := dist y z with hρ_def
    have hT1 := hS.abs_sub_average_le_of_mem_goodLebesgueSet hU2 hκ0 hy
      (by positivity : 0 < 2 * ρ) (by linarith)
    have hT3 := hS.abs_sub_average_le_of_mem_goodLebesgueSet hU2 hκ0 hz hρ (by linarith)
    have hsub : ball z ρ ⊆ ball y (2 * ρ) := by
      intro w hw
      rw [mem_ball] at hw ⊢
      calc
        dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
        _ < 2 * ρ := by rw [dist_comm z y]; linarith
    have hT2 := abs_setAverage_sub_setAverage_le hρ hsub (hint y (2 * ρ))
    have hosc := hS.integral_abs_sub_average_le_of_mem_normalizedGoodSet hU2 hκ0 hy.1
      (by positivity : 0 < 2 * ρ) (by linarith)
    have hvol : volume.real (ball y (2 * ρ)) = 2 ^ m * volume.real (ball z ρ) :=
      volume_real_ball_mul y z hρ two_pos
    have hpos := volume_real_ball_pos z hρ
    have hT2' : |(⨍ w in ball y (2 * ρ), g w) - ⨍ w in ball z ρ, g w| ≤
        2 ^ m * (2 ^ (2 * m + 1) * A * (2 * ρ)) := by
      refine hT2.trans ?_
      calc
        (volume.real (ball z ρ))⁻¹ * ∫ w in ball y (2 * ρ), |g w - ⨍ u in ball y (2 * ρ), g u|
            ≤ (volume.real (ball z ρ))⁻¹ *
              (2 ^ (2 * m + 1) * A * (2 * ρ) * volume.real (ball y (2 * ρ))) :=
          mul_le_mul_of_nonneg_left hosc (inv_nonneg.mpr hpos.le)
        _ = 2 ^ m * (2 ^ (2 * m + 1) * A * (2 * ρ)) := by
          rw [hvol]
          field_simp
    have hsum : |g y - g z| ≤ 2 ^ (3 * m + 4) * A * ρ := by
      calc
        |g y - g z| ≤ |g y - ⨍ w in ball y (2 * ρ), g w| +
            |(⨍ w in ball y (2 * ρ), g w) - ⨍ w in ball z ρ, g w| +
            |(⨍ w in ball z ρ, g w) - g z| := by
          have h1 := abs_sub_le (g y) (⨍ w in ball y (2 * ρ), g w) (g z)
          have h2 := abs_sub_le (⨍ w in ball y (2 * ρ), g w) (⨍ w in ball z ρ, g w) (g z)
          linarith
        _ ≤ 2 ^ (3 * m + 2) * A * (2 * ρ) + 2 ^ m * (2 ^ (2 * m + 1) * A * (2 * ρ)) +
            2 ^ (3 * m + 2) * A * ρ := by
          rw [abs_sub_comm (⨍ w in ball z ρ, g w) (g z)]
          exact add_le_add (add_le_add hT1 hT2') hT3
        _ = 2 ^ (3 * m + 4) * A * ρ := by ring
    have hC : 2 ^ (3 * m + 4) * 2 ≤ lipschitzApproxConst m := le_max_left _ _
    calc
      |g y - g z| ≤ 2 ^ (3 * m + 4) * A * ρ := hsum
      _ ≤ 2 ^ (3 * m + 4) * (2 * Real.sqrt κ) * ρ := by gcongr
      _ = (2 ^ (3 * m + 4) * 2) * Real.sqrt κ * ρ := by ring
      _ ≤ lipschitzApproxConst m * Real.sqrt κ * ρ := by gcongr
  · have hr16 : (0 : ℝ) < 1 / 16 := by norm_num
    have hT1 := hS.abs_sub_average_le_of_mem_goodLebesgueSet hU2 hκ0 hy hr16 (by norm_num)
    have hT4 := hS.abs_sub_average_le_of_mem_goodLebesgueSet hU2 hκ0 hz hr16 (by norm_num)
    have hP := integral_abs_columnSignedHeight_sub_average_le hS.measurableSet hS.isOpen hS.pos
      hS.lt hS.rep hS.bot hS.top (y₀ := 0) (r := 7 / 4) (R := 2) (by norm_num) (by norm_num) hU2
    have hM := integral_norm_horizontal_normal_le hS.measurableSet hS.isOpen hS.pos hS.lt hS.rep
      hS.bot hS.top measurableSet_ball hU2
    set V₁ := volume.real (ball (0 : Space m) 1) with hV₁_def
    set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
    have he0 : 0 ≤ e := measureReal_nonneg
    have hV₁pos : 0 < V₁ := volume_real_ball_pos 0 one_pos
    have hV₂ : volume.real (ball (0 : Space m) 2) = 2 ^ m * V₁ := by
      have h := volume_real_ball_mul (0 : Space m) 0 (r := 1) (c := 2) one_pos two_pos
      rwa [mul_one] at h
    have hV16 : ∀ p : Space m, volume.real (ball p (1 / 16)) = (1 / 16) ^ m * V₁ := fun p ↦
      by rw [volume_real_ball_of_pos p (by norm_num)]
    have hsqrt : Real.sqrt (2 * e * (volume.real (ball (0 : Space m) 2) + e)) ≤
        Real.sqrt κ * Real.sqrt (2 * (2 ^ m * V₁ + 1)) := by
      rw [← Real.sqrt_mul hκ0]
      apply Real.sqrt_le_sqrt
      rw [hV₂]
      have hV : 0 ≤ 2 ^ m * V₁ := by positivity
      have h1 : e ≤ 1 := he.trans hκ1
      have h2 : e * (2 ^ m * V₁ + e) ≤ κ * (2 ^ m * V₁ + 1) :=
        mul_le_mul he (by linarith) (by positivity) hκ0
      nlinarith
    set Q := 2 ^ (m + 1) * (7 / 4 : ℝ) * Real.sqrt (2 * (2 ^ m * V₁ + 1)) with hQ_def
    have hosc0 : ∫ w in ball (0 : Space m) (7 / 4), |g w - ⨍ u in ball (0 : Space m) (7 / 4), g u|
        ≤ Q * Real.sqrt κ := by
      refine hP.trans ?_
      calc
        2 ^ (m + 1) * (7 / 4 : ℝ) *
            ∫ x in horizontal ⁻¹' ball (0 : Space m) 2, ‖horizontal (ν x)‖ ∂μ
            ≤ 2 ^ (m + 1) * (7 / 4 : ℝ) *
              (Real.sqrt κ * Real.sqrt (2 * (2 ^ m * V₁ + 1))) :=
          mul_le_mul_of_nonneg_left (hM.trans hsqrt) (by positivity)
        _ = Q * Real.sqrt κ := by rw [hQ_def]; ring
    have hT2 : ∀ p ∈ normalizedGoodSet (projectedExcessMeasure μ ν) κ,
        |(⨍ w in ball (0 : Space m) (7 / 4), g w) - ⨍ w in ball p (1 / 16), g w| ≤
          V₁⁻¹ * 16 ^ m * Q * Real.sqrt κ := by
      intro p hp
      have h := abs_setAverage_sub_setAverage_le hr16
        (ball_subset_of_mem_normalizedGoodSet hp (by norm_num)) (hint 0 (7 / 4))
      refine h.trans ?_
      rw [hV16 p]
      calc
        ((1 / 16 : ℝ) ^ m * V₁)⁻¹ *
            ∫ w in ball (0 : Space m) (7 / 4), |g w - ⨍ u in ball (0 : Space m) (7 / 4), g u|
            ≤ ((1 / 16 : ℝ) ^ m * V₁)⁻¹ * (Q * Real.sqrt κ) :=
          mul_le_mul_of_nonneg_left hosc0 (by positivity)
        _ = V₁⁻¹ * 16 ^ m * Q * Real.sqrt κ := by
          rw [mul_inv, one_div, inv_pow, inv_inv]
          ring
    have hfarb : |g y - g z| ≤ lipschitzApproxFarConst m * Real.sqrt κ := by
      set by' := ⨍ w in ball y (1 / 16), g w with hby
      set bz := ⨍ w in ball z (1 / 16), g w with hbz
      set c0 := ⨍ w in ball (0 : Space m) (7 / 4), g w with hc0
      have hy2 : |c0 - by'| ≤ V₁⁻¹ * 16 ^ m * Q * Real.sqrt κ := hT2 y hy.1
      have hz2 : |c0 - bz| ≤ V₁⁻¹ * 16 ^ m * Q * Real.sqrt κ := hT2 z hz.1
      have hT1' : |g y - by'| ≤ 2 ^ (3 * m + 2) * A * (1 / 16) := hT1
      have hT4' : |g z - bz| ≤ 2 ^ (3 * m + 2) * A * (1 / 16) := hT4
      have t1 := abs_sub_le (g y) by' (g z)
      have t2 := abs_sub_le by' c0 (g z)
      have t3 := abs_sub_le c0 bz (g z)
      have e1 := abs_sub_comm by' c0
      have e2 := abs_sub_comm bz (g z)
      have hA' : 2 ^ (3 * m + 2) * A * (1 / 16) ≤
          2 ^ (3 * m + 2) * (2 * Real.sqrt κ) * (1 / 16) := by gcongr
      calc
        |g y - g z| ≤ 2 ^ (3 * m + 2) * (2 * Real.sqrt κ) * (1 / 16) +
            V₁⁻¹ * 16 ^ m * Q * Real.sqrt κ + V₁⁻¹ * 16 ^ m * Q * Real.sqrt κ +
            2 ^ (3 * m + 2) * (2 * Real.sqrt κ) * (1 / 16) := by linarith
        _ = lipschitzApproxFarConst m * Real.sqrt κ := by
          rw [lipschitzApproxFarConst, hQ_def]
          ring
    have hC : 16 * lipschitzApproxFarConst m ≤ lipschitzApproxConst m := le_max_right _ _
    have hF0 := lipschitzApproxFarConst_nonneg m
    calc
      |g y - g z| ≤ lipschitzApproxFarConst m * Real.sqrt κ := hfarb
      _ ≤ lipschitzApproxFarConst m * Real.sqrt κ * (16 * dist y z) := by
        have : 1 ≤ 16 * dist y z := by linarith
        nlinarith [mul_nonneg hF0 hsk]
      _ = (16 * lipschitzApproxFarConst m) * Real.sqrt κ * dist y z := by ring
      _ ≤ lipschitzApproxConst m * Real.sqrt κ * dist y z := by gcongr

/-- **Lipschitz approximation** (`GR9`, McShane extension and truncation): if
`e = ε(B_2) ≤ κ ≤ 1`, there is a `C √κ`-Lipschitz function `f` with `|f| ≤ H` that equals the
signed height at every good Lebesgue point, hence almost everywhere on the good set. -/
theorem exists_lipschitz_approx
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (he : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ κ) :
    ∃ f : Space m → ℝ,
      LipschitzWith (Real.toNNReal (lipschitzApproxConst m * Real.sqrt κ)) f ∧
      (∀ y, |f y| ≤ H) ∧
      (∀ y ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ,
        f y = columnSignedHeight E H y) ∧
      ∀ᵐ y ∂volume, y ∈ normalizedGoodSet (projectedExcessMeasure μ ν) κ →
        f y = columnSignedHeight E H y := by
  set g := columnSignedHeight E H with hg_def
  set K : ℝ≥0 := Real.toNNReal (lipschitzApproxConst m * Real.sqrt κ) with hK_def
  have hK : (K : ℝ) = lipschitzApproxConst m * Real.sqrt κ :=
    Real.coe_toNNReal _ (mul_nonneg (lipschitzApproxConst_nonneg m) (Real.sqrt_nonneg _))
  have hon : LipschitzOnWith K g (goodLebesgueSet E H (projectedExcessMeasure μ ν) κ) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    rw [Real.dist_eq, hK]
    exact hS.abs_sub_le_of_mem_goodLebesgueSet hU2 hκ0 hκ1 he hy hz
  obtain ⟨f₀, hf₀, hf₀g⟩ := hon.extend_real
  refine ⟨fun y ↦ max (-H) (min H (f₀ y)), (hf₀.const_min H).const_max (-H), ?_, ?_, ?_⟩
  · intro y
    have hH := hS.pos.le
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · intro y hy
    have hgy := abs_le.mp (abs_columnSignedHeight_le E hS.pos.le y)
    show max (-H) (min H (f₀ y)) = g y
    rw [← hf₀g hy, min_eq_right hgy.2, max_eq_right hgy.1]
  · filter_upwards [ae_mem_goodLebesgueSet hS.measurableSet hS.pos.le
      (projectedExcessMeasure μ ν) κ] with y hy hyG
    have hyL := hy hyG
    have hgy := abs_le.mp (abs_columnSignedHeight_le E hS.pos.le y)
    show max (-H) (min H (f₀ y)) = g y
    rw [← hf₀g hyL, min_eq_right hgy.2, max_eq_right hgy.1]

end SlabTrappedRepresentation

end SerrinEpigraph
