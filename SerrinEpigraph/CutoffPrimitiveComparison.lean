module

public import SerrinEpigraph.PhasePrimitiveStep

/-!
# Comparison of the cutoff column integral of `Φ(v)` with the height (Step D)
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ## One-dimensional facts about the cutoff -/

/-- A cutoff `ψ` with values in `[0, 1]` vanishing for `|t| ≥ 1/2` times a function bounded by `M`
is dominated by `M` times the indicator of `(-1/2, 1/2)`. -/
private theorem cutoffCol_norm_mul_le {ψ : ℝ → ℝ} (hψ01 : ∀ t, ψ t ∈ Icc (0 : ℝ) 1)
    (hψ0 : ∀ t, 1 / 2 ≤ |t| → ψ t = 0) {X : ℝ → ℝ} {M : ℝ} (hX : ∀ t, |X t| ≤ M) (t : ℝ) :
    ‖ψ t * X t‖ ≤ (Ioo (-(1 / 2)) (1 / 2 : ℝ)).indicator (fun _ ↦ M) t := by
  by_cases ht : t ∈ Ioo (-(1 / 2)) (1 / 2 : ℝ)
  · rw [indicator_of_mem ht, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ01 t).1]
    calc ψ t * |X t| ≤ 1 * |X t| := mul_le_mul_of_nonneg_right (hψ01 t).2 (abs_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hX t
  · rw [indicator_of_notMem ht, hψ0 t (not_lt.mp fun h' ↦ ht (abs_lt.mp h')), zero_mul,
      norm_zero]

private theorem cutoffCol_integrable_indicator (M : ℝ) :
    Integrable ((Ioo (-(1 / 2)) (1 / 2 : ℝ)).indicator (fun _ ↦ M)) :=
  (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const measure_Ioo_lt_top.ne)

private theorem cutoffCol_integrable_mul {ψ : ℝ → ℝ} (hψm : Measurable ψ)
    (hψ01 : ∀ t, ψ t ∈ Icc (0 : ℝ) 1) (hψ0 : ∀ t, 1 / 2 ≤ |t| → ψ t = 0) {X : ℝ → ℝ}
    (hXm : AEStronglyMeasurable X) {M : ℝ} (hX : ∀ t, |X t| ≤ M) :
    Integrable (fun t ↦ ψ t * X t) :=
  (cutoffCol_integrable_indicator M).mono' (hψm.aestronglyMeasurable.mul hXm)
    (Eventually.of_forall (cutoffCol_norm_mul_le hψ01 hψ0 hX))

private theorem cutoffCol_abs_integral_mul_le {ψ : ℝ → ℝ}
    (hψ01 : ∀ t, ψ t ∈ Icc (0 : ℝ) 1) (hψ0 : ∀ t, 1 / 2 ≤ |t| → ψ t = 0) {X : ℝ → ℝ}
    {M : ℝ} (hX : ∀ t, |X t| ≤ M) :
    |∫ t, ψ t * X t| ≤ M := by
  have h := norm_integral_le_of_norm_le (cutoffCol_integrable_indicator M)
    (Eventually.of_forall (cutoffCol_norm_mul_le hψ01 hψ0 hX))
  rw [integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo_of_le (by norm_num),
    smul_eq_mul, Real.norm_eq_abs] at h
  linarith

/-- Since `ψ = 1` on `[-1/4, 1/4]`, moving the lower limit `a ∈ [-1/4, 1/4]` changes the
integral of `ψ` over `(a, ∞)` linearly. -/
private theorem cutoffCol_setIntegral_Ioi {ψ : ℝ → ℝ} (hψi : Integrable ψ)
    (hψ1 : ∀ t, |t| ≤ 1 / 4 → ψ t = 1) {a : ℝ} (ha : |a| ≤ 1 / 4) :
    ∫ t in Ioi a, ψ t = (1 / 4 - a) + ∫ t in Ioi (1 / 4 : ℝ), ψ t := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  have hI : ∫ t in Ioc a (1 / 4), ψ t = 1 / 4 - a := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ (1 : ℝ))
      fun t ht ↦ hψ1 t (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩), setIntegral_const,
      Real.volume_real_Ioc_of_le ha2, smul_eq_mul, mul_one]
  rw [← Ioc_union_Ioi_eq_Ioi ha2, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    hψi.integrableOn hψi.integrableOn, hI]

/-! ## The column comparison for an abstract profile -/

/-- The cylinder `B_{3/4} × (-1, 1)` lies in the closed ball of radius `7/4`. -/
private theorem cutoffCol_cylinder_subset_closedBall :
    horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
        (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1 ⊆
      closedBall (0 : Space (m + 1)) (3 / 4 + 1) := by
  rintro z ⟨hzB, hzt⟩
  have h1 : ‖horizontal z‖ < 3 / 4 := mem_ball_zero_iff.mp hzB
  have h2 : |z (Fin.last m)| < 1 := abs_lt.mpr hzt
  rw [mem_closedBall, dist_zero_right]
  linarith [norm_le_norm_horizontal_add_abs_last z]

/-- **Column comparison.** `P` plays the role of `Φ(v)`, `w` bounds the distance of `P` from the
step `σ · 1(s₀ < v)`. On good columns the column hypothesis turns the step into `σ · 1(hh < t)`,
whose cutoff integral is `σ (C_ψ - hh)`; bad columns cost at most `σ (2 + τ)`. -/
private theorem cutoffCol_abs_integral_add_height_le
    {P w v : Space (m + 1) → ℝ} {σ s₀ : ℝ} (hPm : Measurable P) (hP : ∀ z, P z ∈ Icc 0 σ)
    (hw : ∀ z, |P z - (if s₀ < v z then σ else 0)| ≤ w z)
    (hwi : IntegrableOn w (horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
      (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1))
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) (hψ01 : ∀ t, ψ t ∈ Icc (0 : ℝ) 1)
    (hψ1 : ∀ t, |t| ≤ 1 / 4 → ψ t = 1) (hψ0 : ∀ t, 1 / 2 ≤ |t| → ψ t = 0)
    {D : Set (Space m)} (hDm : MeasurableSet D) {hh : Space m → ℝ} (hhm : Measurable hh)
    {τ : ℝ} (hhτ : ∀ y, |hh y| ≤ τ)
    (hgood : ∀ y ∈ D ∩ ball (0 : Space m) (3 / 4), |hh y| ≤ 1 / 4 ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1, (s₀ < v (point y t) ↔ hh y < t))
    {gg : Space m → ℝ} (hggm : Measurable gg) {G : ℝ} (hgG : ∀ y, |gg y| ≤ G)
    (hgg0 : ∀ y ∉ ball (0 : Space m) (3 / 4), gg y = 0) (hggint : (∫ y, gg y) = 0) :
    |(∫ z, ψ (z (Fin.last m)) * gg (horizontal z) * P z) + σ * ∫ y, gg y * hh y| ≤
      G * ((∫ z in horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
          (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1, w z) +
        σ * (2 + τ) * volume.real (ball (0 : Space m) (3 / 4) \ D)) := by
  set B : Set (Space m) := ball (0 : Space m) (3 / 4)
  set S : Set (Space (m + 1)) :=
    horizontal ⁻¹' B ∩ (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1 with hSdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hcl : Continuous (fun z : Space (m + 1) ↦ (z (Fin.last m) : ℝ)) := continuous_last
  have hSm : MeasurableSet S := (hBm.preimage continuous_horizontal.measurable).inter
    (measurableSet_Ioo.preimage hcl.measurable)
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hSfin : volume S ≠ ⊤ :=
    ((measure_mono cutoffCol_cylinder_subset_closedBall).trans_lt measure_closedBall_lt_top).ne
  have hσ : 0 ≤ σ := (hP 0).1.trans (hP 0).2
  have hG : 0 ≤ G := (abs_nonneg _).trans (hgG 0)
  have hw0 : ∀ z, 0 ≤ w z := fun z ↦ (abs_nonneg _).trans (hw z)
  have hPb : ∀ z, |P z| ≤ σ := fun z ↦ by rw [abs_of_nonneg (hP z).1]; exact (hP z).2
  -- the cutoff
  have hψi : Integrable ψ := by
    have h1 := cutoffCol_integrable_mul hψm hψ01 hψ0 (X := fun _ ↦ (1 : ℝ))
      aestronglyMeasurable_const (M := 1) (fun _ ↦ by norm_num)
    simpa only [mul_one] using h1
  obtain ⟨Cψ, hCψ⟩ : ∃ Cψ : ℝ, Cψ = ∫ t in Ioi (0 : ℝ), ψ t := ⟨_, rfl⟩
  have hIoi : ∀ a : ℝ, |a| ≤ 1 / 4 → ∫ t in Ioi a, ψ t = Cψ - a := by
    intro a ha
    have h1 := cutoffCol_setIntegral_Ioi hψi hψ1 ha
    have h0 := cutoffCol_setIntegral_Ioi hψi hψ1 (a := 0) (by norm_num)
    linarith
  have hCψ0 : 0 ≤ Cψ := hCψ ▸ setIntegral_nonneg measurableSet_Ioi fun t _ ↦ (hψ01 t).1
  have hCψ1 : Cψ ≤ 1 := by
    have h1 : Cψ ≤ ∫ t, ψ t :=
      hCψ ▸ setIntegral_le_integral hψi (Eventually.of_forall fun t ↦ (hψ01 t).1)
    have h2 := cutoffCol_abs_integral_mul_le hψ01 hψ0 (X := fun _ ↦ (1 : ℝ)) (M := 1)
      (fun _ ↦ by norm_num)
    simp only [mul_one] at h2
    linarith [le_abs_self (∫ t, ψ t)]
  -- the column integrals
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Space m → ℝ, ∀ y, Gc y = ∫ t, ψ t * P (point y t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hPcol : ∀ y, Integrable (fun t ↦ ψ t * P (point y t)) := fun y ↦
    cutoffCol_integrable_mul hψm hψ01 hψ0
      (hPm.comp (continuous_point y).measurable).aestronglyMeasurable (fun t ↦ hPb _)
  -- Fubini for the main term
  have hFm : Measurable (fun z : Space (m + 1) ↦ ψ (z (Fin.last m)) * gg (horizontal z) * P z) :=
    ((hψm.comp hcl.measurable).mul (hggm.comp continuous_horizontal.measurable)).mul hPm
  have hFi : Integrable (fun z : Space (m + 1) ↦ ψ (z (Fin.last m)) * gg (horizontal z) * P z) := by
    refine ((integrable_indicator_iff hSm).mpr (integrableOn_const (C := G * σ) hSfin)).mono'
      hFm.aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hψ01 _).1,
        abs_of_nonneg (hP z).1]
      calc ψ (z (Fin.last m)) * |gg (horizontal z)| * P z ≤ 1 * G * σ :=
            mul_le_mul (mul_le_mul (hψ01 _).2 (hgG _) (abs_nonneg _) zero_le_one) (hP z).2
              (hP z).1 (mul_nonneg zero_le_one hG)
        _ = G * σ := by ring
    · rw [indicator_of_notMem hz, norm_le_zero_iff]
      rw [hSdef, mem_inter_iff, mem_preimage, mem_preimage, not_and_or] at hz
      rcases hz with hz | hz
      · rw [hgg0 _ hz, mul_zero, zero_mul]
      · have h1 : 1 / 2 ≤ |z (Fin.last m)| := by
          by_contra hlt
          exact hz (abs_lt.mp (by linarith [not_le.mp hlt]))
        rw [hψ0 _ h1, zero_mul, zero_mul]
  have hmp := measurePreserving_point m
  have hcolF : ∀ y, (∫ t, ψ (point y t (Fin.last m)) * gg (horizontal (point y t)) *
      P (point y t)) = gg y * Gc y := by
    intro y
    rw [hGc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only [last_point, horizontal_point]
    ring
  have hint1 : Integrable (fun y ↦ gg y * Gc y) :=
    (hmp.integrable_comp_of_integrable hFi).integral_prod_left.congr
      (Eventually.of_forall fun y ↦ hcolF y)
  -- integrability of the weights
  have hBi : ∀ M : ℝ, Integrable (B.indicator (fun _ ↦ M)) := fun M ↦
    (integrable_indicator_iff hBm).mpr (integrableOn_const hBfin)
  have hggi : Integrable gg := by
    refine (hBi G).mono' hggm.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, Real.norm_eq_abs]
      exact hgG y
    · rw [indicator_of_notMem hy, hgg0 y hy, norm_zero]
  have hgghi : Integrable (fun y ↦ gg y * hh y) := by
    refine (hBi (G * τ)).mono' (hggm.mul hhm).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgG y) (hhτ y) (abs_nonneg _) hG
    · rw [indicator_of_notMem hy, hgg0 y hy, zero_mul, norm_zero]
  -- the expression as one horizontal integral
  have hkey : (∫ z, ψ (z (Fin.last m)) * gg (horizontal z) * P z) + σ * ∫ y, gg y * hh y =
      ∫ y, gg y * (Gc y - σ * (Cψ - hh y)) := by
    have h1 : (fun y ↦ gg y * (Gc y - σ * (Cψ - hh y))) =
        fun y ↦ gg y * Gc y + σ * (gg y * hh y) - σ * Cψ * gg y := by
      funext y
      ring
    have h2 : Integrable (fun y ↦ gg y * Gc y + σ * (gg y * hh y)) :=
      hint1.add (hgghi.const_mul σ)
    rw [h1, integral_sub h2 (hggi.const_mul (σ * Cψ)),
      integral_add hint1 (hgghi.const_mul σ), integral_const_mul, integral_const_mul, hggint,
      mul_zero, sub_zero, integral_space_eq_integral_horizontal_vertical hFi]
    congr 1
    exact integral_congr_ae (Eventually.of_forall hcolF)
  -- Fubini for the energy bound
  obtain ⟨E, hE⟩ : ∃ E : Space m → ℝ, ∀ y, E y = ∫ t in Ioo (-1 : ℝ) 1, w (point y t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hE0 : ∀ y, 0 ≤ E y := fun y ↦ by
    rw [hE]
    exact setIntegral_nonneg measurableSet_Ioo fun t _ ↦ hw0 _
  have hHi : Integrable (S.indicator w) := hwi.integrable_indicator hSm
  have hH'i : Integrable (fun p : Space m × ℝ ↦ S.indicator w (point p.1 p.2))
      ((volume : Measure (Space m)).prod volume) := hmp.integrable_comp_of_integrable hHi
  have hcolH : ∀ y ∈ B, (fun t ↦ S.indicator w (point y t)) =
      (Ioo (-1 : ℝ) 1).indicator (fun t ↦ w (point y t)) := by
    intro y hy
    funext t
    by_cases ht : t ∈ Ioo (-1 : ℝ) 1
    · have hmem : point y t ∈ S := ⟨by simpa [horizontal_point] using hy,
        by simpa [last_point] using ht⟩
      rw [indicator_of_mem hmem, indicator_of_mem ht]
    · have hmem : point y t ∉ S := fun hS ↦ ht (by simpa [last_point] using hS.2)
      rw [indicator_of_notMem hmem, indicator_of_notMem ht]
  have hslice : ∀ y, (∫ t, S.indicator w (point y t)) = B.indicator E y := by
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, hE, ← integral_indicator measurableSet_Ioo, hcolH y hy]
    · rw [indicator_of_notMem hy]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
      have hmem : point y t ∉ S := fun hS ↦ hy (by simpa [horizontal_point] using hS.1)
      simp only [indicator_of_notMem hmem, Pi.zero_apply]
  have hEi : Integrable (B.indicator E) :=
    hH'i.integral_prod_left.congr (Eventually.of_forall hslice)
  have hRHS : (∫ z in S, w z) = ∫ y, B.indicator E y := by
    rw [← integral_indicator hSm, integral_space_eq_integral_horizontal_vertical hHi]
    exact integral_congr_ae (Eventually.of_forall hslice)
  -- the good columns
  have hgoodcol : ∀ y ∈ D ∩ B, IntegrableOn (fun t ↦ w (point y t)) (Ioo (-1 : ℝ) 1) →
      |Gc y - σ * (Cψ - hh y)| ≤ E y := by
    intro y hy hyi
    obtain ⟨ha, hcol⟩ := hgood y hy
    have hstep : σ * (Cψ - hh y) = ∫ t, σ * (Ioi (hh y)).indicator ψ t := by
      rw [integral_const_mul, integral_indicator measurableSet_Ioi, hIoi (hh y) ha]
    have heq : Gc y - σ * (Cψ - hh y) = ∫ t in Ioo (-1 : ℝ) 1,
        ψ t * (P (point y t) - if s₀ < v (point y t) then σ else 0) := by
      rw [hstep, hGc, ← integral_sub (hPcol y) ((hψi.indicator measurableSet_Ioi).const_mul σ),
        ← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
      dsimp only
      by_cases ht : t ∈ Ioo (-1 : ℝ) 1
      · rw [indicator_of_mem ht]
        by_cases hlt : hh y < t
        · rw [ite_eq_left ((hcol t ht).mpr hlt),
            indicator_of_mem (show t ∈ Ioi (hh y) from hlt)]
          ring
        · rw [ite_eq_right fun h' ↦ hlt ((hcol t ht).mp h'),
            indicator_of_notMem (show t ∉ Ioi (hh y) from hlt)]
          ring
      · have h1 : 1 / 2 ≤ |t| := by
          by_contra hlt
          exact ht (abs_lt.mp (by linarith [not_le.mp hlt]))
        have hψt : ψ t = 0 := hψ0 t h1
        rw [indicator_of_notMem ht]
        simp [indicator_apply, hψt]
    rw [heq, hE, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hyi (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ01 t).1]
    calc ψ t * |P (point y t) - if s₀ < v (point y t) then σ else 0|
        ≤ 1 * |P (point y t) - if s₀ < v (point y t) then σ else 0| :=
          mul_le_mul_of_nonneg_right (hψ01 t).2 (abs_nonneg _)
      _ ≤ w (point y t) := by rw [one_mul]; exact hw _
  -- the bad columns
  have hbadcol : ∀ y, |Gc y - σ * (Cψ - hh y)| ≤ σ * (2 + τ) := by
    intro y
    have h1 : |Gc y| ≤ σ := by
      rw [hGc]
      exact cutoffCol_abs_integral_mul_le hψ01 hψ0 fun t ↦ hPb _
    have h2 : |Cψ - hh y| ≤ 1 + τ := by
      have := abs_le.mp (hhτ y)
      rw [abs_le]
      constructor <;> linarith
    calc |Gc y - σ * (Cψ - hh y)| ≤ |Gc y| + |σ * (Cψ - hh y)| := abs_sub _ _
      _ = |Gc y| + σ * |Cψ - hh y| := by rw [abs_mul, abs_of_nonneg hσ]
      _ ≤ σ + σ * (1 + τ) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hσ)
      _ = σ * (2 + τ) := by ring
  -- the pointwise bound
  have hDB : MeasurableSet (B \ D) := hBm.diff hDm
  have hconst : Integrable ((B \ D).indicator (fun _ ↦ σ * (2 + τ))) :=
    (integrable_indicator_iff hDB).mpr
      (integrableOn_const ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne)
  have hae : ∀ᵐ y, |gg y * (Gc y - σ * (Cψ - hh y))| ≤
      G * (B.indicator E y + (B \ D).indicator (fun _ ↦ σ * (2 + τ)) y) := by
    filter_upwards [hH'i.prod_right_ae] with y hy
    by_cases hyB : y ∈ B
    · rw [abs_mul, indicator_of_mem hyB]
      by_cases hyD : y ∈ D
      · have hyi : IntegrableOn (fun t ↦ w (point y t)) (Ioo (-1 : ℝ) 1) := by
          rw [← integrable_indicator_iff measurableSet_Ioo, ← hcolH y hyB]
          exact hy
        rw [indicator_of_notMem (fun h' : y ∈ B \ D ↦ h'.2 hyD), add_zero]
        exact mul_le_mul (hgG y) (hgoodcol y ⟨hyD, hyB⟩ hyi) (abs_nonneg _) hG
      · rw [indicator_of_mem (show y ∈ B \ D from ⟨hyB, hyD⟩)]
        calc |gg y| * |Gc y - σ * (Cψ - hh y)| ≤ G * (σ * (2 + τ)) :=
              mul_le_mul (hgG y) (hbadcol y) (abs_nonneg _) hG
          _ ≤ G * (E y + σ * (2 + τ)) := by
              gcongr
              linarith [hE0 y]
    · rw [hgg0 y hyB, zero_mul, abs_zero, indicator_of_notMem hyB,
        indicator_of_notMem (fun h' : y ∈ B \ D ↦ hyB h'.1), add_zero, mul_zero]
  calc |(∫ z, ψ (z (Fin.last m)) * gg (horizontal z) * P z) + σ * ∫ y, gg y * hh y|
      = |∫ y, gg y * (Gc y - σ * (Cψ - hh y))| := by rw [hkey]
    _ ≤ ∫ y, |gg y * (Gc y - σ * (Cψ - hh y))| := abs_integral_le_integral_abs
    _ ≤ ∫ y, G * (B.indicator E y + (B \ D).indicator (fun _ ↦ σ * (2 + τ)) y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y ↦ abs_nonneg _)
          ((hEi.add hconst).const_mul G) hae
    _ = G * ((∫ z in S, w z) + σ * (2 + τ) * volume.real (B \ D)) := by
        rw [integral_const_mul, integral_add hEi hconst, ← hRHS,
          integral_indicator_const _ hDB, smul_eq_mul]
        ring

/-! ## Step D -/

/-- **Step D.** On good columns the cutoff column integral of `Φ(v)` is `σ (C_ψ - hh y)` up to
`C R⁻¹` times the column energy (one-dimensional step comparison); bad columns cost at most
`σ (2 + τ)` each. Since `∫ gg = 0`, the constant `σ C_ψ` drops out. -/
theorem RigidityHypotheses.exists_abs_integral_cutoff_phasePrimitive_add_height_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {s₂ : ℝ} (hs₂ : s₂ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Space (m + 1)) (R : ℝ), 0 < R → ∀ (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
        (s₀ : ℝ), 0 ≤ s₀ → s₀ ≤ s₂ →
      ∀ ψ : ℝ → ℝ, Measurable ψ → (∀ t, ψ t ∈ Icc (0 : ℝ) 1) →
        (∀ t, |t| ≤ 1 / 4 → ψ t = 1) → (∀ t, 1 / 2 ≤ |t| → ψ t = 0) →
      ∀ D : Set (Space m), MeasurableSet D → ∀ hh : Space m → ℝ, Continuous hh →
      ∀ τ : ℝ, 0 ≤ τ → (∀ y, |hh y| ≤ τ) →
        (∀ y ∈ D ∩ ball (0 : Space m) (3 / 4), |hh y| ≤ 1 / 4 ∧
          ∀ t ∈ Ioo (-1 : ℝ) 1,
            (s₀ < zeroExtension g u (c + R • Q (point y t)) ↔ hh y < t)) →
      ∀ gg : Space m → ℝ, Measurable gg → ∀ G : ℝ, (∀ y, |gg y| ≤ G) →
        (∀ y ∉ ball (0 : Space m) (3 / 4), gg y = 0) → (∫ y, gg y) = 0 →
      |(∫ z, ψ (z (Fin.last m)) * gg (horizontal z) *
            phasePrimitive f (zeroExtension g u (c + R • Q z))) +
          phasePrimitive f 1 * ∫ y, gg y * hh y| ≤
        G * (C * R⁻¹ * (∫ z in horizontal ⁻¹' ball (0 : Space m) (3 / 4) ∩
              (fun z : Space (m + 1) ↦ z (Fin.last m)) ⁻¹' Ioo (-1) 1,
              rescaledPhaseEnergyDensity f R (fun z ↦ zeroExtension g u (c + R • Q z)) z) +
          phasePrimitive f 1 * (2 + τ) * volume.real (ball (0 : Space m) (3 / 4) \ D)) := by
  obtain ⟨C, hC0, hC⟩ := hr.exists_abs_phasePrimitive_rescaled_sub_ite_le h hs₂
  refine ⟨C, hC0, ?_⟩
  intro c R hR Q s₀ hs₀ hs₀₂ ψ hψm hψ01 hψ1 hψ0 D hDm hh hhc τ _ hhτ hgood gg hggm G hgG hgg0
    hggint
  have hvL : LocallyLipschitz (fun z ↦ zeroExtension g u (c + R • Q z)) :=
    locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz _ _ _
  have hval : ∀ z, (fun z ↦ zeroExtension g u (c + R • Q z)) z ∈ Icc (0 : ℝ) 1 := fun z ↦
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hPc : Continuous (fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z))) :=
    (hr.phasePrimitive_comp_locallyLipschitz h hvL hval).continuous
  have hEint := (h.integrableOn_rescaledPhaseEnergy hvL hval R
    (isCompact_closedBall _ _)).mono_set cutoffCol_cylinder_subset_closedBall
  have key := cutoffCol_abs_integral_add_height_le
    (P := fun z ↦ phasePrimitive f (zeroExtension g u (c + R • Q z)))
    (w := fun z ↦ C * R⁻¹ *
      rescaledPhaseEnergyDensity f R (fun z ↦ zeroExtension g u (c + R • Q z)) z)
    (v := fun z ↦ zeroExtension g u (c + R • Q z)) (σ := phasePrimitive f 1) (s₀ := s₀)
    hPc.measurable (fun z ↦ h.phasePrimitive_mem_Icc (hval z))
    (fun z ↦ hC c R hR Q s₀ hs₀ hs₀₂ z) (hEint.const_mul _) hψm hψ01 hψ1 hψ0 hDm
    hhc.measurable hhτ hgood hggm hgG hgg0 hggint
  rw [integral_const_mul] at key
  exact key

end SerrinEpigraph
