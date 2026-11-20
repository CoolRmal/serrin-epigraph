module

public import SerrinEpigraph.DiffuseStressEstimates
public import SerrinEpigraph.QuadraticPotential
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The one-dimensional layer profile and one-dimensional Hamiltonian profiles (HA9.a)

* `layerTravelTime f s = ∫₀ˢ (2W)^{-1/2}` (`W = normalizedPotential f`) is continuous and strictly
  increasing on `[0, 1)` and unbounded (`RigidityHypotheses.exists_layerTravelTime_ge`, from the
  quadratic stable well).
* `layerProfile f` (the profile `q` of the blueprint) vanishes on `(-∞, 0]`, inverts the travel
  time on `[0, ∞)`, is continuous and increasing, satisfies `q' = √(2W(q))` on `(0, ∞)`, and grows
  at least linearly: `c_q min(τ, s₁) ≤ q τ` (`RigidityHypotheses.exists_layerProfile_linear_lower`).
* `ae_eq_const_of_integral_mul_deriv_eq_zero`: the du Bois-Reymond lemma on open intervals.
* `IsHamiltonianProfile f P P'`: a continuous `[0, 1]`-valued profile, `C¹` on its positive set
  with `P'² = 2W(P)` there (zero one-dimensional Hamiltonian). The classification HA9.a:
  `eq_layerProfile_of_deriv_pos` (an increasing positive piece is a whole half-line
  `P = q(· - τ₁)` on `[τ₁, ∞)`), its reflection `eq_layerProfile_of_deriv_neg`, and
  `eq_one_of_eq_one` (a profile touching `1` is identically `1`).
* `IsHamiltonianProfile.anchored_dichotomy`: at a point `0` of the closure of the positive set with
  `P 0 ≤ 1 - b₀`, either `P = q(· + T(P 0))` on `[-M₀, ∞)`, or `P` crosses a given level `s`
  downward inside an explicit bounded window.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-! ### Travel time and the layer profile -/

/-- The travel time `T(s) = ∫₀ˢ (2W)^{-1/2}` of the one-dimensional layer. -/
def layerTravelTime (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, (Real.sqrt (2 * normalizedPotential f r))⁻¹

/-- The one-dimensional one-phase layer profile `q`: zero on `(-∞, 0]` and the inverse of the
travel time on `[0, ∞)`, so that `q' = √(2 W(q))` on `(0, ∞)`. -/
def layerProfile (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  if τ ≤ 0 then 0 else Function.invFunOn (layerTravelTime f) (Ico (0 : ℝ) 1) τ

@[simp] theorem layerTravelTime_zero (f : ℝ → ℝ) : layerTravelTime f 0 = 0 := by
  simp [layerTravelTime]

theorem layerProfile_of_nonpos (f : ℝ → ℝ) {τ : ℝ} (hτ : τ ≤ 0) : layerProfile f τ = 0 := by
  simp [layerProfile, hτ]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

theorem RigidityHypotheses.layerSpeed_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {r : ℝ} (hr' : r ∈ Ico (0 : ℝ) 1) :
    0 < (Real.sqrt (2 * normalizedPotential f r))⁻¹ := by
  have hW := hr.normalizedPotential_pos h hr'.1 hr'.2
  positivity

theorem RigidityHypotheses.layerSpeed_continuousOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ContinuousOn (fun r ↦ (Real.sqrt (2 * normalizedPotential f r))⁻¹) (Ico (0 : ℝ) 1) := by
  apply (continuousOn_const.mul (h.normalizedPotential_continuousOn.mono
    Ico_subset_Icc_self)).sqrt.inv₀
  intro r hr'
  have hW := hr.normalizedPotential_pos h hr'.1 hr'.2
  change Real.sqrt (2 * normalizedPotential f r) ≠ 0
  exact (Real.sqrt_pos.mpr (by linarith)).ne'

theorem RigidityHypotheses.layerSpeed_intervalIntegrable (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1) :
    IntervalIntegrable (fun r ↦ (Real.sqrt (2 * normalizedPotential f r))⁻¹) volume a b :=
  ((hr.layerSpeed_continuousOn h).mono (ordConnected_Ico.uIcc_subset ha hb)).intervalIntegrable

/-- The travel time has derivative `(2W)^{-1/2}` inside `(0, 1)`. -/
theorem RigidityHypotheses.layerTravelTime_hasDerivAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (layerTravelTime f) (Real.sqrt (2 * normalizedPotential f s))⁻¹ s := by
  have hc := hr.layerSpeed_continuousOn h
  exact intervalIntegral.integral_hasDerivAt_right
    (hr.layerSpeed_intervalIntegrable h ⟨le_rfl, zero_lt_one⟩ ⟨hs.1.le, hs.2⟩)
    ((hc.mono Ioo_subset_Ico_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hc.continuousAt (Ico_mem_nhds hs.1 hs.2))

theorem RigidityHypotheses.layerTravelTime_continuousOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) : ContinuousOn (layerTravelTime f) (Ico (0 : ℝ) 1) := by
  intro s hs
  obtain ⟨s', hss', hs'1⟩ := exists_between hs.2
  have hs'0 : 0 ≤ s' := hs.1.trans hss'.le
  have hint : IntegrableOn (fun r ↦ (Real.sqrt (2 * normalizedPotential f r))⁻¹)
      (uIcc 0 s') volume := by
    rw [uIcc_of_le hs'0]
    exact ((hr.layerSpeed_continuousOn h).mono (Icc_subset_Ico_right hs'1)).integrableOn_compact
      isCompact_Icc
  have hcont := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le hs'0] at hcont
  have hmem : Icc 0 s' ∈ 𝓝[Ico (0 : ℝ) 1] s :=
    mem_nhdsWithin.mpr ⟨Iio s', isOpen_Iio, hss', fun x hx ↦ ⟨hx.2.1, hx.1.le⟩⟩
  exact (hcont s ⟨hs.1, hss'.le⟩).mono_of_mem_nhdsWithin hmem

theorem RigidityHypotheses.layerTravelTime_strictMonoOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) : StrictMonoOn (layerTravelTime f) (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  have hsub := intervalIntegral.integral_interval_sub_left
    (hr.layerSpeed_intervalIntegrable h h0 hb) (hr.layerSpeed_intervalIntegrable h h0 ha)
  have hpos : 0 < ∫ r in a..b, (Real.sqrt (2 * normalizedPotential f r))⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hr.layerSpeed_intervalIntegrable h ha hb)
      (fun r hr' ↦ hr.layerSpeed_pos h ⟨by linarith [ha.1, hr'.1], by linarith [hb.2, hr'.2]⟩)
      hab
  change ∫ r in (0 : ℝ)..a, (Real.sqrt (2 * normalizedPotential f r))⁻¹ <
    ∫ r in (0 : ℝ)..b, (Real.sqrt (2 * normalizedPotential f r))⁻¹
  linarith

theorem RigidityHypotheses.layerTravelTime_nonneg (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : 0 ≤ layerTravelTime f s := by
  have := (hr.layerTravelTime_strictMonoOn h).monotoneOn ⟨le_rfl, zero_lt_one⟩ hs hs.1
  simpa using this

theorem RigidityHypotheses.layerTravelTime_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < layerTravelTime f s := by
  have := (hr.layerTravelTime_strictMonoOn h) ⟨le_rfl, zero_lt_one⟩ ⟨hs.1.le, hs.2⟩ hs.1
  simpa using this

/-- The travel time is unbounded: the stable well is quadratic, so `(2W)^{-1/2}` is not integrable
at `1`. -/
theorem RigidityHypotheses.exists_layerTravelTime_ge (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (M : ℝ) : ∃ s ∈ Ico (0 : ℝ) 1, M ≤ layerTravelTime f s := by
  obtain ⟨b, c, C, hb, hc, hcC, hpot⟩ := hr.exists_stable_well_potential_bounds h
  have hC : 0 < C := hc.trans_le hcC
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set δ := b * Real.exp (-(Real.sqrt C * M')) with hδ
  have hδpos : 0 < δ := mul_pos hb.1 (Real.exp_pos _)
  have hδb : δ ≤ b := by
    have : Real.exp (-(Real.sqrt C * M')) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg C; nlinarith)
    calc δ = b * Real.exp (-(Real.sqrt C * M')) := rfl
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left this hb.1.le
      _ = b := mul_one b
  set s := 1 - δ with hs
  have hs01 : s ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith⟩
  have hb01 : 1 - b ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have hbs : 1 - b ≤ s := by linarith
  refine ⟨s, hs01, ?_⟩
  -- the lower bound of the speed on the well
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hlow : ∀ r ∈ Icc (1 - b) s, (Real.sqrt C * (1 - r))⁻¹ ≤
      (Real.sqrt (2 * normalizedPotential f r))⁻¹ := by
    intro r hr'
    have hr1 : 0 < 1 - r := by linarith [hr'.2]
    have hW := hr.normalizedPotential_pos h (show 0 ≤ r by linarith [hr'.1, hb.2]) (by linarith)
    have hWle := (hpot r ⟨hr'.1, by linarith⟩).2.2.2
    have h2W : 2 * normalizedPotential f r ≤ (Real.sqrt C * (1 - r)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC.le]
      linarith
    have hsq : Real.sqrt (2 * normalizedPotential f r) ≤ Real.sqrt C * (1 - r) := by
      calc Real.sqrt (2 * normalizedPotential f r) ≤ Real.sqrt ((Real.sqrt C * (1 - r)) ^ 2) :=
            Real.sqrt_le_sqrt h2W
        _ = Real.sqrt C * (1 - r) := Real.sqrt_sq (by positivity)
    exact inv_anti₀ (by positivity) hsq
  have hcont_low : ContinuousOn (fun r ↦ (Real.sqrt C * (1 - r))⁻¹) (uIcc (1 - b) s) := by
    rw [uIcc_of_le hbs]
    apply (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).inv₀
    intro r hr'
    have : 0 < 1 - r := by linarith [hr'.2]
    exact (mul_pos hsC this).ne'
  have hmono := intervalIntegral.integral_mono_on hbs hcont_low.intervalIntegrable
    (hr.layerSpeed_intervalIntegrable h hb01 hs01) hlow
  -- the explicit logarithmic integral
  have hlog : ∫ r in (1 - b)..s, (Real.sqrt C * (1 - r))⁻¹ = M' := by
    have h1 : ∫ r in (1 - b)..s, (Real.sqrt C * (1 - r))⁻¹ =
        (Real.sqrt C)⁻¹ * ∫ r in (1 - b)..s, (1 - r)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext r
      rw [mul_inv]
    have h2 : ∫ r in (1 - b)..s, (1 - r)⁻¹ = ∫ x in (1 - s)..(1 - (1 - b)), x⁻¹ :=
      intervalIntegral.integral_comp_sub_left (fun x ↦ x⁻¹) 1
    have h3 : ∫ x in (1 - s)..(1 - (1 - b)), x⁻¹ = Real.log (b / δ) := by
      have hsδ : 1 - s = δ := by rw [hs]; ring
      have h1b : 1 - (1 - b) = b := by ring
      rw [hsδ, h1b, integral_inv_of_pos hδpos hb.1]
    have h4 : Real.log (b / δ) = Real.sqrt C * M' := by
      rw [hδ, div_mul_eq_div_div, div_self hb.1.ne', one_div, ← Real.exp_neg, neg_neg,
        Real.log_exp]
    rw [h1, h2, h3, h4, ← mul_assoc, inv_mul_cancel₀ hsC.ne', one_mul]
  have hsplit := intervalIntegral.integral_interval_sub_left
    (hr.layerSpeed_intervalIntegrable h ⟨le_rfl, zero_lt_one⟩ hs01)
    (hr.layerSpeed_intervalIntegrable h ⟨le_rfl, zero_lt_one⟩ hb01)
  have hT0 := hr.layerTravelTime_nonneg h hb01
  have hMM' : M ≤ M' := le_max_left _ _
  change M ≤ ∫ r in (0 : ℝ)..s, (Real.sqrt (2 * normalizedPotential f r))⁻¹
  change 0 ≤ ∫ r in (0 : ℝ)..(1 - b), (Real.sqrt (2 * normalizedPotential f r))⁻¹ at hT0
  linarith

/-- The travel time maps `[0, 1)` onto `[0, ∞)`. -/
theorem RigidityHypotheses.exists_layerTravelTime_eq (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ s ∈ Ico (0 : ℝ) 1, layerTravelTime f s = τ := by
  obtain ⟨s', hs', hτs'⟩ := hr.exists_layerTravelTime_ge h τ
  have hcont : ContinuousOn (layerTravelTime f) (Icc 0 s') :=
    (hr.layerTravelTime_continuousOn h).mono (Icc_subset_Ico_right hs'.2)
  obtain ⟨s, hs, hTs⟩ := intermediate_value_Icc hs'.1 hcont
    (show τ ∈ Icc (layerTravelTime f 0) (layerTravelTime f s') by simp [hτ, hτs'])
  exact ⟨s, ⟨hs.1, lt_of_le_of_lt hs.2 hs'.2⟩, hTs⟩

theorem RigidityHypotheses.layerProfile_spec (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {τ : ℝ} (hτ : 0 ≤ τ) :
    layerProfile f τ ∈ Ico (0 : ℝ) 1 ∧ layerTravelTime f (layerProfile f τ) = τ := by
  rcases hτ.eq_or_lt with rfl | hpos
  · simp [layerProfile]
  · have hne : ¬τ ≤ 0 := not_le.mpr hpos
    simp only [layerProfile, hne, ↓reduceIte]
    exact Function.invFunOn_pos (hr.exists_layerTravelTime_eq h hpos.le)

theorem RigidityHypotheses.layerProfile_travelTime (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    layerProfile f (layerTravelTime f s) = s := by
  obtain ⟨hmem, heq⟩ := hr.layerProfile_spec h (hr.layerTravelTime_nonneg h hs)
  exact (hr.layerTravelTime_strictMonoOn h).injOn hmem hs heq

theorem RigidityHypotheses.layerProfile_mem_Ico (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (τ : ℝ) : layerProfile f τ ∈ Ico (0 : ℝ) 1 := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [layerProfile_of_nonpos f hτ]
    exact ⟨le_rfl, zero_lt_one⟩
  · exact (hr.layerProfile_spec h hτ.le).1

theorem RigidityHypotheses.layerProfile_pos (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {τ : ℝ} (hτ : 0 < τ) : 0 < layerProfile f τ := by
  obtain ⟨hmem, heq⟩ := hr.layerProfile_spec h hτ.le
  rcases hmem.1.eq_or_lt with h0 | h0
  · rw [← h0, layerTravelTime_zero] at heq
    exact absurd heq hτ.ne
  · exact h0

theorem RigidityHypotheses.layerProfile_strictMonoOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) : StrictMonoOn (layerProfile f) (Ici 0) := by
  intro a ha b hb hab
  by_contra hn
  have hle : layerProfile f b ≤ layerProfile f a := not_lt.mp hn
  have hT := (hr.layerTravelTime_strictMonoOn h).monotoneOn (hr.layerProfile_mem_Ico h b)
    (hr.layerProfile_mem_Ico h a) hle
  rw [(hr.layerProfile_spec h hb).2, (hr.layerProfile_spec h ha).2] at hT
  linarith

theorem RigidityHypotheses.layerProfile_monotone (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) : Monotone (layerProfile f) := by
  intro a b hab
  rcases le_or_gt a 0 with ha | ha
  · rw [layerProfile_of_nonpos f ha]
    exact (hr.layerProfile_mem_Ico h b).1
  · exact (hr.layerProfile_strictMonoOn h).monotoneOn (mem_Ici.mpr ha.le)
      (mem_Ici.mpr (ha.le.trans hab)) hab

theorem RigidityHypotheses.layerProfile_lt_of_lt_travelTime (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s τ : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hτ : τ < layerTravelTime f s) : layerProfile f τ < s := by
  have hs' : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  rcases le_or_gt τ 0 with hτ0 | hτ0
  · rw [layerProfile_of_nonpos f hτ0]
    exact hs.1
  · have := (hr.layerProfile_strictMonoOn h) (mem_Ici.mpr hτ0.le)
      (mem_Ici.mpr (hr.layerTravelTime_nonneg h hs')) hτ
    rwa [hr.layerProfile_travelTime h hs'] at this

theorem RigidityHypotheses.lt_layerProfile_of_travelTime_lt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {s τ : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (hτ : layerTravelTime f s < τ) : s < layerProfile f τ := by
  have := (hr.layerProfile_strictMonoOn h) (mem_Ici.mpr (hr.layerTravelTime_nonneg h hs))
    (mem_Ici.mpr ((hr.layerTravelTime_nonneg h hs).trans hτ.le)) hτ
  rwa [hr.layerProfile_travelTime h hs] at this

theorem RigidityHypotheses.continuous_layerProfile (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) : Continuous (layerProfile f) := by
  rw [continuous_iff_continuousAt]
  intro τ
  rcases lt_trichotomy τ 0 with hτ | rfl | hτ
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [Iio_mem_nhds hτ] with σ hσ
    exact (layerProfile_of_nonpos f (le_of_lt hσ)).symm
  · rw [ContinuousAt, layerProfile_of_nonpos f le_rfl]
    rw [tendsto_order]
    refine ⟨fun a ha ↦ Eventually.of_forall fun σ ↦ ha.trans_le (hr.layerProfile_mem_Ico h σ).1,
      fun a ha ↦ ?_⟩
    rcases le_or_gt 1 a with ha1 | ha1
    · exact Eventually.of_forall fun σ ↦ (hr.layerProfile_mem_Ico h σ).2.trans_le ha1
    · have hhalf : a / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hT := hr.layerTravelTime_pos h hhalf
      filter_upwards [Iio_mem_nhds hT] with σ hσ
      have := hr.layerProfile_lt_of_lt_travelTime h hhalf hσ
      linarith
  · apply continuousAt_of_monotoneOn_of_image_mem_nhds
      ((hr.layerProfile_monotone h).monotoneOn (Ioi 0)) (Ioi_mem_nhds hτ)
    have himg : layerProfile f '' Ioi 0 = Ioo 0 1 := by
      ext s
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨hr.layerProfile_pos h hσ, (hr.layerProfile_mem_Ico h σ).2⟩
      · intro hs
        exact ⟨layerTravelTime f s, hr.layerTravelTime_pos h hs,
          hr.layerProfile_travelTime h ⟨hs.1.le, hs.2⟩⟩
    rw [himg]
    exact Ioo_mem_nhds (hr.layerProfile_pos h hτ) (hr.layerProfile_mem_Ico h τ).2

/-- The layer profile solves `q' = √(2 W(q))` on `(0, ∞)`. -/
theorem RigidityHypotheses.layerProfile_hasDerivAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (layerProfile f) (Real.sqrt (2 * normalizedPotential f (layerProfile f τ))) τ := by
  have hmem : layerProfile f τ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hr.layerProfile_pos h hτ, (hr.layerProfile_mem_Ico h τ).2⟩
  have hT := hr.layerTravelTime_hasDerivAt h hmem
  have hne : (Real.sqrt (2 * normalizedPotential f (layerProfile f τ)))⁻¹ ≠ 0 :=
    (hr.layerSpeed_pos h ⟨hmem.1.le, hmem.2⟩).ne'
  have hinv := HasDerivAt.of_local_left_inverse ((hr.continuous_layerProfile h).continuousAt)
    hT hne (by
      filter_upwards [Ioi_mem_nhds hτ] with σ hσ
      exact (hr.layerProfile_spec h (le_of_lt hσ)).2)
  rwa [inv_inv] at hinv

/-- The layer profile grows at least linearly near its zero end. -/
theorem RigidityHypotheses.exists_layerProfile_linear_lower (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ c s₁ : ℝ, 0 < c ∧ 0 < s₁ ∧ ∀ τ, 0 ≤ τ → c * min τ s₁ ≤ layerProfile f τ := by
  have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right (by norm_num)
  obtain ⟨w₀, hw₀, hWmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num))
    (h.normalizedPotential_continuousOn.mono hsub)
  have hWpos : 0 < normalizedPotential f w₀ :=
    hr.normalizedPotential_pos h hw₀.1 (by linarith [hw₀.2])
  set c := Real.sqrt (2 * normalizedPotential f w₀) with hcdef
  have hc : 0 < c := by positivity
  have hhalf : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set s₁ := layerTravelTime f (1 / 2) with hs₁
  have hs₁pos : 0 < s₁ := hr.layerTravelTime_pos h ⟨by norm_num, by norm_num⟩
  -- the travel time grows at most like `s / c` on `[0, 1/2]`
  have hTle : ∀ s ∈ Icc (0 : ℝ) (1 / 2), layerTravelTime f s ≤ s / c := by
    intro s hs
    have hs' : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
    have hmono := intervalIntegral.integral_mono_on hs.1
      (hr.layerSpeed_intervalIntegrable h ⟨le_rfl, zero_lt_one⟩ hs')
      (intervalIntegrable_const (c := c⁻¹)) (fun r hr' ↦ by
        have hrW : normalizedPotential f w₀ ≤ normalizedPotential f r :=
          hWmin ⟨hr'.1, hr'.2.trans hs.2⟩
        have hle : c ≤ Real.sqrt (2 * normalizedPotential f r) :=
          Real.sqrt_le_sqrt (by linarith)
        exact inv_anti₀ hc hle)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    change ∫ r in (0 : ℝ)..s, (Real.sqrt (2 * normalizedPotential f r))⁻¹ ≤ s / c
    calc _ ≤ s * c⁻¹ := hmono
      _ = s / c := by rw [div_eq_mul_inv]
  refine ⟨c, s₁, hc, hs₁pos, fun τ hτ ↦ ?_⟩
  rcases le_or_gt τ s₁ with hτs | hτs
  · rw [min_eq_left hτs]
    obtain ⟨hmem, heq⟩ := hr.layerProfile_spec h hτ
    have hq : layerProfile f τ ≤ 1 / 2 := by
      have := hr.layerProfile_monotone h hτs
      rwa [hs₁, hr.layerProfile_travelTime h hhalf] at this
    have := hTle _ ⟨hmem.1, hq⟩
    rw [heq, le_div_iff₀ hc] at this
    linarith
  · rw [min_eq_right hτs.le]
    have hmono := hr.layerProfile_monotone h hτs.le
    rw [hs₁, hr.layerProfile_travelTime h hhalf] at hmono
    have := hTle (1 / 2) ⟨by norm_num, le_rfl⟩
    rw [le_div_iff₀ hc] at this
    rw [← hs₁] at this
    linarith

/-! ### The du Bois-Reymond lemma -/

/-- A locally integrable function times a continuous compactly supported weight supported in the
domain is integrable. -/
private theorem integrable_mul_of_locallyIntegrableOn {J : Set ℝ} {k ψ : ℝ → ℝ}
    (hk : LocallyIntegrableOn k J) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψJ : tsupport ψ ⊆ J) : Integrable (fun τ ↦ k τ * ψ τ) := by
  have hkK : IntegrableOn k (tsupport ψ) := hk.integrableOn_compact_subset hψJ hψc
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ
  have h1 : IntegrableOn (fun τ ↦ k τ * ψ τ) (tsupport ψ) :=
    hkK.mul_bdd hψ.aestronglyMeasurable.restrict (Eventually.of_forall hC)
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro τ hτ
  by_contra hn
  exact hτ (by simp [image_eq_zero_of_notMem_tsupport hn])

/-- **du Bois-Reymond.** A locally integrable function on an open interval whose distributional
derivative vanishes is almost everywhere constant there. -/
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {J : Set ℝ} (hJo : IsOpen J)
    (hJc : J.OrdConnected) (hJn : J.Nonempty) {k : ℝ → ℝ} (hk : LocallyIntegrableOn k J)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
      ∫ τ, k τ * deriv ψ τ = 0) :
    ∃ c : ℝ, ∀ᵐ τ, τ ∈ J → k τ = c := by
  obtain ⟨τ₀, hτ₀⟩ := hJn
  obtain ⟨r, hr, hrJ⟩ := Metric.isOpen_iff.mp hJo τ₀ hτ₀
  let ρ : ContDiffBump τ₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set ρn : ℝ → ℝ := ρ.normed volume with hρn
  have hρs : ContDiff ℝ (⊤ : ℕ∞) ρn := ρ.contDiff_normed
  have hρc : HasCompactSupport ρn := ρ.hasCompactSupport_normed
  have hρJ : tsupport ρn ⊆ J := by
    rw [hρn, ρ.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans hrJ
  have hρ1 : ∫ τ, ρn τ = 1 := ρ.integral_normed
  set c := ∫ τ, k τ * ρn τ with hcdef
  refine ⟨c, ?_⟩
  have hkey : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J →
      ∫ τ, φ τ • (k τ - c) = 0 := by
    intro φ hφ hφc hφJ
    set I := ∫ τ, φ τ with hI
    set ψ : ℝ → ℝ := fun τ ↦ φ τ - I * ρn τ with hψdef
    have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.sub (contDiff_const.mul hρs)
    have hψcont : Continuous ψ := hψs.continuous
    set K := tsupport φ ∪ tsupport ρn with hK
    have hKc : IsCompact K := hφc.union hρc
    have hKJ : K ⊆ J := union_subset hφJ hρJ
    have hKn : K.Nonempty := ⟨τ₀, Or.inr (by
      rw [hρn, ρ.tsupport_normed_eq]
      exact Metric.mem_closedBall_self (by positivity))⟩
    have hψK : ∀ τ ∉ K, ψ τ = 0 := by
      intro τ hτ
      have h1 : φ τ = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hτ (Or.inl hh))
      have h2 : ρn τ = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hτ (Or.inr hh))
      simp [hψdef, h1, h2]
    set α := sInf K with hα
    set β := sSup K with hβ
    have hαK : α ∈ K := hKc.sInf_mem hKn
    have hβK : β ∈ K := hKc.sSup_mem hKn
    have hKαβ : K ⊆ Icc α β := fun τ hτ ↦ ⟨csInf_le hKc.bddBelow hτ, le_csSup hKc.bddAbove hτ⟩
    obtain ⟨δ₁, hδ₁, hδ₁J⟩ := Metric.isOpen_iff.mp hJo α (hKJ hαK)
    obtain ⟨δ₂, hδ₂, hδ₂J⟩ := Metric.isOpen_iff.mp hJo β (hKJ hβK)
    set δ := min δ₁ δ₂ / 2 with hδ
    have hδpos : 0 < δ := by positivity
    have hδ₁' : δ < δ₁ := by
      have := min_le_left δ₁ δ₂
      rw [hδ]; linarith
    have hδ₂' : δ < δ₂ := by
      have := min_le_right δ₁ δ₂
      rw [hδ]; linarith
    have hα'J : α - δ ∈ J := hδ₁J (by
      rw [Metric.mem_ball, Real.dist_eq, show α - δ - α = -δ by ring, abs_neg,
        abs_of_pos hδpos]
      exact hδ₁')
    have hβ'J : β + δ ∈ J := hδ₂J (by
      rw [Metric.mem_ball, Real.dist_eq, show β + δ - β = δ by ring, abs_of_pos hδpos]
      exact hδ₂')
    have hIccJ : Icc (α - δ) (β + δ) ⊆ J := hJc.out hα'J hβ'J
    set Ψ : ℝ → ℝ := fun τ ↦ ∫ σ in (α - δ)..τ, ψ σ with hΨdef
    have hΨd : ∀ τ, HasDerivAt Ψ (ψ τ) τ := fun τ ↦
      (hψcont.integral_hasStrictDerivAt (α - δ) τ).hasDerivAt
    have hderiv : deriv Ψ = ψ := funext fun τ ↦ (hΨd τ).deriv
    have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ :=
      contDiff_infty_iff_deriv.mpr ⟨fun τ ↦ (hΨd τ).differentiableAt, by rw [hderiv]; exact hψs⟩
    have hφint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hρint : Integrable ρn := hρs.continuous.integrable_of_hasCompactSupport hρc
    have hψint : ∫ τ, ψ τ = 0 := by
      rw [hψdef, integral_sub hφint (hρint.const_mul I), integral_const_mul, hρ1, mul_one,
        ← hI, sub_self]
    have hΨzero : ∀ τ ∉ Ioo (α - δ) (β + δ), Ψ τ = 0 := by
      intro τ hτ
      rcases le_or_gt τ (α - δ) with hle | hgt
      · change ∫ σ in (α - δ)..τ, ψ σ = 0
        rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)), intervalIntegral.integral_zero]
        intro σ hσ
        rw [uIcc_of_ge hle] at hσ
        apply hψK
        intro hσK
        have := (hKαβ hσK).1
        linarith [hσ.2]
      · have hge : β + δ ≤ τ := by
          by_contra hn
          exact hτ ⟨hgt, lt_of_not_ge hn⟩
        change ∫ σ in (α - δ)..τ, ψ σ = 0
        rw [intervalIntegral.integral_of_le (by linarith : α - δ ≤ τ),
          setIntegral_eq_integral_of_forall_compl_eq_zero, hψint]
        intro σ hσ
        apply hψK
        intro hσK
        have := hKαβ hσK
        exact hσ ⟨by linarith [this.1], by linarith [this.2]⟩
    have hΨc : HasCompactSupport Ψ := HasCompactSupport.intro (isCompact_Icc (a := α - δ)
      (b := β + δ)) (fun τ hτ ↦ hΨzero τ (fun hh ↦ hτ (Ioo_subset_Icc_self hh)))
    have hΨJ : tsupport Ψ ⊆ J := by
      refine (closure_minimal ?_ isClosed_Icc).trans hIccJ
      intro τ hτ
      by_contra hn
      exact hτ (hΨzero τ (fun hh ↦ hn (Ioo_subset_Icc_self hh)))
    have hh := h Ψ hΨs hΨc hΨJ
    rw [hderiv] at hh
    have hkφ : Integrable (fun τ ↦ k τ * φ τ) :=
      integrable_mul_of_locallyIntegrableOn hk hφ.continuous hφc hφJ
    have hkρ : Integrable (fun τ ↦ k τ * ρn τ) :=
      integrable_mul_of_locallyIntegrableOn hk hρs.continuous hρc hρJ
    have hsplit : ∫ τ, k τ * ψ τ = (∫ τ, k τ * φ τ) - I * c := by
      have heq : (fun τ ↦ k τ * ψ τ) = fun τ ↦ k τ * φ τ - I * (k τ * ρn τ) := by
        funext τ
        simp only [hψdef]
        ring
      rw [heq, integral_sub hkφ (hkρ.const_mul I), integral_const_mul]
    have hkφI : ∫ τ, k τ * φ τ = I * c := by linarith
    have hfinal : (fun τ ↦ φ τ • (k τ - c)) = fun τ ↦ k τ * φ τ - c * φ τ := by
      funext τ
      rw [smul_eq_mul]
      ring
    rw [hfinal, integral_sub hkφ (hφint.const_mul c), integral_const_mul, hkφI, ← hI]
    ring
  have hae := hJo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hk.sub (locallyIntegrableOn_const c)) hkey
  filter_upwards [hae] with τ hτ hτJ
  exact sub_eq_zero.mp (hτ hτJ)

/-! ### One-dimensional Hamiltonian profiles (HA9.a) -/

/-- A continuous `[0, 1]`-valued profile which is `C¹` on its positive set with vanishing
one-dimensional Hamiltonian `P'² = 2 W(P)` there. -/
structure IsHamiltonianProfile (f : ℝ → ℝ) (P P' : ℝ → ℝ) : Prop where
  continuous : Continuous P
  mem_Icc : ∀ τ, P τ ∈ Icc (0 : ℝ) 1
  hasDerivAt : ∀ τ, 0 < P τ → HasDerivAt P (P' τ) τ
  continuousAt : ∀ τ, 0 < P τ → ContinuousAt P' τ
  hamiltonian : ∀ τ, 0 < P τ → P' τ ^ 2 = 2 * normalizedPotential f (P τ)

variable {P P' : ℝ → ℝ}

theorem IsHamiltonianProfile.deriv_ne_zero (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {τ : ℝ} (h0 : 0 < P τ)
    (h1 : P τ < 1) : P' τ ≠ 0 := by
  intro hz
  have hH := hP.hamiltonian τ h0
  rw [hz] at hH
  have hW := hr.normalizedPotential_pos h h0.le h1
  nlinarith

/-- Locally near a point of `{0 < P < 1}` where `P' > 0`, the profile is a translate of the layer
profile. -/
theorem IsHamiltonianProfile.eventually_eq_layerProfile (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {τ : ℝ} (h0 : 0 < P τ)
    (h1 : P τ < 1) (hd : 0 < P' τ) :
    ∀ᶠ σ in 𝓝 τ, P σ = layerProfile f (σ - (τ - layerTravelTime f (P τ))) := by
  have hP0 : ∀ᶠ σ in 𝓝 τ, 0 < P σ := hP.continuous.continuousAt.eventually (lt_mem_nhds h0)
  have hP1 : ∀ᶠ σ in 𝓝 τ, P σ < 1 := hP.continuous.continuousAt.eventually (gt_mem_nhds h1)
  have hd' : ∀ᶠ σ in 𝓝 τ, 0 < P' σ := (hP.continuousAt τ h0).eventually (lt_mem_nhds hd)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hP0.and (hP1.and hd'))
  have hE : ∀ σ ∈ Metric.ball τ ε,
      HasDerivAt (fun σ ↦ layerTravelTime f (P σ) - σ) 0 σ := by
    intro σ hσ
    obtain ⟨hσ0, hσ1, hσd⟩ := hball σ hσ
    have hT := hr.layerTravelTime_hasDerivAt h ⟨hσ0, hσ1⟩
    have hcomp := hT.comp σ (hP.hasDerivAt σ hσ0)
    have hsq : P' σ = Real.sqrt (2 * normalizedPotential f (P σ)) := by
      rw [← hP.hamiltonian σ hσ0, Real.sqrt_sq hσd.le]
    have hpos : 0 < Real.sqrt (2 * normalizedPotential f (P σ)) := hsq ▸ hσd
    have h1' : (Real.sqrt (2 * normalizedPotential f (P σ)))⁻¹ * P' σ - 1 = 0 := by
      rw [hsq, inv_mul_cancel₀ hpos.ne', sub_self]
    have := hcomp.sub (hasDerivAt_id' σ)
    rw [h1'] at this
    exact this
  have hconst : ∀ σ ∈ Metric.ball τ ε,
      layerTravelTime f (P σ) - σ = layerTravelTime f (P τ) - τ := by
    intro σ hσ
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball τ ε).isPreconnected
      (fun x hx ↦ (hE x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hE x hx).deriv) hσ (Metric.mem_ball_self hε)
  filter_upwards [Metric.ball_mem_nhds τ hε] with σ hσ
  obtain ⟨hσ0, hσ1, -⟩ := hball σ hσ
  have hT := hconst σ hσ
  rw [← hr.layerProfile_travelTime h ⟨hσ0.le, hσ1⟩]
  congr 1
  linarith

/-- **HA9.a, increasing half-lines.** If `0 < P τ < 1` and `P' τ > 0`, then with
`τ₁ = τ - T(P τ)`, the profile is `q(· - τ₁)` on all of `[τ₁, ∞)`. -/
theorem IsHamiltonianProfile.eq_layerProfile_of_deriv_pos (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {τ : ℝ} (h0 : 0 < P τ)
    (h1 : P τ < 1) (hd : 0 < P' τ) :
    τ - layerTravelTime f (P τ) < τ ∧
      ∀ σ, τ - layerTravelTime f (P τ) ≤ σ →
        P σ = layerProfile f (σ - (τ - layerTravelTime f (P τ))) := by
  set τ₁ := τ - layerTravelTime f (P τ) with hτ₁
  have hT : 0 < layerTravelTime f (P τ) := hr.layerTravelTime_pos h ⟨h0, h1⟩
  have hτ₁τ : τ₁ < τ := by linarith
  refine ⟨hτ₁τ, ?_⟩
  have hqc : Continuous (fun σ ↦ layerProfile f (σ - τ₁)) :=
    (hr.continuous_layerProfile h).comp (continuous_id.sub continuous_const)
  set U := {σ | τ₁ < σ ∧ ∀ᶠ σ' in 𝓝 σ, P σ' = layerProfile f (σ' - τ₁)} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter isOpen_setOfPred_eventually_nhds
  have hτU : τ ∈ U := ⟨hτ₁τ, hP.eventually_eq_layerProfile hr h h0 h1 hd⟩
  have hUeq : ∀ σ ∈ U, P σ = layerProfile f (σ - τ₁) := fun σ hσ ↦ hσ.2.self_of_nhds
  have hUd : ∀ σ ∈ U, 0 < P' σ := by
    intro σ hσ
    have hpos : 0 < σ - τ₁ := by linarith [hσ.1]
    have hq := HasDerivAt.comp_sub_const σ τ₁ (hr.layerProfile_hasDerivAt h hpos)
    have hP0 : 0 < P σ := by rw [hUeq σ hσ]; exact hr.layerProfile_pos h hpos
    have huniq := (hP.hasDerivAt σ hP0).unique (hq.congr_of_eventuallyEq hσ.2)
    rw [huniq]
    have hmem := hr.layerProfile_mem_Ico h (σ - τ₁)
    have hW := hr.normalizedPotential_pos h hmem.1 hmem.2
    exact Real.sqrt_pos.mpr (by linarith)
  have hsub : Ioi τ₁ ⊆ U := by
    refine isPreconnected_Ioi.subset_of_closure_inter_subset hUo ⟨τ, hτ₁τ, hτU⟩ ?_
    rintro σ ⟨hσc, hσ⟩
    have hσ' : τ₁ < σ := hσ
    have hσeq : P σ = layerProfile f (σ - τ₁) :=
      (closure_minimal hUeq (isClosed_eq hP.continuous hqc)) hσc
    have hσpos : 0 < σ - τ₁ := sub_pos.mpr hσ'
    have hσ0 : 0 < P σ := by rw [hσeq]; exact hr.layerProfile_pos h hσpos
    have hσ1 : P σ < 1 := by rw [hσeq]; exact (hr.layerProfile_mem_Ico h _).2
    have hσd0 : 0 ≤ P' σ := by
      have hmem := mem_closure_image (hP.continuousAt σ hσ0) hσc
      have hsubset : P' '' U ⊆ Ici 0 := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hUd x hx).le
      exact closure_minimal hsubset isClosed_Ici hmem
    have hσd : 0 < P' σ := lt_of_le_of_ne hσd0 (Ne.symm (hP.deriv_ne_zero hr h hσ0 hσ1))
    refine ⟨hσ', ?_⟩
    have hev := hP.eventually_eq_layerProfile hr h hσ0 hσ1 hσd
    have hshift : σ - layerTravelTime f (P σ) = τ₁ := by
      rw [hσeq, (hr.layerProfile_spec h hσpos.le).2]
      ring
    rwa [hshift] at hev
  intro σ hσ
  rcases hσ.eq_or_lt with heq | hlt
  · rw [← heq]
    have hcl : τ₁ ∈ closure (Ioi τ₁) := by rw [closure_Ioi]; exact mem_Ici.mpr le_rfl
    exact (closure_minimal (fun x hx ↦ hUeq x (hsub hx))
      (isClosed_eq hP.continuous hqc)) hcl
  · exact hUeq σ (hsub hlt)

/-- The reflected profile `σ ↦ P (-σ)` is again a Hamiltonian profile. -/
theorem IsHamiltonianProfile.comp_neg (hP : IsHamiltonianProfile f P P') :
    IsHamiltonianProfile f (fun σ ↦ P (-σ)) (fun σ ↦ -P' (-σ)) where
  continuous := hP.continuous.comp continuous_neg
  mem_Icc σ := hP.mem_Icc (-σ)
  hasDerivAt σ hσ := by
    have := (hP.hasDerivAt (-σ) hσ).comp σ (hasDerivAt_neg (x := σ))
    simpa [Function.comp_def, mul_neg, mul_one] using this
  continuousAt σ hσ :=
    ((hP.continuousAt (-σ) hσ).comp (f := Neg.neg) continuous_neg.continuousAt).neg
  hamiltonian σ hσ := by
    rw [neg_sq]
    exact hP.hamiltonian (-σ) hσ

/-- **HA9.a, decreasing half-lines.** If `0 < P τ < 1` and `P' τ < 0`, then with
`τ₀ = τ + T(P τ)`, the profile is `q(τ₀ - ·)` on all of `(-∞, τ₀]`. -/
theorem IsHamiltonianProfile.eq_layerProfile_of_deriv_neg (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {τ : ℝ} (h0 : 0 < P τ)
    (h1 : P τ < 1) (hd : P' τ < 0) :
    τ < τ + layerTravelTime f (P τ) ∧
      ∀ σ, σ ≤ τ + layerTravelTime f (P τ) →
        P σ = layerProfile f (τ + layerTravelTime f (P τ) - σ) := by
  have hQ := hP.comp_neg
  have h0' : 0 < P (-(-τ)) := by rwa [neg_neg]
  have h1' : P (-(-τ)) < 1 := by rwa [neg_neg]
  have hd' : 0 < -P' (-(-τ)) := by rw [neg_neg]; linarith
  obtain ⟨hlt, heq⟩ := hQ.eq_layerProfile_of_deriv_pos hr h (τ := -τ) h0' h1' hd'
  simp only [neg_neg] at hlt heq
  refine ⟨by linarith, fun σ hσ ↦ ?_⟩
  have := heq (-σ) (by linarith)
  rw [neg_neg] at this
  rw [this]
  congr 1
  ring

/-- **HA9.a, the stable equilibrium.** A Hamiltonian profile touching `1` is identically `1`. -/
theorem IsHamiltonianProfile.eq_one_of_eq_one (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {τ : ℝ} (h1 : P τ = 1) :
    ∀ σ, P σ = 1 := by
  set A := {σ | P σ = 1} with hA
  have hAc : IsClosed A := isClosed_eq hP.continuous continuous_const
  have hAo : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro σ₀ hσ₀
    have hσ₀' : P σ₀ = 1 := hσ₀
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (hP.continuous.continuousAt.eventually (lt_mem_nhds
        (show (1 / 2 : ℝ) < P σ₀ by rw [hσ₀']; norm_num)))
    refine ⟨ε, hε, fun σ hσ ↦ ?_⟩
    by_contra hne
    have hσ1 : P σ < 1 := lt_of_le_of_ne (hP.mem_Icc σ).2 hne
    have hσ0 : 0 < P σ := by linarith [hball σ hσ]
    have hσdist : |σ - σ₀| < ε := by rwa [Metric.mem_ball, Real.dist_eq] at hσ
    rcases lt_or_gt_of_ne (hP.deriv_ne_zero hr h hσ0 hσ1) with hneg | hpos
    · obtain ⟨hlt, heq⟩ := hP.eq_layerProfile_of_deriv_neg hr h hσ0 hσ1 hneg
      set τ₀ := σ + layerTravelTime f (P σ)
      by_cases hle : σ₀ ≤ τ₀
      · have := heq σ₀ hle
        rw [hσ₀'] at this
        linarith [(hr.layerProfile_mem_Ico h (τ₀ - σ₀)).2]
      · have hball' : τ₀ ∈ Metric.ball σ₀ ε := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          rw [abs_lt] at hσdist
          constructor <;> linarith
        have := heq τ₀ le_rfl
        rw [sub_self, layerProfile_of_nonpos f le_rfl] at this
        linarith [hball τ₀ hball']
    · obtain ⟨hlt, heq⟩ := hP.eq_layerProfile_of_deriv_pos hr h hσ0 hσ1 hpos
      set τ₁ := σ - layerTravelTime f (P σ)
      by_cases hle : τ₁ ≤ σ₀
      · have := heq σ₀ hle
        rw [hσ₀'] at this
        linarith [(hr.layerProfile_mem_Ico h (σ₀ - τ₁)).2]
      · have hball' : τ₁ ∈ Metric.ball σ₀ ε := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          rw [abs_lt] at hσdist
          constructor <;> linarith
        have := heq τ₁ le_rfl
        rw [sub_self, layerProfile_of_nonpos f le_rfl] at this
        linarith [hball τ₁ hball']
  rcases isClopen_iff.mp ⟨hAc, hAo⟩ with hAe | hAu
  · have : τ ∈ A := h1
    rw [hAe] at this
    exact absurd this (notMem_empty τ)
  · intro σ
    have : σ ∈ A := by rw [hAu]; trivial
    exact this

/-- **HA9.a at an anchor.** Let `0` lie in the closure of the positive set, with
`P 0 ≤ 1 - b₀`. Then either `P = q(· + T(P 0))` on `[-M₀, ∞)`, or `P` crosses the level `s`
downward inside the window `[-(M₀ + T(s) + 2), T(1 - b₀)]`. -/
theorem IsHamiltonianProfile.anchored_dichotomy (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {b₀ s M₀ : ℝ}
    (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) (hM₀ : 0 ≤ M₀) (h0 : P 0 ≤ 1 - b₀)
    (hcl : (0 : ℝ) ∈ closure {τ | 0 < P τ}) :
    (∀ σ, -M₀ ≤ σ → P σ = layerProfile f (σ + layerTravelTime f (P 0))) ∨
    ∃ σ₁ σ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ σ₁ ∧ σ₁ < σ₂ ∧
      σ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < P σ₁ ∧ P σ₂ < s := by
  have hb₀' : 1 - b₀ ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs : 0 < layerTravelTime f s := hr.layerTravelTime_pos h hs
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) := hr.layerTravelTime_nonneg h hb₀'
  -- the profile never reaches `1`
  have hlt1 : ∀ σ, P σ < 1 := by
    intro σ
    by_contra hn
    have hσ1 : P σ = 1 := le_antisymm (hP.mem_Icc σ).2 (not_lt.mp hn)
    have := hP.eq_one_of_eq_one hr h hσ1 0
    linarith [hb₀.1]
  have hnn : ∀ σ, 0 ≤ P σ := fun σ ↦ (hP.mem_Icc σ).1
  -- a decreasing component ending in the window gives the second alternative
  have hdown : ∀ σ, 0 < P σ → P' σ < 0 → -M₀ - 1 ≤ σ + layerTravelTime f (P σ) →
      σ + layerTravelTime f (P σ) ≤ layerTravelTime f (1 - b₀) →
      ∃ σ₁ σ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ σ₁ ∧ σ₁ < σ₂ ∧
        σ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < P σ₁ ∧ P σ₂ < s := by
    intro σ hσ0 hσd hlow hup
    obtain ⟨-, heq⟩ := hP.eq_layerProfile_of_deriv_neg hr h hσ0 (hlt1 σ) hσd
    set τ₀ := σ + layerTravelTime f (P σ)
    refine ⟨τ₀ - layerTravelTime f s - 1, τ₀ - layerTravelTime f s / 2, by linarith,
      by linarith, by linarith, ?_, ?_⟩
    · rw [heq _ (by linarith), show τ₀ - (τ₀ - layerTravelTime f s - 1) =
        layerTravelTime f s + 1 by ring]
      exact hr.lt_layerProfile_of_travelTime_lt h ⟨hs.1.le, hs.2⟩ (by linarith)
    · rw [heq _ (by linarith), show τ₀ - (τ₀ - layerTravelTime f s / 2) =
        layerTravelTime f s / 2 by ring]
      exact hr.layerProfile_lt_of_lt_travelTime h hs (by linarith)
  by_cases hex : ∃ σ₁ σ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ σ₁ ∧ σ₁ < σ₂ ∧
      σ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < P σ₁ ∧ P σ₂ < s
  · exact Or.inr hex
  left
  have hno : ∀ σ, 0 < P σ → P' σ < 0 → -M₀ - 1 ≤ σ + layerTravelTime f (P σ) →
      σ + layerTravelTime f (P σ) ≤ layerTravelTime f (1 - b₀) → False :=
    fun σ h1 h2 h3 h4 ↦ hex (hdown σ h1 h2 h3 h4)
  have hTP : ∀ σ, 0 < P σ → 0 < layerTravelTime f (P σ) := fun σ hσ ↦
    hr.layerTravelTime_pos h ⟨hσ, hlt1 σ⟩
  -- a zero of `P` lies at or below the left end of every increasing component
  have hzero_incr : ∀ σ x, 0 < P σ → 0 < P' σ → P x = 0 →
      x ≤ σ - layerTravelTime f (P σ) := by
    intro σ x hσ0 hσd hx
    by_contra hn
    obtain ⟨-, heq⟩ := hP.eq_layerProfile_of_deriv_pos hr h hσ0 (hlt1 σ) hσd
    have := heq x (not_le.mp hn).le
    rw [hx] at this
    have hpos := hr.layerProfile_pos h (sub_pos.mpr (not_le.mp hn))
    linarith
  -- a zero of `P` lies at or above the right end of every decreasing component
  have hzero_decr : ∀ σ x, 0 < P σ → P' σ < 0 → P x = 0 →
      σ + layerTravelTime f (P σ) ≤ x := by
    intro σ x hσ0 hσd hx
    by_contra hn
    obtain ⟨-, heq⟩ := hP.eq_layerProfile_of_deriv_neg hr h hσ0 (hlt1 σ) hσd
    have := heq x (not_le.mp hn).le
    rw [hx] at this
    have hpos := hr.layerProfile_pos h (sub_pos.mpr (not_le.mp hn))
    linarith
  rcases (hnn 0).eq_or_lt with hz | hpos0
  · -- the anchor is a zero of `P`
    have hP00 : P 0 = 0 := hz.symm
    rw [hP00, layerTravelTime_zero]
    -- every positive point within distance `1` increases
    have hA : ∀ σ, |σ| < 1 → 0 < P σ → 0 < P' σ := by
      intro σ hσ hσ0
      rcases lt_or_gt_of_ne (hP.deriv_ne_zero hr h hσ0 (hlt1 σ)) with hneg | hpos
      · exfalso
        have hle := hzero_decr σ 0 hσ0 hneg hP00
        have := hTP σ hσ0
        rw [abs_lt] at hσ
        exact hno σ hσ0 hneg (by linarith) (by linarith)
      · exact hpos
    obtain ⟨σ', hσ'P, hσ'd⟩ := Metric.mem_closure_iff.mp hcl 1 one_pos
    have hσ'P' : 0 < P σ' := hσ'P
    have hσ'abs : |σ'| < 1 := by rwa [Real.dist_eq, zero_sub, abs_neg] at hσ'd
    have hσ'd' := hA σ' hσ'abs hσ'P'
    obtain ⟨-, heq⟩ := hP.eq_layerProfile_of_deriv_pos hr h hσ'P' (hlt1 σ') hσ'd'
    set τ₁ := σ' - layerTravelTime f (P σ') with hτ₁
    have hτ₁0 : 0 ≤ τ₁ := by
      by_contra hn
      have := heq 0 (not_le.mp hn).le
      rw [hP00] at this
      have hpos := hr.layerProfile_pos h (show 0 < 0 - τ₁ by linarith [not_le.mp hn])
      linarith
    have hτ₁eq : τ₁ = 0 := by
      by_contra hne
      have hτ₁pos : 0 < τ₁ := lt_of_le_of_ne hτ₁0 (Ne.symm hne)
      obtain ⟨σ'', hσ''P, hσ''d⟩ := Metric.mem_closure_iff.mp hcl (min 1 τ₁)
        (lt_min one_pos hτ₁pos)
      have hσ''P' : 0 < P σ'' := hσ''P
      have hσ''abs : |σ''| < min 1 τ₁ := by rwa [Real.dist_eq, zero_sub, abs_neg] at hσ''d
      have h1' : |σ''| < 1 := hσ''abs.trans_le (min_le_left _ _)
      have h2' : |σ''| < τ₁ := hσ''abs.trans_le (min_le_right _ _)
      have hσ''d' := hA σ'' h1' hσ''P'
      have hPτ₁ : P τ₁ = 0 := by
        rw [heq τ₁ le_rfl, sub_self, layerProfile_of_nonpos f le_rfl]
      have hle := hzero_incr σ'' τ₁ hσ''P' hσ''d' hPτ₁
      have := hTP σ'' hσ''P'
      rw [abs_lt] at h2'
      linarith [h2'.2]
    intro σ hσ
    rcases le_or_gt 0 σ with hσ0 | hσ0
    · rw [heq σ (by rw [hτ₁eq]; exact hσ0), hτ₁eq, sub_zero, add_zero]
    · rw [add_zero, layerProfile_of_nonpos f hσ0.le]
      by_contra hne
      have hσpos : 0 < P σ := lt_of_le_of_ne (hnn σ) (Ne.symm hne)
      rcases lt_or_gt_of_ne (hP.deriv_ne_zero hr h hσpos (hlt1 σ)) with hneg | hpos
      · have hle := hzero_decr σ 0 hσpos hneg hP00
        have := hTP σ hσpos
        exact hno σ hσpos hneg (by linarith) (by linarith)
      · have hle := hzero_incr σ 0 hσpos hpos hP00
        have := hTP σ hσpos
        linarith
  · -- the anchor is a positive point
    rcases lt_or_gt_of_ne (hP.deriv_ne_zero hr h hpos0 (hlt1 0)) with hneg | hpos
    · exfalso
      have hle : layerTravelTime f (P 0) ≤ layerTravelTime f (1 - b₀) :=
        (hr.layerTravelTime_strictMonoOn h).monotoneOn ⟨hpos0.le, hlt1 0⟩ hb₀' h0
      exact hno 0 hpos0 hneg (by linarith [hTP 0 hpos0]) (by linarith)
    · obtain ⟨-, heq⟩ := hP.eq_layerProfile_of_deriv_pos hr h hpos0 (hlt1 0) hpos
      set τ₁ := 0 - layerTravelTime f (P 0) with hτ₁
      have hPτ₁ : P τ₁ = 0 := by rw [heq τ₁ le_rfl, sub_self, layerProfile_of_nonpos f le_rfl]
      intro σ hσ
      rcases le_or_gt τ₁ σ with hστ | hστ
      · rw [heq σ hστ]
        congr 1
        rw [hτ₁]
        ring
      · rw [layerProfile_of_nonpos f (by rw [hτ₁] at hστ; linarith)]
        by_contra hne
        have hσpos : 0 < P σ := lt_of_le_of_ne (hnn σ) (Ne.symm hne)
        rcases lt_or_gt_of_ne (hP.deriv_ne_zero hr h hσpos (hlt1 σ)) with hneg | hpos'
        · have hle := hzero_decr σ τ₁ hσpos hneg hPτ₁
          have := hTP σ hσpos
          have := hTP 0 hpos0
          exact hno σ hσpos hneg (by linarith) (by linarith)
        · have hle := hzero_incr σ τ₁ hσpos hpos' hPτ₁
          have := hTP σ hσpos
          linarith

end SerrinEpigraph
