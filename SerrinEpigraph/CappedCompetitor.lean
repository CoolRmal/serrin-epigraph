module

public import SerrinEpigraph.LipschitzMinimality

/-!
# Competitors capped below equilibrium without changing their positive phase
-/

public section
noncomputable section

open Set Filter
open scoped Topology

namespace SerrinEpigraph

/-- Cap a competitor below one using a ceiling which stays above the reference solution. -/
@[expose] def cappedCompetitor {d : ℕ} (U v : Space d → ℝ) (t : ℝ) (x : Space d) : ℝ :=
  min (v x) (1 - t + t * U x)

/-- The moving ceiling stays above every reference value at most one. -/
theorem le_competitor_ceiling {a t : ℝ} (ha : a ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    a ≤ 1 - t + t * a := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha)]

/-- Capping preserves local Lipschitz regularity. -/
theorem cappedCompetitor_locallyLipschitz {d : ℕ} {U v : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (t : ℝ) :
    LocallyLipschitz (cappedCompetitor U v t) := by
  have hc : ContDiff ℝ 1 (fun s : ℝ ↦ 1 - t + t * s) := by fun_prop
  exact hv.min (hc.locallyLipschitz.comp hU)

/-- A positive cap parameter places every normalized competitor strictly below one. -/
theorem cappedCompetitor_mem_Ico {d : ℕ} {U v : Space d → ℝ}
    (hU : ∀ x, U x ∈ Ico (0 : ℝ) 1) (hv : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space d) :
    cappedCompetitor U v t x ∈ Ico (0 : ℝ) 1 := by
  have hc : 0 < 1 - t + t * U x := by
    nlinarith [ht.2, mul_nonneg ht.1.le (hU x).1]
  have hc1 : 1 - t + t * U x < 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr (hU x).2)]
  exact ⟨le_min (hv x).1 hc.le, (min_le_right _ _).trans_lt hc1⟩

/-- The ceiling is positive, so capping changes neither zeros nor the positive phase. -/
theorem cappedCompetitor_pos_iff {d : ℕ} {U v : Space d → ℝ}
    (hU : ∀ x, 0 ≤ U x) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space d) :
    0 < cappedCompetitor U v t x ↔ 0 < v x := by
  have hc : 0 < 1 - t + t * U x := by nlinarith [ht.2, mul_nonneg ht.1.le (hU x)]
  exact lt_min_iff.trans (and_iff_left hc)

/-- Capping does not enlarge the support of the difference from the reference function. -/
theorem cappedCompetitor_tsupport_sub_subset {d : ℕ} {U v : Space d → ℝ}
    (hU : ∀ x, U x ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tsupport (fun x ↦ cappedCompetitor U v t x - U x) ⊆ tsupport (fun x ↦ v x - U x) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.notMem_support] at hx ⊢
  have he : v x = U x := sub_eq_zero.mp hx
  change min (v x) (1 - t + t * U x) - U x = 0
  rw [he, min_eq_left (le_competitor_ceiling (hU x) ht), sub_self]

/-- At zero cap parameter the normalized competitor is recovered continuously. -/
theorem cappedCompetitor_tendsto {d : ℕ} {U v : Space d → ℝ}
    (hv : ∀ x, v x ≤ 1) (x : Space d) :
    Tendsto (fun t : ℝ ↦ cappedCompetitor U v t x) (𝓝 0) (𝓝 (v x)) := by
  have hc : ContinuousAt (fun t : ℝ ↦ min (v x) (1 - t + t * U x)) 0 := by fun_prop
  simpa only [cappedCompetitor, zero_mul, sub_zero, add_zero, min_eq_left (hv x)] using hc.tendsto

/-- Where a competitor lies strictly below the ceiling, capping does not change its gradient. -/
theorem cappedCompetitor_gradient_of_lt {d : ℕ} {U v : Space d → ℝ}
    (hU : Continuous U) (hv : Continuous v) {t : ℝ} {x : Space d}
    (hx : v x < 1 - t + t * U x) :
    gradient (cappedCompetitor U v t) x = gradient v x := by
  have hc : Continuous (fun z ↦ 1 - t + t * U z) := by fun_prop
  have he : cappedCompetitor U v t =ᶠ[𝓝 x] v := by
    filter_upwards [(isOpen_lt hv hc).mem_nhds hx] with z hz
    exact min_eq_left hz.le
  exact he.gradient_eq

/-- Where the ceiling lies strictly below the competitor, its gradient is the scaled
reference gradient. -/
theorem cappedCompetitor_gradient_of_gt {d : ℕ} {U v : Space d → ℝ}
    (hU : Continuous U) (hv : Continuous v) {t : ℝ} {x : Space d}
    (hd : DifferentiableAt ℝ U x) (hx : 1 - t + t * U x < v x) :
    gradient (cappedCompetitor U v t) x = t • gradient U x := by
  have hc : Continuous (fun z ↦ 1 - t + t * U z) := by fun_prop
  have he : cappedCompetitor U v t =ᶠ[𝓝 x] (fun z ↦ 1 - t + t * U z) := by
    filter_upwards [(isOpen_lt hc hv).mem_nhds hx] with z hz
    exact min_eq_right hz.le
  rw [he.gradient_eq]
  simp only [gradient, fderiv_const_add, fderiv_const_mul hd, map_smul]

/-- The gradients of capped competitors converge at every differentiability point
of the reference function, including where the competitor attains one. -/
theorem cappedCompetitor_gradient_tendsto {d : ℕ} {U v : Space d → ℝ}
    (hU : Continuous U) (hv : Continuous v) (hU1 : ∀ x, U x < 1)
    (hv1 : ∀ x, v x ≤ 1) {x : Space d} (hd : DifferentiableAt ℝ U x) :
    Tendsto (fun t : ℝ ↦ gradient (cappedCompetitor U v t) x) (𝓝[>] 0)
      (𝓝 (gradient v x)) := by
  by_cases hx : v x < 1
  · have hc : ContinuousAt (fun t : ℝ ↦ 1 - t + t * U x) 0 := by fun_prop
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), v x < 1 - t + t * U x := by
      apply (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually
      have hh : ∀ᶠ y : ℝ in 𝓝 1, v x < y := Ioi_mem_nhds hx
      simpa only [sub_zero, zero_mul, add_zero] using hh
    apply tendsto_const_nhds.congr'
    filter_upwards [ht] with t ht
    exact (cappedCompetitor_gradient_of_lt hU hv ht).symm
  · have hx1 : v x = 1 := le_antisymm (hv1 x) (not_lt.mp hx)
    have hmax : IsLocalMax v x := by
      filter_upwards with z
      rw [hx1]
      exact hv1 z
    have hz : gradient v x = 0 := by simp only [gradient, hmax.fderiv_eq_zero, map_zero]
    rw [hz]
    have ht : Tendsto (fun t : ℝ ↦ t • gradient U x) (𝓝[>] 0) (𝓝 (0 : Space d)) := by
      have hi : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [zero_smul] using
        hi.smul (tendsto_const_nhds (x := gradient U x))
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply (cappedCompetitor_gradient_of_gt hU hv hd ?_).symm
    rw [hx1]
    have hp := mul_pos (show 0 < t from ht) (sub_pos.mpr (hU1 x))
    nlinarith

end SerrinEpigraph
