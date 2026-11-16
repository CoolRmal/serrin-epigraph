module

public import SerrinEpigraph.PhaseClearingBounds
public import SerrinEpigraph.RadialCutoffCompetitor
public import SerrinEpigraph.BallCutoff

/-!
# Localized minimum competitors for phase clearing
-/

public section
noncomputable section

open Set Metric Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The amount removed by cutting a nonnegative function below a positive-part barrier. -/
@[expose] def phaseClearingRemoval {d : ℕ} (U w η : Space d → ℝ) (x : Space d) : ℝ :=
  η x * (U x - min (U x) (max 0 (w x)))

/-- The localized cut-down competitor. -/
@[expose] def phaseClearingCompetitor {d : ℕ} (U w η : Space d → ℝ) (x : Space d) : ℝ :=
  U x - phaseClearingRemoval U w η x

theorem phaseClearingRemoval_locallyLipschitz {d : ℕ} {U w η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hw : LocallyLipschitz w) (hη : LocallyLipschitz η) :
    LocallyLipschitz (phaseClearingRemoval U w η) := by
  have hm : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_fst.mul contDiff_snd
  exact hm.locallyLipschitz.comp (hη.prodMk (hU.sub (hU.min (hw.const_max 0))))

theorem phaseClearingCompetitor_locallyLipschitz {d : ℕ} {U w η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hw : LocallyLipschitz w) (hη : LocallyLipschitz η) :
    LocallyLipschitz (phaseClearingCompetitor U w η) :=
  hU.sub (phaseClearingRemoval_locallyLipschitz hU hw hη)

theorem phaseClearingRemoval_mem_Icc {d : ℕ} {U w η : Space d → ℝ}
    {x : Space d} (hU : 0 ≤ U x) (hη : η x ∈ Icc (0 : ℝ) 1) :
    phaseClearingRemoval U w η x ∈ Icc (0 : ℝ) (U x) := by
  have hm : 0 ≤ min (U x) (max 0 (w x)) := le_min hU (le_max_left _ _)
  have hd : 0 ≤ U x - min (U x) (max 0 (w x)) := sub_nonneg.mpr (min_le_left _ _)
  constructor
  · exact mul_nonneg hη.1 hd
  · dsimp [phaseClearingRemoval]
    nlinarith [hη.1, hη.2]

theorem phaseClearingCompetitor_mem_Icc {d : ℕ} {U w η : Space d → ℝ}
    {B : ℝ} {x : Space d} (hU : U x ∈ Icc (0 : ℝ) B)
    (hη : η x ∈ Icc (0 : ℝ) 1) :
    phaseClearingCompetitor U w η x ∈ Icc (0 : ℝ) B := by
  have hz := phaseClearingRemoval_mem_Icc (w := w) hU.1 hη
  dsimp [phaseClearingCompetitor]
  constructor <;> linarith [hz.1, hz.2, hU.2]

theorem phaseClearingRemoval_tsupport_subset {d : ℕ} (U w η : Space d → ℝ) :
    tsupport (phaseClearingRemoval U w η) ⊆ tsupport η := by
  apply closure_minimal ?_ (isClosed_tsupport η)
  intro x hx
  apply subset_tsupport η
  intro hz
  exact hx (by simp [phaseClearingRemoval, hz])

theorem phaseClearingCompetitor_eq_min {d : ℕ} {U w η : Space d → ℝ} {x : Space d}
    (hη : η x = 1 ∨ U x ≤ w x) :
    phaseClearingCompetitor U w η x = min (U x) (max 0 (w x)) := by
  rcases hη with hη | hw
  · simp [phaseClearingCompetitor, phaseClearingRemoval, hη]
  · simp [phaseClearingCompetitor, phaseClearingRemoval,
      min_eq_left (hw.trans (le_max_right _ _))]

theorem phaseClearingCompetitor_zero {d : ℕ} {U w η : Space d → ℝ} {x : Space d}
    (hU : 0 ≤ U x) (hw : w x ≤ 0) (hη : η x = 1) :
    phaseClearingCompetitor U w η x = 0 := by
  rw [phaseClearingCompetitor_eq_min (Or.inl hη), max_eq_left hw, min_eq_right hU]

/-- At a differentiability point, the minimum has the original gradient even on
the equality set, whenever its value selects the original function. -/
theorem gradient_min_eq_left_of_le {d : ℕ} {U w : Space d → ℝ} {x : Space d}
    (hU : Continuous U) (hw : Continuous w) (hdU : DifferentiableAt ℝ U x)
    (hdv : DifferentiableAt ℝ (fun y ↦ min (U y) (w y)) x) (hle : U x ≤ w x) :
    gradient (fun y ↦ min (U y) (w y)) x = gradient U x := by
  rcases hle.eq_or_lt with he | ht
  · have hm : IsLocalMax (fun y ↦ min (U y) (w y) - U y) x := by
      filter_upwards with y
      simp only [min_eq_left he.le, sub_self]
      exact sub_nonpos.mpr (min_le_left _ _)
    have hz := hm.fderiv_eq_zero
    rw [fderiv_fun_sub hdv hdU] at hz
    simp only [gradient, sub_eq_zero.mp hz]
  · apply EventuallyEq.gradient_eq
    filter_upwards [(isOpen_lt hU hw).mem_nhds ht] with y hy
    exact min_eq_left hy.le

/-- Convexity of the squared norm in the exact form used by the barrier comparison. -/
theorem half_norm_sq_sub_ge_inner {d : ℕ} (p q : Space d) :
    inner ℝ q (p - q) ≤ ‖p‖ ^ 2 / 2 - ‖q‖ ^ 2 / 2 := by
  have hh := sq_nonneg ‖p - q‖
  rw [norm_sub_sq_real] at hh
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  nlinarith

/-- The pointwise phase-energy decrease of a minimum dominates its barrier flux. -/
theorem Hypotheses.phaseClearing_min_energy_lower_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {U w : Space (m + 1) → ℝ}
    (hU : Continuous U) (hw : Continuous w) {δ F : ℝ} (hδ : δ ≤ 1)
    (hF : ∀ s ∈ Icc (0 : ℝ) δ, f s ≤ F) {x : Space (m + 1)}
    (hval : U x ∈ Icc (0 : ℝ) δ) (hwpos : 0 < w x)
    (hdU : DifferentiableAt ℝ U x)
    (hdv : DifferentiableAt ℝ (fun y ↦ min (U y) (w y)) x) :
    inner ℝ (gradient w x)
        (gradient U x - gradient (fun y ↦ min (U y) (w y)) x) -
        F * (U x - min (U x) (w x)) ≤
      phaseEnergyDensity f 0 U x -
        phaseEnergyDensity f 0 (fun y ↦ min (U y) (w y)) x := by
  by_cases hle : U x ≤ w x
  · rw [gradient_min_eq_left_of_le hU hw hdU hdv hle, sub_self, inner_zero_right,
      min_eq_left hle, sub_self, mul_zero, sub_zero]
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq,
      gradient_min_eq_left_of_le hU hw hdU hdv hle, min_eq_left hle, sub_self, le_refl]
  · have hlt : w x < U x := lt_of_not_ge hle
    have hg : gradient (fun y ↦ min (U y) (w y)) x = gradient w x := by
      apply EventuallyEq.gradient_eq
      filter_upwards [(isOpen_lt hw hU).mem_nhds hlt] with y hy
      exact min_eq_right hy.le
    have hp := h.low_phase_potential_sub_lower_bound hδ hF hwpos.le hlt.le hval.2
    have hs := half_norm_sq_sub_ge_inner (gradient U x) (gradient w x)
    rw [hg, min_eq_right hlt.le]
    have hUp : 0 < U x := hwpos.trans hlt
    simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, hUp,
      min_eq_right hlt.le, hwpos, ite_true, hg, add_zero]
    linarith

end SerrinEpigraph
