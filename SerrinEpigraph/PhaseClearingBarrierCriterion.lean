module

public import SerrinEpigraph.PhaseClearingComparison
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Clearing from a smooth signed barrier

All barrier hypotheses below are pointwise differential inequalities. The
vanishing conclusion follows from the already proved energy minimality.
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The localized cut-down agrees with the original function outside its inner
cutoff ball, once the barrier dominates throughout the cutoff transition. -/
theorem phaseClearingCompetitor_eq_outside {d : ℕ} {U w η : Space d → ℝ}
    {c : Space d} {r R : ℝ}
    (hs : Function.support η ⊆ ball c R)
    (hdom : ∀ x ∈ ball c R, r ≤ dist x c → U x ≤ w x)
    {x : Space d} (hx : r ≤ dist x c) :
    phaseClearingCompetitor U w η x = U x := by
  by_cases hR : x ∈ ball c R
  · simp [phaseClearingCompetitor, phaseClearingRemoval,
      min_eq_left ((hdom x hR hx).trans (le_max_right _ _))]
  · have hz : η x = 0 := Function.notMem_support.mp (fun hh ↦ hR (hs hh))
    simp [phaseClearingCompetitor, phaseClearingRemoval, hz]

/-- A smooth signed barrier with a strictly absorbable inner flux clears its
inner ball. No vanishing or phase-density property is assumed. -/
theorem RigidityHypotheses.zeroExtension_eq_zero_of_clearing_barrier
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {c : Space (m + 1)} {s r R δ c₀ F₀ M D : ℝ}
    (hs : 0 < s) (hsr : s < r) (hrR : r < R) (hδ : δ ≤ 1)
    (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hW : ∀ t ∈ Icc (0 : ℝ) δ, c₀ ≤ normalizedPotential f t)
    (hf : ∀ t ∈ Icc (0 : ℝ) δ, f t ≤ F₀)
    (hsmall : ∀ x ∈ ball c R, zeroExtension g u x ≤ δ)
    {w η : Space (m + 1) → ℝ} (hw : ContDiff ℝ 1 w) (hη : ContDiff ℝ 1 η)
    (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hηone : ∀ x ∈ closedBall c r, η x = 1)
    (hηsupp : Function.support η ⊆ ball c R)
    (hinner : ∀ x ∈ ball c s, w x ≤ 0)
    (houter : ∀ x ∈ ball c r, s < dist x c → 0 < w x)
    (hdom : ∀ x ∈ ball c R, r ≤ dist x c → zeroExtension g u x ≤ w x)
    {Q : Space (m + 1) → Space (m + 1)} (hQ : ContDiff ℝ 1 Q)
    (hQc : HasCompactSupport Q) (hQs : tsupport Q ⊆ closedBall c R)
    (hQeq : ∀ x ∈ ball c r, Q x = gradient w x)
    (hQdiv : ∀ x ∈ ball c r, s < dist x c →
      fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) Q x ≤ -F₀)
    (hQbound : ∀ x ∈ ball c s, ‖Q x‖ ≤ M)
    (hQdivbound : ∀ x ∈ ball c s,
      fieldDivergence (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) Q x ≤ D)
    (habs : M / Real.sqrt (2 * c₀) + δ * D / c₀ < 1) :
    EqOn (zeroExtension g u) 0 (ball c s) := by
  let U := zeroExtension g u
  let v := phaseClearingCompetitor U w η
  let z := phaseClearingRemoval U w η
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  let θ := M / Real.sqrt (2 * c₀) + δ * D / c₀
  have hU : LocallyLipschitz U := h.zeroExtension_locallyLipschitz
  have hUv (x : Space (m + 1)) : U x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩
  have hv : LocallyLipschitz v :=
    phaseClearingCompetitor_locallyLipschitz hU hw.locallyLipschitz hη.locallyLipschitz
  have hz : LocallyLipschitz z :=
    phaseClearingRemoval_locallyLipschitz hU hw.locallyLipschitz hη.locallyLipschitz
  have hvval (x : Space (m + 1)) : v x ∈ Icc (0 : ℝ) 1 :=
    phaseClearingCompetitor_mem_Icc (hUv x) (hηval x)
  have hzval (x : Space (m + 1)) : z x ∈ Icc (0 : ℝ) 1 := by
    have hh := phaseClearingRemoval_mem_Icc (w := w) (hUv x).1 (hηval x)
    exact ⟨hh.1, hh.2.trans (hUv x).2⟩
  have hveq (x : Space (m + 1)) (hx : r ≤ dist x c) : v x = U x :=
    phaseClearingCompetitor_eq_outside hηsupp hdom hx
  have hzdef (x : Space (m + 1)) : z x = U x - v x := by
    dsimp [v, z, phaseClearingCompetitor]
    ring
  have hvsupp : tsupport (fun x ↦ v x - U x) ⊆ closedBall c R := by
    apply closure_minimal ?_ isClosed_closedBall
    intro x hx
    by_contra hn
    have hd : R < dist x c := lt_of_not_ge hn
    exact hx (sub_eq_zero.mpr (hveq x ((hrR.trans hd).le)))
  have hinzero (x : Space (m + 1)) (hx : x ∈ ball c s) : v x = 0 :=
    phaseClearingCompetitor_zero (hUv x).1 (hinner x hx)
      (hηone x (ball_subset_closedBall (ball_subset_ball hsr.le hx)))
  have hminlocal (x : Space (m + 1)) (hx : x ∈ ball c r) (hwp : 0 < w x) :
      v =ᶠ[𝓝 x] (fun y ↦ min (U y) (w y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx, (isOpen_lt continuous_const hw.continuous).mem_nhds hwp]
      with y hy hyw
    change phaseClearingCompetitor U w η y = _
    rw [phaseClearingCompetitor_eq_min (Or.inl (hηone y (ball_subset_closedBall hy))),
      max_eq_right hyw.le]
  have hnotSphere (t : ℝ) (ht : t ≠ 0) :
      ∀ᵐ x ∂volume, dist x c ≠ t := by
    have he : ∀ᵐ x ∂volume, x ∉ sphere c t :=
      (ae_iff.mpr (by
        simpa only [not_not, Set.ofPred_mem_eq] using
          Measure.addHaar_sphere_of_ne_zero volume c ht))
    exact he
  have hpoint : ∀ᵐ x ∂volume.restrict (closedBall c R),
      (1 - θ) * (ball c s).indicator (phaseEnergyDensity f 0 U) x ≤
        phaseEnergyDensity f 0 U x - phaseEnergyDensity f 0 v x -
          inner ℝ (gradient z x) (Q x) - z x * fieldDivergence b Q x := by
    filter_upwards [ae_restrict_of_ae (hnotSphere s hs.ne'),
      ae_restrict_of_ae (hnotSphere r (hs.trans hsr).ne'),
      ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hU),
      ae_restrict_of_ae (ae_differentiableAt_of_locallyLipschitz hv)] with x hxs hxr hdU hdv
    by_cases hxin : dist x c < s
    · have hx : x ∈ ball c s := hxin
      have he : v =ᶠ[𝓝 x] (0 : Space (m + 1) → ℝ) := by
        filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact hinzero y hy
      have hze : z =ᶠ[𝓝 x] U := by
        filter_upwards [he] with y hy
        rw [hzdef, hy]
        simp
      have hflux := h.phaseClearing_inner_flux_le_energy hc₀ hM hD hW
        (hsmall x (ball_subset_ball (hsr.trans hrR).le hx)) (hQbound x hx) (hQdivbound x hx)
      have hvzero : phaseEnergyDensity f 0 v x = 0 := by
        simp [phaseEnergyDensity, hinzero x hx]
      rw [Set.indicator_of_mem hx, hvzero, hze.gradient_eq, hze.eq_of_nhds]
      change (1 - θ) * phaseEnergyDensity f 0 U x ≤ _
      dsimp [θ, U, b] at *
      linarith
    · have hsx : s < dist x c := lt_of_le_of_ne (le_of_not_gt hxin) (Ne.symm hxs)
      have hxnot : x ∉ ball c s := hxin
      by_cases hxrlt : dist x c < r
      · have hx : x ∈ ball c r := hxrlt
        have he := hminlocal x hx (houter x hx hsx)
        have hdmin := hdv.congr_of_eventuallyEq he.symm
        have hgradz : gradient z x = gradient U x - gradient v x := by
          rw [show z = (fun y ↦ U y - v y) from funext hzdef]
          simp only [gradient, fderiv_fun_sub hdU hdv, map_sub]
        have hE := h.phaseClearing_min_energy_lower_bound hU.continuous hw.continuous hδ hf
          ⟨(hUv x).1, hsmall x (ball_subset_ball hrR.le hx)⟩
          (houter x hx hsx) hdU hdmin
        have heEnergy : phaseEnergyDensity f 0 v x =
            phaseEnergyDensity f 0 (fun y ↦ min (U y) (w y)) x := by
          simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq,
            he.eq_of_nhds, he.gradient_eq]
        rw [Set.indicator_of_notMem hxnot, mul_zero, hgradz, hQeq x hx, he.gradient_eq,
          heEnergy, hzdef, he.eq_of_nhds]
        have hznon : 0 ≤ U x - min (U x) (w x) := sub_nonneg.mpr (min_le_left _ _)
        have hd := mul_le_mul_of_nonneg_left (hQdiv x hx hsx) hznon
        rw [real_inner_comm]
        dsimp [b] at *
        nlinarith
      · have hrx : r < dist x c := lt_of_le_of_ne (le_of_not_gt hxrlt) (Ne.symm hxr)
        have he : v =ᶠ[𝓝 x] U := by
          filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hrx]
            with y hy
          exact hveq y hy.le
        have hze : z =ᶠ[𝓝 x] (0 : Space (m + 1) → ℝ) := by
          filter_upwards [he] with y hy
          simp [hzdef, hy]
        have hgzero : gradient z x = 0 := by rw [hze.gradient_eq]; simp [gradient]
        simp only [Set.indicator_of_notMem hxnot, mul_zero, hgzero, inner_zero_left,
          hze.eq_of_nhds, Pi.zero_apply, zero_mul, sub_zero]
        have heEnergy : phaseEnergyDensity f 0 v x = phaseEnergyDensity f 0 U x := by
          simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq,
            he.eq_of_nhds, he.gradient_eq]
        rw [heEnergy, sub_self]
  have hzero := hr.phaseClearing_integral_absorption h hv hz hvval hzval
    (isCompact_closedBall c R) hvsupp hQ hQc hQs isOpen_ball.measurableSet
    (fun _ hx ↦ ball_subset_closedBall (ball_subset_ball (hsr.trans hrR).le hx)) habs hpoint
  exact h.zeroExtension_eq_zero_of_low_phase_energy_zero isOpen_ball hc₀ hW
    (fun x hx ↦ hsmall x (ball_subset_ball (hsr.trans hrR).le hx)) hzero

end SerrinEpigraph
