module

public import SerrinEpigraph.Barrier
public import SerrinEpigraph.WeakBarrierComparison

/-!
# Annular comparison for propagation of positivity

A positive shift keeps the negative part of a barrier comparison strictly inside its annulus.
-/

public section

noncomputable section

open MeasureTheory InnerProductSpace Metric Filter
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A shifted barrier difference, clipped outside the region where `v` is nonnegative. -/
@[expose]
def shiftedBarrierDifference (v : E → ℝ) (c : E) (α R ε δ : ℝ) (x : E) : ℝ :=
  max (v x) 0 - ε * annularBarrier c α R x + δ

/-- The negative part of the shifted comparison is supported strictly inside the annulus. -/
theorem shiftedBarrierDifference_support {Ω : Set E} {v : E → ℝ} {c : E}
    {α r R ε δ : ℝ} (hΩ : IsOpen Ω) (hv : ContinuousOn v Ω)
    (hball : closedBall c R ⊆ Ω) (hα : 0 < α) (hε : 0 < ε) (hδ : 0 < δ)
    (hR : 0 ≤ R)
    (hinner : ∀ x ∈ closedBall c r, ε ≤ v x) :
    HasCompactSupport (fun x ↦ max (-shiftedBarrierDifference v c α R ε δ x) 0) ∧
      tsupport (fun x ↦ max (-shiftedBarrierDifference v c α R ε δ x) 0) ⊆
        {x | r < ‖x - c‖ ∧ ‖x - c‖ < R} := by
  let w := shiftedBarrierDifference v c α R ε δ
  let z : E → ℝ := fun x ↦ max (-w x) 0
  have houtside {x : E} (hx : R ≤ ‖x - c‖) : 0 < w x := by
    have hb := annularBarrier_nonpos hα.le hR hx
    have hm := mul_nonpos_of_nonneg_of_nonpos hε.le hb
    have hp := le_max_right (v x) 0
    change 0 < max (v x) 0 - ε * annularBarrier c α R x + δ
    linarith
  have hsupport : Function.support z ⊆ closedBall c R := by
    intro x hx
    by_cases hn : ‖x - c‖ ≤ R
    · simpa only [mem_closedBall, dist_eq_norm] using hn
    · have hp := houtside (lt_of_not_ge hn).le
      exact False.elim (hx (by dsimp [z]; rw [max_eq_right (by linarith)]))
  have hclosure : tsupport z ⊆ closedBall c R := closure_minimal hsupport isClosed_closedBall
  have hc : HasCompactSupport z :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure hclosure
  have hwle : ∀ x ∈ tsupport z, w x ≤ 0 := by
    intro x hx
    by_contra hpos
    have hwcont : ContinuousAt w x :=
      (((hv.continuousAt (hΩ.mem_nhds (hball (hclosure hx)))).max continuousAt_const).sub
        (continuousAt_const.mul
          (contDiff_annularBarrier c α R (n := 0)).continuous.continuousAt)).add
        continuousAt_const
    have hev : ∀ᶠ y in 𝓝 x, 0 < w y := hwcont (isOpen_Ioi.mem_nhds (lt_of_not_ge hpos))
    have hz : z =ᶠ[𝓝 x] 0 := by
      filter_upwards [hev] with y hy
      change max (-w y) 0 = 0
      exact max_eq_right (by linarith)
    exact (notMem_tsupport_iff_eventuallyEq.2 hz) hx
  refine ⟨hc, fun x hx ↦ ⟨?_, ?_⟩⟩
  · by_contra hn
    have hxinner : x ∈ closedBall c r := by
      simpa only [mem_closedBall, dist_eq_norm] using le_of_not_gt hn
    have hvx := hinner x hxinner
    have hb := annularBarrier_lt_one c x hα.le R
    have hm := mul_lt_mul_of_pos_left hb hε
    have hp := le_max_left (v x) 0
    have hw := hwle x hx
    change max (v x) 0 - ε * annularBarrier c α R x + δ ≤ 0 at hw
    linarith
  · by_contra hn
    exact (not_lt_of_ge (hwle x hx)) (houtside (le_of_not_gt hn))

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A positive lower bound on an inner ball propagates by an explicit annular barrier. -/
theorem IsWeakSupersolution.annularBarrier_le {Ω : Set E} {v : E → ℝ} {c : E}
    {M α r R ε : ℝ} (hweak : IsWeakSupersolution μ Ω M v) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hv0 : ∀ x ∈ Ω, 0 ≤ v x)
    (hball : closedBall c R ⊆ Ω) (hM : 0 < M) (hα : 0 < α) (hε : 0 < ε)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hparameter : 2 * α * Module.finrank ℝ E + M ≤ 4 * α ^ 2 * r ^ 2)
    (hinner : ∀ x ∈ closedBall c r, ε ≤ v x) :
    ∀ x ∈ ball c R, ε * annularBarrier c α R x ≤ v x := by
  let A : Set E := {x | r < ‖x - c‖ ∧ ‖x - c‖ < R}
  have hA : IsOpen A :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hAsub : A ⊆ Ω := fun x hx ↦ hball (by
    simpa only [mem_closedBall, dist_eq_norm] using hx.2.le)
  let v₀ : E → ℝ := fun x ↦ max (v x) 0
  have heq : Set.EqOn v v₀ Ω := fun x hx ↦ (max_eq_left (hv0 x hx)).symm
  have hv₀ : ContDiffOn ℝ 1 v₀ Ω := hv.congr (fun x hx ↦ (heq hx).symm)
  have hweak₀ : IsWeakSupersolution μ A M v₀ := (hweak.congr_on hΩ heq).mono hAsub
  let b : E → ℝ := fun x ↦ ε * annularBarrier c α R x
  have hb : ContDiff ℝ 2 b := contDiff_const.mul (contDiff_annularBarrier c α R)
  have hbsub : ∀ x ∈ A, -(Δ b) x + M * b x ≤ 0 := by
    intro x hx
    have hB := annularBarrier_subsolution hM.le hr hx.1.le hparameter (R := R)
    have hLap : (Δ b) x = ε * (Δ (annularBarrier c α R)) x := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        laplacian_smul ε ((contDiff_annularBarrier c α R (n := 2)).contDiffAt (x := x))
    rw [hLap]
    change -(ε * (Δ (annularBarrier c α R)) x) + M * (ε * annularBarrier c α R x) ≤ 0
    nlinarith [mul_nonneg hε.le hB]
  have hshift (δ : ℝ) (hδ : 0 < δ) : ∀ x, 0 ≤ shiftedBarrierDifference v c α R ε δ x := by
    have hsup := hweak₀.sub_classical_add_const hA (hv₀.mono hAsub) hb.contDiffOn hbsub
      (mul_nonneg hM.le hδ.le)
    have hw : ContDiffOn ℝ 1 (fun x ↦ v₀ x - b x + δ) A :=
      ((hv₀.mono hAsub).sub (hb.of_le (by norm_num)).contDiffOn).add contDiffOn_const
    obtain ⟨hc, hs⟩ := shiftedBarrierDifference_support hΩ hv.continuousOn hball hα hε hδ
      hR hinner
    exact hsup.nonneg_of_hasCompactSupport_negativePart hA hM hw hc hs
  intro x hx
  have hxΩ := hball (ball_subset_closedBall hx)
  by_contra hlt
  have hd : 0 < ε * annularBarrier c α R x - v x := sub_pos.2 (lt_of_not_ge hlt)
  have hw := hshift ((ε * annularBarrier c α R x - v x) / 2) (by positivity) x
  change 0 ≤ max (v x) 0 - ε * annularBarrier c α R x +
    (ε * annularBarrier c α R x - v x) / 2 at hw
  rw [max_eq_left (hv0 x hxΩ)] at hw
  linarith

/-- Positivity at the center propagates throughout every ball compactly contained in the domain. -/
theorem IsWeakSupersolution.pos_on_ball {Ω : Set E} {v : E → ℝ} {M : ℝ}
    (hweak : IsWeakSupersolution μ Ω M v) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hv0 : ∀ x ∈ Ω, 0 ≤ v x) (hM : 0 < M)
    {c : E} {R : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ Ω) (hc : 0 < v c) :
    ∀ x ∈ ball c R, 0 < v x := by
  have hcΩ : c ∈ Ω := hball (mem_closedBall_self hR.le)
  have hvcont := hv.continuousOn.continuousAt (hΩ.mem_nhds hcΩ)
  have hε : 0 < v c / 2 := by positivity
  have hev : ∀ᶠ x in 𝓝 c, v c / 2 < v x :=
    hvcont (isOpen_Ioi.mem_nhds (by linarith : v c / 2 < v c))
  obtain ⟨s, hs, hsv⟩ := Metric.mem_nhds_iff.1 hev
  have hr : 0 < s / 2 := by positivity
  have hinner : ∀ x ∈ closedBall c (s / 2), v c / 2 ≤ v x := by
    intro x hx
    exact (hsv (show x ∈ ball c s from
      lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith))).le
  obtain ⟨α, hα, hparameter⟩ := exists_annularBarrier_parameter (E := E) hr hM.le
  have hcompare := hweak.annularBarrier_le hΩ hv hv0 hball hM hα hε hr.le hR.le hparameter
    hinner
  intro x hx
  have hB : 0 < annularBarrier c α R x :=
    annularBarrier_pos hα hR.le (by simpa only [mem_ball, dist_eq_norm] using hx)
  exact lt_of_lt_of_le (mul_pos hε hB) (hcompare x hx)

end SerrinEpigraph
