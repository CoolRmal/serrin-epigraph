module

public import SerrinEpigraph.LevelHeightDerivative
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Joint smoothness of inverse level height
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The inverse height is jointly twice continuously differentiable at intermediate levels. -/
theorem RigidityHypotheses.levelHeightReal_contDiffAt (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : Space m × ℝ ↦ hr.levelHeightReal h q.1 q.2) p := by
  let t := hr.levelHeightReal h p.1 p.2
  have ht : g p.1 < t := by
    simpa only [t, hr.levelHeightReal_eq h p.1 hs] using
      (hr.levelHeight_spec h p.1 ⟨p.2, hs⟩).1
  have hu : u (point p.1 t) = p.2 := by
    simpa only [t, hr.levelHeightReal_eq h p.1 hs] using
      (hr.levelHeight_spec h p.1 ⟨p.2, hs⟩).2
  have hx : point p.1 t ∈ epigraph g := by simpa [epigraph] using ht
  let F : (Space m × ℝ) × ℝ → ℝ := fun z ↦ u (point z.1.1 z.2) - z.1.2
  have hc : ContDiffAt ℝ 2 F (p, t) := by
    have hcU := h.solution_contDiffOn.contDiffAt
      ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
    have hcP : ContDiffAt ℝ 2 (fun z : (Space m × ℝ) × ℝ ↦ point z.1.1 z.2)
        (p, t) :=
      pointContinuousLinearMap.contDiff.contDiffAt.comp _
        ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
    exact (hcU.comp (p, t) hcP).sub contDiffAt_fst.snd
  have hp := h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg _ hx
  have hi : (fderiv ℝ F (p, t) ∘L
      ContinuousLinearMap.inr ℝ (Space m × ℝ) ℝ).IsInvertible := by
    have hd := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp t
      ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))
    have hv := ((h.vertical_section_hasDerivAt p.1 ht).sub_const p.2).hasFDerivAt_equiv
      (ne_of_gt hp)
    have he : fderiv ℝ F (p, t) ∘L ContinuousLinearMap.inr ℝ (Space m × ℝ) ℝ =
        (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ (ne_of_gt hp)) : ℝ →L[ℝ] ℝ) := by
      exact hd.unique hv
    rw [he]
    exact ContinuousLinearMap.isInvertible_equiv
  let H := hc.implicitFunction (by norm_num) hi
  have hH : ContDiffAt ℝ 2 H p := hc.contDiffAt_implicitFunction (by norm_num) hi
  have hHt : H p = t := hc.implicitFunction_apply_self (by norm_num) hi
  have hEq : ∀ᶠ q in 𝓝 p, F (q, H q) = F (p, t) :=
    hc.eventually_apply_implicitFunction (by norm_num) hi
  have hInt : ∀ᶠ q in 𝓝 p, g q.1 < H q :=
    (h.graph_contDiff.continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      hH.continuousAt (by simpa only [hHt, Function.comp_def] using ht)
  have hLev : ∀ᶠ q in 𝓝 p, q.2 ∈ Set.Ioo (0 : ℝ) 1 :=
    continuous_snd.continuousAt (isOpen_Ioo.mem_nhds hs)
  apply hH.congr_of_eventuallyEq
  filter_upwards [hEq, hInt, hLev] with q hq hiq hsq
  have hval : u (point q.1 (H q)) = q.2 := by
    change u (point q.1 (H q)) - q.2 = u (point p.1 t) - p.2 at hq
    rw [hu] at hq
    linarith
  rw [hr.levelHeightReal_eq h q.1 hsq]
  exact (hr.existsUnique_level_height h q.1 hsq).unique
    (hr.levelHeight_spec h q.1 ⟨q.2, hsq⟩) ⟨hiq, hval⟩

/-- The differential of inverse height solves the differentiated level equation. -/
theorem RigidityHypotheses.levelHeightReal_fderiv_apply (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {p : Space m × ℝ} (hs : p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (q : Space m × ℝ) :
    fderiv ℝ (fun r : Space m × ℝ ↦ hr.levelHeightReal h r.1 r.2) p q =
      (q.2 - fderiv ℝ u (point p.1 (hr.levelHeightReal h p.1 p.2)) (point q.1 0)) /
        verticalDerivative u (point p.1 (hr.levelHeightReal h p.1 p.2)) := by
  let H := fun r : Space m × ℝ ↦ hr.levelHeightReal h r.1 r.2
  have ht : g p.1 < H p := by
    simpa only [H, hr.levelHeightReal_eq h p.1 hs] using
      (hr.levelHeight_spec h p.1 ⟨p.2, hs⟩).1
  have hx : point p.1 (H p) ∈ epigraph g := by simpa [epigraph] using ht
  have hdH : HasFDerivAt H (fderiv ℝ H p) p :=
    ((hr.levelHeightReal_contDiffAt h hs).differentiableAt (by norm_num)).hasFDerivAt
  have hdP := pointContinuousLinearMap.hasFDerivAt.comp p
    (hasFDerivAt_fst.prodMk hdH)
  have hdU := (h.solution_contDiffOn.differentiableOn (by norm_num)).differentiableAt
    ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hx)
  have hd := hdU.hasFDerivAt.comp p hdP
  have he : (fun r : Space m × ℝ ↦ u (point r.1 (H r))) =ᶠ[𝓝 p] Prod.snd := by
    filter_upwards [continuous_snd.continuousAt (isOpen_Ioo.mem_nhds hs)] with r hr'
    change u (point r.1 (hr.levelHeightReal h r.1 r.2)) = r.2
    rw [hr.levelHeightReal_eq h r.1 hr']
    exact (hr.levelHeight_spec h r.1 ⟨r.2, hr'⟩).2
  have hdeq := (hd.congr_of_eventuallyEq he.symm).unique hasFDerivAt_snd
  have hv := congrArg (fun L : (Space m × ℝ) →L[ℝ] ℝ ↦ L q) hdeq
  change fderiv ℝ u (point p.1 (H p)) (point q.1 (fderiv ℝ H p q)) = q.2 at hv
  have hpoint : point q.1 (fderiv ℝ H p q) =
      point q.1 0 + (fderiv ℝ H p q) • verticalDirection m := by
    simpa using (point_add_vertical q.1 0 (fderiv ℝ H p q)).symm
  rw [hpoint, map_add, map_smul] at hv
  have hp := h.verticalDerivative_pos_of_nonneg h.verticalDerivative_nonneg _ hx
  apply (eq_div_iff (ne_of_gt hp)).mpr
  change fderiv ℝ H p q * verticalDerivative u (point p.1 (H p)) = _
  change fderiv ℝ u (point p.1 (H p)) (point q.1 0) +
    fderiv ℝ H p q * verticalDerivative u (point p.1 (H p)) = q.2 at hv
  linarith

end SerrinEpigraph
