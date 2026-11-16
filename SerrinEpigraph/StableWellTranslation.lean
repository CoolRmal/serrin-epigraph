module

public import SerrinEpigraph.StableWellMaximum
public import SerrinEpigraph.EquilibriumEstimates
public import SerrinEpigraph.ZeroExtension
public import SerrinEpigraph.TranslationOrderSet

/-!
# Failure of translation order must occur below the stable well

The negative derivative at the equilibrium gives a fixed threshold below which
comparison-failure points can always be selected. This rules out constant-one
critical contact limits.
-/

public section

noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- A quantitative reaction difference bound near the stable equilibrium. -/
theorem RigidityHypotheses.exists_stable_reaction_difference
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ b c : ℝ, b ∈ Ioo 0 1 ∧ 0 < c ∧ ∀ s t : ℝ,
      b ≤ s → s < t → t ≤ 1 → c * (t - s) ≤ f s - f t := by
  obtain ⟨c, δ, hc, hδ, hd⟩ := hr.exists_reaction_deriv_bound h
  let b := 1 - min δ 1 / 2
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    have hmin := lt_min hδ zero_lt_one
    have hle := min_le_right δ 1
    dsimp only [b]
    constructor <;> linarith
  refine ⟨b, c, hb, hc, ?_⟩
  intro s t hbs hst ht1
  have hs : 0 < s := hb.1.trans_le hbs
  have hcont : ContinuousOn f (Icc s t) :=
    h.reaction_contDiffOn.continuousOn.mono (fun z hz ↦ hs.le.trans hz.1)
  have hdiff : DifferentiableOn ℝ f (Ioo s t) := by
    intro z hz
    exact ((h.reaction_contDiffOn.differentiableOn_one z (hs.le.trans hz.1.le)).differentiableAt
      (Ici_mem_nhds (hs.trans hz.1))).differentiableWithinAt
  obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope f hst hcont hdiff
  have hzδ : |z - 1| < δ := by
    rw [abs_of_neg (sub_neg.mpr (hz.2.trans_le ht1))]
    have hmin := min_le_left δ 1
    dsimp only [b] at hbs
    linarith [hz.1]
  have hbound := (hd z hzδ).2
  have heq' := (eq_div_iff (sub_pos.mpr hst).ne').mp heq
  have hmul := mul_le_mul_of_nonneg_right hbound (sub_pos.mpr hst).le
  nlinarith

/-- Bounded comparison excludes all failures confined to the stable well. -/
theorem RigidityHypotheses.translation_order_of_failures_in_stable_well
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hdifference : ∀ s t : ℝ, b ≤ s → s < t → t ≤ 1 → c * (t - s) ≤ f s - f t)
    (a : Space (m + 1))
    (hwell : ∀ x, zeroExtension g u (x + a) < zeroExtension g u x →
      b < zeroExtension g u (x + a)) : a ∈ translationOrderSet (zeroExtension g u) := by
  let U := zeroExtension g u
  let Ω := {x | U (x + a) < U x}
  let Q := fun x ↦ U x - U (x + a)
  let F := fun x ↦ f (U (x + a)) - f (U x)
  have hU : Continuous U := h.zeroExtension_continuous
  have hshift : Continuous (fun x ↦ U (x + a)) := hU.comp (continuous_id.add continuous_const)
  have hΩ : IsOpen Ω := isOpen_lt hshift hU
  have hmem (x : Space (m + 1)) (hx : x ∈ Ω) :
      x ∈ epigraph g ∧ x + a ∈ epigraph g := by
    have hs : 0 < U (x + a) := hb.trans (hwell x hx)
    exact ⟨(h.zeroExtension_pos_iff x).mp (hs.trans hx),
      (h.zeroExtension_pos_iff (x + a)).mp hs⟩
  have hUC : ContDiffOn ℝ 2 U Ω := by
    apply (h.solution_contDiffOn.mono (fun x hx ↦ (hmem x hx).1)).congr
    intro x hx
    exact zeroExtension_of_mem (hmem x hx).1
  have hSC : ContDiffOn ℝ 2 (fun x ↦ U (x + a)) Ω := by
    have hC : ContDiffOn ℝ 2 (fun x ↦ u (x + a)) Ω :=
      h.solution_contDiffOn.comp (contDiff_id.add contDiff_const).contDiffOn
        (fun x hx ↦ (hmem x hx).2)
    apply hC.congr
    intro x hx
    exact zeroExtension_of_mem (hmem x hx).2
  have hF : ContinuousOn F Ω := by
    exact (h.reaction_contDiffOn.continuousOn.comp hshift.continuousOn
      (fun x _ ↦ h.zeroExtension_nonneg _)).sub
        (h.reaction_contDiffOn.continuousOn.comp hU.continuousOn
          (fun x _ ↦ h.zeroExtension_nonneg _))
  have heq : ∀ x ∈ Ω, (Δ Q) x = F x := by
    intro x hx
    have hux := hUC.contDiffAt (hΩ.mem_nhds hx)
    have hsx := hSC.contDiffAt (hΩ.mem_nhds hx)
    change (Δ (U - fun y ↦ U (y + a))) x = F x
    rw [hux.laplacian_sub hsx, laplacian_comp_add_right]
    have hleft := (laplacian_congr_nhds (zeroExtension_eventuallyEq (u := u)
      h.graph_contDiff.continuous (hmem x hx).1)).self_of_nhds
    have hright := (laplacian_congr_nhds (zeroExtension_eventuallyEq (u := u)
      h.graph_contDiff.continuous (hmem x hx).2)).self_of_nhds
    change (Δ (zeroExtension g u)) x - (Δ (zeroExtension g u)) (x + a) = _
    rw [hleft, hright]
    dsimp only [F, U]
    rw [zeroExtension_of_mem (hmem x hx).1, zeroExtension_of_mem (hmem x hx).2]
    linarith [h.equation x (hmem x hx).1, h.equation (x + a) (hmem x hx).2]
  have hn := nonpos_of_bounded_laplacian_ge_mul hΩ (hUC.sub hSC)
    (hU.sub hshift).continuousOn hF heq hc
    (M := 1) (fun x _ ↦ by dsimp only [Q, U]; linarith [hr.zeroExtension_lt_one x,
      h.zeroExtension_nonneg (x + a)])
    (fun x _ hx ↦ by change ¬U (x + a) < U x at hx; linarith)
    (fun x hx _ ↦ hdifference _ _ (hwell x hx).le hx (hr.zeroExtension_lt_one x).le)
  intro x
  by_contra hx
  have hxΩ : x ∈ Ω := lt_of_not_ge hx
  have hq := hn x (subset_closure hxΩ)
  change U x - U (x + a) ≤ 0 at hq
  exact hx (by linarith)

/-- Every disallowed translation has a failure point below one fixed threshold
strictly below the equilibrium. The threshold is independent of the translation. -/
theorem RigidityHypotheses.exists_low_failure_threshold
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ b : ℝ, b ∈ Ioo 0 1 ∧ ∀ a : Space (m + 1),
      a ∉ translationOrderSet (zeroExtension g u) → ∃ x : Space (m + 1),
        zeroExtension g u (x + a) < zeroExtension g u x ∧
        zeroExtension g u (x + a) ≤ b := by
  obtain ⟨b, c, hb, hc, hd⟩ := hr.exists_stable_reaction_difference h
  refine ⟨b, hb, fun a ha ↦ ?_⟩
  by_contra hn
  push Not at hn
  exact ha (hr.translation_order_of_failures_in_stable_well h hb.1 hc hd a hn)

end SerrinEpigraph
