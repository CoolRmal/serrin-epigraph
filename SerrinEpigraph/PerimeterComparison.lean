module

public import SerrinEpigraph.InnerEnergyComparison
public import SerrinEpigraph.PerimeterEnergyLiminf

/-!
# Transferring competitor-energy upper bounds to phase perimeter
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- A comparison with convergent energies and vanishing errors bounds the extended
nonnegative energy liminf. -/
theorem liminf_ofReal_le_of_comparison {E F ε : ℕ → ℝ} {L : ℝ}
    (hcomp : ∀ j, E j ≤ F j + ε j) (hF : Tendsto F atTop (𝓝 L))
    (hε : Tendsto ε atTop (𝓝 0)) :
    liminf (fun j ↦ ENNReal.ofReal (E j)) atTop ≤ ENNReal.ofReal L := by
  have ht : Tendsto (fun j ↦ F j + ε j) atTop (𝓝 L) := by
    simpa only [add_zero] using hF.add hε
  calc
    _ ≤ liminf (fun j ↦ ENNReal.ofReal (F j + ε j)) atTop :=
      liminf_le_liminf (Eventually.of_forall (fun j ↦ ENNReal.ofReal_le_ofReal (hcomp j)))
    _ = _ := (ENNReal.tendsto_ofReal ht).liminf_eq

/-- An inner-ball comparison with a convergent candidate energy bounds the limiting
weighted perimeter on every strictly smaller ball. -/
theorem RigidityHypotheses.perimeter_le_of_inner_energy_comparison
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) {a r : ℝ} (har : a < r)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 a,
      ‖phasePrimitive f (zeroExtension g u (R j • x)) -
        E.indicator (fun _ ↦ phasePrimitive f 1) x‖) atTop (𝓝 0))
    {F ε : ℕ → ℝ} {L : ℝ}
    (hcomp : ∀ j, (∫ x in ball 0 r,
      rescaledPhaseEnergyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x) ≤
        F j + ε j)
    (hF : Tendsto F atTop (𝓝 L)) (hε : Tendsto ε atTop (𝓝 0)) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter b E (ball 0 a) ≤
      ENNReal.ofReal L := by
  apply (hr.perimeter_le_energy_liminf h b R hR a hE ht).trans
  apply liminf_ofReal_le_of_comparison _ hF hε
  intro j
  have hU := h.zeroExtension_locallyLipschitz.comp
    (lipschitzWith_smul (R j)).locallyLipschitz
  have hUval : ∀ x, zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hi := (h.integrableOn_rescaledPhaseEnergy hU hUval (R j)
    (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have he := setIntegral_mono_set hi
    (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hR j).le hUval))
    (Eventually.of_forall (closedBall_subset_ball har))
  exact he.trans (hcomp j)

end SerrinEpigraph
