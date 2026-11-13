module

public import SerrinEpigraph.ClosedCalibrationPath

/-!
# Stability of compact calibration integrals under bounded approximation
-/

public section
noncomputable section

open InnerProductSpace MeasureTheory Filter Metric
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Uniform bounds on levels and vector fields allow almost-everywhere limits inside calibration
integrals. The limiting fields need not be smooth. -/
theorem RigidityHypotheses.tendsto_integral_boundaryCalibration
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) {b C : ℝ} (hb : b < 1)
    {v : ℕ → Space (m + 1) → ℝ} {Z : ℕ → Space (m + 1) → Space (m + 1)}
    {v₀ : Space (m + 1) → ℝ} {Z₀ : Space (m + 1) → Space (m + 1)}
    (hv : ∀ n, ContinuousOn (v n) K) (hZ : ∀ n, ContinuousOn (Z n) K)
    (hval : ∀ n x, x ∈ K → v n x ∈ Set.Icc (0 : ℝ) b)
    (hbound : ∀ n x, x ∈ K → ‖Z n x‖ ≤ C)
    (hvlim : ∀ᵐ x ∂volume.restrict K, Tendsto (fun n ↦ v n x) atTop (𝓝 (v₀ x)))
    (hZlim : ∀ᵐ x ∂volume.restrict K, Tendsto (fun n ↦ Z n x) atTop (𝓝 (Z₀ x))) :
    Tendsto (fun n ↦ ∫ x in K,
      hr.boundaryCalibratedDensity h (horizontal x) (v n x) (Z n x)) atTop
      (𝓝 (∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v₀ x) (Z₀ x))) := by
  let Q := (K ×ˢ Set.Icc (0 : ℝ) b) ×ˢ closedBall (0 : Space (m + 1)) C
  let F := fun p : (Space (m + 1) × ℝ) × Space (m + 1) ↦
    hr.boundaryCalibratedDensity h (horizontal p.1.1) p.1.2 p.2
  have hQ : IsCompact Q := (hK.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  have hF : ContinuousOn F Q := by
    apply hr.boundaryCalibratedDensity_continuousOn_comp h
      (continuous_horizontal.comp (continuous_fst.comp continuous_fst)).continuousOn
      (continuous_snd.comp continuous_fst).continuousOn continuous_snd.continuousOn
    intro p hp
    exact ⟨hp.1.2.1, hp.1.2.2.trans_lt hb⟩
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn hF
  have hmem (n : ℕ) (x : Space (m + 1)) (hx : x ∈ K) :
      ((x, v n x), Z n x) ∈ Q := by
    exact ⟨⟨hx, hval n x hx⟩, by simpa only [mem_closedBall, dist_zero_right] using hbound n x hx⟩
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ M)
  · intro n
    have hc := hF.comp
      ((continuous_id.continuousOn.prodMk (hv n)).prodMk (hZ n))
      (fun x hx ↦ hmem n x hx)
    exact hc.aestronglyMeasurable hK.measurableSet
  · exact continuousOn_const.integrableOn_compact hK
  · intro n
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hM ((x, v n x), Z n x) (hmem n x hx)
  · filter_upwards [ae_restrict_mem hK.measurableSet, hvlim, hZlim] with x hx hvx hZx
    have hp : Tendsto (fun n ↦ ((x, v n x), Z n x)) atTop (𝓝 ((x, v₀ x), Z₀ x)) :=
      (tendsto_const_nhds.prodMk_nhds hvx).prodMk_nhds hZx
    have hmem₀ : ((x, v₀ x), Z₀ x) ∈ Q :=
      hQ.isClosed.mem_of_tendsto hp (Eventually.of_forall (fun n ↦ hmem n x hx))
    have hpQ : Tendsto (fun n ↦ ((x, v n x), Z n x)) atTop
        (𝓝[Q] ((x, v₀ x), Z₀ x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hp, Eventually.of_forall (fun n ↦ hmem n x hx)⟩
    have ht := (hF ((x, v₀ x), Z₀ x) hmem₀).tendsto.comp hpQ
    simpa only [F, Function.comp_def] using ht

/-- A bounded smooth approximation of the zero extension recovers its phase energy through
calibration integrals. The existence of such an approximation is a separate requirement. -/
theorem RigidityHypotheses.tendsto_calibration_zeroExtension_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) {b C : ℝ} (hb : b < 1)
    {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ n, ContDiff ℝ 1 (v n))
    (hval : ∀ n x, x ∈ K → v n x ∈ Set.Icc (0 : ℝ) b)
    (hbound : ∀ n x, x ∈ K → ‖gradient (v n) x‖ ≤ C)
    (hvlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun n ↦ v n x) atTop (𝓝 (zeroExtension g u x)))
    (hZlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun n ↦ gradient (v n) x) atTop (𝓝 (gradient (zeroExtension g u) x))) :
    Tendsto (fun n ↦ ∫ x in K,
      hr.boundaryCalibratedDensity h (horizontal x) (v n x) (gradient (v n) x)) atTop
      (𝓝 (∫ x in K,
        phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) (zeroExtension g u) x)) := by
  have hG (n : ℕ) : ContinuousOn (gradient (v n)) K :=
    ((toDual ℝ (Space (m + 1))).symm.continuous.comp
      ((hv n).continuous_fderiv one_ne_zero)).continuousOn
  have ht := hr.tendsto_integral_boundaryCalibration h hK hb
    (fun n ↦ (hv n).continuous.continuousOn) hG hval hbound hvlim hZlim
  simpa only [hr.boundaryCalibratedDensity_zeroExtension h] using ht

end SerrinEpigraph
