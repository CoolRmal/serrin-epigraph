module

public import SerrinEpigraph.RecoveryPerimeter
public import SerrinEpigraph.PerimeterComparison

/-!
# Transferring recovery energy bounds to the limiting phase
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Integral norm convergence restricts to any smaller measurable integration region. -/
theorem integral_norm_sub_tendsto_of_subset {d : ℕ} {v : ℕ → Space d → ℝ}
    {z : Space d → ℝ} {K S : Set (Space d)} (hS : S ⊆ K)
    (hi : ∀ j, IntegrableOn (fun x ↦ ‖v j x - z x‖) K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖v j x - z x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in S, ‖v j x - z x‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
  intro j
  exact setIntegral_mono_set (hi j) (Eventually.of_forall (fun x ↦ norm_nonneg _))
    (Eventually.of_forall hS)

/-- A recovery sequence for a competitor phase agreeing with the limiting phase
on an annulus bounds the limiting phase perimeter on smaller balls. The annular
energy bound is derived from surface growth and the convergent recovery bound. -/
theorem RigidityHypotheses.perimeter_le_recovery_bound_of_annular_agreement
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {r t a : ℝ} (hradius : 0 < r) (ht : 0 < t) (har : a < r)
    {R B : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRtop : Tendsto R atTop atTop)
    {v : ℕ → Space (m + 1) → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E D : Set (Space (m + 1))} (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hagree : ∀ x ∈ closedBall 0 (r + t) \ ball 0 r, x ∈ E ↔ x ∈ D)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hvlim : Tendsto (fun j ↦ ∫ x in closedBall 0 (r + t),
      ‖v j x - D.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (hbound : ∀ j, (∫ x in closedBall 0 (r + t),
      rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B j)
    {L : ℝ} (hBt : Tendsto B atTop (𝓝 L)) :
    ENNReal.ofReal (phasePrimitive f 1) * variationalPerimeter basis E (ball 0 a) ≤
      ENNReal.ofReal L := by
  let U := fun j x ↦ zeroExtension g u (R j • x)
  let K : Set (Space (m + 1)) := closedBall 0 (r + t)
  let S : Set (Space (m + 1)) := K \ ball 0 r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  have hUval (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hRpos (j : ℕ) : 0 < R j := zero_lt_one.trans_le (hR j)
  have hiE : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hiD : IntegrableOn (D.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hD
  have hUi (j : ℕ) := ((hU j).continuous.continuousOn.integrableOn_compact hK).sub hiE
  have hvi (j : ℕ) := ((hv j).continuous.continuousOn.integrableOn_compact hK).sub hiD
  have hUz := integral_norm_sub_tendsto_of_subset (show S ⊆ K from sdiff_subset)
    (fun j ↦ (hUi j).norm) hUlim
  have hvz := integral_norm_sub_tendsto_of_subset (show S ⊆ K from sdiff_subset)
    (fun j ↦ (hvi j).norm) hvlim
  have hsame (x : Space (m + 1)) (hx : x ∈ S) :
      E.indicator (fun _ ↦ (1 : ℝ)) x = D.indicator (fun _ ↦ (1 : ℝ)) x := by
    by_cases hxE : x ∈ E
    · simp only [indicator_of_mem hxE, indicator_of_mem ((hagree x hx).mp hxE)]
    · have hxD : x ∉ D := fun hh ↦ hxE ((hagree x hx).mpr hh)
      simp only [indicator_of_notMem hxE, indicator_of_notMem hxD]
  have hvz' : Tendsto (fun j ↦ ∫ x in S,
      ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    convert hvz using 1
    funext j
    exact setIntegral_congr_fun (μ := volume) (hK.measurableSet.diff measurableSet_ball)
      (fun x hx ↦ by rw [hsame x hx])
  obtain ⟨C, _, hC⟩ := hr.rescaledPhaseEnergy_bound h
  obtain ⟨M, hM⟩ := hBt.bddAbove_range
  let q := max 1 (r + t)
  have hq : 1 ≤ q := le_max_left _ _
  have hSq : S ⊆ closedBall 0 q := sdiff_subset.trans
    (closedBall_subset_closedBall (le_max_right _ _))
  have hEB (j : ℕ) :
      (∫ x in S, rescaledPhaseEnergyDensity f (R j) (U j) x) +
      (∫ x in S, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ C * q ^ m + M := by
    have hiU := h.integrableOn_rescaledPhaseEnergy (hU j) (hUval j) (R j)
      (isCompact_closedBall 0 q)
    have hiv := h.integrableOn_rescaledPhaseEnergy (hv j) (hval j) (R j) hK
    have hEU := setIntegral_mono_set hiU
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hUval j)))
      (Eventually.of_forall hSq)
    have hEv := setIntegral_mono_set hiv
      (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hRpos j).le (hval j)))
      (Eventually.of_forall (show S ⊆ K from sdiff_subset))
    have hRq : 1 ≤ R j * q := by nlinarith [hR j, hq]
    exact add_le_add (hEU.trans (hC (R j) q (hRpos j) hRq))
      (hEv.trans ((hbound j).trans (hM (mem_range_self j))))
  obtain ⟨ε, hεt, hcomp⟩ := hr.exists_inner_energy_comparison_error h hv hval hradius ht
    (hiE.mono_set sdiff_subset) hR hRtop hEB hUz hvz'
  have hsmall : closedBall (0 : Space (m + 1)) a ⊆ K :=
    closedBall_subset_closedBall (by linarith)
  have hUsmall := integral_norm_sub_tendsto_of_subset hsmall (fun j ↦ (hUi j).norm) hUlim
  have hprimitive := hr.competitorPrimitive_integral_limit h hU hUval hE
    (isCompact_closedBall 0 a) hUsmall
  exact hr.perimeter_le_of_inner_energy_comparison h basis R hRpos har hE hprimitive
    (fun j ↦ (hcomp j).trans (add_le_add (hbound j) le_rfl)) hBt hεt

end SerrinEpigraph
