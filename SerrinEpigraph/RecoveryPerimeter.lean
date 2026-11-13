module

public import SerrinEpigraph.CompetitorPrimitiveBound

/-!
# Perimeter bounds from normalized recovery sequences
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

variable {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Normalized L1 convergence to a phase indicator passes through the phase primitive. -/
theorem RigidityHypotheses.competitorPrimitive_integral_limit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : ℕ → Space d → ℝ} (hv : ∀ j, LocallyLipschitz (v j))
    (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E K : Set (Space d)} (hE : MeasurableSet E) (hK : IsCompact K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖phasePrimitive f (v j x) - E.indicator (fun _ ↦ phasePrimitive f 1) x‖)
      atTop (𝓝 0) := by
  have hi (c : ℝ) : IntegrableOn (E.indicator (fun _ : Space d ↦ c)) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have hp (j : ℕ) : Continuous (fun x ↦ phasePrimitive f (v j x)) :=
    (hr.phasePrimitive_comp_locallyLipschitz h (hv j) (hval j)).continuous
  have hb (j : ℕ) (x : Space d) :
      ‖phasePrimitive f (v j x) - E.indicator (fun _ ↦ phasePrimitive f 1) x‖ ≤
        Real.sqrt (2 * normalizedPotential f 0) *
          ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖ := by
    have hz : E.indicator (fun _ ↦ (1 : ℝ)) x ∈ Icc (0 : ℝ) 1 := by
      by_cases hx : x ∈ E <;> simp [hx]
    have he := (hr.phasePrimitive_lipschitzOn h).dist_le_mul _ (hval j x) _ hz
    change dist (phasePrimitive f (v j x))
      (phasePrimitive f (E.indicator (fun _ ↦ (1 : ℝ)) x)) ≤
      Real.sqrt (2 * normalizedPotential f 0) *
        dist (v j x) (E.indicator (fun _ ↦ (1 : ℝ)) x) at he
    have heq : phasePrimitive f (E.indicator (fun _ ↦ (1 : ℝ)) x) =
        E.indicator (fun _ ↦ phasePrimitive f 1) x := by
      by_cases hx : x ∈ E <;> simp [hx]
    simpa only [dist_eq_norm, heq] using he
  have ht' := ht.const_mul (Real.sqrt (2 * normalizedPotential f 0))
  simp only [mul_zero] at ht'
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht'
  intro j
  rw [← integral_const_mul]
  exact integral_mono (((hp j).continuousOn.integrableOn_compact hK).sub (hi _)).norm
    ((((hv j).continuous.continuousOn.integrableOn_compact hK).sub (hi 1)).norm.const_mul _)
    (hb j)

/-- A normalized recovery sequence with the correct area-energy upper bound
bounds variational perimeter on every test domain contained in the compact set. -/
theorem RigidityHypotheses.perimeter_le_of_recovery_sequence
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {R B : ℕ → ℝ} {v : ℕ → Space d → ℝ} (hR : ∀ j, 0 < R j)
    (hv : ∀ j, LocallyLipschitz (v j)) (hval : ∀ j x, v j x ∈ Icc (0 : ℝ) 1)
    {E K Ω : Set (Space d)} (hE : MeasurableSet E) (hK : IsCompact K) (hΩ : Ω ⊆ K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖v j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
      atTop (𝓝 0))
    (hbound : ∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B j)
    {P : ℝ} (hB : Tendsto B atTop (𝓝 (P * phasePrimitive f 1))) :
    variationalPerimeter b E Ω ≤ ENNReal.ofReal P := by
  apply variationalPerimeter_le_of_vector_bound b hΩ
  intro F hF hc hs hunit
  have hcont := fieldDivergence_continuous b hF
  have hsupport : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hcompact : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  have hp (j : ℕ) : Continuous (fun x ↦ phasePrimitive f (v j x)) :=
    (hr.phasePrimitive_comp_locallyLipschitz h (hv j) (hval j)).continuous
  have hptest := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict K)
    (fun j x ↦ phasePrimitive f (v j x)) (E.indicator (fun _ ↦ phasePrimitive f 1))
    (fieldDivergence b F) C
    (fun j ↦ (hp j).continuousOn.integrableOn_compact hK)
    ((continuousOn_const.integrableOn_compact hK).indicator hE)
    hcont.aestronglyMeasurable hC
    (hr.competitorPrimitive_integral_limit h hv hval hE hK ht)
  have hle := le_of_tendsto_of_tendsto hptest.norm hB
    (Eventually.of_forall (fun j ↦
      (hr.competitorPrimitive_divergence_test_le_energy h b (hv j) (hval j)
        (hR j) hK hF hc hs hunit).trans (hbound j)))
  have heq : (∫ x in K, E.indicator (fun _ ↦ phasePrimitive f 1) x * fieldDivergence b F x) =
      phasePrimitive f 1 * ∫ x in K, E.indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence b F x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by by_cases hx : x ∈ E <;> simp [hx])
  rw [heq, norm_mul, Real.norm_of_nonneg (hr.phasePrimitive_one_pos h).le] at hle
  nlinarith [hr.phasePrimitive_one_pos h]

/-- The graph recovery construction bounds epigraph perimeter by graph area on
any compact base neighborhood of the ambient compact test region. -/
theorem RigidityHypotheses.graph_perimeter_le_area
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {A D : Set (Space d)} (hA : IsCompact A) (hD : IsCompact D) (hDA : D ⊆ interior A)
    {K Ω : Set (Space (d + 1))} (hK : IsCompact K) (hΩ : Ω ⊆ K)
    (hproj : ∀ x ∈ K, horizontal x ∈ D) :
    variationalPerimeter basis (epigraph b) Ω ≤
      ENNReal.ofReal (∫ y in A, graphAreaDensity b y) := by
  obtain ⟨R, B, v, hR, _, hv, hval, ht, hbound, hBt⟩ :=
    hr.exists_graphRecovery_sequence h hb hA hD hDA hK hproj
  exact hr.perimeter_le_of_recovery_sequence h basis hR hv hval
    (isOpen_epigraph hb.continuous).measurableSet hK hΩ ht hbound hBt

end SerrinEpigraph
