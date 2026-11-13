module

public import SerrinEpigraph.VaryingRecoveryLimit

/-!
# A common sequence for graph recovery energy and phase convergence
-/

public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- Compatible refining partitions admit one sequence of normalized locally
Lipschitz recovery functions with L1 convergence and the sharp area energy bound. -/
theorem RigidityHypotheses.exists_graphRecovery_sequence_of_partitions
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)] {m d : ℕ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ ε τ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hδt : Tendsto δ atTop (𝓝 0))
    (hε : ∀ j, 0 ≤ ε j) (hεt : Tendsto ε atTop (𝓝 0))
    (hτ : ∀ j, 0 < τ j) (hτt : Tendsto τ atTop (𝓝 0))
    {C : ℝ≥0} (hW : LipschitzOnWith C (normalizedPotential f) (Icc 0 1))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {w : (j : ℕ) → ι j → Space d → ℝ}
    (hw : ∀ j i, ContDiff ℝ 1 (w j i)) (hwi : ∀ j i, Integrable (w j i))
    (hpos : ∀ j i y, 0 ≤ w j i y) (hsum : ∀ j y, ∑ i, w j i y ≤ 1)
    {A : Set (Space d)} (hA : IsCompact A)
    (hsupp : ∀ j i y, y ∉ A → w j i y = 0)
    {L : (j : ℕ) → ι j → ℝ} {H : ℝ}
    (hL : ∀ j i, 0 < L j i) (hLH : ∀ j i, L j i ≤ H) (hH : 0 ≤ H)
    (hscale : ∀ j i y, 0 < w j i y →
      graphAreaDensity b y ≤ L j i ∧ L j i ≤ graphAreaDensity b y + ε j)
    (hcost : Tendsto (fun j ↦ C * Real.sqrt (2 * (normalizedPotential f 0 + δ j)) *
      (recoveryTravelTime f (δ j) 1 * H) ^ 2 * ε j) atTop (𝓝 0))
    {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hproj : ∀ x ∈ K, horizontal x ∈ A)
    (hone : ∀ j x, x ∈ K → ∑ i, w j i (horizontal x) = 1) :
    ∃ (R B : ℕ → ℝ) (v : ℕ → Space (d + 1) → ℝ),
      (∀ j, 0 < R j) ∧ Tendsto R atTop atTop ∧
      (∀ j, LocallyLipschitz (v j)) ∧ (∀ j x, v j x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in K, ‖v j x - (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) ∧
      (∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B j) ∧
      Tendsto B atTop (𝓝 ((∫ y in A, graphAreaDensity b y) * phasePrimitive f 1)) := by
  classical
  let S : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  have hS (k : ℕ) : 0 < S k := by dsimp [S]; positivity
  have hSt : Tendsto S atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hrow (j : ℕ) := hr.exists_graphRecovery_energy_error h (hδ j) hW hb
    (hw j) (hwi j) (hpos j) (hsum j) hA (hsupp j) (hL j) (hLH j) hH
    (hε j) (hτ j) (hscale j) hK hproj (hone j) hS hSt
  choose e he het hebound using hrow
  obtain ⟨n, _, hRt, hediag, hwidth⟩ := exists_recovery_diagonal_scale he het
    (fun j ↦ mul_nonneg (hr.recoveryTravelTime_one_pos h (hδ j)).le hH)
  let R : ℕ → ℝ := fun j ↦ S (n j)
  let η := fun j (i : ι j) x ↦ w j i (horizontal x)
  let q := fun j (i : ι j) x ↦ recoveryProfile f (δ j) (R j * graphHeight b x / L j i)
  let v := fun j ↦ partitionRecovery (η j) (q j)
  let B := fun j ↦ (1 + τ j) *
    (((∫ y in A, graphAreaDensity b y) + ε j * (volume A).toReal) *
      recoveryActionPrimitive f (δ j) 1) + e j (n j) +
    (volume A).toReal * (C * Real.sqrt (2 * (normalizedPotential f 0 + δ j)) *
      (recoveryTravelTime f (δ j) 1 * H) ^ 2 * ε j)
  have hR (j : ℕ) : 0 < R j := hS _
  have hη (j : ℕ) (i : ι j) : ContDiff ℝ 1 (η j i) :=
    (hw j i).comp (horizontalContinuousLinearMap (m := d)).contDiff
  have hheight : ContDiff ℝ 1 (graphHeight b) := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).contDiff.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).contDiff)
  have hq (j : ℕ) (i : ι j) : LocallyLipschitz (q j i) :=
    (hr.recoveryProfile_lipschitz h (hδ j)).locallyLipschitz.comp
      ((contDiff_const.mul hheight).div_const (L j i)).locallyLipschitz
  refine ⟨R, B, v, hR, hRt, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j ↦ partitionRecovery_locallyLipschitz
      (fun i ↦ (hη j i).locallyLipschitz) (hq j)
  · exact fun j x ↦ partitionRecovery_mem_Icc (fun i x ↦ hpos j i _)
      (fun x ↦ hsum j _) (fun i x ↦ hr.recoveryProfile_mem_Icc h (hδ j) _) x
  · exact hr.varying_graphRecovery_integral_limit h hδ hR hL hLH hwidth hb.continuous
      (fun j i ↦ (hη j i).continuous) (fun j i x ↦ hpos j i _)
      (fun j x ↦ hsum j _) hK hone
  · exact fun j ↦ hebound j (n j)
  · have ha := hr.recoveryActionPrimitive_tendsto h hδ hδt
    have hp := ((hεt.mul_const (volume A).toReal).const_add
      (∫ y in A, graphAreaDensity b y)).mul ha
    have ht := ((hτt.const_add 1).mul hp).add hediag
    simpa only [B, mul_zero, zero_mul, add_zero, one_mul] using
      ht.add (hcost.const_mul (volume A).toReal)

/-- Every C1 graph admits normalized local recovery functions whose energy is
bounded by a sequence converging to its area on a compact base neighborhood. -/
theorem RigidityHypotheses.exists_graphRecovery_sequence
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {A D : Set (Space d)} (hA : IsCompact A) (hD : IsCompact D) (hDA : D ⊆ interior A)
    {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hproj : ∀ x ∈ K, horizontal x ∈ D) :
    ∃ (R B : ℕ → ℝ) (v : ℕ → Space (d + 1) → ℝ),
      (∀ j, 0 < R j) ∧ Tendsto R atTop atTop ∧
      (∀ j, LocallyLipschitz (v j)) ∧ (∀ j x, v j x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in K, ‖v j x - (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) ∧
      (∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (R j) (v j) x) ≤ B j) ∧
      Tendsto B atTop (𝓝 ((∫ y in A, graphAreaDensity b y) * phasePrimitive f 1)) := by
  classical
  obtain ⟨C, hC⟩ := h.exists_normalizedPotential_lipschitzOn
  obtain ⟨H, hH, hpart⟩ := exists_uniformly_bounded_graphPartitions hb hA hD hDA
  let δ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδt : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ℕ → ℝ := fun j ↦ C * Real.sqrt (2 * (normalizedPotential f 0 + δ j)) *
    (recoveryTravelTime f (δ j) 1 * H) ^ 2
  have ha (j : ℕ) : 0 ≤ a j := by dsimp [a]; positivity
  obtain ⟨ε, hε, hεt, hcost⟩ := exists_graphPartition_precision a ha
  have hp (j : ℕ) := hpart (ε j) (hε j).1 (hε j).2
  choose s L w hL hw hwc hws hwpos hwsum hwone hwscale using hp
  have hw1 (j : ℕ) (i : s j) : ContDiff ℝ 1 (w j i) := (hw j i).of_le (by simp)
  have hwi (j : ℕ) (i : s j) : Integrable (w j i) :=
    (hw1 j i).continuous.integrable_of_hasCompactSupport (hwc j i)
  have hsupp (j : ℕ) (i : s j) (y : Space d) (hy : y ∉ A) : w j i y = 0 := by
    by_contra hne
    exact hy (hws j i (subset_closure (show y ∈ Function.support (w j i) from hne)))
  exact hr.exists_graphRecovery_sequence_of_partitions h hδ hδt
    (fun j ↦ (hε j).1.le) hεt hδ hδt hC hb hw1 hwi hwpos hwsum hA hsupp
    (fun j i ↦ lt_of_lt_of_le zero_lt_one (hL j i).1)
    (fun j i ↦ (hL j i).2) (zero_le_one.trans hH) hwscale hcost hK
    (fun x hx ↦ interior_subset (hDA (hproj x hx)))
    (fun j x hx ↦ hwone j _ (hproj x hx))

end SerrinEpigraph
