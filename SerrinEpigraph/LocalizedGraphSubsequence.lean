module

public import SerrinEpigraph.LocalizedGraphComparison

/-!
# Localized graph recovery along prescribed scales
-/

public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- Compatible refining partitions admit recovery along prescribed scales, with
energy bounded by the ambient cutoff-weighted graph area times the interface constant. -/
theorem RigidityHypotheses.exists_localized_graphRecovery_subsequence_of_partitions
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)] {m d : ℕ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (S : ℕ → ℝ) (hS : ∀ k, 0 < S k) (hSt : Tendsto S atTop atTop)
    {δ ε τ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hδt : Tendsto δ atTop (𝓝 0))
    (hε : ∀ j, 0 ≤ ε j) (hεt : Tendsto ε atTop (𝓝 0))
    (hτ : ∀ j, 0 < τ j) (hτt : Tendsto τ atTop (𝓝 0))
    {C : ℝ≥0} (hW : LipschitzOnWith C (normalizedPotential f) (Icc 0 1))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {w : (j : ℕ) → ι j → Space d → ℝ}
    (hw : ∀ j i, ContDiff ℝ 1 (w j i)) (hwc : ∀ j i, HasCompactSupport (w j i))
    (hpos : ∀ j i y, 0 ≤ w j i y) (hsum : ∀ j y, ∑ i, w j i y ≤ 1)
    {A : Set (Space d)} (hA : IsCompact A)
    (hsupp : ∀ j i y, y ∉ A → w j i y = 0)
    {L : (j : ℕ) → ι j → ℝ} {H : ℝ}
    (hL : ∀ j i, 0 < L j i) (hLH : ∀ j i, L j i ≤ H) (hH : 0 ≤ H)
    (hscale : ∀ j i y, 0 < w j i y →
      graphAreaDensity b y ≤ L j i ∧ L j i ≤ graphAreaDensity b y + ε j)
    (hcost : Tendsto (fun j ↦ C * Real.sqrt (2 * (normalizedPotential f 0 + δ j)) *
      (recoveryTravelTime f (δ j) 1 * H) ^ 2 * ε j) atTop (𝓝 0))
    {χ : Space (d + 1) → ℝ} {M : ℝ≥0} (hχ : LipschitzWith M χ)
    (hχpos : ∀ x, 0 ≤ χ x)
    {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hproj : ∀ x ∈ K, horizontal x ∈ A)
    (hone : ∀ j x, x ∈ K → ∑ i, w j i (horizontal x) = 1)
    (hχone : ∀ x ∈ K, 1 ≤ χ x) :
    ∃ (n : ℕ → ℕ) (B : ℕ → ℝ) (v : ℕ → Space (d + 1) → ℝ),
      (∀ j, j ≤ n j) ∧ Tendsto n atTop atTop ∧
      (∀ j, 0 < S (n j)) ∧ Tendsto (fun j ↦ S (n j)) atTop atTop ∧
      (∀ j, LocallyLipschitz (v j)) ∧ (∀ j x, v j x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in K, ‖v j x - (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) ∧
      (∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (S (n j)) (v j) x) ≤ B j) ∧
      Tendsto B atTop (𝓝 ((∫ y in A, χ (point y (b y)) * graphAreaDensity b y) * phasePrimitive f 1)) := by
  classical
  have hrow (j : ℕ) := hr.exists_localized_graphRecovery_energy_error h (hδ j) hW hb
    (hw j) (hwc j) (hpos j) (hsum j) hA (hsupp j) (hL j) (hLH j) hH
    (hε j) (hτ j) (hscale j) hχ hχpos hK hproj (hone j) hχone hS hSt
  choose e he het hebound using hrow
  obtain ⟨n, hn, hnt, hediag, hwidth⟩ := exists_recovery_diagonal_subsequence he het
    (fun j ↦ mul_nonneg (hr.recoveryTravelTime_one_pos h (hδ j)).le hH) hS hSt
  have hRt := hSt.comp hnt
  let R : ℕ → ℝ := fun j ↦ S (n j)
  let η := fun j (i : ι j) x ↦ w j i (horizontal x)
  let q := fun j (i : ι j) x ↦ recoveryProfile f (δ j) (R j * graphHeight b x / L j i)
  let v := fun j ↦ partitionRecovery (η j) (q j)
  let B := fun j ↦ (1 + τ j) *
    ((∫ y in A, (χ (point y (b y)) +
      M * (recoveryTravelTime f (δ j) 1 * H / R j)) * (graphAreaDensity b y + ε j)) *
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
  refine ⟨n, B, v, hn, hnt, hR, hRt, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j ↦ partitionRecovery_locallyLipschitz
      (fun i ↦ (hη j i).locallyLipschitz) (hq j)
  · exact fun j x ↦ partitionRecovery_mem_Icc (fun i x ↦ hpos j i _)
      (fun x ↦ hsum j _) (fun i x ↦ hr.recoveryProfile_mem_Icc h (hδ j) _) x
  · exact hr.varying_graphRecovery_integral_limit h hδ hR hL hLH hwidth hb.continuous
      (fun j i ↦ (hη j i).continuous) (fun j i x ↦ hpos j i _)
      (fun j x ↦ hsum j _) hK hone
  · exact fun j ↦ hebound j (n j)
  · have ha := hr.recoveryActionPrimitive_tendsto h hδ hδt
    have hp := (((hεt.mul_const (∫ y in A, χ (point y (b y)))).const_add
      (∫ y in A, χ (point y (b y)) * graphAreaDensity b y)).add
      ((hwidth.const_mul (M : ℝ)).mul ((hεt.mul_const (volume A).toReal).const_add
        (∫ y in A, graphAreaDensity b y)))).mul ha
    have ht := ((hτt.const_add 1).mul hp).add hediag
    simpa only [B, R, integral_graph_cutoff_expansion hb hχ.continuous hA,
      mul_zero, zero_mul, add_zero, one_mul] using ht.add (hcost.const_mul (volume A).toReal)

/-- Every C1 graph admits normalized recovery along prescribed scales with a
localized bound given by any Lipschitz ambient cutoff equal to one on the compact set. -/
theorem RigidityHypotheses.exists_localized_graphRecovery_subsequence
    {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (S : ℕ → ℝ) (hS : ∀ k, 0 < S k) (hSt : Tendsto S atTop atTop)
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b)
    {A D : Set (Space d)} (hA : IsCompact A) (hD : IsCompact D) (hDA : D ⊆ interior A)
    {χ : Space (d + 1) → ℝ} {M : ℝ≥0} (hχ : LipschitzWith M χ)
    (hχpos : ∀ x, 0 ≤ χ x)
    {K : Set (Space (d + 1))} (hK : IsCompact K)
    (hproj : ∀ x ∈ K, horizontal x ∈ D) (hχone : ∀ x ∈ K, 1 ≤ χ x) :
    ∃ (n : ℕ → ℕ) (B : ℕ → ℝ) (v : ℕ → Space (d + 1) → ℝ),
      (∀ j, j ≤ n j) ∧ Tendsto n atTop atTop ∧
      (∀ j, 0 < S (n j)) ∧ Tendsto (fun j ↦ S (n j)) atTop atTop ∧
      (∀ j, LocallyLipschitz (v j)) ∧ (∀ j x, v j x ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫ x in K, ‖v j x - (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) ∧
      (∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (S (n j)) (v j) x) ≤ B j) ∧
      Tendsto B atTop (𝓝 ((∫ y in A, χ (point y (b y)) * graphAreaDensity b y) * phasePrimitive f 1)) := by
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
  have hsupp (j : ℕ) (i : s j) (y : Space d) (hy : y ∉ A) : w j i y = 0 := by
    by_contra hne
    exact hy (hws j i (subset_closure (show y ∈ Function.support (w j i) from hne)))
  exact hr.exists_localized_graphRecovery_subsequence_of_partitions h S hS hSt hδ hδt
    (fun j ↦ (hε j).1.le) hεt hδ hδt hC hb hw1 hwc hwpos hwsum hA hsupp
    (fun j i ↦ lt_of_lt_of_le zero_lt_one (hL j i).1)
    (fun j i ↦ (hL j i).2) (zero_le_one.trans hH) hwscale hcost hχ hχpos hK
    (fun x hx ↦ interior_subset (hDA (hproj x hx)))
    (fun j x hx ↦ hwone j _ (hproj x hx)) hχone

end SerrinEpigraph
