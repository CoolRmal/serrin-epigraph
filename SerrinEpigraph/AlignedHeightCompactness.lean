module

public import SerrinEpigraph.AlignedHeightDecomposition
public import SerrinEpigraph.PerimeterFlattening

/-!
# (A) Compactness of the normalized heights along aligned sequences

This module proves the input (A) of `SerrinEpigraph.AlignedHeightDecomposition`,
`HasAlignedHeightCompactness`, from the HA9 input (D), `HasAlignedLevelStructure`:
`RigidityHypotheses.hasAlignedHeightCompactness_of_levelStructure`.

## Parameter conditions

* `0 < ℓ`, `0 ≤ b < 1`, `0 < ρ`, `0 < τ`, `0 < s₁ < s₂ < 1`, `0 < c`: the hypotheses of
  `RigidityHypotheses.exists_normalizedHeight_limit_of_cone`;
* `ρ + τ + |r₀| < 2`: the ball `B̄_{ρ+τ+|r₀|}` then lies in the HA0 cylinder `Q₂`, whose
  normalized tilt along an aligned sequence is `𝓔(2, e_n) = δ_j²`; this is the total tilt bound
  with budget `Θ = 2ᵐ` (`setIntegral_closedBall_diffuseTiltDensity_le_cylinderTilt`);
* `alignedHeightEnergyBound m ℓ ρ s₁ s₂ c L ≤ K`: the explicit `W^{1,2}(B_ρ)` bound of HA2–HA3
  for `Θ = 2ᵐ`.

## Proof

Along an aligned sequence, (D) gives the cone condition and the unsigned slope bound eventually,
and `RigidityHypotheses.exists_normalizedHeight_limit_of_cone` gives the subsequence, the levels,
the centers, the uniform `W^{1,2}(B_ρ)` bound and the `L²(B_r)` limit. The cone and slope
conditions pass to the subsequence. The Lipschitz property of the normalized heights holds at
every index, not only eventually: the McShane extension `y ↦ inf_{z ∈ D} (h z + L |y - z|)` is
`L`-Lipschitz for every domain and every function (`mcShaneExtension_lipschitzWith_of_any`; in the
degenerate cases it is identically `0`), so no passage to a tail is needed.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

/-! ### Lipschitz bounds without nondegeneracy assumptions -/

/-- McShane's extension is `L`-Lipschitz for every domain and every function: when the defining
infima are bounded below this is the usual argument, and otherwise (in particular for an empty
domain) the extension is identically `0`. -/
theorem mcShaneExtension_lipschitzWith_of_any {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (L : ℝ≥0) (h : X → ℝ) : LipschitzWith L (mcShaneExtension D L h) := by
  by_cases hB : ∀ y : X, BddBelow (range fun z : D ↦ h z + (L : ℝ) * dist y (z : X))
  · rcases isEmpty_or_nonempty D with hD | hD
    · have h0 : mcShaneExtension D L h = fun _ ↦ 0 :=
        funext fun y ↦ Real.iInf_of_isEmpty _
      rw [h0]
      exact LipschitzWith.const' 0
    · refine LipschitzWith.of_le_add_mul L fun y₁ y₂ ↦ ?_
      have hle : mcShaneExtension D L h y₁ - L * dist y₁ y₂ ≤ mcShaneExtension D L h y₂ := by
        refine le_ciInf fun z ↦ ?_
        have h1 : mcShaneExtension D L h y₁ ≤ h z + L * dist y₁ z := ciInf_le (hB y₁) z
        have h2 : dist y₁ z ≤ dist y₁ y₂ + dist y₂ z := dist_triangle _ _ _
        have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
        linarith
      linarith
  · rw [not_forall] at hB
    obtain ⟨y₀, hy₀⟩ := hB
    have hall : ∀ y : X, ¬BddBelow (range fun z : D ↦ h z + (L : ℝ) * dist y (z : X)) := by
      rintro y ⟨B, hB⟩
      apply hy₀
      refine ⟨B - L * dist y y₀, ?_⟩
      rintro w ⟨z, rfl⟩
      have h1 : B ≤ h z + L * dist y z := hB ⟨z, rfl⟩
      have h2 : dist y z ≤ dist y y₀ + dist y₀ z := dist_triangle _ _ _
      have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
      dsimp only
      linarith
    have h0 : mcShaneExtension D L h = fun _ ↦ 0 :=
      funext fun y ↦ Real.iInf_of_not_bddBelow (hall y)
    rw [h0]
    exact LipschitzWith.const' 0

/-- The extended heights are `L`-Lipschitz for every domain and every family of heights. -/
theorem extendedHeight_lipschitzWith_of_any {m : ℕ} (D : Set (Space m)) (L : ℝ≥0)
    (τ s₁ s₂ : ℝ) (h : ℝ → Space m → ℝ) (s : ℝ) :
    LipschitzWith L (extendedHeight D L τ s₁ s₂ h s) := by
  have hh := (slabClamp_lipschitzWith τ).comp
    (mcShaneExtension_lipschitzWith_of_any D L (h (clampLevel s₁ s₂ s)))
  rw [one_mul] at hh
  exact hh

/-- The normalized heights of an aligned sequence are Lipschitz at every index. -/
theorem alignedSeqHeight_lipschitzWith {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (ℓ r₀ b ρ τ s₁ s₂ : ℝ) (L : ℝ≥0) (x : ℕ → Space (m + 1)) (R : ℕ → ℝ)
    (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {δ : ℕ → ℝ} {k : ℕ} (hδ : 0 < δ k)
    (s a : ℝ) :
    LipschitzWith (L * Real.toNNReal (δ k)⁻¹)
      (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ k s a) :=
  normalizedHeight_lipschitzWith (extendedHeight_lipschitzWith_of_any _ _ _ _ _ _ _) a hδ

/-! ### The total tilt budget -/

/-- **Total tilt from the cylinder normalization.** A closed ball `B̄_Λ` with `Λ < 2` lies in the
HA0 cylinder `Q₂`, so its diffuse vertical tilt is at most `2ᵐ 𝓔(2, e_n)`. -/
theorem setIntegral_closedBall_diffuseTiltDensity_le_cylinderTilt {m : ℕ} {T : ℝ} (hT : 0 < T)
    {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v) {Λ : ℝ} (hΛ : Λ < 2) :
    ∫ z in closedBall (0 : Space (m + 1)) Λ, diffuseTiltDensity T v (verticalDirection m) z ≤
      2 ^ m * cylinderTilt T v 2 (verticalDirection m) := by
  have hvert : ‖verticalDirection m‖ = 1 := norm_verticalDirection m
  have hct : (2 : ℝ) ^ m * cylinderTilt T v 2 (verticalDirection m) =
      ∫ z in tiltCylinder (verticalDirection m) 2,
        diffuseTiltDensity T v (verticalDirection m) z := by
    unfold cylinderTilt
    rw [← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero),
      one_mul]
  rw [hct]
  have hsub : closedBall (0 : Space (m + 1)) Λ ⊆ tiltCylinder (verticalDirection m) 2 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_tiltCylinder_vertical_iff]
    exact ⟨(norm_horizontal_le_norm_of_space z).trans_lt (hz.trans_lt hΛ),
      (abs_apply_last_le_norm z).trans_lt (hz.trans_lt hΛ)⟩
  have hint : IntegrableOn (diffuseTiltDensity T v (verticalDirection m))
      (tiltCylinder (verticalDirection m) 2) :=
    (integrableOn_diffuseTiltDensity hv (isBounded_tiltCylinder hvert 2).isCompact_closure T
      hvert).mono_set subset_closure
  exact setIntegral_mono_set hint
    (Eventually.of_forall fun z ↦ diffuseTiltDensity_nonneg hT v hvert z)
    (Eventually.of_forall hsub)

/-! ### (A) from (D) -/

/-- The explicit `W^{1,2}(B_ρ)` bound of HA2–HA3
(`RigidityHypotheses.exists_normalizedHeight_limit_of_cone`) for the tilt budget `Θ = 2ᵐ` of the
cylinder normalization `𝓔(2, e_n) = δ²`. -/
def alignedHeightEnergyBound (m : ℕ) (ℓ ρ s₁ s₂ c : ℝ) (L : ℝ≥0) : ℝ :=
  (2 ^ (m + 1) * ρ ^ 2 + 1) * ((c⁻¹ * 2 ^ m + (s₂ - s₁) * (L : ℝ) ^ 2 *
    ((5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) * 2 ^ m / ℓ)) / (s₂ - s₁))

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **(A) from (D).** Under the sharp energy bound, for parameters with `0 < ℓ`, `0 ≤ b < 1`,
`0 < ρ`, `0 < τ`, `0 < s₁ < s₂ < 1`, `0 < c`, `ρ + τ + |r₀| < 2` and
`alignedHeightEnergyBound m ℓ ρ s₁ s₂ c L ≤ K`, the HA9 level structure (D) along aligned
sequences gives the normalized-height compactness (A). -/
theorem RigidityHypotheses.hasAlignedHeightCompactness_of_levelStructure
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0}
    (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hρ : 0 < ρ) (hτ : 0 < τ) (hs₁ : 0 < s₁)
    (hs : s₁ < s₂) (hs₂ : s₂ < 1) (hc : 0 < c) (hΛ : ρ + τ + |r₀| < 2)
    (hK : alignedHeightEnergyBound m ℓ ρ s₁ s₂ c L ≤ K)
    (hD : HasAlignedLevelStructure g u ℓ r₀ b ρ τ s₁ s₂ L c) :
    HasAlignedHeightCompactness g u ℓ r₀ b ρ τ s₁ s₂ L c K := by
  intro x R Q δ e hal
  have hDev := hD x R Q δ e hal
  obtain ⟨-, hR, hRt, hδ, hδ0, hRδ, htilt, he, hloc, hQ⟩ := hal
  have htot : ∀ᶠ j in atTop, ∫ z in closedBall (0 : Space (m + 1)) (ρ + τ + |r₀|),
      diffuseTiltDensity (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z))
        (verticalDirection m) z ≤ 2 ^ m * δ j ^ 2 := by
    refine Eventually.of_forall fun j ↦ ?_
    rw [← htilt j]
    exact setIntegral_closedBall_diffuseTiltDensity_le_cylinderTilt (hR j)
      (hr.lipschitzWith_rescaled h (x j) (hR j).le (Q j)).locallyLipschitz hΛ
  obtain ⟨φ, hφ, σl, a, hσ, ha, hbound, H, -, hHL2, hlim⟩ :=
    hr.exists_normalizedHeight_limit_of_cone h hsharp x hR hRt he hloc hQ
      (v := fun j z ↦ zeroExtension g u (x j + R j • Q j z)) (fun j ↦ rfl) hδ hδ0 hRδ
      hℓ hb0 hb1 hρ hτ hs₁ hs hs₂ hc (Θ := 2 ^ m) (by positivity) htot
      (D := fun j ↦ verticalGoodSet (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z))
        ℓ r₀ b ρ) (fun j ↦ rfl) (hDev.mono fun j hj ↦ hj.1) (hDev.mono fun j hj ↦ hj.2)
  exact ⟨φ, σl, a, H, hφ, hσ, ha, hφ.tendsto_atTop.eventually hDev,
    fun j ↦ ⟨_, alignedSeqHeight_lipschitzWith g u ℓ r₀ b ρ τ s₁ s₂ L x R Q (hδ (φ j)) (σl j)
      (a j)⟩,
    fun j ↦ (hbound j).trans hK, hHL2, fun r hr' ↦ hlim σl hσ r hr'⟩

end SerrinEpigraph
