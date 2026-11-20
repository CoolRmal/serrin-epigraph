module

public import SerrinEpigraph.AlignedHeightDecomposition
public import SerrinEpigraph.LevelConeCondition

/-!
# The aligned level structure (HA8 with HA9.d–HA9.e)

This module assembles the HA9 input `HasAlignedLevelStructure` of
`SerrinEpigraph.AlignedHeightDecomposition` (input (D)) from the cone condition and the
microscopic slope on good lines, `RigidityHypotheses.eventually_hasLevelCone_of_planarLayers`
(`SerrinEpigraph.LevelConeCondition`), and the planar layers of aligned HA11 sequences
(`RigidityHypotheses.verticalPlanarLayers_of_rotated`, HA8).

The lines of the vertical good set `verticalGoodSet (R j) v_j ℓ r₀ b ρ` carry good points of
height less than `1` (`exists_isLayerGoodPoint_of_mem_verticalGoodSet`). The cone theorem is
applied in the slab `|t| < max τ 1`, which contains these anchors, and its conclusions restrict
to the slab `|t| < τ` (`HasLevelCone.mono`, `HasLevelSlope.mono`).

* `RigidityHypotheses.exists_hasAlignedLevelStructure`: for interior levels
  `0 < s₁ ≤ s₂ < 1 - b`, `b > 0` and a cone constant `L > 0` there are `ℓ, c > 0` such that
  `HasAlignedLevelStructure g u ℓ r₀ b ρ τ s₁ s₂ L c` holds for all `r₀ > 0`, `τ > 0` and `ρ`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ### Monotonicity of the level conditions -/

/-- The cone condition restricts to smaller horizontal sets and thinner slabs. -/
theorem HasLevelCone.mono {v : Space (m + 1) → ℝ} {D D' : Set (Space m)} {τ τ' s₁ s₂ : ℝ}
    {L : ℝ≥0} (h : HasLevelCone v D τ s₁ s₂ L) (hD : D' ⊆ D) (hτ : τ' ≤ τ) :
    HasLevelCone v D' τ' s₁ s₂ L :=
  fun s hs y hy y' hy' t ht t' ht' hv hv' ↦
    h s hs y (hD hy) y' (hD hy') t ⟨by linarith [ht.1], by linarith [ht.2]⟩ t'
      ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ hv hv'

/-- The slope bound restricts to smaller horizontal sets and thinner slabs. -/
theorem HasLevelSlope.mono {v : Space (m + 1) → ℝ} {D D' : Set (Space m)} {τ τ' s₁ s₂ T c : ℝ}
    (h : HasLevelSlope v D τ s₁ s₂ T c) (hD : D' ⊆ D) (hτ : τ' ≤ τ) :
    HasLevelSlope v D' τ' s₁ s₂ T c :=
  fun s hs y hy t ht hv ↦ h s hs y (hD hy) t ⟨by linarith [ht.1], by linarith [ht.2]⟩ hv

/-! ### The HA9 input on the vertical good sets -/

/-- **HA9 input (D).** For interior levels `0 < s₁ ≤ s₂ < 1 - b` with `b > 0` and a cone constant
`L > 0` there are `ℓ, c > 0` such that for all `r₀ > 0`, `τ > 0` and `ρ`, along every aligned
sequence, eventually the crossings of `[s₁, s₂]` over the vertical good sets in the slab `|t| < τ`
satisfy the cone condition with constant `L` and the slope bound `c ≤ |R_j⁻¹ ∂ₜ v_j|`. -/
theorem RigidityHypotheses.exists_hasAlignedLevelStructure (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {s₁ s₂ b : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ < 1 - b) (hb : 0 < b)
    {L : ℝ≥0} (hL : 0 < L) :
    ∃ ℓ c : ℝ, 0 < ℓ ∧ 0 < c ∧ ∀ r₀ ρ τ : ℝ, 0 < r₀ → 0 < τ →
      HasAlignedLevelStructure g u ℓ r₀ b ρ τ s₁ s₂ L c := by
  obtain ⟨ℓ, c, hℓ, hc, hmain⟩ :=
    hr.eventually_hasLevelCone_of_planarLayers h hsharp hs₁ hs₁₂ hs₂ hb hL
  refine ⟨ℓ, c, hℓ, hc, fun r₀ ρ τ hr₀ hτ x R Q δ e hal ↦ ?_⟩
  obtain ⟨-, hR, hRt, -, -, -, -, he, hloc, hQ⟩ := hal
  have hV := hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hloc hQ
  have hτ1 : τ ≤ max τ 1 := le_max_left τ 1
  filter_upwards [hmain ℓ ⟨hℓ, le_rfl⟩ x R Q hR hRt hV r₀ (max τ 1) ρ hr₀
    (lt_max_of_lt_right one_pos)] with j hj
  have hsub : verticalGoodSet (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) ℓ r₀ b ρ ⊆
      {y | ‖y‖ < ρ ∧ ∃ t, |t| < max τ 1 ∧ IsLayerGoodPoint (R j)
        (fun z ↦ zeroExtension g u (x j + R j • Q j z)) (verticalDirection m) ℓ r₀ b
          (point y t)} := by
    intro y hy
    obtain ⟨hyρ, t, ht, hgood⟩ := exists_isLayerGoodPoint_of_mem_verticalGoodSet hy
    exact ⟨hyρ, t, ht.trans_le (le_max_right τ 1), hgood⟩
  exact ⟨hj.1.mono hsub hτ1, (hj.2.mono hsub hτ1).hasLevelSlopeAbs⟩

end SerrinEpigraph
