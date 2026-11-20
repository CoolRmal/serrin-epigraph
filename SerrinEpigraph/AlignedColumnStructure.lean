module

public import SerrinEpigraph.AlignedFluxVertical

/-!
# Column structure over the vertical good set

Eventually, over every point of the vertical good set, the extended height at the reference
level is small and is the unique upcrossing of that level on `(-1, 1)`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **Column structure for one function.** Let the slab crossings form a level graph family over
`D`, and let `v` exceed `s₂` above the height `η' < τ` and vanish below `-η'` on the lines over
`D`. Then over every point of `D` the extended height at a level `σ ∈ [s₁, s₂]` lies in
`(-η', η')`, and it is the unique upcrossing of `σ` on `(-1, 1)`. -/
private theorem columnStructure_of_levelGraphFamily_acs {v : Space (m + 1) → ℝ}
    {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
    (hG : LevelGraphFamily v D τ s₁ s₂ T c L (fun s y ↦ slabLevelHeight v τ s y))
    {σ η' : ℝ} (hσ : σ ∈ Icc s₁ s₂) (hs₁ : 0 < s₁) (hη' : 0 < η') (hη'τ : η' < τ)
    (hup : ∀ y ∈ D, ∀ t, η' ≤ t → t ≤ τ + 1 → s₂ < v (point y t))
    (hlow : ∀ y ∈ D, ∀ t, -(τ + 1) ≤ t → t ≤ -η' → v (point y t) = 0)
    {y : Space m} (hy : y ∈ D) :
    |extendedHeight D L τ s₁ s₂ (fun s y ↦ slabLevelHeight v τ s y) σ y| < η' ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1, (σ < v (point y t) ↔
        extendedHeight D L τ s₁ s₂ (fun s y ↦ slabLevelHeight v τ s y) σ y < t) := by
  rw [hG.extendedHeight_eq hσ hy]
  have hslab : slabLevelHeight v τ σ y ∈ Ioo (-τ) τ := hG.mem_slab σ hσ y hy
  have hlev : v (point y (slabLevelHeight v τ σ y)) = σ := hG.level σ hσ y hy
  have huniq : ∀ t ∈ Ioo (-τ) τ, v (point y t) = σ → t = slabLevelHeight v τ σ y :=
    fun t ht hvt ↦ hG.unique σ hσ y hy t ht hvt
  have hcont : Continuous fun t ↦ v (point y t) := hG.continuous.comp (continuous_point y)
  have hσ0 : 0 < σ := hs₁.trans_le hσ.1
  have habs : |slabLevelHeight v τ σ y| < η' := by
    rw [abs_lt]
    constructor
    · by_contra hn
      push Not at hn
      have := hlow y hy _ (by linarith [hslab.1]) hn
      linarith
    · by_contra hn
      push Not at hn
      have := hup y hy _ hn (by linarith [hslab.2])
      linarith [hσ.2]
  refine ⟨habs, fun t ht ↦ ⟨fun hvt ↦ ?_, fun hht ↦ ?_⟩⟩
  · by_contra hn
    push Not at hn
    rcases le_or_gt t (-η') with htη | htη
    · have := hlow y hy t (by linarith [ht.1]) htη
      linarith
    · have hlow' := hlow y hy (-η') (by linarith) le_rfl
      obtain ⟨t', ht', hvt'⟩ := intermediate_value_Icc htη.le hcont.continuousOn
        (show σ ∈ Icc (v (point y (-η'))) (v (point y t)) from
          ⟨by rw [hlow']; exact hσ0.le, hvt.le⟩)
      have heq := huniq t' ⟨by linarith [ht'.1], by linarith [ht'.2, hslab.2]⟩ hvt'
      have hteq : t = slabLevelHeight v τ σ y := by linarith [ht'.2]
      rw [hteq, hlev] at hvt
      exact lt_irrefl _ hvt
  · rcases le_or_gt η' t with htη | htη
    · have := hup y hy t htη (by linarith [ht.2])
      linarith [hσ.2]
    · by_contra hn
      push Not at hn
      have hup' := hup y hy η' le_rfl (by linarith)
      obtain ⟨t', ht', hvt'⟩ := intermediate_value_Icc htη.le hcont.continuousOn
        (show σ ∈ Icc (v (point y t)) (v (point y η')) from ⟨hn, by linarith [hσ.2]⟩)
      have heq := huniq t' ⟨by linarith [ht'.1, hslab.1], by linarith [ht'.2]⟩ hvt'
      linarith [ht'.1]

theorem RigidityHypotheses.eventually_columnStructure_of_alignedHeightLimit
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0} (hτ : 0 < τ) (hs₁ : 0 < s₁) (hs₂ : s₂ < 1)
    {x : ℕ → Space (m + 1)} {R : ℕ → ℝ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {δ : ℕ → ℝ} {e : Space (m + 1)} (hal : IsAlignedSequence g u x R Q δ e)
    {φ : ℕ → ℕ} {σl a : ℕ → ℝ} {H : Space m → ℝ}
    (hlim : IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, ∀ y ∈ verticalGoodSet (R (φ j))
        (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) ℓ r₀ b ρ,
      |extendedHeight (verticalGoodSet (R (φ j))
            (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) ℓ r₀ b ρ) L τ s₁ s₂
          (fun s y ↦ slabLevelHeight
            (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) τ s y) (σl j) y| < η ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1,
        (σl j < zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) (point y t)) ↔
          extendedHeight (verticalGoodSet (R (φ j))
              (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) ℓ r₀ b ρ) L τ s₁ s₂
            (fun s y ↦ slabLevelHeight
              (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) τ s y)
            (σl j) y < t) := by
  obtain ⟨-, hR, hRt, -, -, -, -, he, hloc, hQ⟩ := hal
  obtain ⟨hφ, hσ, -, hcone, -⟩ := hlim
  have hV : VerticalPlanarLayers (fun k z ↦ zeroExtension g u (x k + R k • Q k z)) :=
    hr.verticalPlanarLayers_of_rotated h hsharp x hR hRt he hloc hQ
  have hdiff : ∀ k z, 0 < zeroExtension g u (x k + R k • Q k z) →
      DifferentiableAt ℝ (fun z ↦ zeroExtension g u (x k + R k • Q k z)) z :=
    fun k z hz ↦ h.differentiableAt_rescaled_of_pos (x k) (R k) (Q k) hz
  have hmin : 0 < min η τ := lt_min hη hτ
  set η' : ℝ := min η τ / 2
  have hη' : 0 < η' := half_pos hmin
  have hη'τ : η' < τ := (half_lt_self hmin).trans_le (min_le_right _ _)
  have hη'η : η' < η := (half_lt_self hmin).trans_le (min_le_left _ _)
  have h2 := hV.eventually_hasLevelSlope_of_cone hdiff (ρ := ρ) (c := c) hτ hs₁ hs₂ hR L
  have h3 := hV.eventually_levelGraphFamily hdiff ρ (c := c) hτ hs₁ hs₂ R L
  have h4 := hV.upper (ρ + τ + 1) η' (1 - s₂) hη' (by linarith)
  have h5 := hV.lower (ρ + τ + 1) η' hη'
  filter_upwards [hcone, hφ.tendsto_atTop.eventually (h2.and (h3.and (h4.and h5)))]
    with j hj hj'
  obtain ⟨hj2, hj3, hj4, hj5⟩ := hj'
  set D := verticalGoodSet (R (φ j))
    (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) ℓ r₀ b ρ
  have hD : D ⊆ closedBall (0 : Space m) ρ :=
    verticalGoodSet_subset_ball.trans ball_subset_closedBall
  have hG : LevelGraphFamily (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) D τ
      s₁ s₂ (R (φ j)) c L (fun s y ↦ slabLevelHeight
        (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) τ s y) :=
    hj3 D hD hj.1 (hj2 D hD hj.1 hj.2)
  have hmem : ∀ y ∈ D, ∀ t, |t| ≤ τ + 1 →
      point y t ∈ closedBall (0 : Space (m + 1)) (ρ + τ + 1) := by
    intro y hy t ht
    have hyρ : ‖y‖ < ρ := mem_ball_zero_iff.mp (verticalGoodSet_subset_ball hy)
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_point_le y t]
  have hup : ∀ y ∈ D, ∀ t, η' ≤ t → t ≤ τ + 1 →
      s₂ < zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) (point y t)) := by
    intro y hy t ht1 ht2
    have := hj4 (point y t) (hmem y hy t (abs_le.mpr ⟨by linarith, ht2⟩))
      (by rw [last_point]; exact ht1)
    linarith
  have hlow : ∀ y ∈ D, ∀ t, -(τ + 1) ≤ t → t ≤ -η' →
      zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) (point y t)) = 0 := by
    intro y hy t ht1 ht2
    exact hj5 (point y t) (hmem y hy t (abs_le.mpr ⟨ht1, by linarith⟩))
      (by rw [last_point]; exact ht2)
  intro y hy
  obtain ⟨habs, hiff⟩ :=
    columnStructure_of_levelGraphFamily_acs hG (hσ j) hs₁ hη' hη'τ hup hlow hy
  exact ⟨habs.trans hη'η, hiff⟩

end SerrinEpigraph
