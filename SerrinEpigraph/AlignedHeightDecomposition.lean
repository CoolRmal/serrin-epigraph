module

public import SerrinEpigraph.AlignedHarmonicLayers
public import SerrinEpigraph.SobolevBallCompactness

/-!
# Decomposition of the aligned harmonic layer data into four independent inputs

`RigidityHypotheses.hasCylinderTiltDecay_of_harmonicLayerData` reduces the HA0 tilt decay to
`∃ M, 0 ≤ M ∧ HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M`. This module splits that
statement into four inputs about the *normalized extended level heights* of
`SerrinEpigraph.DiffuseGoodLayers` (`alignedSeqHeight`), for fixed parameters
`ℓ r₀ b ρ τ s₁ s₂ L c` with `3/4 < ρ`, and proves (`exists_hasAlignedHarmonicLayerData_of_inputs`)
that together they give the layer data:

* **(A)** `HasAlignedHeightCompactness`: HA2/HA3 (with HA9 inputs) — along every aligned HA11
  sequence there are a subsequence, levels `σ_j ∈ [s₁, s₂]`, centers `a_j` and an `L²` limit `H`
  of the Lipschitz normalized heights, with a uniform `W^{1,2}(B_ρ)` bound `K`
  (`IsAlignedHeightLimit`);
* **(B)** `HasAlignedHeightMoments`: HA5, HA6.1, HA10 — for such data `a_j → 0` and the weighted
  height approximation `∫_{Q_{1/2}} ((t - a_j)/δ_j - H(y))² ε |∇v_j|² → 0`;
* **(C)** `HasAlignedFluxIdentification`: HA4.1 with HA1 and the HA11 weight convergence — for such
  data the normalized flux is `-σ ∇f_j ⊗ δ_{t=0}` up to `o(1)` against continuous test fields;
* **(E)** `WeakGradientLimit`: a general Sobolev fact — `L²` convergence with bounded Dirichlet
  energy to a `C¹` limit gives weak convergence of the gradients against continuous fields.

The HA9 input of (A) is recorded as `HasAlignedLevelStructure` (`HasLevelCone`,
`HasLevelSlopeAbs`).

The assembly proves harmonicity of the limit (HA4) from (A) and (C): the flux of a horizontal
gradient vanishes (FE4 with the FE3 tails), so the Dirichlet pairings of the heights vanish,
the limit is weakly harmonic (`weakHarmonic_of_sq_tendsto`) and smooth (`weyl_lemma`); the
Dirichlet bound passes to the limit (`integral_norm_fderiv_sq_le_of_bound`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian NNReal

namespace SerrinEpigraph

variable {m : ℕ}

/-! ## The normalized heights -/

/-- The normalized extended height at level `s` over `D`, with center `a` and scale `δ`. -/
def alignedHeight (v : Space (m + 1) → ℝ) (D : Set (Space m)) (L : ℝ≥0) (τ s₁ s₂ s a δ : ℝ) :
    Space m → ℝ :=
  normalizedHeight (extendedHeight D L τ s₁ s₂ (fun s' y ↦ slabLevelHeight v τ s' y) s) a δ

/-- The normalized height at index `k` of an HA11 sequence, over the vertical good set
`verticalGoodSet (R k) v_k ℓ r₀ b ρ` of the rotated rescaling `v_k`. -/
def alignedSeqHeight (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (ℓ r₀ b ρ τ s₁ s₂ : ℝ)
    (L : ℝ≥0) (x : ℕ → Space (m + 1)) (R : ℕ → ℝ)
    (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (δ : ℕ → ℝ) (k : ℕ) (s a : ℝ) :
    Space m → ℝ :=
  alignedHeight (fun z ↦ zeroExtension g u (x k + R k • Q k z))
    (verticalGoodSet (R k) (fun z ↦ zeroExtension g u (x k + R k • Q k z)) ℓ r₀ b ρ)
    L τ s₁ s₂ s a (δ k)

/-- The aligned HA11 sequences: free-boundary centers, `R → ∞`, `δ → 0`, `R δ → ∞`, vertical
cylinder tilt `δ²`, planar blow-down limit `{⟪e, ·⟫ > 0}` with `Q j e_n → e`. -/
def IsAlignedSequence (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (x : ℕ → Space (m + 1))
    (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (δ : ℕ → ℝ)
    (e : Space (m + 1)) : Prop :=
  (∀ j, x j ∈ frontier (epigraph g)) ∧ (∀ j, 0 < R j) ∧ Tendsto R atTop atTop ∧
    (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) ∧ Tendsto (fun j ↦ R j * δ j) atTop atTop ∧
    (∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
      (verticalDirection m) = δ j ^ 2) ∧
    ‖e‖ = 1 ∧
    (∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ z in K, ‖zeroExtension g u (x j + R j • z) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) z‖) atTop (𝓝 0)) ∧
    Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e)

/-! ## The four inputs -/

/-- **(D) HA9 inputs.** Along every aligned sequence, eventually the crossings of the levels
`[s₁, s₂]` over the vertical good sets satisfy the cone condition with slope `L` and the
microscopic slope bound `c ≤ |ε ∂ₜ v|` (input of (A) through
`RigidityHypotheses.exists_normalizedHeight_limit_of_cone`). -/
def HasAlignedLevelStructure (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (ℓ r₀ b ρ τ s₁ s₂ : ℝ) (L : ℝ≥0) (c : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
    ∀ᶠ j in atTop,
      HasLevelCone (fun z ↦ zeroExtension g u (x j + R j • Q j z))
        (verticalGoodSet (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) ℓ r₀ b ρ)
        τ s₁ s₂ L ∧
      HasLevelSlopeAbs (fun z ↦ zeroExtension g u (x j + R j • Q j z))
        (verticalGoodSet (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) ℓ r₀ b ρ)
        τ s₁ s₂ (R j) c

/-- The output of HA2/HA3 along a subsequence `φ`: levels `σ_j ∈ [s₁, s₂]`, centers `a_j`
(averages of the extended heights over `B_ρ`), the HA9 inputs eventually, Lipschitz normalized
heights `f_j = alignedSeqHeight … (φ j) (σ_j) (a_j)` with `∫_{B_ρ} (f_j² + |∇f_j|²) ≤ K`, and an
`L²(B_r)` limit `H` for every `r < ρ`. -/
def IsAlignedHeightLimit (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (ℓ r₀ b ρ τ s₁ s₂ : ℝ)
    (L : ℝ≥0) (c K : ℝ) (x : ℕ → Space (m + 1)) (R : ℕ → ℝ)
    (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (δ : ℕ → ℝ) (φ : ℕ → ℕ) (σl a : ℕ → ℝ)
    (H : Space m → ℝ) : Prop :=
  StrictMono φ ∧ (∀ j, σl j ∈ Icc s₁ s₂) ∧
    (∀ j, a j = ⨍ z in ball (0 : Space m) ρ,
      extendedHeight (verticalGoodSet (R (φ j))
          (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) ℓ r₀ b ρ) L τ s₁ s₂
        (fun s y ↦ slabLevelHeight (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
          τ s y) (σl j) z) ∧
    (∀ᶠ j in atTop,
      HasLevelCone (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
        (verticalGoodSet (R (φ j)) (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
          ℓ r₀ b ρ) τ s₁ s₂ L ∧
      HasLevelSlopeAbs (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
        (verticalGoodSet (R (φ j)) (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
          ℓ r₀ b ρ) τ s₁ s₂ (R (φ j)) c) ∧
    (∀ j, ∃ C, LipschitzWith C (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j)
      (a j))) ∧
    (∀ j, ∫ y in ball (0 : Space m) ρ,
      (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j) y ^ 2 +
        ‖fderiv ℝ (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y‖ ^ 2)
          ≤ K) ∧
    (∀ r < ρ, MemLp H 2 (volume.restrict (ball (0 : Space m) r))) ∧
    ∀ r < ρ, Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
      (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j) y - H y) ^ 2)
        atTop (𝓝 0)

/-- **(A) HA2/HA3 normalized-height compactness** (from (D) by
`RigidityHypotheses.exists_normalizedHeight_limit_of_cone`, with the tilt budget `Θ = 2ᵐ` of the
cylinder normalization; the Lipschitz bound of the extended heights comes from
`VerticalPlanarLayers.eventually_levelGraphFamily`, `eventually_hasLevelSlope_of_cone` and
`extendedHeight_lipschitzWith` after passing to a tail). -/
def HasAlignedHeightCompactness (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (ℓ r₀ b ρ τ s₁ s₂ : ℝ) (L : ℝ≥0) (c K : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
    ∃ (φ : ℕ → ℕ) (σl a : ℕ → ℝ) (H : Space m → ℝ),
      IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H

/-- **(B) HA6.1 (with HA5, HA10, HA1).** For height-limit data along an aligned sequence, the
centers tend to `0` and the weighted height approximation holds on `Q_{1/2}`. -/
def HasAlignedHeightMoments (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (ℓ r₀ b ρ τ s₁ s₂ : ℝ) (L : ℝ≥0) (c K : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
    ∀ (φ : ℕ → ℕ) (σl a : ℕ → ℝ) (H : Space m → ℝ),
      IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H →
      Tendsto a atTop (𝓝 0) ∧
      Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 2),
        ((z (Fin.last m) - a j) / δ (φ j) - H (horizontal z)) ^ 2 *
          ((R (φ j))⁻¹ * ‖gradient (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z‖ ^ 2)) atTop (𝓝 0)

/-- **(C) HA4.1 flux identification (with HA1 and the HA11 weight convergence
`ε ∂ₜ v(y, h_s(y)) → √(2W(s))`).** For height-limit data along an aligned sequence, the
normalized flux `F_j = ε ∂ₜ v_j ∇_y v_j / δ_j` agrees with `-σ ∇f_j ⊗ δ_{t=0}` up to `o(1)` against
continuous `ζ` supported in `B_{3/4}` and continuous `ψ` supported in `(-1/2, 1/2)`. -/
def HasAlignedFluxIdentification (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ : ℝ)
    (ℓ r₀ b ρ τ s₁ s₂ : ℝ) (L : ℝ≥0) (c K : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ) (e : Space (m + 1)), IsAlignedSequence g u x R Q δ e →
    ∀ (φ : ℕ → ℕ) (σl a : ℕ → ℝ) (H : Space m → ℝ),
      IsAlignedHeightLimit g u ℓ r₀ b ρ τ s₁ s₂ L c K x R Q δ φ σl a H →
      ∀ ζ : Space m → Space m, Continuous ζ → tsupport ζ ⊆ ball (0 : Space m) (3 / 4) →
      ∀ ψ : ℝ → ℝ, Continuous ψ → tsupport ψ ⊆ Ioo (-(1 / 2)) (1 / 2) →
      Tendsto (fun j ↦ (∫ z, ψ (z (Fin.last m)) * inner ℝ (ζ (horizontal z))
        (((δ (φ j))⁻¹ * (R (φ j))⁻¹ * verticalDerivative (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z) •
          horizontal (gradient (fun z ↦ zeroExtension g u
            (x (φ j) + R (φ j) • Q (φ j) z)) z))) +
        σ * ψ 0 * ∫ y, inner ℝ (ζ y)
          (gradient (alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j)) y))
        atTop (𝓝 0)

/-- **(E) Weak convergence of gradients (general Sobolev fact).** Lipschitz functions converging
in `L²(B_R)` to a function `C¹` on `B_R`, with bounded Dirichlet energy on `B_R`, have gradients
converging weakly against continuous fields supported in `B_r`, `r < R`. -/
def WeakGradientLimit (m : ℕ) : Prop :=
  ∀ (f : ℕ → Space m → ℝ) (H : Space m → ℝ) (K r R : ℝ), r < R →
    (∀ j, ∃ C, LipschitzWith C (f j)) → ContDiffOn ℝ 1 H (ball (0 : Space m) R) →
    MemLp H 2 (volume.restrict (ball (0 : Space m) R)) →
    (∀ j, ∫ y in ball (0 : Space m) R, ‖fderiv ℝ (f j) y‖ ^ 2 ≤ K) →
    Tendsto (fun j ↦ ∫ y in ball (0 : Space m) R, (f j y - H y) ^ 2) atTop (𝓝 0) →
    ∀ ζ : Space m → Space m, Continuous ζ → tsupport ζ ⊆ ball (0 : Space m) r →
      Tendsto (fun j ↦ ∫ y, inner ℝ (ζ y) (gradient (f j) y)) atTop
        (𝓝 (∫ y, inner ℝ (ζ y) (gradient H y)))

/-! ## Auxiliary facts -/

/-- A function smooth on `B_{3/4}` agrees near every point of `B_{5/8}` with a global `C²`
function (a bump cutoff). -/
theorem exists_contDiff_eventuallyEq_ball {H' : Space m → ℝ}
    (hH' : ContDiffOn ℝ (⊤ : ℕ∞) H' (ball (0 : Space m) (3 / 4))) :
    ∃ H'' : Space m → ℝ, ContDiff ℝ 2 H'' ∧
      ∀ y ∈ ball (0 : Space m) (5 / 8), H'' =ᶠ[𝓝 y] H' := by
  let bκ : ContDiffBump (0 : Space m) := ⟨5 / 8, 11 / 16, by norm_num, by norm_num⟩
  have htsκ : tsupport (⇑bκ) = closedBall 0 (11 / 16) := bκ.tsupport_eq
  refine ⟨fun y ↦ bκ y * H' y, ?_, fun y hy ↦ ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun y ↦ ?_
    by_cases hy : y ∈ ball (0 : Space m) (3 / 4)
    · exact (bκ.contDiff.contDiffAt).mul
        ((hH'.contDiffAt (isOpen_ball.mem_nhds hy)).of_le (by norm_num))
    · have hyt : y ∉ tsupport (⇑bκ) := by
        rw [htsκ, mem_closedBall, dist_zero_right]
        intro hle
        apply hy
        rw [mem_ball, dist_zero_right]
        linarith
      have hev : (fun y ↦ bκ y * H' y) =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport (⇑bκ)).isOpen_compl.mem_nhds hyt] with z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    have h1 : bκ z = 1 := bκ.one_of_mem_closedBall (ball_subset_closedBall hz)
    simp [h1]

theorem integrableOn_sq_of_lipschitz {d : ℕ} {f : Space d → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {r : ℝ} : IntegrableOn (fun y ↦ f y ^ 2) (ball (0 : Space d) r) :=
  ((hf.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
    ball_subset_closedBall

theorem integrableOn_fderiv_sq_of_lipschitz {d : ℕ} {f : Space d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) {r : ℝ} :
    IntegrableOn (fun y ↦ ‖fderiv ℝ f y‖ ^ 2) (ball (0 : Space d) r) := by
  refine Measure.integrableOn_of_bounded (M := (C : ℝ) ^ 2) measure_ball_lt_top.ne
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable ?_
  refine Eventually.of_forall fun y ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2

/-! ## The assembly -/

variable {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **Assembly.** The four inputs (A), (B), (C), (E) give the aligned harmonic layer data with
`M = 2 max K 0`. -/
theorem RigidityHypotheses.exists_hasAlignedHarmonicLayerData_of_inputs
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {ℓ r₀ b ρ τ s₁ s₂ c K : ℝ} {L : ℝ≥0} (hρ : 3 / 4 < ρ)
    (hA : HasAlignedHeightCompactness g u ℓ r₀ b ρ τ s₁ s₂ L c K)
    (hB : HasAlignedHeightMoments g u ℓ r₀ b ρ τ s₁ s₂ L c K)
    (hC : HasAlignedFluxIdentification g u (phasePrimitive f 1) ℓ r₀ b ρ τ s₁ s₂ L c K)
    (hE : WeakGradientLimit m) :
    ∃ M : ℝ, 0 ≤ M ∧ HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M := by
  refine ⟨2 * max K 0, by positivity, ?_⟩
  intro x R Q δ e hx hR hRt hδ hδ0 hRδ htilt he hloc hQ
  have hal : IsAlignedSequence g u x R Q δ e := ⟨hx, hR, hRt, hδ, hδ0, hRδ, htilt, he, hloc, hQ⟩
  obtain ⟨φ, σl, a, H, hlim⟩ := hA x R Q δ e hal
  obtain ⟨hB1, hB2⟩ := hB x R Q δ e hal φ σl a H hlim
  have hCC := hC x R Q δ e hal φ σl a H hlim
  obtain ⟨hφ, -, -, -, hLip, hK, hHL2, hconv⟩ := hlim
  set fj : ℕ → Space m → ℝ := fun j ↦
    alignedSeqHeight g u ℓ r₀ b ρ τ s₁ s₂ L x R Q δ (φ j) (σl j) (a j) with hfj
  have hσ : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  -- the vertical cutoff
  let bψ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 3 / 8, by norm_num, by norm_num⟩
  have htsψ : tsupport (⇑bψ) = closedBall 0 (3 / 8) := bψ.tsupport_eq
  have hψone : ∀ t : ℝ, |t| < 1 / 4 → bψ t = 1 := fun t ht ↦
    bψ.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact ht.le)
  have hψ0 : bψ 0 = 1 := hψone 0 (by norm_num)
  have hdψ : ∀ t : ℝ, |t| < 1 / 4 → deriv (⇑bψ) t = 0 := fun t ht ↦ by
    have hev : (⇑bψ) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      have hmem : t ∈ ball (0 : ℝ) (1 / 4) := by
        rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
        exact ht
      filter_upwards [isOpen_ball.mem_nhds hmem] with s hs
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
      exact hψone s hs
    rw [hev.deriv_eq, deriv_const]
  have hψs : tsupport (⇑bψ) ⊆ Ioo (-(1 / 2)) (1 / 2) := by
    rw [htsψ]
    intro t ht
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hψs1 : tsupport (⇑bψ) ⊆ Ioo (-1) 1 :=
    hψs.trans (Ioo_subset_Ioo (by norm_num) (by norm_num))
  -- step 1: the Dirichlet pairings of the heights vanish
  have hweak : ∀ ψs : Space m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψs → HasCompactSupport ψs →
      tsupport ψs ⊆ ball (0 : Space m) (3 / 4) →
        Tendsto (fun j ↦ ∫ y, inner ℝ (gradient (fj j) y) (gradient ψs y)) atTop (𝓝 0) := by
    intro ψs hψsm hcψs hsubs
    have hψs1' : ContDiff ℝ 1 ψs := hψsm.of_le (by norm_num)
    have hgs : tsupport (gradient ψs) ⊆ ball (0 : Space m) (3 / 4) := by
      refine (closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport ψs)).trans hsubs
      by_contra hn
      exact hy (ha6_gradient_eq_zero_of_notMem_tsupport hn)
    have h1 := hCC (gradient ψs) (ha6_continuous_gradient hψs1') hgs (⇑bψ) bψ.continuous hψs
    have h2 := (hr.tendsto_flux_gradient_of_aligned h hsharp x hR hRt hδ hδ0 hRδ he hloc hQ
      hψs1' hcψs (hsubs.trans (ball_subset_ball (by norm_num))) bψ.contDiff
      bψ.hasCompactSupport hψs1 (c₀ := 1 / 4) (by norm_num) hdψ).comp hφ.tendsto_atTop
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    have h4 : Tendsto (fun j ↦ phasePrimitive f 1 *
        ∫ y, inner ℝ (gradient ψs y) (gradient (fj j) y)) atTop (𝓝 0) := by
      refine h3.congr fun j ↦ ?_
      simp only [Function.comp, hψ0, mul_one, hfj]
      ring
    have h5 := h4.const_mul (phasePrimitive f 1)⁻¹
    rw [mul_zero] at h5
    refine h5.congr fun j ↦ ?_
    rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
    exact integral_congr_ae (Eventually.of_forall fun y ↦ real_inner_comm _ _)
  -- step 2: the limit is weakly harmonic, hence smooth (Weyl)
  have hvw : IsVeryWeaklyHarmonicOn (ball (0 : Space m) (3 / 4)) H :=
    weakHarmonic_of_sq_tendsto (x := (0 : Space m)) (R := 3 / 4) (f := fj) (fun j ↦ hLip j)
      (fun r hr' ↦ hHL2 r (hr'.trans hρ)) (fun r hr' ↦ hconv r (hr'.trans hρ)) hweak
  obtain ⟨H', hH'c, hΔ', hae⟩ := weyl_lemma isOpen_ball hvw
  have haeB : ∀ᵐ y, y ∈ ball (0 : Space m) (3 / 4) → H y = H' y :=
    (ae_restrict_iff' measurableSet_ball).mp hae
  have hH'1 : ContDiffOn ℝ 1 H' (ball (0 : Space m) (3 / 4)) := hH'c.of_le (by norm_num)
  obtain ⟨H'', hH''c, hH''ev⟩ := exists_contDiff_eventuallyEq_ball hH'c
  have hH''eq : ∀ y ∈ ball (0 : Space m) (5 / 8), H'' y = H' y := fun y hy ↦
    (hH''ev y hy).eq_of_nhds
  have hgrad'' : ∀ y ∈ ball (0 : Space m) (5 / 8), gradient H'' y = gradient H' y :=
    fun y hy ↦ by simp only [gradient, (hH''ev y hy).fderiv_eq]
  have hhalf : ball (0 : Space m) (1 / 2) ⊆ ball (0 : Space m) (5 / 8) :=
    ball_subset_ball (by norm_num)
  have h58 : ball (0 : Space m) (5 / 8) ⊆ ball (0 : Space m) (3 / 4) :=
    ball_subset_ball (by norm_num)
  have hH''H : ∀ᵐ y, y ∈ ball (0 : Space m) (1 / 2) → H'' y = H y := by
    filter_upwards [haeB] with y hy hyh
    rw [hH''eq y (hhalf hyh), hy (h58 (hhalf hyh))]
  -- convergence to `H'` and energy bounds
  have hconvH' : ∀ r ≤ 3 / 4, Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
      (fj j y - H' y) ^ 2) atTop (𝓝 0) := by
    intro r hr'
    refine (hconv r (hr'.trans_lt hρ)).congr fun j ↦ setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [haeB] with y hy hyr
    rw [hy (ball_subset_ball hr' hyr)]
  have hKr : ∀ r ≤ ρ, ∀ j, ∫ y in ball (0 : Space m) r, ‖fderiv ℝ (fj j) y‖ ^ 2 ≤ K := by
    intro r hr' j
    obtain ⟨C, hC⟩ := hLip j
    calc (∫ y in ball (0 : Space m) r, ‖fderiv ℝ (fj j) y‖ ^ 2)
        ≤ ∫ y in ball (0 : Space m) ρ, ‖fderiv ℝ (fj j) y‖ ^ 2 :=
          setIntegral_mono_set (integrableOn_fderiv_sq_of_lipschitz hC)
            (Eventually.of_forall fun y ↦ sq_nonneg _)
            (Eventually.of_forall (ball_subset_ball hr'))
      _ ≤ ∫ y in ball (0 : Space m) ρ, (fj j y ^ 2 + ‖fderiv ℝ (fj j) y‖ ^ 2) :=
          setIntegral_mono_on (integrableOn_fderiv_sq_of_lipschitz hC)
            ((integrableOn_sq_of_lipschitz hC).add (integrableOn_fderiv_sq_of_lipschitz hC))
            measurableSet_ball fun y _ ↦ by nlinarith [sq_nonneg (fj j y)]
      _ ≤ K := hK j
  have hK0 : 0 ≤ K := (setIntegral_nonneg measurableSet_ball fun y _ ↦ by positivity).trans
    (hK 0)
  -- the Dirichlet bound of the limit
  have hDir : (∫ y in ball (0 : Space m) (1 / 2), ‖fderiv ℝ H' y‖ ^ 2) ≤ K :=
    integral_norm_fderiv_sq_le_of_bound (x := (0 : Space m)) (r := 1 / 2) (R := 3 / 4)
      (by norm_num) (fun j ↦ hLip j) hH'1 (hconvH' (1 / 2) (by norm_num))
      (hKr (1 / 2) (by linarith))
  refine ⟨φ, hφ, H'', ball (0 : Space m) (5 / 8), a, isOpen_ball,
    closedBall_subset_ball (by norm_num), hH''c,
    fun y hy ↦ by
      rw [(laplacian_congr_nhds (hH''ev y hy)).eq_of_nhds]
      exact hΔ' y (h58 hy), ?_, ?_, hB1, ?_, ?_⟩
  · -- `L²` bound
    have hHint : IntegrableOn (fun y ↦ H y ^ 2) (ball (0 : Space m) (1 / 2)) :=
      (hHL2 (1 / 2) (by linarith)).integrable_sq
    have hbound : ∀ j, (∫ y in ball (0 : Space m) (1 / 2), H y ^ 2) ≤
        2 * K + 2 * ∫ y in ball (0 : Space m) (1 / 2), (fj j y - H y) ^ 2 := by
      intro j
      obtain ⟨C, hC⟩ := hLip j
      have hfint := integrableOn_sq_of_lipschitz hC (r := 1 / 2)
      have hdint : IntegrableOn (fun y ↦ (fj j y - H y) ^ 2) (ball (0 : Space m) (1 / 2)) := by
        refine ((hfint.const_mul 2).add (hHint.const_mul 2)).mono'
          ((hC.continuous.aestronglyMeasurable.sub
            (hHL2 (1 / 2) (by linarith)).aestronglyMeasurable).pow 2) ?_
        refine Eventually.of_forall fun y ↦ ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        show (fj j y - H y) ^ 2 ≤ 2 * fj j y ^ 2 + 2 * H y ^ 2
        nlinarith [sq_nonneg (fj j y + H y)]
      have hf2 : (∫ y in ball (0 : Space m) (1 / 2), fj j y ^ 2) ≤ K := by
        calc (∫ y in ball (0 : Space m) (1 / 2), fj j y ^ 2)
            ≤ ∫ y in ball (0 : Space m) ρ, fj j y ^ 2 :=
              setIntegral_mono_set (integrableOn_sq_of_lipschitz hC)
                (Eventually.of_forall fun y ↦ sq_nonneg _)
                (Eventually.of_forall (ball_subset_ball (by linarith)))
          _ ≤ ∫ y in ball (0 : Space m) ρ, (fj j y ^ 2 + ‖fderiv ℝ (fj j) y‖ ^ 2) :=
              setIntegral_mono_on (integrableOn_sq_of_lipschitz hC)
                ((integrableOn_sq_of_lipschitz hC).add (integrableOn_fderiv_sq_of_lipschitz hC))
                measurableSet_ball fun y _ ↦ by nlinarith [sq_nonneg ‖fderiv ℝ (fj j) y‖]
          _ ≤ K := hK j
      have hsum : IntegrableOn (fun y ↦ 2 * fj j y ^ 2 + 2 * (fj j y - H y) ^ 2)
          (ball (0 : Space m) (1 / 2)) := (hfint.const_mul 2).add (hdint.const_mul 2)
      calc (∫ y in ball (0 : Space m) (1 / 2), H y ^ 2)
          ≤ ∫ y in ball (0 : Space m) (1 / 2), (2 * fj j y ^ 2 + 2 * (fj j y - H y) ^ 2) :=
            setIntegral_mono_on hHint hsum
              measurableSet_ball fun y _ ↦ by nlinarith [sq_nonneg (fj j y + (fj j y - H y))]
        _ = 2 * (∫ y in ball (0 : Space m) (1 / 2), fj j y ^ 2) +
            2 * ∫ y in ball (0 : Space m) (1 / 2), (fj j y - H y) ^ 2 := by
            rw [integral_add (hfint.const_mul 2) (hdint.const_mul 2), integral_const_mul,
              integral_const_mul]
        _ ≤ 2 * K + 2 * ∫ y in ball (0 : Space m) (1 / 2), (fj j y - H y) ^ 2 := by
            linarith
    have hlimK : Tendsto (fun j ↦ 2 * K + 2 * ∫ y in ball (0 : Space m) (1 / 2),
        (fj j y - H y) ^ 2) atTop (𝓝 (2 * K)) := by
      have := (tendsto_const_nhds (x := 2 * K)).add ((hconv (1 / 2) (by linarith)).const_mul 2)
      rwa [mul_zero, add_zero] at this
    have hH2 : (∫ y in ball (0 : Space m) (1 / 2), H y ^ 2) ≤ 2 * K :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hlimK hbound
    calc (∫ y in ball (0 : Space m) (1 / 2), H'' y ^ 2)
        = ∫ y in ball (0 : Space m) (1 / 2), H y ^ 2 :=
          setIntegral_congr_ae measurableSet_ball (by
            filter_upwards [hH''H] with y hy hyh
            rw [hy hyh])
      _ ≤ 2 * K := hH2
      _ ≤ 2 * max K 0 := by linarith [le_max_left K 0]
  · -- Dirichlet bound
    calc (∫ y in ball (0 : Space m) (1 / 2), ‖gradient H'' y‖ ^ 2)
        = ∫ y in ball (0 : Space m) (1 / 2), ‖fderiv ℝ H' y‖ ^ 2 := by
          refine setIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
          rw [hgrad'' y (hhalf hy), gradient, LinearIsometryEquiv.norm_map]
      _ ≤ K := hDir
      _ ≤ 2 * max K 0 := by linarith [le_max_left K 0]
  · -- weighted height approximation
    refine hB2.congr fun j ↦ setIntegral_congr_ae (isOpen_tiltCylinder _ _).measurableSet ?_
    filter_upwards [ae_comp_horizontal hH''H] with z hz hzQ
    have h1 : horizontal z ∈ ball (0 : Space m) (1 / 2) := by
      rw [mem_ball, dist_zero_right]
      exact (mem_tiltCylinder_vertical_iff.mp hzQ).1
    rw [hz h1]
  · -- flux limit
    intro ζ hζ hζs ψ hψ hψs'
    have h1 := hCC ζ hζ (hζs.trans (ball_subset_ball (by norm_num))) ψ hψ hψs'
    obtain ⟨C0, -⟩ := hLip 0
    have hH'L2 : MemLp H' 2 (volume.restrict (ball (0 : Space m) (3 / 4))) :=
      (hHL2 (3 / 4) hρ).ae_eq hae
    have h2 := hE fj H' K (1 / 2) (3 / 4) (by norm_num) (fun j ↦ hLip j) hH'1 hH'L2
      (hKr (3 / 4) hρ.le) (hconvH' (3 / 4) le_rfl) ζ hζ hζs
    have h3 := h1.sub (h2.const_mul (phasePrimitive f 1 * ψ 0))
    have h4 : (∫ y, inner ℝ (ζ y) (gradient H' y)) = ∫ y, inner ℝ (ζ y) (gradient H'' y) := by
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      by_cases hy : y ∈ ball (0 : Space m) (1 / 2)
      · simp only
        rw [hgrad'' y (hhalf hy)]
      · have : ζ y = 0 := image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hζs h'))
        simp [this]
    rw [h4, zero_sub] at h3
    convert h3 using 1
    · funext j
      simp only [hfj]
      ring
    · ring_nf

end SerrinEpigraph
