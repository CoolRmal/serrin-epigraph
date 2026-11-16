module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Positive decomposition of bounded real functionals

This supplies the signed Riesz step needed for distributional derivatives. The two positive
functionals are constructed by the ordered Riesz extension theorem, not postulated.
-/

public section

open MeasureTheory
open scoped Topology BoundedContinuousFunction CompactlySupported

namespace SerrinEpigraph

variable {X : Type*} [TopologicalSpace X]

/-- The pointwise positive cone in a pair of bounded function spaces. -/
@[expose] def boundedPairPositiveCone : PointedCone ℝ ((X →ᵇ ℝ) × (X →ᵇ ℝ)) where
  carrier := {p | 0 ≤ p}
  zero_mem' := by
    change (0 : (X →ᵇ ℝ) × (X →ᵇ ℝ)) ≤ 0
    exact le_rfl
  add_mem' hp hq := ⟨fun x ↦ add_nonneg (hp.1 x) (hq.1 x),
    fun x ↦ add_nonneg (hp.2 x) (hq.2 x)⟩
  smul_mem' c p hp := ⟨fun x ↦ mul_nonneg c.property (hp.1 x),
    fun x ↦ mul_nonneg c.property (hp.2 x)⟩

/-- Pairs of bounded functions whose sum is constant. -/
@[expose] def constantSumSubmodule (x₀ : X) :
    Submodule ℝ ((X →ᵇ ℝ) × (X →ᵇ ℝ)) where
  carrier := {p | ∀ x, p.1 x + p.2 x = p.1 x₀ + p.2 x₀}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq x
    change (p.1 x + q.1 x) + (p.2 x + q.2 x) =
      (p.1 x₀ + q.1 x₀) + (p.2 x₀ + q.2 x₀)
    linarith [hp x, hq x]
  smul_mem' := by
    intro c p hp x
    change c * p.1 x + c * p.2 x = c * p.1 x₀ + c * p.2 x₀
    simpa only [mul_add] using congrArg (c * ·) (hp x)

/-- The linear prescription on the constant-sum subspace before positive extension. -/
@[expose] noncomputable def constantSumFunctional (x₀ : X)
    (L : (X →ᵇ ℝ) →L[ℝ] ℝ) : ((X →ᵇ ℝ) × (X →ᵇ ℝ)) →ₗ[ℝ] ℝ where
  toFun p := (‖L‖ * (p.1 x₀ + p.2 x₀) + L (p.1 - p.2)) / 2
  map_add' p q := by
    change (‖L‖ * ((p.1 x₀ + q.1 x₀) + (p.2 x₀ + q.2 x₀)) +
      L ((p.1 + q.1) - (p.2 + q.2))) / 2 = _
    rw [show (p.1 + q.1) - (p.2 + q.2) = (p.1 - p.2) + (q.1 - q.2) by abel,
      map_add]
    ring
  map_smul' c p := by
    change (‖L‖ * (c * p.1 x₀ + c * p.2 x₀) + L (c • p.1 - c • p.2)) / 2 = _
    rw [← smul_sub c p.1 p.2, map_smul]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

/-- Positivity of the prescription follows from the operator-norm estimate. -/
theorem constantSumFunctional_nonneg (x₀ : X) (L : (X →ᵇ ℝ) →L[ℝ] ℝ)
    (p : constantSumSubmodule x₀) (hp : 0 ≤ p.val) :
    0 ≤ constantSumFunctional x₀ L p.val := by
  have hc : 0 ≤ p.val.1 x₀ + p.val.2 x₀ := add_nonneg (hp.1 x₀) (hp.2 x₀)
  have hn : ‖p.val.1 - p.val.2‖ ≤ p.val.1 x₀ + p.val.2 x₀ := by
    apply (BoundedContinuousFunction.norm_le hc).mpr
    intro x
    change |p.val.1 x - p.val.2 x| ≤ p.val.1 x₀ + p.val.2 x₀
    rw [← p.property x]
    have h₁ : 0 ≤ p.val.1 x := hp.1 x
    have h₂ : 0 ≤ p.val.2 x := hp.2 x
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hL := L.le_opNorm (p.val.1 - p.val.2)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg L)
  have hlower := neg_le_abs (L (p.val.1 - p.val.2))
  change 0 ≤ (‖L‖ * (p.val.1 x₀ + p.val.2 x₀) + L (p.val.1 - p.val.2)) / 2
  rw [Real.norm_eq_abs] at hL
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- A bounded real functional is a difference of positive linear functionals, with the
sum of their values on one equal to its operator norm. -/
theorem exists_positive_decomposition (x₀ : X) (L : (X →ᵇ ℝ) →L[ℝ] ℝ) :
    ∃ A B : (X →ᵇ ℝ) →ₗ[ℝ] ℝ,
      (∀ f, 0 ≤ f → 0 ≤ A f) ∧ (∀ f, 0 ≤ f → 0 ≤ B f) ∧
      (∀ f, L f = A f - B f) ∧
      A (BoundedContinuousFunction.const X 1) +
        B (BoundedContinuousFunction.const X 1) = ‖L‖ := by
  obtain ⟨G, hG, hpos⟩ := riesz_extension
    (boundedPairPositiveCone (X := X))
    ((constantSumFunctional x₀ L).toPMap (constantSumSubmodule x₀))
    (fun p hp ↦ constantSumFunctional_nonneg x₀ L p hp) (by
      intro p
      let c := ‖p.1‖ + ‖p.2‖
      refine ⟨⟨(BoundedContinuousFunction.const X c,
        BoundedContinuousFunction.const X c), ?_⟩, ?_⟩
      · intro x
        rfl
      · change 0 ≤ (BoundedContinuousFunction.const X c + p.1,
          BoundedContinuousFunction.const X c + p.2)
        constructor
        · intro x
          change 0 ≤ c + p.1 x
          have h := BoundedContinuousFunction.norm_coe_le_norm p.1 x
          have hl := neg_le_abs (p.1 x)
          rw [Real.norm_eq_abs] at h
          dsimp [c]
          linarith [norm_nonneg p.2]
        · intro x
          change 0 ≤ c + p.2 x
          have h := BoundedContinuousFunction.norm_coe_le_norm p.2 x
          have hl := neg_le_abs (p.2 x)
          rw [Real.norm_eq_abs] at h
          dsimp [c]
          linarith [norm_nonneg p.1])
  let A := G.comp (LinearMap.inl ℝ (X →ᵇ ℝ) (X →ᵇ ℝ))
  let B := G.comp (LinearMap.inr ℝ (X →ᵇ ℝ) (X →ᵇ ℝ))
  refine ⟨A, B, ?_, ?_, ?_, ?_⟩
  · intro f hf
    exact hpos (f, 0) ⟨hf, le_rfl⟩
  · intro f hf
    exact hpos (0, f) ⟨le_rfl, hf⟩
  · intro f
    have he := hG ⟨(f, -f), by intro x; simp⟩
    change G (f, -f) = (‖L‖ * (f x₀ + (-f) x₀) + L (f - -f)) / 2 at he
    have hpair : (f, -f) = (f, (0 : X →ᵇ ℝ)) - (0, f) := by simp
    rw [hpair, map_sub] at he
    simp only [BoundedContinuousFunction.neg_apply, add_neg_cancel, mul_zero,
      zero_add, sub_neg_eq_add, map_add] at he
    change L f = G (f, 0) - G (0, f)
    linarith
  · let one := BoundedContinuousFunction.const X (1 : ℝ)
    have he := hG ⟨(one, one), by intro x; rfl⟩
    change G (one, one) = (‖L‖ * (1 + 1) + L (one - one)) / 2 at he
    have hpair : (one, one) = (one, (0 : X →ᵇ ℝ)) + (0, one) := by simp
    rw [hpair, map_add, sub_self, map_zero] at he
    change G (one, 0) + G (0, one) = ‖L‖
    linarith

/-- The inclusion of compactly supported functions in bounded functions is linear. -/
@[expose] def compactToBoundedLinear : C_c(X, ℝ) →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun := CompactlySupportedContinuousMap.toBoundedContinuousFunction
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a positive functional to compactly supported functions. -/
@[expose] def positiveCompactRestriction (A : (X →ᵇ ℝ) →ₗ[ℝ] ℝ)
    (hA : ∀ f, 0 ≤ f → 0 ≤ A f) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := A.comp compactToBoundedLinear
  monotone' := by
    intro f g hfg
    change A (compactToBoundedLinear f) ≤ A (compactToBoundedLinear g)
    have h := hA (compactToBoundedLinear (g - f)) (fun x ↦ sub_nonneg.mpr (hfg x))
    rw [map_sub, map_sub] at h
    exact sub_nonneg.mp h

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Positivity controls the total mass of the Riesz measure by the value on one. -/
theorem positiveCompactRestriction_mass_le (A : (X →ᵇ ℝ) →ₗ[ℝ] ℝ)
    (hA : ∀ f, 0 ≤ f → 0 ≤ A f) :
    RealRMK.rieszMeasure (positiveCompactRestriction A hA) Set.univ ≤
      ENNReal.ofReal (A (BoundedContinuousFunction.const X 1)) := by
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  refine iSup_le fun K ↦ iSup_le fun _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨f, hfK, hfc, -, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (Set.subset_univ K)
  let g : C_c(X, ℝ) := ⟨f, hfc⟩
  refine (RealRMK.rieszMeasure_le_of_eq_one (positiveCompactRestriction A hA)
    (f := g) (fun x ↦ (hf x).1) hK (fun x hx ↦ hfK hx)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have h := hA (BoundedContinuousFunction.const X 1 - compactToBoundedLinear g)
    (by intro x; change 0 ≤ 1 - f x; exact sub_nonneg.mpr (hf x).2)
  change A (compactToBoundedLinear g) ≤ A (BoundedContinuousFunction.const X 1)
  simpa only [map_sub, sub_nonneg] using h

/-- Signed Riesz representation as a difference of two finite regular positive measures.
The total mass bound is the operator norm, with no dimension-dependent loss. -/
theorem exists_riesz_measure_pair (x₀ : X) (L : (X →ᵇ ℝ) →L[ℝ] ℝ) :
    ∃ μ ν : Measure X, μ.Regular ∧ ν.Regular ∧
      μ Set.univ + ν Set.univ ≤ ENNReal.ofReal ‖L‖ ∧
      ∀ f : C_c(X, ℝ), L (compactToBoundedLinear f) =
        (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by
  obtain ⟨A, B, hA, hB, hL, hnorm⟩ := exists_positive_decomposition x₀ L
  refine ⟨RealRMK.rieszMeasure (positiveCompactRestriction A hA),
    RealRMK.rieszMeasure (positiveCompactRestriction B hB), inferInstance, inferInstance,
    ?_, ?_⟩
  · have h₁ := positiveCompactRestriction_mass_le A hA
    have h₂ := positiveCompactRestriction_mass_le B hB
    refine (add_le_add h₁ h₂).trans ?_
    rw [← ENNReal.ofReal_add (hA _ (fun _ ↦ zero_le_one))
      (hB _ (fun _ ↦ zero_le_one)), hnorm]
  · intro f
    rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    exact hL (compactToBoundedLinear f)

/-- A bounded real functional has an actual signed-measure representation on compact tests. -/
theorem exists_signed_riesz_measure (x₀ : X) (L : (X →ᵇ ℝ) →L[ℝ] ℝ) :
    ∃ σ : SignedMeasure X,
      σ.variation Set.univ ≤ ENNReal.ofReal ‖L‖ ∧
      ∀ f : C_c(X, ℝ), L (compactToBoundedLinear f) = ∫ᵛ x, f x ∂<•σ := by
  obtain ⟨μ, ν, -, -, hmass, hrep⟩ := exists_riesz_measure_pair x₀ L
  have hμ : μ Set.univ < ⊤ := lt_of_le_of_lt (le_self_add.trans hmass) (by finiteness)
  have hν : ν Set.univ < ⊤ := lt_of_le_of_lt (le_add_self.trans hmass) (by finiteness)
  let : IsFiniteMeasure μ := ⟨hμ⟩
  let : IsFiniteMeasure ν := ⟨hν⟩
  refine ⟨μ.toSignedMeasure - ν.toSignedMeasure, ?_, ?_⟩
  · have hvar := VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure)
      (ν := ν.toSignedMeasure)
    simp only [Measure.variation_toSignedMeasure] at hvar
    exact (hvar Set.univ).trans hmass
  · intro f
    have hiμ : μ.toSignedMeasure.Integrable (fun x ↦ f x) := by
      change Integrable (f : X → ℝ) μ.toSignedMeasure.variation
      rw [Measure.variation_toSignedMeasure]
      exact f.continuous.integrable_of_hasCompactSupport (μ := μ) f.hasCompactSupport
    have hiν : ν.toSignedMeasure.Integrable (fun x ↦ f x) := by
      change Integrable (f : X → ℝ) ν.toSignedMeasure.variation
      rw [Measure.variation_toSignedMeasure]
      exact f.continuous.integrable_of_hasCompactSupport (μ := ν) f.hasCompactSupport
    rw [VectorMeasure.integral_sub_vectorMeasure hiμ hiν,
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
    exact hrep f

end SerrinEpigraph
