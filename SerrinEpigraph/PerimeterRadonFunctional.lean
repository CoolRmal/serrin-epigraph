module

public import SerrinEpigraph.PerimeterLowerSemicontinuity
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The bounded distribution-gradient functional

The original divergence supremum bounds the distribution gradient in the uniform norm.
This constructs the actual linear functional on compactly supported C¹ vector fields and
extends it to bounded continuous vector fields by Hahn–Banach.
-/

public section

open MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

namespace SerrinEpigraph

theorem fieldDivergence_add {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F G : Space d → Space d}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (x : Space d) :
    fieldDivergence b (F + G) x = fieldDivergence b F x + fieldDivergence b G x := by
  simp [fieldDivergence, fderiv_add (hF.differentiable_one x) (hG.differentiable_one x),
    inner_add_right, Finset.sum_add_distrib]

theorem fieldDivergence_const_smul {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F : Space d → Space d}
    (hF : ContDiff ℝ 1 F) (c : ℝ) (x : Space d) :
    fieldDivergence b (c • F) x = c * fieldDivergence b F x := by
  simp [fieldDivergence, fderiv_const_smul (hF.differentiable_one x),
    inner_smul_right, Finset.mul_sum]

theorem integrable_indicator_divergence {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    (hE : MeasurableSet E) {F : Space d → Space d}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    Integrable (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) := by
  have hs : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hi := (fieldDivergence_continuous b hF).integrable_of_hasCompactSupport (μ := volume)
    (hc.of_isClosed_subset (isClosed_tsupport _) hs)
  convert hi.indicator hE using 1
  ext x
  by_cases hx : x ∈ E <;> simp [hx]

/-- Compactly supported C¹ vector fields in an open test region, with the uniform norm. -/
@[expose] def perimeterTestSubmodule {d : ℕ} (Ω : Set (Space d)) :
    Submodule ℝ (Space d →ᵇ Space d) where
  carrier := {F | ContDiff ℝ 1 (F : Space d → Space d) ∧
    HasCompactSupport (F : Space d → Space d) ∧ tsupport F ⊆ Ω}
  zero_mem' := by
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro F G hF hG
    exact ⟨hF.1.add hG.1, hF.2.1.add hG.2.1,
      (tsupport_add F G).trans (Set.union_subset hF.2.2 hG.2.2)⟩
  smul_mem' := by
    intro c F hF
    have hs := tsupport_smul_subset_right (fun _ : Space d ↦ c) (F : Space d → Space d)
    exact ⟨hF.1.const_smul c,
      hF.2.1.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hF.2.2⟩

/-- The distribution-gradient pairing is minus the divergence pairing. -/
@[expose] noncomputable def perimeterDistribution {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)}
    (hE : MeasurableSet E) (Ω : Set (Space d)) :
    perimeterTestSubmodule Ω →ₗ[ℝ] ℝ where
  toFun F := -∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F.val x
  map_add' F G := by
    change -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
      fieldDivergence b (F.val + G.val) x) = _
    simp_rw [fieldDivergence_add b F.property.1 G.property.1, mul_add]
    rw [integral_add (integrable_indicator_divergence b hE F.property.1 F.property.2.1)
      (integrable_indicator_divergence b hE G.property.1 G.property.2.1), neg_add]
  map_smul' c F := by
    change -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
      fieldDivergence b (c • F.val) x) = _
    simp_rw [fieldDivergence_const_smul b F.property.1, mul_left_comm _ c]
    rw [integral_const_mul]
    simp

/-- Each unit test is bounded by the finite perimeter in the original definition. -/
theorem norm_perimeterDistribution_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤)
    (F : perimeterTestSubmodule Ω) (hF : ∀ x, ‖F.val x‖ ≤ 1) :
    ‖perimeterDistribution b hE Ω F‖ ≤ (variationalPerimeter b E Ω).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hP).mp
  simp only [perimeterDistribution, LinearMap.coe_mk, AddHom.coe_mk, norm_neg]
  exact le_iSup_of_le (F.val : Space d → Space d) (le_iSup_of_le F.property.1
    (le_iSup_of_le F.property.2.1 (le_iSup_of_le F.property.2.2
      (le_iSup_of_le hF le_rfl))))

set_option backward.isDefEq.respectTransparency false in
/-- The distribution-gradient pairing has the uniform-norm bound furnished by perimeter. -/
theorem norm_perimeterDistribution_le_mul {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤)
    (F : perimeterTestSubmodule Ω) :
    ‖perimeterDistribution b hE Ω F‖ ≤ (variationalPerimeter b E Ω).toReal * ‖F‖ := by
  by_cases hzero : F = 0
  · rw [hzero, map_zero]
    change ‖(0 : ℝ)‖ ≤ (variationalPerimeter b E Ω).toReal * ‖(0 : Space d →ᵇ Space d)‖
    simp
  have hp : 0 < ‖F‖ := (norm_pos_iff (a := F)).mpr hzero
  let G : perimeterTestSubmodule Ω := ‖F‖⁻¹ • F
  have hG (x : Space d) : ‖G.val x‖ ≤ 1 := by
    calc
      ‖G.val x‖ = ‖F‖⁻¹ * ‖F.val x‖ := by
        simp [G, norm_smul]
      _ ≤ ‖F‖⁻¹ * ‖F‖ := mul_le_mul_of_nonneg_left
        (F.val.norm_coe_le_norm x) (inv_nonneg.mpr hp.le)
      _ = 1 := inv_mul_cancel₀ hp.ne'
  have hbound := norm_perimeterDistribution_le b hE hP G hG
  have heq : ‖perimeterDistribution b hE Ω G‖ =
      ‖perimeterDistribution b hE Ω F‖ / ‖F‖ := by
    simp [G, map_smul, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  rw [heq] at hbound
  exact (div_le_iff₀ hp).mp hbound

set_option backward.isDefEq.respectTransparency false in
/-- The continuous distribution-gradient functional, with no assumed representing measure. -/
@[expose] noncomputable def perimeterDistributionCLM {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    perimeterTestSubmodule Ω →L[ℝ] ℝ :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := perimeterTestSubmodule Ω) (F := ℝ)
    (perimeterDistribution b hE Ω) (variationalPerimeter b E Ω).toReal
    (norm_perimeterDistribution_le_mul b hE hP)

/-- The normed dual of the perimeter test submodule. Explicit parameters avoid an
instance-elaboration ambiguity between the submodule and subtype topologies. -/
noncomputable instance perimeterDualNormedGroup {d : ℕ} (Ω : Set (Space d)) :
    NormedAddCommGroup ((perimeterTestSubmodule Ω) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := perimeterTestSubmodule Ω) (F := ℝ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- The original divergence supremum is exactly the norm of its continuous functional. -/
theorem norm_perimeterDistributionCLM {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ‖perimeterDistributionCLM b hE hP‖ = (variationalPerimeter b E Ω).toReal := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := perimeterTestSubmodule Ω) (F := ℝ) (perimeterDistribution b hE Ω)
      ENNReal.toReal_nonneg (norm_perimeterDistribution_le_mul b hE hP)
  have hbound : variationalPerimeter b E Ω ≤
      ENNReal.ofReal ‖perimeterDistributionCLM b hE hP‖ := by
    refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
      iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
    let Fc : CompactlySupportedContinuousMap (Space d) (Space d) :=
      ⟨⟨F, hF.continuous⟩, hc⟩
    let Fb := Fc.toBoundedContinuousFunction
    let Ft : perimeterTestSubmodule Ω := ⟨Fb, hF, hc, hs⟩
    have hn : ‖Ft‖ ≤ 1 := (BoundedContinuousFunction.norm_le zero_le_one).mpr hunit
    have hle := (perimeterDistributionCLM b hE hP).le_opNorm Ft
    have hm := mul_le_mul_of_nonneg_left hn
      (norm_nonneg (perimeterDistributionCLM b hE hP))
    have he : ‖perimeterDistributionCLM b hE hP Ft‖ =
        ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x‖ := by
      change ‖-(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x)‖ = _
      exact norm_neg _
    rw [he] at hle
    apply ENNReal.ofReal_le_ofReal
    exact hle.trans (by simpa only [mul_one] using hm)
  exact (ENNReal.toReal_mono (by finiteness) hbound).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg _))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Finite variational perimeter gives a bounded extension of the actual gradient pairing. -/
theorem exists_perimeterDistribution_extension {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ L : (Space d →ᵇ Space d) →L[ℝ] ℝ,
      (∀ F : perimeterTestSubmodule Ω,
        L F.val = -∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F.val x) ∧
      ‖L‖ ≤ (variationalPerimeter b E Ω).toReal := by
  obtain ⟨L, hL, hn⟩ := exists_extension_norm_eq (perimeterTestSubmodule Ω)
    (perimeterDistributionCLM b hE hP)
  refine ⟨L, hL, ?_⟩
  rw [hn]
  exact LinearMap.mkContinuous_norm_le (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := perimeterTestSubmodule Ω) (F := ℝ) (perimeterDistribution b hE Ω)
    ENNReal.toReal_nonneg (norm_perimeterDistribution_le_mul b hE hP)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The Hahn–Banach extension preserves the exact perimeter norm. -/
theorem exists_perimeterDistribution_extension_exact {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ L : (Space d →ᵇ Space d) →L[ℝ] ℝ,
      (∀ F : perimeterTestSubmodule Ω,
        L F.val = -∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F.val x) ∧
      ‖L‖ = (variationalPerimeter b E Ω).toReal := by
  obtain ⟨L, hL, hn⟩ := exists_extension_norm_eq (perimeterTestSubmodule Ω)
    (perimeterDistributionCLM b hE hP)
  exact ⟨L, hL, hn.trans (norm_perimeterDistributionCLM b hE hP)⟩

end SerrinEpigraph
