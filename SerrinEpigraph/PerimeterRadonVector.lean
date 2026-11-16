module

public import SerrinEpigraph.PerimeterRadonFunctional
public import SerrinEpigraph.PerimeterRadonSigned
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A positive lift for Euclidean vector-valued Riesz representation

The lift to the closed unit ball preserves the Euclidean norm and avoids a dimension factor
in the resulting total-variation estimate.
-/

public section

open MeasureTheory
open scoped Topology BoundedContinuousFunction CompactlySupported

namespace SerrinEpigraph

/-- The compact Euclidean closed unit ball, including in dimension zero. -/
abbrev PerimeterUnitBall (d : ℕ) := Metric.closedBall (0 : Space d) 1

/-- A vector of norm at most one whose pairing with a given vector is its negative norm. -/
theorem exists_unitBall_inner_eq_neg_norm {d : ℕ} (v : Space d) :
    ∃ w : PerimeterUnitBall d, inner ℝ v w.val = -‖v‖ := by
  by_cases hv : v = 0
  · subst v
    exact ⟨⟨0, by simp⟩, by simp⟩
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨⟨-‖v‖⁻¹ • v, ?_⟩, ?_⟩
  · simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_neg,
      norm_inv, norm_norm, inv_mul_cancel₀ hn]
    exact le_rfl
  · rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

/-- Nonnegativity of all lifted evaluations bounds the vector field by the constant part. -/
theorem norm_le_of_unitBall_eval_nonneg {d : ℕ} {X : Type*} [TopologicalSpace X]
    (x₀ : X) (F : X →ᵇ Space d) (c : ℝ)
    (h : ∀ x (v : PerimeterUnitBall d), 0 ≤ c + inner ℝ (F x) v.val) :
    ‖F‖ ≤ c := by
  have hc : 0 ≤ c := by simpa using h x₀ ⟨0, by simp⟩
  apply (BoundedContinuousFunction.norm_le hc).mpr
  intro x
  obtain ⟨v, hv⟩ := exists_unitBall_inner_eq_neg_norm (F x)
  have hp := h x v
  rw [hv] at hp
  linarith

/-- Embed a vector field and a constant as scalar evaluations on the unit ball. -/
@[expose] noncomputable def unitBallLift {d : ℕ} {X : Type*} [TopologicalSpace X] :
    ((X →ᵇ Space d) × ℝ) →ₗ[ℝ] ((X × PerimeterUnitBall d) →ᵇ ℝ) where
  toFun p := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q ↦ p.2 + inner ℝ (p.1 q.1) q.2.val)
    (by fun_prop) (|p.2| + ‖p.1‖) (by
      intro q
      calc
        ‖p.2 + inner ℝ (p.1 q.1) q.2.val‖ ≤ |p.2| +
            |inner ℝ (p.1 q.1) q.2.val| := norm_add_le _ _
        _ ≤ |p.2| + ‖p.1 q.1‖ * ‖q.2.val‖ :=
          add_le_add (le_refl _) (abs_real_inner_le_norm _ _)
        _ ≤ |p.2| + ‖p.1‖ := by
          have hv : ‖q.2.val‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using q.2.property
          have hprod := mul_le_mul (p.1.norm_coe_le_norm q.1) hv
            (norm_nonneg _) (norm_nonneg _)
          simpa only [mul_one] using add_le_add (le_refl |p.2|) hprod)
  map_add' p q := by ext x; simp [inner_add_left]; ring
  map_smul' c p := by ext x; simp [inner_smul_left]; ring

@[simp] theorem unitBallLift_apply {d : ℕ} {X : Type*} [TopologicalSpace X]
    (p : (X →ᵇ Space d) × ℝ) (q : X × PerimeterUnitBall d) :
    unitBallLift p q = p.2 + inner ℝ (p.1 q.1) q.2.val := rfl

/-- The lifted scalar function determines both the field and the constant. -/
theorem unitBallLift_injective {d : ℕ} {X : Type*} [TopologicalSpace X] (x₀ : X) :
    Function.Injective (unitBallLift (d := d) (X := X)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have hc : p.2 = 0 := by
    have he := congrArg (fun f : (X × PerimeterUnitBall d) →ᵇ ℝ ↦
      f (x₀, ⟨0, by simp⟩)) hp
    simpa using he
  have hf : ‖p.1‖ ≤ 0 := by
    apply norm_le_of_unitBall_eval_nonneg x₀ p.1 0
    intro x v
    have he := congrArg (fun f : (X × PerimeterUnitBall d) →ᵇ ℝ ↦ f (x, v)) hp
    simpa [hc] using he.ge
  exact Prod.ext (norm_le_zero_iff.mp hf) hc

/-- The pointwise positive cone of bounded real functions. -/
@[expose] def boundedPositiveCone {X : Type*} [TopologicalSpace X] :
    PointedCone ℝ (X →ᵇ ℝ) where
  carrier := {f | ∀ x, 0 ≤ f x}
  zero_mem' := fun _ ↦ le_rfl
  add_mem' hf hg := fun x ↦ add_nonneg (hf x) (hg x)
  smul_mem' c _f hf := fun x ↦ mul_nonneg c.property (hf x)

set_option backward.isDefEq.respectTransparency false in
/-- A bounded vector functional admits a positive scalar lift whose mass is its norm. -/
theorem exists_positive_unitBall_lift {d : ℕ} {X : Type*} [TopologicalSpace X]
    (x₀ : X) (L : (X →ᵇ Space d) →L[ℝ] ℝ) :
    ∃ A : ((X × PerimeterUnitBall d) →ᵇ ℝ) →ₗ[ℝ] ℝ,
      (∀ f, 0 ≤ f → 0 ≤ A f) ∧
      ∀ F c, A (unitBallLift (F, c)) = L F + ‖L‖ * c := by
  let H := unitBallLift (d := d) (X := X)
  let e := LinearEquiv.ofInjective H (unitBallLift_injective x₀)
  let T : ((X →ᵇ Space d) × ℝ) →ₗ[ℝ] ℝ :=
    L.toLinearMap.comp (LinearMap.fst ℝ (X →ᵇ Space d) ℝ) +
      ‖L‖ • LinearMap.snd ℝ (X →ᵇ Space d) ℝ
  let p : ((X × PerimeterUnitBall d) →ᵇ ℝ) →ₗ.[ℝ] ℝ :=
    ⟨H.range, T.comp e.symm.toLinearMap⟩
  obtain ⟨A, hA, hpos⟩ := riesz_extension boundedPositiveCone p (by
    intro f hf
    let z := e.symm f
    have he : H z = f.val := LinearEquiv.ofInjective_symm_apply H f
    have hn : ‖z.1‖ ≤ z.2 := by
      apply norm_le_of_unitBall_eval_nonneg x₀ z.1 z.2
      intro x v
      have h := hf (x, v)
      rw [← he] at h
      exact h
    have hb := L.le_opNorm z.1
    have hl := neg_le_abs (L z.1)
    have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg L)
    change 0 ≤ L z.1 + ‖L‖ * z.2
    rw [Real.norm_eq_abs] at hb
    linarith) (by
    intro f
    refine ⟨e (0, ‖f‖), ?_⟩
    intro x
    change 0 ≤ ‖f‖ + inner ℝ (0 : Space d) x.2.val + f x
    rw [inner_zero_left, add_zero]
    have hn := f.norm_coe_le_norm x
    have hl := neg_le_abs (f x)
    rw [Real.norm_eq_abs] at hn
    linarith)
  refine ⟨A, hpos, ?_⟩
  intro F c
  have h := hA (e (F, c))
  change A (H (F, c)) = T (e.symm (e (F, c))) at h
  simpa only [LinearEquiv.symm_apply_apply, T, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, ContinuousLinearMap.coe_coe, smul_eq_mul] using h

instance perimeterUnitBallCompactSpace (d : ℕ) : CompactSpace (PerimeterUnitBall d) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space d) 1)

/-- A compact vector test gives a compact scalar test on the product with the unit ball. -/
@[expose] noncomputable def unitBallCompactLift {d : ℕ} {X : Type*} [TopologicalSpace X]
    (F : C_c(X, Space d)) : C_c(X × PerimeterUnitBall d, ℝ) where
  toFun q := inner ℝ (F q.1) q.2.val
  continuous_toFun := by fun_prop
  hasCompactSupport' := by
    have hs : Function.support (fun q : X × PerimeterUnitBall d ↦
        inner ℝ (F q.1) q.2.val) ⊆ tsupport F ×ˢ Set.univ := by
      intro q hq
      refine ⟨?_, Set.mem_univ _⟩
      by_contra hn
      apply hq
      change inner ℝ (F q.1) q.2.val = 0
      rw [image_eq_zero_of_notMem_tsupport hn, inner_zero_left]
    exact (F.hasCompactSupport.prod isCompact_univ).of_isClosed_subset
      (isClosed_tsupport _) (closure_minimal hs ((isClosed_tsupport F).prod isClosed_univ))

@[simp] theorem unitBallCompactLift_apply {d : ℕ} {X : Type*} [TopologicalSpace X]
    (F : C_c(X, Space d)) (q : X × PerimeterUnitBall d) :
    unitBallCompactLift F q = inner ℝ (F q.1) q.2.val := rfl

/-- Positive Riesz representation of the vector functional on the compact ball lift. -/
theorem exists_unitBall_riesz_measure {d : ℕ} {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x₀ : X) (L : (X →ᵇ Space d) →L[ℝ] ℝ) :
    ∃ μ : Measure (X × PerimeterUnitBall d), μ.Regular ∧
      μ Set.univ ≤ ENNReal.ofReal ‖L‖ ∧
      ∀ F : C_c(X, Space d), L F.toBoundedContinuousFunction =
        ∫ q, inner ℝ (F q.1) q.2.val ∂μ := by
  obtain ⟨A, hA, hrep⟩ := exists_positive_unitBall_lift x₀ L
  let μ := RealRMK.rieszMeasure (positiveCompactRestriction A hA)
  refine ⟨μ, inferInstance, ?_, ?_⟩
  · have hmass := positiveCompactRestriction_mass_le A hA
    have hone : A (BoundedContinuousFunction.const (X × PerimeterUnitBall d) 1) = ‖L‖ := by
      have h := hrep 0 1
      have he : unitBallLift ((0 : X →ᵇ Space d), (1 : ℝ)) =
          BoundedContinuousFunction.const (X × PerimeterUnitBall d) 1 := by ext q; simp
      rw [he, map_zero, zero_add, mul_one] at h
      exact h
    simpa only [hone] using hmass
  · intro F
    have h := RealRMK.integral_rieszMeasure (positiveCompactRestriction A hA)
      (unitBallCompactLift F)
    have he : compactToBoundedLinear (unitBallCompactLift F) =
        unitBallLift (F.toBoundedContinuousFunction, 0) := by
      ext q
      change inner ℝ (F q.1) q.2.val = 0 + inner ℝ (F q.1) q.2.val
      exact (zero_add _).symm
    change (∫ q, inner ℝ (F q.1) q.2.val ∂μ) =
      A (compactToBoundedLinear (unitBallCompactLift F)) at h
    rw [he, hrep, mul_zero, add_zero] at h
    exact h.symm

/-- A vector density bounded by one has variation bounded by its underlying measure. -/
theorem variation_withDensity_le_of_norm_le_one {d : ℕ} {Y : Type*}
    [MeasurableSpace Y] {μ : Measure Y} {w : Y → Space d} (hw : Integrable w μ)
    (hbound : ∀ x, ‖w x‖ ≤ 1) : (μ.withDensityᵥ w).variation ≤ μ := by
  rw [Measure.variation_withDensityᵥ hw]
  calc
    μ.withDensity (fun x ↦ ‖w x‖ₑ) ≤ μ.withDensity 1 := withDensity_mono
      (Filter.Eventually.of_forall fun x ↦ by
        change ‖w x‖ₑ ≤ (1 : ENNReal)
        simpa only [ofReal_norm, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (hbound x))
    _ = μ := withDensity_one

/-- Integration of simple vector tests against a vector density is ordinary scalar integration. -/
theorem integral_simple_withDensity_inner {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} [IsFiniteMeasure μ] {w : Y → Space d}
    (hw : Integrable w μ) (hbound : ∀ x, ‖w x‖ ≤ 1) (f : SimpleFunc Y (Space d)) :
    (∫ᵛ x, f x ∂[innerSL ℝ; μ.withDensityᵥ w]) = ∫ x, inner ℝ (f x) (w x) ∂μ := by
  let ν := μ.withDensityᵥ w
  have hvar : ν.variation ≤ μ := variation_withDensity_le_of_norm_le_one hw hbound
  let : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le μ hvar
  have hi (g : SimpleFunc Y (Space d)) : Integrable (fun x ↦ inner ℝ (g x) (w x)) μ := by
    apply g.integrable_of_isFiniteMeasure.norm.mono'
      (g.aestronglyMeasurable.inner hw.aestronglyMeasurable)
    filter_upwards [] with x
    exact (norm_inner_le_norm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg (g x)))
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    have he : (fun x ↦ (SimpleFunc.piecewise s hs
        (SimpleFunc.const Y c) (SimpleFunc.const Y 0)) x) =
        s.indicator (fun _ ↦ c) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [he, VectorMeasure.integral_indicator_const c hs,
      withDensityᵥ_apply hw hs]
    change inner ℝ c (∫ x in s, w x ∂μ) = _
    rw [← integral_inner hw.integrableOn c, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [hx]
  | @add f g _ hf hg =>
    change (∫ᵛ x, f x + g x ∂[innerSL ℝ; ν]) = _
    rw [VectorMeasure.integral_fun_add f.integrable_of_isFiniteMeasure
      g.integrable_of_isFiniteMeasure, hf, hg]
    simp_rw [SimpleFunc.add_apply, inner_add_left]
    exact (integral_add (hi f) (hi g)).symm

/-- The vector-density integration formula for bounded measurable vector tests. -/
theorem integral_withDensity_inner_of_bounded {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} [IsFiniteMeasure μ] {w f : Y → Space d}
    (hw : Integrable w μ) (hwb : ∀ x, ‖w x‖ ≤ 1) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x, ‖f x‖ ≤ C) :
    (∫ᵛ x, f x ∂[innerSL ℝ; μ.withDensityᵥ w]) = ∫ x, inner ℝ (f x) (w x) ∂μ := by
  let ν := μ.withDensityᵥ w
  have hvar : ν.variation ≤ μ := variation_withDensity_le_of_norm_le_one hw hwb
  let : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le μ hvar
  have hz : (0 : Space d) ∈ Metric.closedBall 0 C := by simp [hC]
  let a n := SimpleFunc.approxOn f hf (Metric.closedBall 0 C) 0 hz n
  have hab (n : ℕ) (x : Y) : ‖a n x‖ ≤ C := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      SimpleFunc.approxOn_mem hf hz n x
  have hat (x : Y) : Filter.Tendsto (fun n ↦ a n x) Filter.atTop (𝓝 (f x)) :=
    SimpleFunc.tendsto_approxOn hf hz (subset_closure (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hfb x))
  have hv := VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := ν) (B := innerSL ℝ) (fun _ : Y ↦ C)
    (fun n ↦ (a n).aestronglyMeasurable) (integrable_const C)
    (fun n ↦ Filter.Eventually.of_forall (hab n)) (Filter.Eventually.of_forall hat)
  have hs := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x ↦ inner ℝ (a n x) (w x)) (f := fun x ↦ inner ℝ (f x) (w x))
    (fun _ : Y ↦ C)
    (fun n ↦ (a n).aestronglyMeasurable.inner hw.aestronglyMeasurable)
    (integrable_const C) (fun n ↦ Filter.Eventually.of_forall fun x ↦
      (norm_inner_le_norm _ _).trans (by
        simpa only [mul_one] using mul_le_mul (hab n x) (hwb x) (norm_nonneg _) hC))
    (Filter.Eventually.of_forall fun x ↦ (hat x).inner tendsto_const_nhds)
  exact tendsto_nhds_unique_of_forall hv hs (fun n ↦
    integral_simple_withDensity_inner hw hwb (a n))

/-- Euclidean vector Riesz representation with its exact, dimension-independent mass bound. -/
theorem exists_vector_riesz_measure {d : ℕ} {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (x₀ : X) (L : (X →ᵇ Space d) →L[ℝ] ℝ) :
    ∃ σ : VectorMeasure X (Space d),
      σ.variation Set.univ ≤ ENNReal.ofReal ‖L‖ ∧
      ∀ F : C_c(X, Space d), L F.toBoundedContinuousFunction =
        ∫ᵛ x, F x ∂[innerSL ℝ; σ] := by
  obtain ⟨μ, -, hmass, hrep⟩ := exists_unitBall_riesz_measure x₀ L
  let : IsFiniteMeasure μ := ⟨hmass.trans_lt (by finiteness)⟩
  let w : X × PerimeterUnitBall d → Space d := fun q ↦ q.2.val
  have hwb (q : X × PerimeterUnitBall d) : ‖w q‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using q.2.property
  have hwc : Continuous w := by fun_prop
  have hw : Integrable w μ := Integrable.of_bound hwc.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hwb)
  let ν := μ.withDensityᵥ w
  have hvar : ν.variation ≤ μ := variation_withDensity_le_of_norm_le_one hw hwb
  let : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le μ hvar
  refine ⟨ν.map Prod.fst, ?_, ?_⟩
  · calc
      (ν.map Prod.fst).variation Set.univ ≤ (ν.variation.map Prod.fst) Set.univ :=
        VectorMeasure.variation_map_le Set.univ
      _ = ν.variation Set.univ := by rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
      _ ≤ μ Set.univ := hvar Set.univ
      _ ≤ ENNReal.ofReal ‖L‖ := hmass
  · intro F
    have hFm : AEStronglyMeasurable (F : X → Space d) (ν.variation.map Prod.fst) :=
      F.continuous.aestronglyMeasurable
    have hFb (q : X × PerimeterUnitBall d) : ‖F q.1‖ ≤ ‖F.toBoundedContinuousFunction‖ :=
      F.toBoundedContinuousFunction.norm_coe_le_norm q.1
    have hFc : Continuous (fun q : X × PerimeterUnitBall d ↦ F q.1) := by fun_prop
    have hFi : ν.Integrable ((F : X → Space d) ∘ Prod.fst) :=
      Integrable.of_bound hFc.aestronglyMeasurable ‖F.toBoundedContinuousFunction‖
        (Filter.Eventually.of_forall hFb)
    have hm := VectorMeasure.integral_map (μ := ν) (B := innerSL ℝ)
      measurable_fst hFm hFi
    have hd := integral_withDensity_inner_of_bounded hw hwb hFc.measurable
      (norm_nonneg F.toBoundedContinuousFunction) hFb
    exact (hrep F).trans (hd.symm.trans hm.symm)

/-- Unit vector tests have pairing bounded by the actual Euclidean total variation. -/
theorem enorm_vector_inner_integral_le_variation {d : ℕ} {Y : Type*}
    [MeasurableSpace Y] (σ : VectorMeasure Y (Space d)) {F : Y → Space d}
    (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ᵛ x, F x ∂[innerSL ℝ; σ]‖ₑ ≤ σ.variation Set.univ := by
  have hB : ‖innerSL ℝ (E := Space d)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal (norm_innerSL_le (𝕜 := ℝ) (E := Space d))).trans_eq
      ENNReal.ofReal_one
  have hb := VectorMeasure.enorm_integral_le_of_enorm_le_const (μ := σ)
    (B := innerSL ℝ) (C := 1) (Filter.Eventually.of_forall fun x ↦ by
      simpa only [ofReal_norm, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hF x))
  exact hb.trans (by grw [hB]; simp)

set_option backward.isDefEq.respectTransparency false in
/-- Finite variational perimeter produces its distribution-gradient vector measure, and its
Euclidean total variation is exactly the original divergence supremum. -/
theorem exists_perimeter_vector_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ σ : VectorMeasure (Space d) (Space d),
      σ.variation Set.univ = variationalPerimeter b E Ω ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ Ω →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ᵛ x, F x ∂[innerSL ℝ; σ] := by
  obtain ⟨L, hL, hnorm⟩ := exists_perimeterDistribution_extension b hE hP
  obtain ⟨σ, hσ, hrep⟩ := exists_vector_riesz_measure (0 : Space d) L
  have hupper : σ.variation Set.univ ≤ variationalPerimeter b E Ω :=
    hσ.trans ((ENNReal.ofReal_le_ofReal hnorm).trans_eq (ENNReal.ofReal_toReal hP))
  have hdist (F : C_c(Space d, Space d))
      (hF : ContDiff ℝ 1 (F : Space d → Space d)) (hs : tsupport F ⊆ Ω) :
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ᵛ x, F x ∂[innerSL ℝ; σ] := by
    let Ft : perimeterTestSubmodule Ω :=
      ⟨F.toBoundedContinuousFunction, hF, F.hasCompactSupport, hs⟩
    exact (hL Ft).symm.trans (hrep F)
  refine ⟨σ, le_antisymm hupper ?_, hdist⟩
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
    iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
  let Fc : C_c(Space d, Space d) := ⟨⟨F, hF.continuous⟩, hc⟩
  have he := hdist Fc hF hs
  change ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
    fieldDivergence b F x‖ ≤ σ.variation Set.univ
  rw [← norm_neg (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x)]
  change ENNReal.ofReal ‖-(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
    fieldDivergence b Fc x)‖ ≤ σ.variation Set.univ
  rw [he, ofReal_norm]
  exact enorm_vector_inner_integral_le_variation σ hunit

end SerrinEpigraph
