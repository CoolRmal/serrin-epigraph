module

public import SerrinEpigraph.BVColumnGraph
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Auxiliary calculus for the GR8 flattening competitor

This module collects the analytic ingredients of the directed reverse Poincaré inequality
(`GR8`, `docs/rigidity-proof/gmt-regularity.md`) that do not involve perimeter minimizers:

1. The Piola (cofactor) identity for the vertical shear `F x = x - θ x • e`:
   for the cofactor pull-back `Z = cof(DF)ᵀ (X ∘ F)` of a `C¹` field `X`
   (`shearPiolaField`), `div Z = det DF · (div X) ∘ F` with `det DF = 1 - ∂_e θ`
   (`fieldDivergence_shearPiolaField`). This is a pointwise differential identity valid for every
   `C²` height `θ`, including those for which `F` is not injective; it never identifies the
   perimeter of an image set.
2. The one-dimensional column change of variables for the flattened column
   (`flattenedColumn`, `integral_flattenedColumn_eq`): on the band the column is an affine
   compression (invertible whenever the compression factor is positive and collapsing to the
   level `λ` in the core), above the band it is filled and below it is emptied.
3. Explicit smooth cutoff profiles (`verticalFlatteningProfile`, `radialFlatteningCutoff`)
   with a universal derivative constant.
4. The pointwise cofactor inequality `GR8.1`
   `|cof DF ν| ≤ 1 - η² |ν_h|² / 4 + 6 w² |∇η|²` in the scalar form used for the pairing.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-! ### 1. The shear Piola identity -/

/-- Expansion of a linear functional in an orthonormal basis. -/
theorem sum_apply_mul_inner_orthonormalBasis {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (a : Space d →L[ℝ] ℝ) (w : Space d) :
    ∑ i, a (b i) * inner ℝ (b i) w = a w := by
  conv_rhs => rw [← b.sum_repr' w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- Piola (cofactor) pull-back of a vector field `X` along the vertical shear
`x ↦ x - θ x • e`: with `DF = I - e ⊗ ∇θ` one has `cof(DF)ᵀ = (1 - ∂_e θ) I + e ⊗ ∇θ`. -/
def shearPiolaField {d : ℕ} (θ : Space d → ℝ) (e : Space d) (X : Space d → Space d) :
    Space d → Space d :=
  fun x ↦ (1 - fderiv ℝ θ x e) • X (x - θ x • e) + (fderiv ℝ θ x (X (x - θ x • e))) • e

/-- The Piola identity for the vertical shear: `div Z = (1 - ∂_e θ) (div X) ∘ F`. It holds for
every `C²` height `θ`; no injectivity of `x ↦ x - θ x • e` is needed. -/
theorem fieldDivergence_shearPiolaField {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {θ : Space d → ℝ} (hθ : ContDiff ℝ 2 θ) {X : Space d → Space d} (hX : ContDiff ℝ 1 X)
    (e x : Space d) :
    fieldDivergence b (shearPiolaField θ e X) x =
      (1 - fderiv ℝ θ x e) * fieldDivergence b X (x - θ x • e) := by
  let F : Space d → Space d := fun x ↦ x - θ x • e
  have hDθ : ContDiff ℝ 1 (fderiv ℝ θ) := hθ.fderiv_right (by norm_num)
  have hθd : DifferentiableAt ℝ θ x := (hθ.differentiable (by norm_num)) x
  set Dθ : Space d →L[ℝ] ℝ := fderiv ℝ θ x with hDθ_def
  set D2 : Space d →L[ℝ] (Space d →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ θ) x with hD2_def
  set DX : Space d →L[ℝ] Space d := fderiv ℝ X (F x) with hDX_def
  set w : Space d := X (F x) with hw_def
  have hF : HasFDerivAt F (ContinuousLinearMap.id ℝ (Space d) - Dθ.smulRight e) x :=
    (hasFDerivAt_id x).sub (hθd.hasFDerivAt.smul_const e)
  have hXd : HasFDerivAt X DX (F x) := ((hX.differentiable one_ne_zero) (F x)).hasFDerivAt
  have hW : HasFDerivAt (fun x ↦ X (F x))
      (DX.comp (ContinuousLinearMap.id ℝ (Space d) - Dθ.smulRight e)) x := hXd.comp x hF
  have hD2 : HasFDerivAt (fderiv ℝ θ) D2 x := ((hDθ.differentiable one_ne_zero) x).hasFDerivAt
  have hc : HasFDerivAt (fun x ↦ fderiv ℝ θ x e) (Dθ.comp 0 + D2.flip e) x :=
    hD2.clm_apply (hasFDerivAt_const e x)
  have hp : HasFDerivAt (fun x ↦ fderiv ℝ θ x (X (F x)))
      (Dθ.comp (DX.comp (ContinuousLinearMap.id ℝ (Space d) - Dθ.smulRight e)) + D2.flip w) x :=
    hD2.clm_apply hW
  have hZ := (((hasFDerivAt_const (1 : ℝ) x).sub hc).smul hW).add (hp.smul_const e)
  have hsymm : D2 e w = D2 w e := (hθ.contDiffAt.isSymmSndFDerivAt (by simp)) e w
  have hfun : shearPiolaField θ e X = (((fun _ ↦ (1 : ℝ)) - fun x ↦ fderiv ℝ θ x e) •
      fun x ↦ X (F x)) + fun y ↦ fderiv ℝ θ y (X (F y)) • e := by
    funext y
    simp [shearPiolaField, F]
  have key (i : Fin d) : inner ℝ (b i) (fderiv ℝ (shearPiolaField θ e X) x (b i)) =
      (1 - Dθ e) * inner ℝ (b i) (DX (b i)) - (1 - Dθ e) * (Dθ (b i) * inner ℝ (b i) (DX e))
        - (D2.flip e) (b i) * inner ℝ (b i) w + (Dθ.comp DX) (b i) * inner ℝ (b i) e
        - Dθ (DX e) * (Dθ (b i) * inner ℝ (b i) e) + (D2.flip w) (b i) * inner ℝ (b i) e := by
    rw [hfun, hZ.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.flip_apply, Pi.sub_apply,
      map_sub, map_smul, smul_eq_mul, inner_add_right, inner_smul_right, inner_sub_right,
      ContinuousLinearMap.comp_zero, zero_add, zero_sub, _root_.neg_apply]
    ring
  unfold fieldDivergence
  rw [Finset.sum_congr rfl (fun i _ ↦ key i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_apply_mul_inner_orthonormalBasis, sum_apply_mul_inner_orthonormalBasis,
    sum_apply_mul_inner_orthonormalBasis, sum_apply_mul_inner_orthonormalBasis,
    sum_apply_mul_inner_orthonormalBasis]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hsymm]
  ring

/-- The shear Piola field of a `C¹` field along a `C²` height is `C¹`. -/
theorem contDiff_shearPiolaField {d : ℕ} {θ : Space d → ℝ} (hθ : ContDiff ℝ 2 θ)
    {X : Space d → Space d} (hX : ContDiff ℝ 1 X) (e : Space d) :
    ContDiff ℝ 1 (shearPiolaField θ e X) := by
  have hDθ : ContDiff ℝ 1 (fderiv ℝ θ) := hθ.fderiv_right (by norm_num)
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hF : ContDiff ℝ 1 (fun x ↦ x - θ x • e) := contDiff_id.sub (hθ1.smul contDiff_const)
  have hW : ContDiff ℝ 1 (fun x ↦ X (x - θ x • e)) := hX.comp hF
  exact ((contDiff_const.sub (hDθ.clm_apply contDiff_const)).smul hW).add
    ((hDθ.clm_apply hW).smul contDiff_const)

theorem shearPiolaField_eq_zero_of_eq_zero {d : ℕ} {θ : Space d → ℝ} {e : Space d}
    {X : Space d → Space d} {x : Space d} (h : X (x - θ x • e) = 0) :
    shearPiolaField θ e X x = 0 := by
  simp [shearPiolaField, h]

/-- The support of the Piola field lies in the shear preimage of the support of `X`. -/
theorem tsupport_shearPiolaField_subset {d : ℕ} {θ : Space d → ℝ} (hθ : Continuous θ)
    (e : Space d) (X : Space d → Space d) :
    tsupport (shearPiolaField θ e X) ⊆ (fun x ↦ x - θ x • e) ⁻¹' tsupport X := by
  apply closure_minimal _
    ((isClosed_tsupport X).preimage (continuous_id.sub (hθ.smul continuous_const)))
  intro x hx
  by_contra hn
  exact hx (shearPiolaField_eq_zero_of_eq_zero (image_eq_zero_of_notMem_tsupport hn))

/-- A bounded shear has compact preimages of compact sets. -/
theorem isCompact_preimage_shear {d : ℕ} {θ : Space d → ℝ} (hθ : Continuous θ) {M : ℝ}
    (hM : ∀ x, |θ x| ≤ M) (e : Space d) {K : Set (Space d)} (hK : IsCompact K) :
    IsCompact ((fun x ↦ x - θ x • e) ⁻¹' K) := by
  apply Metric.isCompact_of_isClosed_isBounded
    (hK.isClosed.preimage (continuous_id.sub (hθ.smul continuous_const)))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : Space d)) (r := R + M * ‖e‖)).subset ?_
  intro x hx
  have hxK := hR hx
  rw [mem_closedBall, dist_zero_right] at hxK ⊢
  have hθe : ‖θ x • e‖ ≤ M * ‖e‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg e)
  calc
    ‖x‖ = ‖(x - θ x • e) + θ x • e‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - θ x • e‖ + ‖θ x • e‖ := norm_add_le _ _
    _ ≤ R + M * ‖e‖ := add_le_add hxK hθe

/-- Pairing of the Piola field with a vector. -/
theorem inner_shearPiolaField {d : ℕ} (θ : Space d → ℝ) (e : Space d) (X : Space d → Space d)
    (x v : Space d) :
    inner ℝ (shearPiolaField θ e X x) v =
      (1 - fderiv ℝ θ x e) * inner ℝ (X (x - θ x • e)) v +
        fderiv ℝ θ x (X (x - θ x • e)) * inner ℝ e v := by
  simp [shearPiolaField, inner_add_left, inner_smul_left]

/-! ### 2. One-dimensional column change of variables -/

/-- Interval integrals agree when the integrands agree on the open interval. -/
theorem intervalIntegral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioo a b, f x = g x) : ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- Interval integrals agree when the integrands agree almost everywhere on the open interval. -/
theorem intervalIntegral_congr_ae_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ᵐ x, x ∈ Ioo a b → f x = g x) : ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_ae measurableSet_Ioo h

/-- A function vanishing outside `Ioo a b` has whole-line integral equal to its interval
integral. -/
theorem integral_eq_intervalIntegral_of_vanish {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, x ∉ Ioo a b → f x = 0) : ∫ x, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ h x ?_).symm
  exact fun hx' ↦ hx (Ioo_subset_Ioc_self hx')

/-- The flattened vertical column of GR8. With compression factor `s` and band `[a, b]`,
`a = λ - s (H₁ + λ)`, `b = λ + s (H₁ - λ)`: on `[a, b]` the column is the affine compression
`t ↦ λ + s (t - λ)` of `S ∩ [-H₁, H₁]` (for `s = 0` the band degenerates to the level `λ`),
above `b` (up to height `H₂`) it is full, below `a` it is empty, and outside `[-H₂, H₂]` it
equals `S`. -/
def flattenedColumn (S : Set ℝ) (lam s H₁ H₂ : ℝ) : Set ℝ :=
  {τ | if |τ| ≤ H₂ then (lam + s * (H₁ - lam) < τ ∨
      (lam - s * (H₁ + lam) ≤ τ ∧ τ ≤ lam + s * (H₁ - lam) ∧ lam + (τ - lam) / s ∈ S))
    else τ ∈ S}

theorem measurableSet_flattenedColumn {S : Set ℝ} (hS : MeasurableSet S) (lam s H₁ H₂ : ℝ) :
    MeasurableSet (flattenedColumn S lam s H₁ H₂) := by
  have hpre : MeasurableSet ((fun τ : ℝ ↦ lam + (τ - lam) / s) ⁻¹' S) :=
    hS.preimage (by fun_prop)
  have heq : flattenedColumn S lam s H₁ H₂ =
      ({τ : ℝ | |τ| ≤ H₂} ∩ ({τ | lam + s * (H₁ - lam) < τ} ∪
        ({τ | lam - s * (H₁ + lam) ≤ τ} ∩ {τ | τ ≤ lam + s * (H₁ - lam)} ∩
          ((fun τ : ℝ ↦ lam + (τ - lam) / s) ⁻¹' S)))) ∪ ({τ : ℝ | |τ| ≤ H₂}ᶜ ∩ S) := by
    ext τ
    by_cases hτ : |τ| ≤ H₂ <;> simp [flattenedColumn, hτ, and_assoc]
  rw [heq]
  refine (MeasurableSet.inter ?_ (MeasurableSet.union ?_ ?_)).union (MeasurableSet.inter ?_ hS)
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_lt measurable_const measurable_id
  · exact ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)).inter hpre
  · exact (measurableSet_le (by fun_prop) measurable_const).compl

/-- Column change of variables for the GR8 flattening: integrating a continuous test `g` over
the flattened column equals integrating `g` composed with the vertical compression
`t ↦ t - σ ψ t` against its Jacobian `1 - σ ψ'` over the original column. The band is handled
by the affine substitution (no injectivity is used when `σ = 1`, where both sides of the band
contribution vanish), the transition above the band by the `C¹` substitution with a continuous
integrand, and the slabs below/above by the trapping hypotheses. -/
theorem integral_flattenedColumn_eq {S : Set ℝ} (hS : MeasurableSet S) {g : ℝ → ℝ}
    (hg : Continuous g) {H H₁ H₂ H' lam σ : ℝ} (h1 : H < H₁) (h2 : H₁ < H₂)
    (h3 : H₂ < H') (hlam : |lam| ≤ H₁) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hg0 : ∀ τ, H' ≤ |τ| → g τ = 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψband : ∀ t, |t| ≤ H₁ → ψ t = t - lam) (hψ'band : ∀ t, |t| ≤ H₁ → deriv ψ t = 1)
    (hψout : ∀ t, H₂ ≤ |t| → ψ t = 0) (hψ'out : ∀ t, H₂ ≤ |t| → deriv ψ t = 0)
    (hbot : ∀ᵐ t, t ∈ Ioo (-H') (-H) → t ∉ S) (htop : ∀ᵐ t, t ∈ Ioo H H' → t ∈ S) :
    ∫ τ, (flattenedColumn S lam (1 - σ) H₁ H₂).indicator (fun _ ↦ (1 : ℝ)) τ * g τ =
      ∫ t, S.indicator (fun _ ↦ (1 : ℝ)) t * ((1 - σ * deriv ψ t) * g (t - σ * ψ t)) := by
  set s : ℝ := 1 - σ with hs_def
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hH₁ : 0 ≤ H₁ := (abs_nonneg lam).trans hlam
  obtain ⟨hlam1, hlam2⟩ := abs_le.mp hlam
  set a : ℝ := lam - s * (H₁ + lam) with ha_def
  set b : ℝ := lam + s * (H₁ - lam) with hb_def
  have ha : -H₁ ≤ a := by nlinarith
  have hab : a ≤ b := by nlinarith
  have hb : b ≤ H₁ := by nlinarith
  set S'' := flattenedColumn S lam s H₁ H₂ with hS''_def
  set k : ℝ → ℝ := fun t ↦ (1 - σ * deriv ψ t) * g (t - σ * ψ t) with hk_def
  have hψc : Continuous ψ := hψ.continuous
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hkc : Continuous k := by
    simp only [hk_def]
    fun_prop
  have hk0 : ∀ t, H' ≤ |t| → k t = 0 := by
    intro t ht
    have hψt : ψ t = 0 := hψout t (by linarith)
    simp [hk_def, hψt, hg0 t ht]
  have hcs : ∀ {f : ℝ → ℝ}, (∀ t, H' ≤ |t| → f t = 0) → HasCompactSupport f := by
    intro f hf
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -H') (b := H'))
    intro t ht
    by_contra hn
    apply ht
    apply hf t
    rw [mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hg_int : Integrable g := hg.integrable_of_hasCompactSupport (hcs hg0)
  have hk_int : Integrable k := hkc.integrable_of_hasCompactSupport (hcs hk0)
  have hS''m : MeasurableSet S'' := measurableSet_flattenedColumn hS lam s H₁ H₂
  have hfL_eq : (fun τ ↦ S''.indicator (fun _ ↦ (1 : ℝ)) τ * g τ) = S''.indicator g := by
    funext τ
    by_cases hτ : τ ∈ S'' <;> simp [hτ]
  have hfR_eq : (fun t ↦ S.indicator (fun _ ↦ (1 : ℝ)) t * k t) = S.indicator k := by
    funext t
    by_cases ht : t ∈ S <;> simp [ht]
  have hfL_int : Integrable (fun τ ↦ S''.indicator (fun _ ↦ (1 : ℝ)) τ * g τ) := by
    rw [hfL_eq]
    exact hg_int.indicator hS''m
  have hfR_int : Integrable (fun t ↦ S.indicator (fun _ ↦ (1 : ℝ)) t * k t) := by
    rw [hfR_eq]
    exact hk_int.indicator hS
  set fL : ℝ → ℝ := fun τ ↦ S''.indicator (fun _ ↦ (1 : ℝ)) τ * g τ with hfL_def
  set fR : ℝ → ℝ := fun t ↦ S.indicator (fun _ ↦ (1 : ℝ)) t * k t with hfR_def
  change ∫ τ, fL τ = ∫ t, fR t
  have hH' : -H' ≤ H' := by linarith
  have hout : ∀ x, x ∉ Ioo (-H') H' → H' ≤ |x| := by
    intro x hx
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact hx
  rw [integral_eq_intervalIntegral_of_vanish hH' (fun x hx ↦ by simp [fL, hg0 x (hout x hx)]),
    integral_eq_intervalIntegral_of_vanish hH' (fun x hx ↦ by simp [fR, hk0 x (hout x hx)])]
  have hiL : ∀ c d : ℝ, IntervalIntegrable fL volume c d :=
    fun c d ↦ hfL_int.intervalIntegrable
  have hiR : ∀ c d : ℝ, IntervalIntegrable fR volume c d :=
    fun c d ↦ hfR_int.intervalIntegrable
  -- Split both sides into five pieces.
  have hsplitL : ∫ x in -H'..H', fL x = (∫ x in -H'..-H₂, fL x) + (∫ x in -H₂..a, fL x) +
      (∫ x in a..b, fL x) + (∫ x in b..H₂, fL x) + ∫ x in H₂..H', fL x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hiL _ _) (hiL _ _),
      intervalIntegral.integral_add_adjacent_intervals (hiL _ _) (hiL _ _),
      intervalIntegral.integral_add_adjacent_intervals (hiL _ _) (hiL _ _),
      intervalIntegral.integral_add_adjacent_intervals (hiL _ _) (hiL _ _)]
  have hsplitR : ∫ x in -H'..H', fR x = (∫ x in -H'..-H₂, fR x) + (∫ x in -H₂..-H₁, fR x) +
      (∫ x in -H₁..H₁, fR x) + (∫ x in H₁..H₂, fR x) + ∫ x in H₂..H', fR x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hiR _ _) (hiR _ _),
      intervalIntegral.integral_add_adjacent_intervals (hiR _ _) (hiR _ _),
      intervalIntegral.integral_add_adjacent_intervals (hiR _ _) (hiR _ _),
      intervalIntegral.integral_add_adjacent_intervals (hiR _ _) (hiR _ _)]
  -- Outer pieces: the flattening is the identity there.
  have houter : ∀ x, H₂ < |x| → fL x = fR x := by
    intro x hx
    have hnot : ¬ |x| ≤ H₂ := not_le.mpr hx
    have hψx : ψ x = 0 := hψout x hx.le
    have hψ'x : deriv ψ x = 0 := hψ'out x hx.le
    have hmem : x ∈ S'' ↔ x ∈ S := by
      simp only [hS''_def, flattenedColumn, mem_ofPred_eq, hnot, ite_false]
    by_cases hxS : x ∈ S
    · simp [fL, fR, hk_def, hψx, hψ'x, hxS, hmem.mpr hxS]
    · have hxS'' : x ∉ S'' := fun h ↦ hxS (hmem.mp h)
      simp [fL, fR, hxS, hxS'']
  have hP1 : ∫ x in -H'..-H₂, fL x = ∫ x in -H'..-H₂, fR x := by
    refine intervalIntegral_congr_Ioo (by linarith) fun x hx ↦ houter x ?_
    rw [abs_of_neg (by linarith [hx.2])]
    linarith [hx.2]
  have hP5 : ∫ x in H₂..H', fL x = ∫ x in H₂..H', fR x := by
    refine intervalIntegral_congr_Ioo (by linarith) fun x hx ↦ houter x ?_
    rw [abs_of_pos (by linarith [hx.1])]
    exact hx.1
  -- Bottom transition: both sides vanish.
  have hP2L : ∫ x in -H₂..a, fL x = 0 := by
    rw [intervalIntegral_congr_Ioo (by linarith) (g := fun _ ↦ (0 : ℝ)) fun x hx ↦ ?_]
    · simp
    have hxabs : |x| ≤ H₂ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxS'' : x ∉ S'' := by
      simp only [hS''_def, flattenedColumn, mem_ofPred_eq, hxabs, ite_true, not_or, not_and,
        not_lt]
      exact ⟨by linarith [hx.2], fun h ↦ absurd h (not_le.mpr hx.2)⟩
    simp [fL, hxS'']
  have hP2R : ∫ x in -H₂..-H₁, fR x = 0 := by
    rw [intervalIntegral_congr_ae_Ioo (by linarith) (g := fun _ ↦ (0 : ℝ)) ?_]
    · simp
    filter_upwards [hbot] with x hx hxI
    have hxS : x ∉ S := hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    simp [fR, hxS]
  -- Band: affine change of variables.
  set k₃ : ℝ → ℝ := fun τ ↦ S.indicator (fun _ ↦ (1 : ℝ)) (lam + (τ - lam) / s) * g τ
    with hk₃_def
  have hP3L : ∫ x in a..b, fL x = ∫ x in a..b, k₃ x := by
    refine intervalIntegral_congr_Ioo hab fun x hx ↦ ?_
    have hxabs : |x| ≤ H₂ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmem : x ∈ S'' ↔ lam + (x - lam) / s ∈ S := by
      simp only [hS''_def, flattenedColumn, mem_ofPred_eq, hxabs, ite_true]
      constructor
      · rintro (h | ⟨-, -, h⟩)
        · exact absurd h (not_lt.mpr hx.2.le)
        · exact h
      · intro h
        exact Or.inr ⟨hx.1.le, hx.2.le, h⟩
    by_cases hxS : lam + (x - lam) / s ∈ S
    · simp [fL, k₃, hxS, hmem.mpr hxS]
    · have hxS'' : x ∉ S'' := fun h ↦ hxS (hmem.mp h)
      simp [fL, k₃, hxS, hxS'']
  have hP3R : ∫ x in -H₁..H₁, fR x = ∫ x in -H₁..H₁, s * k₃ (s * x + (1 - s) * lam) := by
    refine intervalIntegral_congr_Ioo (by linarith) fun x hx ↦ ?_
    have hxabs : |x| ≤ H₁ := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have hψx : ψ x = x - lam := hψband x hxabs
    have hψ'x : deriv ψ x = 1 := hψ'band x hxabs
    have harg : x - σ * (x - lam) = s * x + (1 - s) * lam := by
      simp only [hs_def]
      ring
    by_cases hs : s = 0
    · simp [fR, k₃, hk_def, hψx, hψ'x, hs, show σ = 1 by linarith]
    · have hinv : lam + (s * x + (1 - s) * lam - lam) / s = x := by
        field_simp
        ring
      simp only [fR, k₃, hk_def, hψx, hψ'x, hinv, mul_one, harg]
      rw [show (1 : ℝ) - σ = s from rfl]
      ring
  have hP3 : ∫ x in a..b, fL x = ∫ x in -H₁..H₁, fR x := by
    rw [hP3L, hP3R, intervalIntegral.integral_const_mul,
      ← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_add]
    congr 1 <;> ring
  -- Top transition: smooth change of variables with a continuous integrand.
  have hP4L : ∫ x in b..H₂, fL x = ∫ x in b..H₂, g x := by
    refine intervalIntegral_congr_Ioo (by linarith) fun x hx ↦ ?_
    have hxabs : |x| ≤ H₂ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxS'' : x ∈ S'' := by
      simp only [hS''_def, flattenedColumn, mem_ofPred_eq, hxabs, ite_true]
      exact Or.inl hx.1
    simp [fL, hxS'']
  have hP4R : ∫ x in H₁..H₂, fR x = ∫ x in b..H₂, g x := by
    have hΦ : ∀ x ∈ uIcc H₁ H₂, HasDerivAt (fun t ↦ t - σ * ψ t) (1 - σ * deriv ψ x) x := by
      intro x _
      exact (hasDerivAt_id x).sub
        (((hψ.differentiable one_ne_zero) x).hasDerivAt.const_mul σ)
    have hsub := intervalIntegral.integral_comp_mul_deriv (g := g) hΦ
      (by fun_prop : Continuous fun x ↦ 1 - σ * deriv ψ x).continuousOn hg
    have hΦ1 : H₁ - σ * ψ H₁ = b := by
      rw [hψband H₁ (by rw [abs_of_nonneg hH₁])]
      simp only [hb_def, hs_def]
      ring
    have hΦ2 : H₂ - σ * ψ H₂ = H₂ := by
      rw [hψout H₂ (by rw [abs_of_nonneg (by linarith)])]
      ring
    rw [hΦ1, hΦ2] at hsub
    rw [← hsub]
    refine intervalIntegral_congr_ae_Ioo (by linarith) ?_
    filter_upwards [htop] with x hx hxI
    have hxS : x ∈ S := hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    simp [fR, hk_def, hxS, mul_comm]
  rw [hsplitL, hsplitR, hP1, hP2L, hP2R, hP3, hP4L, ← hP4R, hP5]

/-! ### 3. Smooth cutoff profiles -/

/-- Smooth step in the squared radius: `1` for `u ≤ r ^ 2` and `0` for `R ^ 2 ≤ u`. -/
def sqCutoffProfile (r R u : ℝ) : ℝ :=
  Real.smoothTransition ((R ^ 2 - u) / (R ^ 2 - r ^ 2))

theorem contDiff_sqCutoffProfile (r R : ℝ) {n : ℕ∞} : ContDiff ℝ n (sqCutoffProfile r R) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem sqCutoffProfile_nonneg (r R u : ℝ) : 0 ≤ sqCutoffProfile r R u :=
  Real.smoothTransition.nonneg _

theorem sqCutoffProfile_le_one (r R u : ℝ) : sqCutoffProfile r R u ≤ 1 :=
  Real.smoothTransition.le_one _

theorem sqCutoffProfile_eq_one {r R u : ℝ} (hrR : r ^ 2 < R ^ 2) (hu : u ≤ r ^ 2) :
    sqCutoffProfile r R u = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (by linarith)]
  linarith

theorem sqCutoffProfile_eq_zero {r R u : ℝ} (hrR : r ^ 2 < R ^ 2) (hu : R ^ 2 ≤ u) :
    sqCutoffProfile r R u = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- The derivative of `Real.smoothTransition` is bounded. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ B : ℝ, 0 < B ∧ ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  have hsupp : HasCompactSupport (deriv Real.smoothTransition) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    intro t ht
    by_contra hn
    apply ht
    rw [mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h0 | h1
    · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h0] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq).deriv
    · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      exact ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq).deriv
  obtain ⟨B, hB⟩ := hsupp.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
  exact ⟨max B 1, by positivity, fun t ↦ (hB t).trans (le_max_left B 1)⟩

/-- A fixed universal bound for `|deriv Real.smoothTransition|`. -/
def smoothTransitionDerivBound : ℝ :=
  Classical.choose exists_abs_deriv_smoothTransition_le

theorem smoothTransitionDerivBound_pos : 0 < smoothTransitionDerivBound :=
  (Classical.choose_spec exists_abs_deriv_smoothTransition_le).1

theorem abs_deriv_smoothTransition_le (t : ℝ) :
    |deriv Real.smoothTransition t| ≤ smoothTransitionDerivBound :=
  (Classical.choose_spec exists_abs_deriv_smoothTransition_le).2 t

/-- Vertical cutoff of the GR8 compression: `1` for `|t| ≤ H₁` and `0` for `H₂ ≤ |t|`. -/
def verticalFlatteningCutoff (H₁ H₂ t : ℝ) : ℝ := sqCutoffProfile H₁ H₂ (t ^ 2)

/-- Vertical profile `ψ(t) = (t - λ) χ(t)` of the GR8 compression: equal to `t - λ` on
`[-H₁, H₁]` and vanishing for `H₂ ≤ |t|`. -/
def verticalFlatteningProfile (lam H₁ H₂ t : ℝ) : ℝ :=
  (t - lam) * verticalFlatteningCutoff H₁ H₂ t

theorem contDiff_verticalFlatteningCutoff (H₁ H₂ : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (verticalFlatteningCutoff H₁ H₂) :=
  (contDiff_sqCutoffProfile H₁ H₂).comp (contDiff_id.pow 2)

theorem contDiff_verticalFlatteningProfile (lam H₁ H₂ : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (verticalFlatteningProfile lam H₁ H₂) :=
  (contDiff_id.sub contDiff_const).mul (contDiff_verticalFlatteningCutoff H₁ H₂)

private theorem sq_le_sq_of_abs_le {t c : ℝ} (h : |t| ≤ c) : t ^ 2 ≤ c ^ 2 := by
  have := abs_le.mp h
  nlinarith

private theorem sq_le_sq_of_le_abs {t c : ℝ} (hc : 0 ≤ c) (h : c ≤ |t|) : c ^ 2 ≤ t ^ 2 := by
  have h' : c ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ hc h 2
  rwa [sq_abs] at h'

theorem verticalFlatteningCutoff_eq_one {H₁ H₂ t : ℝ} (hH₁ : 0 ≤ H₁) (h12 : H₁ < H₂)
    (ht : |t| ≤ H₁) : verticalFlatteningCutoff H₁ H₂ t = 1 :=
  sqCutoffProfile_eq_one (by nlinarith) (sq_le_sq_of_abs_le ht)

theorem verticalFlatteningCutoff_eq_zero {H₁ H₂ t : ℝ} (hH₁ : 0 ≤ H₁) (h12 : H₁ < H₂)
    (ht : H₂ ≤ |t|) : verticalFlatteningCutoff H₁ H₂ t = 0 :=
  sqCutoffProfile_eq_zero (by nlinarith) (sq_le_sq_of_le_abs (by linarith) ht)

theorem deriv_verticalFlatteningCutoff_eq_zero_of_le {H₁ H₂ t : ℝ} (hH₁ : 0 ≤ H₁)
    (h12 : H₁ < H₂) (ht : |t| ≤ H₁) : deriv (verticalFlatteningCutoff H₁ H₂) t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s ↦ ?_
  rw [verticalFlatteningCutoff_eq_one hH₁ h12 ht]
  exact sqCutoffProfile_le_one _ _ _

theorem deriv_verticalFlatteningCutoff_eq_zero_of_ge {H₁ H₂ t : ℝ} (hH₁ : 0 ≤ H₁)
    (h12 : H₁ < H₂) (ht : H₂ ≤ |t|) : deriv (verticalFlatteningCutoff H₁ H₂) t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun s ↦ ?_
  rw [verticalFlatteningCutoff_eq_zero hH₁ h12 ht]
  exact sqCutoffProfile_nonneg _ _ _

theorem hasDerivAt_verticalFlatteningProfile (lam H₁ H₂ t : ℝ) :
    HasDerivAt (verticalFlatteningProfile lam H₁ H₂)
      (verticalFlatteningCutoff H₁ H₂ t +
        (t - lam) * deriv (verticalFlatteningCutoff H₁ H₂) t) t := by
  have hχ : HasDerivAt (verticalFlatteningCutoff H₁ H₂)
      (deriv (verticalFlatteningCutoff H₁ H₂) t) t :=
    ((contDiff_verticalFlatteningCutoff H₁ H₂ (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have h : HasDerivAt (fun y ↦ (y - lam) * verticalFlatteningCutoff H₁ H₂ y)
      (1 * verticalFlatteningCutoff H₁ H₂ t +
        (t - lam) * deriv (verticalFlatteningCutoff H₁ H₂) t) t :=
    ((hasDerivAt_id' t).sub_const lam).mul hχ
  rw [one_mul] at h
  exact h

theorem verticalFlatteningProfile_band {lam H₁ H₂ t : ℝ} (hH₁ : 0 ≤ H₁) (h12 : H₁ < H₂)
    (ht : |t| ≤ H₁) :
    verticalFlatteningProfile lam H₁ H₂ t = t - lam ∧
      deriv (verticalFlatteningProfile lam H₁ H₂) t = 1 := by
  refine ⟨?_, ?_⟩
  · rw [verticalFlatteningProfile, verticalFlatteningCutoff_eq_one hH₁ h12 ht, mul_one]
  · rw [(hasDerivAt_verticalFlatteningProfile lam H₁ H₂ t).deriv,
      verticalFlatteningCutoff_eq_one hH₁ h12 ht,
      deriv_verticalFlatteningCutoff_eq_zero_of_le hH₁ h12 ht, mul_zero, add_zero]

theorem verticalFlatteningProfile_out {lam H₁ H₂ t : ℝ} (hH₁ : 0 ≤ H₁) (h12 : H₁ < H₂)
    (ht : H₂ ≤ |t|) :
    verticalFlatteningProfile lam H₁ H₂ t = 0 ∧
      deriv (verticalFlatteningProfile lam H₁ H₂) t = 0 := by
  refine ⟨?_, ?_⟩
  · rw [verticalFlatteningProfile, verticalFlatteningCutoff_eq_zero hH₁ h12 ht, mul_zero]
  · rw [(hasDerivAt_verticalFlatteningProfile lam H₁ H₂ t).deriv,
      verticalFlatteningCutoff_eq_zero hH₁ h12 ht,
      deriv_verticalFlatteningCutoff_eq_zero_of_ge hH₁ h12 ht, mul_zero, add_zero]

/-- The vertical profile is bounded by `H₂ + |λ|`. -/
theorem abs_verticalFlatteningProfile_le {lam H₁ H₂ : ℝ} (hH₁ : 0 ≤ H₁) (h12 : H₁ < H₂)
    (t : ℝ) : |verticalFlatteningProfile lam H₁ H₂ t| ≤ H₂ + |lam| := by
  have hpos : 0 ≤ H₂ + |lam| := by
    have := abs_nonneg lam
    linarith
  by_cases ht : H₂ ≤ |t|
  · rw [(verticalFlatteningProfile_out hH₁ h12 ht).1, abs_zero]
    exact hpos
  · have ht' : |t| ≤ H₂ := (not_le.mp ht).le
    rw [verticalFlatteningProfile, abs_mul]
    have hχ0 := sqCutoffProfile_nonneg H₁ H₂ (t ^ 2)
    have hχ1 := sqCutoffProfile_le_one H₁ H₂ (t ^ 2)
    have hχ : |verticalFlatteningCutoff H₁ H₂ t| ≤ 1 := by
      unfold verticalFlatteningCutoff
      rw [abs_of_nonneg hχ0]
      exact hχ1
    calc
      |t - lam| * |verticalFlatteningCutoff H₁ H₂ t| ≤ (H₂ + |lam|) * 1 :=
        mul_le_mul ((abs_sub _ _).trans (add_le_add ht' le_rfl)) hχ (abs_nonneg _) hpos
      _ = H₂ + |lam| := mul_one _

/-- Smooth radial cutoff of GR8.2: `1` on `closedBall y₀ r`, `0` outside `ball y₀ R`. -/
def radialFlatteningCutoff {m : ℕ} (y₀ : Space m) (r R : ℝ) (y : Space m) : ℝ :=
  sqCutoffProfile r R (‖y - y₀‖ ^ 2)

theorem contDiff_radialFlatteningCutoff {m : ℕ} (y₀ : Space m) (r R : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (radialFlatteningCutoff y₀ r R) :=
  (contDiff_sqCutoffProfile r R).comp ((contDiff_id.sub contDiff_const).norm_sq ℝ)

theorem radialFlatteningCutoff_nonneg {m : ℕ} (y₀ : Space m) (r R : ℝ) (y : Space m) :
    0 ≤ radialFlatteningCutoff y₀ r R y :=
  sqCutoffProfile_nonneg _ _ _

theorem radialFlatteningCutoff_le_one {m : ℕ} (y₀ : Space m) (r R : ℝ) (y : Space m) :
    radialFlatteningCutoff y₀ r R y ≤ 1 :=
  sqCutoffProfile_le_one _ _ _

theorem radialFlatteningCutoff_eq_one {m : ℕ} {y₀ : Space m} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) {y : Space m} (hy : y ∈ closedBall y₀ r) :
    radialFlatteningCutoff y₀ r R y = 1 := by
  rw [mem_closedBall, dist_eq_norm] at hy
  exact sqCutoffProfile_eq_one (by nlinarith) (pow_le_pow_left₀ (norm_nonneg _) hy 2)

theorem radialFlatteningCutoff_eq_zero {m : ℕ} {y₀ : Space m} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) {y : Space m} (hy : R ≤ ‖y - y₀‖) :
    radialFlatteningCutoff y₀ r R y = 0 :=
  sqCutoffProfile_eq_zero (by nlinarith) (pow_le_pow_left₀ (by linarith) hy 2)

theorem tsupport_radialFlatteningCutoff_subset {m : ℕ} {y₀ : Space m} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) : tsupport (radialFlatteningCutoff y₀ r R) ⊆ closedBall y₀ R := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  by_contra hn
  exact hy (radialFlatteningCutoff_eq_zero hr hrR (not_le.mp hn).le)

theorem hasCompactSupport_radialFlatteningCutoff {m : ℕ} {y₀ : Space m} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) : HasCompactSupport (radialFlatteningCutoff y₀ r R) :=
  (isCompact_closedBall y₀ R).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_radialFlatteningCutoff_subset hr hrR)

theorem fderiv_radialFlatteningCutoff_eq_zero {m : ℕ} {y₀ : Space m} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) {y : Space m} (hy : R ≤ ‖y - y₀‖) :
    fderiv ℝ (radialFlatteningCutoff y₀ r R) y = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  refine Filter.Eventually.of_forall fun z ↦ ?_
  rw [radialFlatteningCutoff_eq_zero hr hrR hy]
  exact radialFlatteningCutoff_nonneg _ _ _ _

/-- Universal gradient bound `|∇η| ≤ 2 B / (R - r)` for the radial cutoff, where `B` bounds the
derivative of `Real.smoothTransition`. -/
theorem norm_fderiv_radialFlatteningCutoff_le {m : ℕ} {y₀ : Space m} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (y : Space m) :
    ‖fderiv ℝ (radialFlatteningCutoff y₀ r R) y‖ ≤ 2 * smoothTransitionDerivBound / (R - r) := by
  have hB := smoothTransitionDerivBound_pos
  have hRr : 0 < R - r := by linarith
  by_cases hy : R ≤ ‖y - y₀‖
  · rw [fderiv_radialFlatteningCutoff_eq_zero hr hrR hy, norm_zero]
    positivity
  · have hy' : ‖y - y₀‖ < R := not_le.mp hy
    have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
    set u : ℝ := ‖y - y₀‖ ^ 2
    have hlin : HasDerivAt (fun v : ℝ ↦ (R ^ 2 - v) / (R ^ 2 - r ^ 2))
        (-1 / (R ^ 2 - r ^ 2)) u := by
      simpa using ((hasDerivAt_id u).const_sub (R ^ 2)).div_const (R ^ 2 - r ^ 2)
    have hst : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition ((R ^ 2 - u) / (R ^ 2 - r ^ 2)))
        ((R ^ 2 - u) / (R ^ 2 - r ^ 2)) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    have hprof : HasDerivAt (sqCutoffProfile r R)
        (deriv Real.smoothTransition ((R ^ 2 - u) / (R ^ 2 - r ^ 2)) *
          (-1 / (R ^ 2 - r ^ 2))) u := hst.comp u hlin
    have hnsq : HasFDerivAt (fun z : Space m ↦ ‖z - y₀‖ ^ 2)
        (2 • (innerSL ℝ (y - y₀)).comp (ContinuousLinearMap.id ℝ (Space m))) y :=
      ((hasFDerivAt_id y).sub_const y₀).norm_sq
    have hcomp := hprof.comp_hasFDerivAt y hnsq
    have heq : fderiv ℝ (radialFlatteningCutoff y₀ r R) y =
        (deriv Real.smoothTransition ((R ^ 2 - u) / (R ^ 2 - r ^ 2)) *
          (-1 / (R ^ 2 - r ^ 2))) •
          (2 • (innerSL ℝ (y - y₀)).comp (ContinuousLinearMap.id ℝ (Space m))) :=
      hcomp.fderiv
    rw [heq, norm_smul, Real.norm_eq_abs, abs_mul]
    have h2 : ‖(2 : ℕ) • (innerSL ℝ (y - y₀)).comp (ContinuousLinearMap.id ℝ (Space m))‖ ≤
        2 * ‖y - y₀‖ := by
      rw [two_nsmul]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖(innerSL ℝ (y - y₀)).comp (ContinuousLinearMap.id ℝ (Space m))‖ ≤ ‖y - y₀‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [innerSL_apply_norm]
        exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
      linarith
    have habs : |-1 / (R ^ 2 - r ^ 2)| = 1 / (R ^ 2 - r ^ 2) := by
      rw [neg_div, abs_neg, abs_of_pos (by positivity)]
    rw [habs]
    calc
      |deriv Real.smoothTransition ((R ^ 2 - u) / (R ^ 2 - r ^ 2))| * (1 / (R ^ 2 - r ^ 2)) *
          ‖(2 : ℕ) • (innerSL ℝ (y - y₀)).comp (ContinuousLinearMap.id ℝ (Space m))‖
          ≤ smoothTransitionDerivBound * (1 / (R ^ 2 - r ^ 2)) * (2 * R) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (abs_deriv_smoothTransition_le _)
          (by positivity)) (h2.trans (by linarith)) (norm_nonneg _) (by positivity)
      _ = 2 * smoothTransitionDerivBound / (R - r) * (R / (R + r)) := by
        have hRr' : 0 < R + r := by linarith
        field_simp
        ring
      _ ≤ 2 * smoothTransitionDerivBound / (R - r) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by linarith)]
        linarith
      _ = 2 * smoothTransitionDerivBound / (R - r) := mul_one _

/-! ### 4. The pointwise cofactor inequality (`GR8.1`) -/

/-- Scalar core of `GR8.1`: Young's inequality on the mixed term, `s² ≤ 1 - η²`, and the
concavity bound `√(1 + u) ≤ 1 + u / 2`, written for `W = |w| ≥ 0`. -/
theorem flattening_scalar_bound {P Q h V η W g : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hPQ : P ^ 2 + Q ^ 2 ≤ 1) (hh : 0 ≤ h) (hV : 0 ≤ V) (hhV : h ^ 2 + V ^ 2 = 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hW : 0 ≤ W) (hg : 0 ≤ g) :
    P * ((1 - η ^ 2) * h + 2 * η * W * V * g) + Q * V ≤
      1 - η ^ 2 * h ^ 2 / 4 + 6 * W ^ 2 * g ^ 2 := by
  have hη2' : 0 ≤ η ^ 2 := sq_nonneg η
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have hs0 : 0 ≤ 1 - η ^ 2 := by linarith
  have hs1 : 1 - η ^ 2 ≤ 1 := by linarith
  have hss : (1 - η ^ 2) ^ 2 ≤ 1 - η ^ 2 := by nlinarith
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  have hV1 : V ^ 2 ≤ 1 := by linarith
  have hA : 0 ≤ (1 - η ^ 2) * h + 2 * η * W * V * g := by positivity
  have hAM : 4 * (1 - η ^ 2) * h * η * W * V * g ≤
      η ^ 2 * h ^ 2 / 2 + 8 * (1 - η ^ 2) ^ 2 * W ^ 2 * V ^ 2 * g ^ 2 := by
    have := sq_nonneg (η * h - 4 * (1 - η ^ 2) * W * V * g)
    nlinarith
  have hshh : (1 - η ^ 2) ^ 2 * h ^ 2 ≤ (1 - η ^ 2) * h ^ 2 :=
    mul_le_mul_of_nonneg_right hss hh2
  have hcoef : (8 * (1 - η ^ 2) ^ 2 + 4 * η ^ 2) * V ^ 2 ≤ 12 := by
    have h1 : (1 - η ^ 2) ^ 2 ≤ 1 := hss.trans hs1
    have h3 : 0 ≤ 8 * (1 - η ^ 2) ^ 2 + 4 * η ^ 2 := by positivity
    calc
      (8 * (1 - η ^ 2) ^ 2 + 4 * η ^ 2) * V ^ 2 ≤ (8 * (1 - η ^ 2) ^ 2 + 4 * η ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hV1 h3
      _ ≤ 12 := by linarith
  have hmix : (8 * (1 - η ^ 2) ^ 2 + 4 * η ^ 2) * V ^ 2 * (W ^ 2 * g ^ 2) ≤
      12 * (W ^ 2 * g ^ 2) :=
    mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hA2 : ((1 - η ^ 2) * h + 2 * η * W * V * g) ^ 2 + V ^ 2 ≤
      1 - η ^ 2 * h ^ 2 / 2 + 12 * W ^ 2 * g ^ 2 := by
    linear_combination hshh + hAM + hmix + hhV
  have hX0 : 0 ≤ P * ((1 - η ^ 2) * h + 2 * η * W * V * g) + Q * V := by positivity
  have hCS : (P * ((1 - η ^ 2) * h + 2 * η * W * V * g) + Q * V) ^ 2 ≤
      ((1 - η ^ 2) * h + 2 * η * W * V * g) ^ 2 + V ^ 2 := by
    have hAV : 0 ≤ ((1 - η ^ 2) * h + 2 * η * W * V * g) ^ 2 + V ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hPQ hAV
    have h2 := sq_nonneg (P * V - Q * ((1 - η ^ 2) * h + 2 * η * W * V * g))
    linear_combination h1 + h2
  have hc0 : 0 ≤ 1 - η ^ 2 * h ^ 2 / 4 + 6 * W ^ 2 * g ^ 2 := by
    have h1 : η ^ 2 * h ^ 2 ≤ 1 := by nlinarith
    have h6 : 0 ≤ 6 * W ^ 2 * g ^ 2 := by positivity
    linarith
  have hsq : (P * ((1 - η ^ 2) * h + 2 * η * W * V * g) + Q * V) ^ 2 ≤
      (1 - η ^ 2 * h ^ 2 / 4 + 6 * W ^ 2 * g ^ 2) ^ 2 := by
    have := sq_nonneg (-(η ^ 2 * h ^ 2 / 2) + 12 * W ^ 2 * g ^ 2)
    nlinarith
  exact (pow_le_pow_iff_left₀ hX0 hc0 two_ne_zero).mp hsq

/-- Vector form of `GR8.1` at a band point: with `a, c` the horizontal and vertical parts of a
unit-bounded test value, `h, n` those of the unit normal, `η` the cutoff value and `L = Dη`,
`|(1 - η²) ⟪X, ν⟫ + (2 η L(a) w + η² c) n| ≤ 1 - η² |h|² / 4 + 6 w² ‖L‖²`. -/
theorem flattening_pointwise_bound {m : ℕ} {a h : Space m} {c n η w : ℝ}
    {L : Space m →L[ℝ] ℝ} (hac : ‖a‖ ^ 2 + c ^ 2 ≤ 1) (hhn : ‖h‖ ^ 2 + n ^ 2 = 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    |(1 - η ^ 2) * (inner ℝ a h + c * n) + (2 * η * L a * w + η ^ 2 * c) * n| ≤
      1 - η ^ 2 * ‖h‖ ^ 2 / 4 + 6 * w ^ 2 * ‖L‖ ^ 2 := by
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have hs0 : 0 ≤ 1 - η ^ 2 := by linarith
  have hexpr : (1 - η ^ 2) * (inner ℝ a h + c * n) + (2 * η * L a * w + η ^ 2 * c) * n =
      (1 - η ^ 2) * inner ℝ a h + 2 * η * w * n * L a + c * n := by
    ring
  have hLa : |L a| ≤ ‖L‖ * ‖a‖ := by
    simpa [Real.norm_eq_abs] using L.le_opNorm a
  have hah : |inner ℝ a h| ≤ ‖a‖ * ‖h‖ := abs_real_inner_le_norm a h
  have hbound : |(1 - η ^ 2) * inner ℝ a h + 2 * η * w * n * L a + c * n| ≤
      ‖a‖ * ((1 - η ^ 2) * ‖h‖ + 2 * η * |w| * |n| * ‖L‖) + |c| * |n| := by
    calc
      |(1 - η ^ 2) * inner ℝ a h + 2 * η * w * n * L a + c * n|
          ≤ |(1 - η ^ 2) * inner ℝ a h| + |2 * η * w * n * L a| + |c * n| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (1 - η ^ 2) * |inner ℝ a h| + 2 * η * |w| * |n| * |L a| + |c| * |n| := by
        rw [abs_mul, abs_of_nonneg hs0, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hη0,
          abs_two, abs_mul]
      _ ≤ (1 - η ^ 2) * (‖a‖ * ‖h‖) + 2 * η * |w| * |n| * (‖L‖ * ‖a‖) + |c| * |n| := by
        gcongr
      _ = ‖a‖ * ((1 - η ^ 2) * ‖h‖ + 2 * η * |w| * |n| * ‖L‖) + |c| * |n| := by ring
  rw [hexpr]
  refine hbound.trans ?_
  have hsc := flattening_scalar_bound (P := ‖a‖) (Q := |c|) (h := ‖h‖) (V := |n|) (η := η)
    (W := |w|) (g := ‖L‖) (norm_nonneg _) (abs_nonneg _) (by rwa [sq_abs]) (norm_nonneg _)
    (abs_nonneg _) (by rwa [sq_abs]) hη0 hη1 (abs_nonneg _) (norm_nonneg _)
  rwa [sq_abs] at hsc

end SerrinEpigraph
