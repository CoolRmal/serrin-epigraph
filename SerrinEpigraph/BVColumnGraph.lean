module

public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.MinimizerDensity
public import SerrinEpigraph.GraphPerimeter
public import SerrinEpigraph.HarmonicOneDimensionalLimit
public import SerrinEpigraph.LipschitzMollificationDerivative
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Vertical column flux, horizontal moments, jump counting, and good-column graph representation

This module implements BV13–BV14 (`docs/rigidity-proof/bv-minimizers.md`) in the cylinder/slab
setting tailored for GR8–GR11 (`docs/rigidity-proof/gmt-regularity.md`):
1. Slab localization of the perimeter measure `μ` and measurability/bounds for
   `columnSignedHeight`.
2. Net vertical flux `π_# (ν_n μ) = dy` on `U` and exact decomposition
   `projectedPerimeterMeasure μ A = volume A + projectedExcessMeasure μ ν A` for all measurable
   `A ⊆ U`.
3. Horizontal moment formula identifying the weak gradient of `columnSignedHeight` with
   `-π_# (ν_h μ)` and the Cauchy–Schwarz divergence bound (`GR9.1`).
4. Elementary 4-bump 1D jump-counting lemma (requiring no 1D Jordan decomposition), the global
   multi-layer column bound `volume M_set ≤ projectedExcessMeasure μ ν M_set` (`GR10`), and
   single-layer epigraph identification on good column sets (`BV14.2`).
5. Global Radon/polar representation of `epigraph f` for Lipschitz `f`, and strong locality
   identifying `μ` and `ν` on `{x ∈ cylinderSet U H' | horizontal x ∈ G}` with the graph area
   measure and inward unit normal of `f` (`BV13.4–13.5`, `BV14b–14c`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported ENNReal Convolution

namespace SerrinEpigraph

/-! ### 1. Cylinder geometry, product Fubini helpers, slab support, and `columnSignedHeight` -/

/-- Open vertical cylinder over `U ⊆ Space m` with height interval `Ioo (-H') H'`. -/
def cylinderSet {m : ℕ} (U : Set (Space m)) (H' : ℝ) : Set (Space (m + 1)) :=
  {x | horizontal x ∈ U ∧ x (Fin.last m) ∈ Ioo (-H') H'}

@[simp]
theorem mem_cylinderSet {m : ℕ} {U : Set (Space m)} {H' : ℝ} {x : Space (m + 1)} :
    x ∈ cylinderSet U H' ↔ horizontal x ∈ U ∧ x (Fin.last m) ∈ Ioo (-H') H' :=
  Iff.rfl

@[simp]
theorem point_mem_cylinderSet {m : ℕ} {U : Set (Space m)} {H' : ℝ} {y : Space m} {t : ℝ} :
    point y t ∈ cylinderSet U H' ↔ y ∈ U ∧ t ∈ Ioo (-H') H' := by
  simp [cylinderSet]

theorem isOpen_cylinderSet {m : ℕ} {U : Set (Space m)} (hU : IsOpen U) (H' : ℝ) :
    IsOpen (cylinderSet U H') :=
  (hU.preimage continuous_horizontal).inter
    (isOpen_Ioo.preimage ((PiLp.continuous_apply 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m))))

theorem measurableSet_cylinderSet {m : ℕ} {U : Set (Space m)} (hU : MeasurableSet U) (H' : ℝ) :
    MeasurableSet (cylinderSet U H') :=
  (hU.preimage continuous_horizontal.measurable).inter
    (measurableSet_Ioo.preimage
      ((PiLp.continuous_apply 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).measurable))

theorem cylinderSet_mono {m : ℕ} {U₁ U₂ : Set (Space m)} {H₁ H₂ : ℝ}
    (hU : U₁ ⊆ U₂) (hH : H₁ ≤ H₂) :
    cylinderSet U₁ H₁ ⊆ cylinderSet U₂ H₂ := by
  rintro x ⟨hxU, hxH⟩
  exact ⟨hU hxU, ⟨by linarith [hxH.1], by linarith [hxH.2]⟩⟩

/-- Assembling `(y, t) ↦ point y t` preserves Lebesgue product measure. -/
theorem measurePreserving_point (m : ℕ) :
    MeasurePreserving (fun p : Space m × ℝ ↦ point p.1 p.2)
      ((volume : Measure (Space m)).prod volume) volume := by
  have hp := measurePreserving_horizontal_last m
  have hmeas_pt : Measurable (fun p : Space m × ℝ ↦ point p.1 p.2) :=
    pointContinuousLinearMap.continuous.measurable
  refine ⟨hmeas_pt, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas_pt hs]
  have hpre : (fun x : Space (m + 1) ↦ (horizontal x, x (Fin.last m))) ⁻¹'
      ((fun p : Space m × ℝ ↦ point p.1 p.2) ⁻¹' s) = s := by
    ext x
    simp [point_horizontal_last]
  have hmeas : MeasurableSet ((fun p : Space m × ℝ ↦ point p.1 p.2) ⁻¹' s) :=
    hs.preimage hmeas_pt
  simpa only [hpre] using (hp.measure_preimage hmeas.nullMeasurableSet).symm

/-- Fubini decomposition of an integrable function on `Space (m + 1)` into horizontal and vertical
integrals. -/
theorem integral_space_eq_integral_horizontal_vertical {m : ℕ}
    {g : Space (m + 1) → ℝ} (hg : Integrable g volume) :
    (∫ x, g x) = ∫ y : Space m, ∫ t : ℝ, g (point y t) := by
  let Q : Space m × ℝ → ℝ := fun p ↦ g (point p.1 p.2)
  have hmp := measurePreserving_point m
  have hQi : Integrable Q ((volume : Measure (Space m)).prod volume) :=
    hmp.integrable_comp_of_integrable hg
  have hmap := integral_map hmp.measurable.aemeasurable
    (show AEStronglyMeasurable g
      (Measure.map (fun p : Space m × ℝ ↦ point p.1 p.2) ((volume : Measure (Space m)).prod volume))
      from by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  rw [hmap, ← integral_prod _ hQi]

/-- Vertical slicing of a `volume`-almost-everywhere property on `Space (m + 1)`. -/
theorem ae_vertical_of_ae_volume {m : ℕ} {P : Space (m + 1) → Prop}
    (hP : ∀ᵐ x : Space (m + 1) ∂volume, P x) :
    ∀ᵐ y : Space m ∂volume, ∀ᵐ t : ℝ ∂volume, P (point y t) := by
  have hprod : ∀ᵐ p : Space m × ℝ ∂((volume : Measure (Space m)).prod volume),
      P (point p.1 p.2) :=
    (measurePreserving_point m).quasiMeasurePreserving.ae hP
  exact Measure.ae_ae_of_ae_prod hprod

/-- If `E` is a.e. empty on the bottom cap `U × Ioo (-H') (-H)` and a.e. full on the top cap
`U × Ioo H H'`, then any measure `μ` agreeing with `variationalPerimeter b E` on open subsets of
`cylinderSet U H'` assigns zero mass to `{x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H}`. -/
theorem measure_cylinderSet_notMem_Icc_eq_zero {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} {U : Set (Space m)} (hU : IsOpen U)
    {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1)))
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E) :
    μ {x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H} = 0 := by
  let Vbot : Set (Space (m + 1)) := {x | horizontal x ∈ U ∧ x (Fin.last m) ∈ Ioo (-H') (-H)}
  let Vtop : Set (Space (m + 1)) := {x | horizontal x ∈ U ∧ x (Fin.last m) ∈ Ioo H H'}
  have hVbot_open : IsOpen Vbot :=
    (hU.preimage continuous_horizontal).inter
      (isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)))
  have hVtop_open : IsOpen Vtop :=
    (hU.preimage continuous_horizontal).inter
      (isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)))
  have hVbot_sub : Vbot ⊆ cylinderSet U H' := fun x ⟨hxU, hxt⟩ ↦
    ⟨hxU, hxt.1, by linarith [hxt.2]⟩
  have hVtop_sub : Vtop ⊆ cylinderSet U H' := fun x ⟨hxU, hxt⟩ ↦
    ⟨hxU, by linarith [hxt.1], hxt.2⟩
  have hsub : {x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H} ⊆ Vbot ∪ Vtop := by
    rintro x ⟨⟨hxU, hxt⟩, hnot⟩
    by_cases hlt : x (Fin.last m) < -H
    · exact Or.inl ⟨hxU, hxt.1, hlt⟩
    · have hgt : H < x (Fin.last m) := lt_of_not_ge fun hle ↦ hnot ⟨not_lt.mp hlt, hle⟩
      exact Or.inr ⟨hxU, hgt, hxt.2⟩
  have hμ_bot : μ Vbot = 0 := by
    rw [hμopen Vbot hVbot_open hVbot_sub]
    have hcongr : variationalPerimeter b E Vbot = variationalPerimeter b ∅ Vbot := by
      apply variationalPerimeter_congr_ae_on b
      filter_upwards [hbot] with x hx hxV
      simp [hx hxV.1 hxV.2]
    rw [hcongr]
    unfold variationalPerimeter
    simp
  have hμ_top : μ Vtop = 0 := by
    rw [hμopen Vtop hVtop_open hVtop_sub]
    have hcongr : variationalPerimeter b E Vtop = variationalPerimeter b univ Vtop := by
      apply variationalPerimeter_congr_ae_on b
      filter_upwards [htop] with x hx hxV
      simp [hx hxV.1 hxV.2]
    rw [hcongr, variationalPerimeter_univ]
  refine nonpos_iff_eq_zero.mp ?_
  calc
    μ {x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H}
        ≤ μ (Vbot ∪ Vtop) := measure_mono hsub
    _ ≤ μ Vbot + μ Vtop := measure_union_le _ _
    _ = 0 := by rw [hμ_bot, hμ_top, add_zero]

/-- When `μ` is concentrated on `cylinderSet U H'`, almost every `μ`-point projects into `U` and
has vertical coordinate inside the closed slab `Icc (-H) H`. -/
theorem ae_mem_slab_of_slab_trapped {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} {U : Set (Space m)} (hU : IsOpen U)
    {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E) :
    ∀ᵐ x ∂μ, horizontal x ∈ U ∧ x (Fin.last m) ∈ Icc (-H) H := by
  have hcap := measure_cylinderSet_notMem_Icc_eq_zero b hU hH hHH' μ hμopen hbot htop
  rw [ae_iff]
  have hsub : {x : Space (m + 1) | ¬(horizontal x ∈ U ∧ x (Fin.last m) ∈ Icc (-H) H)} ⊆
      (cylinderSet U H')ᶜ ∪ {x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H} := by
    intro x hx
    by_cases hxΩ : x ∈ cylinderSet U H'
    · exact Or.inr ⟨hxΩ, fun hI ↦ hx ⟨hxΩ.1, hI⟩⟩
    · exact Or.inl hxΩ
  refine nonpos_iff_eq_zero.mp ?_
  calc
    μ {x | ¬(horizontal x ∈ U ∧ x (Fin.last m) ∈ Icc (-H) H)}
        ≤ μ ((cylinderSet U H')ᶜ ∪ {x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H}) :=
      measure_mono hsub
    _ ≤ μ (cylinderSet U H')ᶜ + μ {x ∈ cylinderSet U H' | x (Fin.last m) ∉ Icc (-H) H} :=
      measure_union_le _ _
    _ = 0 := by rw [hμcompl, hcap, add_zero]

/-- Signed height of a vertical column in `[-H, H]`, defined without assuming single-layer
structure (`BV14`, `GR9`). -/
def columnSignedHeight {m : ℕ} (E : Set (Space (m + 1))) (H : ℝ) (y : Space m) : ℝ :=
  (∫ t in Icc (-H) H, (1 - E.indicator (fun _ ↦ (1 : ℝ)) (point y t))) - H

theorem columnSignedHeight_mem_Icc {m : ℕ} (E : Set (Space (m + 1))) {H : ℝ} (hH : 0 ≤ H)
    (y : Space m) :
    columnSignedHeight E H y ∈ Icc (-H) H := by
  let f : ℝ → ℝ := fun t ↦ 1 - E.indicator (fun _ ↦ (1 : ℝ)) (point y t)
  have hf0 (t : ℝ) : 0 ≤ f t := by
    dsimp [f]
    by_cases hx : point y t ∈ E <;> simp [hx]
  have hf1 (t : ℝ) : f t ≤ 1 := by
    dsimp [f]
    by_cases hx : point y t ∈ E <;> simp [hx]
  have hlow : 0 ≤ ∫ t in Icc (-H) H, f t := integral_nonneg hf0
  have hhigh : (∫ t in Icc (-H) H, f t) ≤ 2 * H := by
    by_cases hfi : IntegrableOn f (Icc (-H) H) volume
    · have hc : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-H) H) volume :=
        integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      have hle := integral_mono hfi hc hf1
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
        sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith)] at hle
      linarith
    · rw [integral_undef hfi]
      linarith
  dsimp [columnSignedHeight]
  change (∫ t in Icc (-H) H, f t) - H ∈ Icc (-H) H
  exact ⟨by linarith, by linarith⟩

theorem measurable_columnSignedHeight {m : ℕ} {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (H : ℝ) :
    Measurable (columnSignedHeight E H) := by
  have hmeas_prod : Measurable (fun p : Space m × ℝ ↦
      (1 : ℝ) - E.indicator (fun _ ↦ (1 : ℝ)) (point p.1 p.2)) :=
    measurable_const.sub ((measurable_const.indicator hE).comp
      pointContinuousLinearMap.continuous.measurable)
  have hsm := hmeas_prod.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc (-H) H))
  exact hsm.measurable.sub measurable_const

theorem columnSignedHeight_eq_sub_integral {m : ℕ} {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {H : ℝ} (hH : 0 ≤ H) (y : Space m) :
    columnSignedHeight E H y =
      H - ∫ t in Icc (-H) H, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) := by
  have hfin : volume (Icc (-H) H) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hc : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-H) H) volume := integrableOn_const hfin
  have hi : IntegrableOn (fun t ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t))
      (Icc (-H) H) volume := by
    refine hc.mono' (((measurable_const.indicator hE).comp
      (continuous_point y).measurable).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun t ↦ by by_cases hx : point y t ∈ E <;> simp [hx]
  unfold columnSignedHeight
  rw [integral_sub hc hi, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    Real.volume_Icc, sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith)]
  ring

/-! ### 2. Net vertical flux and projected excess measure (`BV13.2`, `BV14`, `GR8`, `GR9`) -/

@[simp]
theorem horizontal_verticalDirection (m : ℕ) :
    horizontal (verticalDirection m) = 0 := by
  ext i
  simp [horizontal, verticalDirection]

@[simp]
theorem last_verticalDirection (m : ℕ) :
    verticalDirection m (Fin.last m) = 1 := by
  simp [verticalDirection]

@[simp]
theorem point_zero_one_eq_verticalDirection (m : ℕ) :
    point (0 : Space m) 1 = verticalDirection m := by
  have h := point_add_vertical (0 : Space m) 0 1
  have hp0 : point (0 : Space m) 0 = 0 := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]
  rw [hp0, zero_add, zero_add, one_smul] at h
  exact h.symm

@[simp]
theorem inner_verticalDirection_right {m : ℕ} (u : Space (m + 1)) :
    inner ℝ u (verticalDirection m) = u (Fin.last m) := by
  nth_rw 1 [← point_horizontal_last u]
  rw [← point_zero_one_eq_verticalDirection m, inner_point_point]
  simp

@[simp]
theorem inner_point_zero_right {m : ℕ} (u : Space (m + 1)) (w : Space m) :
    inner ℝ u (point w 0) = inner ℝ (horizontal u) w := by
  nth_rw 1 [← point_horizontal_last u]
  rw [inner_point_point]
  simp

/-- Divergence of a product vector field `(φ (horizontal x) * ψ (x_last)) • v` along a constant
ambient vector `v`. -/
private theorem fieldDivergence_horizontal_mul_vertical_smul {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {φ : Space m → ℝ} (hφ : ContDiff ℝ 1 φ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (v : Space (m + 1)) (x : Space (m + 1)) :
    fieldDivergence b (fun z ↦ (φ (horizontal z) * ψ (z (Fin.last m))) • v) x =
      fderiv ℝ φ (horizontal x) (horizontal v) * ψ (x (Fin.last m)) +
        φ (horizontal x) * (deriv ψ (x (Fin.last m)) * v (Fin.last m)) := by
  let Llast : Space (m + 1) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hd_horiz : HasFDerivAt (fun z : Space (m + 1) ↦ φ (horizontal z))
      ((fderiv ℝ φ (horizontal x)).comp horizontalContinuousLinearMap) x :=
    (hφ.differentiable_one (horizontal x)).hasFDerivAt.comp x
      horizontalContinuousLinearMap.hasFDerivAt
  have hd_vert : HasFDerivAt (fun z : Space (m + 1) ↦ ψ (z (Fin.last m)))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ (x (Fin.last m)))).comp Llast) x :=
    ((hψ.differentiable_one (x (Fin.last m))).hasDerivAt.hasFDerivAt).comp x Llast.hasFDerivAt
  have hd_prod := hd_horiz.mul hd_vert
  have hdiv := fieldDivergence_fun_smul b hd_prod.differentiableAt (differentiableAt_const v)
  have hconst : fieldDivergence b (fun _ : Space (m + 1) ↦ v) x = 0 := by
    simp [fieldDivergence]
  rw [hconst, mul_zero, zero_add, inner_gradient_left, hd_prod.fderiv] at hdiv
  dsimp only [Pi.mul_apply] at hdiv
  rw [hdiv]
  simp only [Llast, horizontalContinuousLinearMap, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, PiLp.proj_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

/-- Compactly supported product field `(φ (horizontal x) * ψ (x_last)) • v` inside
`cylinderSet U H'`. -/
private theorem hasCompactSupport_product_field {m : ℕ}
    {U : Set (Space m)} {H' : ℝ}
    {φ : Space m → ℝ} (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ U)
    {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioo (-H') H')
    (v : Space (m + 1)) :
    HasCompactSupport (fun x : Space (m + 1) ↦ (φ (horizontal x) * ψ (x (Fin.last m))) • v) ∧
      tsupport (fun x : Space (m + 1) ↦ (φ (horizontal x) * ψ (x (Fin.last m))) • v) ⊆
        cylinderSet U H' := by
  let F : Space (m + 1) → Space (m + 1) :=
    fun x ↦ (φ (horizontal x) * ψ (x (Fin.last m))) • v
  let K : Set (Space (m + 1)) :=
    (fun p : Space m × ℝ ↦ point p.1 p.2) '' (tsupport φ ×ˢ tsupport ψ)
  have hK : IsCompact K :=
    (hφc.prod hψc).image pointContinuousLinearMap.continuous
  have hsupp : Function.support F ⊆ K := by
    intro x hx
    have hφx : φ (horizontal x) ≠ 0 := fun h0 ↦ hx (by simp [F, h0])
    have hψx : ψ (x (Fin.last m)) ≠ 0 := fun h0 ↦ hx (by simp [F, h0])
    exact ⟨(horizontal x, x (Fin.last m)),
      ⟨subset_tsupport φ hφx, subset_tsupport ψ hψx⟩, point_horizontal_last x⟩
  have htsK : tsupport F ⊆ K := closure_minimal hsupp hK.isClosed
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport F) htsK, htsK.trans ?_⟩
  rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
  exact point_mem_cylinderSet.mpr ⟨hφs hy, hψs ht⟩

/-- Smooth vertical bump equal to `1` on `Icc (-(H + H') / 2) ((H + H') / 2)` and compactly
supported in `Ioo (-H') H'`. -/
private def slabVerticalCutoff {H H' : ℝ} (hH : 0 < H) (hHH' : H < H') : ContDiffBump (0 : ℝ) where
  rIn := (H + H') / 2
  rOut := (H + 3 * H') / 4
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

private theorem slabVerticalCutoff_props {H H' : ℝ} (hH : 0 < H) (hHH' : H < H') :
    let ψ : ℝ → ℝ := slabVerticalCutoff hH hHH'
    ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo (-H') H' ∧
      (∀ t ∈ Icc (-(H + H') / 2) ((H + H') / 2), ψ t = 1) ∧
      (∀ t ∈ Icc (-H) H, deriv ψ t = 0) := by
  let B := slabVerticalCutoff hH hHH'
  refine ⟨B.contDiff, B.hasCompactSupport, ?_, ?_, ?_⟩
  · rw [B.tsupport_eq]
    intro t ht
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc] at ht
    have hrOut : B.rOut = (H + 3 * H') / 4 := rfl
    rw [hrOut] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    apply B.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc]
    have hrIn : B.rIn = (H + H') / 2 := rfl
    rw [hrIn]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    have hmem : Ioo (-(H + H') / 2) ((H + H') / 2) ∈ 𝓝 t :=
      isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hev : (B : ℝ → ℝ) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hmem] with s hs
      apply B.one_of_mem_closedBall
      rw [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc]
      have hrIn : B.rIn = (H + H') / 2 := rfl
      rw [hrIn]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa using hev.deriv_eq

/-- Net vertical flux identity (`BV13.2`, `BV14`, `GR8`): the horizontal projection of `ν_n μ`
equals Lebesgue measure on `U` when tested against `C¹_c(U)` functions. -/
theorem integral_vertical_flux_eq_integral {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)}
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {φ : Space m → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U) :
    (∫ x, φ (horizontal x) * inner ℝ (ν x) (verticalDirection m) ∂μ) = ∫ y, φ y := by
  let ψ : ℝ → ℝ := slabVerticalCutoff hH hHH'
  obtain ⟨hψ, hψc, hψs, hψone, hψderiv0⟩ := slabVerticalCutoff_props hH hHH'
  let F₀ : Space (m + 1) → Space (m + 1) :=
    fun x ↦ (φ (horizontal x) * ψ (x (Fin.last m))) • verticalDirection m
  have hF₀_diff : ContDiff ℝ 1 F₀ :=
    ((hφ.comp horizontalContinuousLinearMap.contDiff).mul
      (hψ.comp (PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).contDiff)).smul contDiff_const
  obtain ⟨hF₀_comp, hF₀_sub⟩ :=
    hasCompactSupport_product_field hφc hφs hψc hψs (verticalDirection m)
  let Fc : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨F₀, hF₀_diff.continuous⟩, hF₀_comp⟩
  have hid := hdist Fc hF₀_diff hF₀_sub
  have hslab := ae_mem_slab_of_slab_trapped b hU hH hHH' μ hμcompl hμopen hbot htop
  have hrhs : (∫ x, inner ℝ (Fc x) (ν x) ∂μ) =
      ∫ x, φ (horizontal x) * inner ℝ (ν x) (verticalDirection m) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hslab] with x ⟨_, hxI⟩
    change inner ℝ ((φ (horizontal x) * ψ (x (Fin.last m))) • verticalDirection m) (ν x) = _
    have h1 : ψ (x (Fin.last m)) = 1 :=
      hψone _ ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    rw [real_inner_smul_left, h1, mul_one, real_inner_comm]
  have hdiv_eq (x : Space (m + 1)) :
      fieldDivergence b Fc x = φ (horizontal x) * deriv ψ (x (Fin.last m)) := by
    change fieldDivergence b F₀ x = _
    dsimp only [F₀, ψ]
    rw [fieldDivergence_horizontal_mul_vertical_smul b hφ hψ (verticalDirection m) x]
    simp
  have hg_int : Integrable
      (fun x : Space (m + 1) ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x)
      volume := by
    have hcont := fieldDivergence_continuous b hF₀_diff
    have hdiv_supp : tsupport (fieldDivergence b F₀) ⊆ tsupport F₀ := by
      apply closure_minimal _ (isClosed_tsupport F₀)
      intro x hx
      by_contra hn
      exact hx (fieldDivergence_zero_of_notMem_tsupport b F₀ hn)
    have hdiv_c : HasCompactSupport (fieldDivergence b F₀) :=
      hF₀_comp.of_isClosed_subset (isClosed_tsupport _) hdiv_supp
    have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hdiv_c).indicator hE
    refine hi.congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ E <;> simp [hx, Fc]
  have hlhs : -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x) = ∫ y, φ y := by
    rw [integral_space_eq_integral_horizontal_vertical hg_int]
    simp_rw [hdiv_eq, horizontal_point, last_point]
    have hbot_slice := ae_vertical_of_ae_volume hbot
    have htop_slice := ae_vertical_of_ae_volume htop
    have hinner : ∀ᵐ y : Space m ∂volume,
        (∫ t : ℝ, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * (φ y * deriv ψ t)) = -φ y := by
      filter_upwards [hbot_slice, htop_slice] with y hybot hytop
      by_cases hyU : y ∈ U
      · have hfactor : (fun t : ℝ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
            (φ y * deriv ψ t)) = fun t ↦ φ y * (E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
              deriv ψ t) := by
          ext t; ring
        rw [hfactor, integral_const_mul]
        have hae_t : (fun t : ℝ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * deriv ψ t) =ᵐ[volume]
            (Ioi H).indicator (deriv ψ) := by
          filter_upwards [hybot, hytop] with t htb htt
          simp only [horizontal_point, last_point] at htb htt
          by_cases htH : H < t
          · rw [indicator_of_mem (mem_Ioi.mpr htH)]
            by_cases htH' : t < H'
            · have hinE : point y t ∈ E := htt hyU ⟨htH, htH'⟩
              simp [hinE]
            · have hnot : t ∉ tsupport ψ := fun hs ↦ htH' (hψs hs).2
              have hev : ψ =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
                filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hnot] with s hs
                exact image_eq_zero_of_notMem_tsupport hs
              have hd0 : deriv ψ t = 0 := by simpa using hev.deriv_eq
              simp [hd0]
          · rw [indicator_of_notMem (mem_Ioi.not.mpr htH)]
            have htle : t ≤ H := not_lt.mp htH
            by_cases htlow : -H ≤ t
            · rw [hψderiv0 t ⟨htlow, htle⟩, mul_zero]
            · have htlt : t < -H := not_le.mp htlow
              by_cases htH' : -H' < t
              · have hnotE : point y t ∉ E := htb hyU ⟨htH', htlt⟩
                simp [hnotE]
              · have hnot : t ∉ tsupport ψ := fun hs ↦ htH' (hψs hs).1
                have hev : ψ =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
                  filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hnot] with s hs
                  exact image_eq_zero_of_notMem_tsupport hs
                have hd0 : deriv ψ t = 0 := by simpa using hev.deriv_eq
                simp [hd0]
        rw [integral_congr_ae hae_t, integral_indicator measurableSet_Ioi,
          hψc.integral_Ioi_deriv_eq hψ H, hψone H ⟨by linarith, by linarith⟩]
        ring
      · have hφ0 : φ y = 0 := image_eq_zero_of_notMem_tsupport fun hs ↦ hyU (hφs hs)
        simp [hφ0]
    rw [integral_congr_ae hinner, integral_neg, neg_neg]
  rw [← hrhs, ← hid, hlhs]

/-- Projected perimeter measure `π_# μ` on the horizontal base `Space m`. -/
def projectedPerimeterMeasure {m : ℕ} (μ : Measure (Space (m + 1))) : Measure (Space m) :=
  Measure.map horizontal μ

/-- Projected tilt-excess measure `π_# ((1 - ν_n) μ)` on `Space m`. -/
def projectedExcessMeasure {m : ℕ} (μ : Measure (Space (m + 1)))
    (ν : Space (m + 1) → Space (m + 1)) : Measure (Space m) :=
  Measure.map horizontal
    (μ.withDensity (fun x ↦ ENNReal.ofReal (1 - inner ℝ (ν x) (verticalDirection m))))

instance instIsFiniteMeasureProjectedPerimeterMeasure {m : ℕ} (μ : Measure (Space (m + 1)))
    [IsFiniteMeasure μ] : IsFiniteMeasure (projectedPerimeterMeasure μ) := by
  unfold projectedPerimeterMeasure
  exact Measure.isFiniteMeasure_map μ horizontal

theorem isFiniteMeasure_projectedExcessMeasure {m : ℕ} (μ : Measure (Space (m + 1)))
    [IsFiniteMeasure μ] {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ) :
    IsFiniteMeasure (projectedExcessMeasure μ ν) := by
  let μe := μ.withDensity (fun x ↦ ENNReal.ofReal (1 - inner ℝ (ν x) (verticalDirection m)))
  have hfin : IsFiniteMeasure μe := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have hle : ∀ x, ENNReal.ofReal (1 - inner ℝ (ν x) (verticalDirection m)) ≤
        1 + ‖ν x‖ₑ := by
      intro x
      have hcs := abs_real_inner_le_norm (ν x) (verticalDirection m)
      rw [norm_verticalDirection, mul_one] at hcs
      have hbound : 1 - inner ℝ (ν x) (verticalDirection m) ≤ 1 + ‖ν x‖ := by
        linarith [(abs_le.mp hcs).1]
      calc
        ENNReal.ofReal (1 - inner ℝ (ν x) (verticalDirection m))
            ≤ ENNReal.ofReal (1 + ‖ν x‖) := ENNReal.ofReal_le_ofReal hbound
        _ = 1 + ‖ν x‖ₑ := by
          rw [ENNReal.ofReal_add zero_le_one (norm_nonneg _), ENNReal.ofReal_one, ofReal_norm]
    calc
      (∫⁻ x, ENNReal.ofReal (1 - inner ℝ (ν x) (verticalDirection m)) ∂μ)
          ≤ ∫⁻ x, (1 + ‖ν x‖ₑ) ∂μ := lintegral_mono hle
      _ = (∫⁻ _, (1 : ℝ≥0∞) ∂μ) + ∫⁻ x, ‖ν x‖ₑ ∂μ := lintegral_add_left measurable_const _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨by simp [measure_lt_top], hν.2⟩
  unfold projectedExcessMeasure
  exact Measure.isFiniteMeasure_map μe horizontal

private theorem isLocallyFiniteMeasure_add {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ₁ μ₂ : Measure α) [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure μ₂] :
    IsLocallyFiniteMeasure (μ₁ + μ₂) := by
  constructor
  intro x
  obtain ⟨s₁, hs₁x, hs₁open, hfin₁⟩ := μ₁.exists_isOpen_measure_lt_top x
  obtain ⟨s₂, hs₂x, hs₂open, hfin₂⟩ := μ₂.exists_isOpen_measure_lt_top x
  refine ⟨s₁ ∩ s₂, (hs₁open.inter hs₂open).mem_nhds ⟨hs₁x, hs₂x⟩, ?_⟩
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.mpr
    ⟨lt_of_le_of_lt (measure_mono inter_subset_left) hfin₁,
     lt_of_le_of_lt (measure_mono inter_subset_right) hfin₂⟩

/-- Two locally finite measures on `Space d` that agree against all `C¹_c` functions supported in an
open set `O` have identical restrictions to `O`. -/
theorem measure_restrict_open_eq_of_integral_contDiff_eq {d : ℕ}
    (μ₁ μ₂ : Measure (Space d)) [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure μ₂]
    {O : Set (Space d)} (hO : IsOpen O)
    (heq : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x, φ x ∂μ₁) = ∫ x, φ x ∂μ₂) :
    μ₁.restrict O = μ₂.restrict O := by
  have hcont_eq : ∀ χ : Space d → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ O →
      (∫ x, χ x ∂μ₁) = ∫ x, χ x ∂μ₂ := by
    intro χ hχ hχc hχs
    let K₀ := tsupport χ
    have hK₀ : IsCompact K₀ := hχc
    obtain ⟨C, hC⟩ := hK₀.exists_bound_of_continuousOn hχ.continuousOn
    have hχ_bound (x : Space d) : ‖χ x‖ ≤ max C 0 := by
      by_cases hx : x ∈ K₀
      · exact (hC x hx).trans (le_max_left _ _)
      · simp [image_eq_zero_of_notMem_tsupport hx]
    let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
    have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
    have hg_ex (j : ℕ) := hχ.exists_contDiff_approx 1 (ε := fun _ ↦ ε j)
      continuous_const (fun _ ↦ hε j)
    choose g hg hclose hsupp using hg_ex
    have hgs (j : ℕ) : tsupport (g j) ⊆ K₀ := closure_mono (hsupp j)
    have hgc (j : ℕ) : HasCompactSupport (g j) := hK₀.of_isClosed_subset (isClosed_tsupport _) (hgs j)
    have hg1 (j : ℕ) : ContDiff ℝ 1 (g j) := by simpa using hg j
    have hgt (x : Space d) : Tendsto (fun j ↦ g j x) atTop (𝓝 (χ x)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ (hclose j x).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim (μ₀ : Measure (Space d)) [IsLocallyFiniteMeasure μ₀] :
        Tendsto (fun j ↦ ∫ x, g j x ∂μ₀) atTop (𝓝 (∫ x, χ x ∂μ₀)) := by
      have hfinK : μ₀ K₀ ≠ ⊤ := hK₀.measure_lt_top.ne
      have hdom : Integrable (K₀.indicator (fun _ ↦ max C 0 + 1)) μ₀ :=
        (integrableOn_const hfinK).integrable_indicator hK₀.measurableSet
      refine tendsto_integral_of_dominated_convergence (K₀.indicator (fun _ ↦ max C 0 + 1))
        (fun j ↦ (hg1 j).continuous.aestronglyMeasurable) hdom (fun j ↦ ?_)
        (Eventually.of_forall hgt)
      refine Eventually.of_forall fun x ↦ ?_
      by_cases hx : x ∈ K₀
      · rw [indicator_of_mem hx]
        have hd := hclose j x
        rw [dist_eq_norm] at hd
        have hε1 : ε j ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
        have htri : ‖g j x‖ ≤ ‖g j x - χ x‖ + ‖χ x‖ := by
          simpa only [sub_add_cancel] using norm_add_le (g j x - χ x) (χ x)
        linarith [hχ_bound x]
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hgs j hh)),
          norm_zero]
    exact tendsto_nhds_unique (hlim μ₁)
      ((hlim μ₂).congr fun j ↦ (heq (g j) (hg1 j) (hgc j) ((hgs j).trans hχs)).symm)
  have hopen_le (ν₁ ν₂ : Measure (Space d)) [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂]
      (hc : ∀ χ : Space d → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ O →
        (∫ x, χ x ∂ν₁) = ∫ x, χ x ∂ν₂)
      {W : Set (Space d)} (hW : IsOpen W) (hWO : W ⊆ O) : ν₁ W ≤ ν₂ W := by
    rw [hW.measure_eq_iSup_isCompact]
    refine iSup_le fun K ↦ iSup_le fun hKW ↦ iSup_le fun hK ↦ ?_
    obtain ⟨χ, hχK, hχc, hχs, hχv⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hW hKW
    have hχi₁ := χ.continuous.integrable_of_hasCompactSupport (μ := ν₁) hχc
    have hχi₂ := χ.continuous.integrable_of_hasCompactSupport (μ := ν₂) hχc
    have hle₁ : ν₁.real K ≤ ∫ x, χ x ∂ν₁ := by
      have he : (∫ x in K, χ x ∂ν₁) = ν₁.real K := by
        calc
          (∫ x in K, χ x ∂ν₁) = ∫ _ in K, (1 : ℝ) ∂ν₁ :=
            setIntegral_congr_fun hK.measurableSet fun x hx ↦ hχK hx
          _ = ν₁.real K := by simp
      rw [← he]
      exact setIntegral_le_integral hχi₁ (Eventually.of_forall fun x ↦ (hχv x).1)
    have hle₂ : (∫ x, χ x ∂ν₂) ≤ ν₂.real (tsupport χ) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ image_eq_zero_of_notMem_tsupport hx)]
      have hc2 : IntegrableOn (fun _ : Space d ↦ (1 : ℝ)) (tsupport χ) ν₂ :=
        integrableOn_const hχc.measure_lt_top.ne
      calc
        (∫ x in tsupport χ, χ x ∂ν₂) ≤ ∫ _ in tsupport χ, (1 : ℝ) ∂ν₂ :=
          integral_mono hχi₂.integrableOn hc2 fun x ↦ (hχv x).2
        _ = ν₂.real (tsupport χ) := by simp
    have hid := hc χ χ.continuous hχc (hχs.trans hWO)
    have hreal : ν₁.real K ≤ ν₂.real (tsupport χ) := by linarith
    calc
      ν₁ K = ENNReal.ofReal (ν₁.real K) := (ENNReal.ofReal_toReal hK.measure_lt_top.ne).symm
      _ ≤ ENNReal.ofReal (ν₂.real (tsupport χ)) := ENNReal.ofReal_le_ofReal hreal
      _ = ν₂ (tsupport χ) := ENNReal.ofReal_toReal hχc.measure_lt_top.ne
      _ ≤ ν₂ W := measure_mono hχs
  have hopen_eq {W : Set (Space d)} (hW : IsOpen W) (hWO : W ⊆ O) : μ₁ W = μ₂ W :=
    le_antisymm (hopen_le μ₁ μ₂ hcont_eq hW hWO)
      (hopen_le μ₂ μ₁ (fun χ hχ hc hs ↦ (hcont_eq χ hχ hc hs).symm) hW hWO)
  ext A hA
  let B : ℕ → Set (Space d) := fun n ↦ ball 0 ((n : ℝ) + 1)
  have hB_mono : Monotone B := fun n k hnk ↦
    ball_subset_ball (add_le_add (Nat.cast_le.mpr hnk) le_rfl)
  have hB_union : (⋃ n : ℕ, B n) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine ⟨n, ?_⟩
    simpa [B, dist_zero_right] using lt_trans hn (by linarith)
  have hball_eq (n : ℕ) : μ₁.restrict (O ∩ B n) = μ₂.restrict (O ∩ B n) := by
    let : IsFiniteMeasure (μ₁.restrict (O ∩ B n)) := ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact lt_of_le_of_lt (measure_mono (inter_subset_right.trans ball_subset_closedBall))
        (isCompact_closedBall 0 ((n : ℝ) + 1)).measure_lt_top⟩
    let : IsFiniteMeasure (μ₂.restrict (O ∩ B n)) := ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact lt_of_le_of_lt (measure_mono (inter_subset_right.trans ball_subset_closedBall))
        (isCompact_closedBall 0 ((n : ℝ) + 1)).measure_lt_top⟩
    apply Measure.OuterRegular.ext_isOpen
    intro W hW
    rw [Measure.restrict_apply hW.measurableSet, Measure.restrict_apply hW.measurableSet]
    exact hopen_eq (hW.inter (hO.inter isOpen_ball)) (inter_subset_right.trans inter_subset_left)
  have hunion₁ : (A ∩ O) = ⋃ n : ℕ, A ∩ (O ∩ B n) := by
    rw [← inter_iUnion, ← inter_iUnion, hB_union, inter_univ]
  have hmono_seq : Monotone (fun n : ℕ ↦ A ∩ (O ∩ B n)) :=
    fun n k hnk ↦ inter_subset_inter_right A (inter_subset_inter_right O (hB_mono hnk))
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hunion₁,
    hmono_seq.measure_iUnion, hmono_seq.measure_iUnion]
  congr 1 with n
  have he := congrArg (fun m : Measure (Space d) ↦ m A) (hball_eq n)
  simpa only [Measure.restrict_apply hA] using he

/-- Exact restriction identity `(projectedPerimeterMeasure μ).restrict U =
(volume + projectedExcessMeasure μ ν).restrict U` (`BV13.2`, `BV14`, `GR9`). -/
theorem projectedPerimeterMeasure_restrict_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E) :
    (projectedPerimeterMeasure μ).restrict U =
      (volume + projectedExcessMeasure μ ν).restrict U := by
  let : IsFiniteMeasure (projectedExcessMeasure μ ν) := isFiniteMeasure_projectedExcessMeasure μ hν
  let : IsLocallyFiniteMeasure (volume + projectedExcessMeasure μ ν) :=
    isLocallyFiniteMeasure_add volume (projectedExcessMeasure μ ν)
  apply measure_restrict_open_eq_of_integral_contDiff_eq (projectedPerimeterMeasure μ)
    (volume + projectedExcessMeasure μ ν) hU
  intro φ hφ hφc hφs
  have hflux := integral_vertical_flux_eq_integral b hE hU hH hHH' μ hμcompl hμopen hdist
    hbot htop hφ hφc hφs
  have hφ_int_vol : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hφ_int_exc : Integrable φ (projectedExcessMeasure μ ν) :=
    hφ.continuous.integrable_of_hasCompactSupport hφc
  rw [integral_add_measure hφ_int_vol hφ_int_exc]
  have hmap_perim : (∫ y, φ y ∂projectedPerimeterMeasure μ) = ∫ x, φ (horizontal x) ∂μ :=
    integral_map continuous_horizontal.measurable.aemeasurable hφ.continuous.aestronglyMeasurable
  let w : Space (m + 1) → ℝ := fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)
  have hw_aesm : AEStronglyMeasurable w μ :=
    aestronglyMeasurable_const.sub (hν.aestronglyMeasurable.inner aestronglyMeasurable_const)
  have hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x := by
    filter_upwards [hνunit] with x hx
    have hcs := real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hcs
    dsimp [w]
    linarith
  have hw_lt_top : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ :=
    Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hmap_exc : (∫ y, φ y ∂projectedExcessMeasure μ ν) =
      ∫ x, φ (horizontal x) * w x ∂μ := by
    unfold projectedExcessMeasure
    rw [integral_map continuous_horizontal.measurable.aemeasurable
      hφ.continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hw_aesm.aemeasurable.ennreal_ofReal hw_lt_top]
    apply integral_congr_ae
    filter_upwards [hw_nonneg] with x hwx
    rw [ENNReal.toReal_ofReal hwx, smul_eq_mul, mul_comm]
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuousOn hφ.continuous.continuousOn
  have hφ_bound (y : Space m) : ‖φ y‖ ≤ max C 0 := by
    by_cases hy : y ∈ tsupport φ
    · exact (hC y hy).trans (le_max_left _ _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hφh_int : Integrable (fun x ↦ φ (horizontal x)) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_horizontal).aestronglyMeasurable
      (max C 0) (Eventually.of_forall fun x ↦ hφ_bound (horizontal x))
  have hφν_int : Integrable (fun x ↦ φ (horizontal x) * inner ℝ (ν x) (verticalDirection m)) μ := by
    refine (hν.norm.const_mul (max C 0)).mono'
      ((hφ.continuous.comp continuous_horizontal).aestronglyMeasurable.mul
        (hν.aestronglyMeasurable.inner aestronglyMeasurable_const)) ?_
    exact Eventually.of_forall fun x ↦ by
      rw [norm_mul]
      have hcs := norm_inner_le_norm (𝕜 := ℝ) (ν x) (verticalDirection m)
      rw [norm_verticalDirection, mul_one] at hcs
      exact mul_le_mul (hφ_bound (horizontal x)) hcs (norm_nonneg _) (le_max_right C 0)
  have hφw_eq : (fun x ↦ φ (horizontal x) * w x) =
      fun x ↦ φ (horizontal x) - φ (horizontal x) * inner ℝ (ν x) (verticalDirection m) := by
    ext x
    dsimp [w]
    ring
  rw [hmap_perim, hmap_exc, hφw_eq, integral_sub hφh_int hφν_int, hflux]
  ring

/-- For every measurable subset `A ⊆ U`, the projected perimeter equals horizontal Lebesgue volume
plus projected tilt-excess (`BV13.2`, `BV14`, `GR9`). -/
theorem projectedPerimeterMeasure_apply_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    projectedPerimeterMeasure μ A = volume A + projectedExcessMeasure μ ν A := by
  have hres := congrArg (fun ρ : Measure (Space m) ↦ ρ A)
    (projectedPerimeterMeasure_restrict_eq b hE hU hH hHH' μ hμcompl hμopen hν hνunit hdist
      hbot htop)
  simpa only [Measure.restrict_apply hA, inter_eq_left.mpr hAU, Measure.add_apply] using hres

/-- A slab-trapped set of finite perimeter over `U` automatically forces `volume U < ⊤`. -/
theorem volume_lt_top_of_slab_trapped {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E) :
    volume U < ⊤ := by
  have heq := projectedPerimeterMeasure_apply_eq b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop hU.measurableSet Subset.rfl
  calc
    volume U ≤ volume U + projectedExcessMeasure μ ν U := le_self_add
    _ = projectedPerimeterMeasure μ U := heq.symm
    _ < ⊤ := measure_lt_top _ _

/-- Real-valued form of `projectedPerimeterMeasure_apply_eq` for any measurable `A ⊆ U`. -/
theorem projectedPerimeterMeasure_real_apply_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    (projectedPerimeterMeasure μ).real A =
      volume.real A + (projectedExcessMeasure μ ν).real A := by
  let : IsFiniteMeasure (projectedExcessMeasure μ ν) := isFiniteMeasure_projectedExcessMeasure μ hν
  have hU_lt := volume_lt_top_of_slab_trapped b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop
  have hA_ne : volume A ≠ ⊤ := (lt_of_le_of_lt (measure_mono hAU) hU_lt).ne
  have heq := projectedPerimeterMeasure_apply_eq b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop hA hAU
  simp only [Measure.real, heq, ENNReal.toReal_add hA_ne (measure_ne_top _ _)]

/-! ### 3. Horizontal moment and weak derivative bound for `columnSignedHeight` (`BV13.3`, `GR9.1`) -/

/-- Horizontal moment / weak directional derivative identity for `columnSignedHeight`
(`BV13.3`, `BV14`, `GR9`). -/
theorem integral_columnSignedHeight_fderiv_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)}
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {φ : Space m → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U) (w : Space m) :
    (∫ y, columnSignedHeight E H y * fderiv ℝ φ y w) =
      ∫ x, φ (horizontal x) * inner ℝ (ν x) (point w 0) ∂μ := by
  let ψ : ℝ → ℝ := slabVerticalCutoff hH hHH'
  obtain ⟨hψ, hψc, hψs, hψone, -⟩ := slabVerticalCutoff_props hH hHH'
  let F₀ : Space (m + 1) → Space (m + 1) :=
    fun x ↦ (φ (horizontal x) * ψ (x (Fin.last m))) • point w 0
  have hF₀_diff : ContDiff ℝ 1 F₀ :=
    ((hφ.comp horizontalContinuousLinearMap.contDiff).mul
      (hψ.comp (PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).contDiff)).smul contDiff_const
  obtain ⟨hF₀_comp, hF₀_sub⟩ :=
    hasCompactSupport_product_field hφc hφs hψc hψs (point w 0)
  let Fc : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨F₀, hF₀_diff.continuous⟩, hF₀_comp⟩
  have hid := hdist Fc hF₀_diff hF₀_sub
  have hslab := ae_mem_slab_of_slab_trapped b hU hH hHH' μ hμcompl hμopen hbot htop
  have hrhs : (∫ x, inner ℝ (Fc x) (ν x) ∂μ) =
      ∫ x, φ (horizontal x) * inner ℝ (ν x) (point w 0) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hslab] with x ⟨_, hxI⟩
    change inner ℝ ((φ (horizontal x) * ψ (x (Fin.last m))) • point w 0) (ν x) = _
    have h1 : ψ (x (Fin.last m)) = 1 :=
      hψone _ ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    rw [real_inner_smul_left, h1, mul_one, real_inner_comm]
  have hdiv_eq (x : Space (m + 1)) :
      fieldDivergence b Fc x = fderiv ℝ φ (horizontal x) w * ψ (x (Fin.last m)) := by
    change fieldDivergence b F₀ x = _
    dsimp only [F₀, ψ]
    rw [fieldDivergence_horizontal_mul_vertical_smul b hφ hψ (point w 0) x]
    simp
  have hg_int : Integrable
      (fun x : Space (m + 1) ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x)
      volume := by
    have hcont := fieldDivergence_continuous b hF₀_diff
    have hdiv_supp : tsupport (fieldDivergence b F₀) ⊆ tsupport F₀ := by
      apply closure_minimal _ (isClosed_tsupport F₀)
      intro x hx
      by_contra hn
      exact hx (fieldDivergence_zero_of_notMem_tsupport b F₀ hn)
    have hdiv_c : HasCompactSupport (fieldDivergence b F₀) :=
      hF₀_comp.of_isClosed_subset (isClosed_tsupport _) hdiv_supp
    have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hdiv_c).indicator hE
    refine hi.congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ E <;> simp [hx, Fc]
  let Cψ : ℝ := ∫ t in Ioi H, ψ t
  have hfd_cont : Continuous (fun y : Space m ↦ fderiv ℝ φ y w) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfd_comp : HasCompactSupport (fun y : Space m ↦ fderiv ℝ φ y w) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ w)
  have hfd_int : Integrable (fun y : Space m ↦ fderiv ℝ φ y w) volume :=
    hfd_cont.integrable_of_hasCompactSupport hfd_comp
  have hg_col_int : Integrable (fun y : Space m ↦ columnSignedHeight E H y * fderiv ℝ φ y w)
      volume := by
    refine (hfd_int.norm.const_mul H).mono'
      ((measurable_columnSignedHeight hE H).aestronglyMeasurable.mul hfd_int.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun y ↦ ?_
    rw [norm_mul]
    have hmem := columnSignedHeight_mem_Icc E hH.le y
    have habs : ‖columnSignedHeight E H y‖ ≤ H := by
      rw [Real.norm_eq_abs, abs_le]
      exact hmem
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg _)
  have hfd_zero : (∫ y : Space m, fderiv ℝ φ y w) = 0 := by
    have hibp := integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := volume)
      (u := fun _ : Space m ↦ (1 : ℝ)) isOpen_univ contDiffOn_const hφ hφc (subset_univ _) w
    simpa using hibp
  have hlhs : -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x) =
      ∫ y, columnSignedHeight E H y * fderiv ℝ φ y w := by
    rw [integral_space_eq_integral_horizontal_vertical hg_int]
    simp_rw [hdiv_eq, horizontal_point, last_point]
    have hbot_slice := ae_vertical_of_ae_volume hbot
    have htop_slice := ae_vertical_of_ae_volume htop
    have hinner : ∀ᵐ y : Space m ∂volume,
        (∫ t : ℝ, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * (fderiv ℝ φ y w * ψ t)) =
          (H + Cψ) * fderiv ℝ φ y w - columnSignedHeight E H y * fderiv ℝ φ y w := by
      filter_upwards [hbot_slice, htop_slice] with y hybot hytop
      by_cases hyU : y ∈ U
      · have hfactor : (fun t : ℝ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
            (fderiv ℝ φ y w * ψ t)) = fun t ↦ fderiv ℝ φ y w *
              (E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * ψ t) := by
          ext t; ring
        rw [hfactor, integral_const_mul]
        have hae_t : (fun t : ℝ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * ψ t) =ᵐ[volume]
            fun t ↦ (Icc (-H) H).indicator (fun s ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y s)) t +
              (Ioi H).indicator ψ t := by
          filter_upwards [hybot, hytop] with t htb htt
          simp only [horizontal_point, last_point] at htb htt
          by_cases htH : H < t
          · have hnotIcc : t ∉ Icc (-H) H := fun hh ↦ not_lt.mpr hh.2 htH
            rw [indicator_of_notMem hnotIcc, indicator_of_mem (mem_Ioi.mpr htH), zero_add]
            by_cases htH' : t < H'
            · have hinE : point y t ∈ E := htt hyU ⟨htH, htH'⟩
              simp [hinE]
            · have hnot : t ∉ tsupport ψ := fun hs ↦ htH' (hψs hs).2
              simp [image_eq_zero_of_notMem_tsupport hnot]
          · rw [indicator_of_notMem (mem_Ioi.not.mpr htH), add_zero]
            have htle : t ≤ H := not_lt.mp htH
            by_cases htlow : -H ≤ t
            · have hinIcc : t ∈ Icc (-H) H := ⟨htlow, htle⟩
              have h1 : ψ t = 1 := hψone t ⟨by linarith, by linarith⟩
              rw [indicator_of_mem hinIcc, h1, mul_one]
            · have hnotIcc : t ∉ Icc (-H) H := fun hh ↦ htlow hh.1
              rw [indicator_of_notMem hnotIcc]
              have htlt : t < -H := not_le.mp htlow
              by_cases htH' : -H' < t
              · have hnotE : point y t ∉ E := htb hyU ⟨htH', htlt⟩
                simp [hnotE]
              · have hnot : t ∉ tsupport ψ := fun hs ↦ htH' (hψs hs).1
                simp [image_eq_zero_of_notMem_tsupport hnot]
        have hi₁ : Integrable
            ((Icc (-H) H).indicator (fun s ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y s))) volume := by
          have hcI : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-H) H) volume :=
            integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          have hi_on : IntegrableOn (fun s ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y s))
              (Icc (-H) H) volume :=
            hcI.mono' (((measurable_const.indicator hE).comp
              (continuous_point y).measurable).aestronglyMeasurable)
              (Eventually.of_forall fun t ↦ by by_cases hx : point y t ∈ E <;> simp [hx])
          exact hi_on.integrable_indicator measurableSet_Icc
        have hi₂ : Integrable ((Ioi H).indicator ψ) volume :=
          (hψ.continuous.integrable_of_hasCompactSupport hψc).indicator measurableSet_Ioi
        rw [integral_congr_ae hae_t, integral_add hi₁ hi₂,
          integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioi]
        have hcol : (∫ t in Icc (-H) H, E.indicator (fun _ ↦ (1 : ℝ)) (point y t)) =
            H - columnSignedHeight E H y := by
          linarith [columnSignedHeight_eq_sub_integral hE hH.le y]
        rw [hcol]
        change fderiv ℝ φ y w * (H - columnSignedHeight E H y + Cψ) =
          (H + Cψ) * fderiv ℝ φ y w - columnSignedHeight E H y * fderiv ℝ φ y w
        ring
      · have hnot : y ∉ tsupport (fun z : Space m ↦ fderiv ℝ φ z w) :=
          fun hs ↦ hyU (hφs (tsupport_fderiv_apply_subset ℝ w hs))
        have hfd0 : fderiv ℝ φ y w = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun z : Space m ↦ fderiv ℝ φ z w) hnot
        simp [hfd0]
    rw [integral_congr_ae hinner, integral_sub (hfd_int.const_mul (H + Cψ)) hg_col_int,
      integral_const_mul, hfd_zero, mul_zero, zero_sub, neg_neg]
  rw [← hlhs, hid, hrhs]

/-- Horizontal divergence pairing for `columnSignedHeight` against any `C¹_c(U)` horizontal vector
field `G : Space m → Space m`. -/
theorem integral_columnSignedHeight_fieldDivergence_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (bm : OrthonormalBasis (Fin m) ℝ (Space m))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {G : Space m → Space m} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (hGs : tsupport G ⊆ U) :
    (∫ y, columnSignedHeight E H y * fieldDivergence bm G y) =
      ∫ x, inner ℝ (horizontal (ν x)) (G (horizontal x)) ∂μ := by
  let φ : Fin m → Space m → ℝ := fun i y ↦ inner ℝ (bm i) (G y)
  have hφ (i : Fin m) : ContDiff ℝ 1 (φ i) :=
    (innerSL ℝ (bm i)).contDiff.comp hG
  have hφs_sub (i : Fin m) : tsupport (φ i) ⊆ tsupport G :=
    tsupport_comp_subset (by simp : inner ℝ (bm i) (0 : Space m) = 0) G
  have hφc (i : Fin m) : HasCompactSupport (φ i) :=
    hGc.of_isClosed_subset (isClosed_tsupport _) (hφs_sub i)
  have hd (i : Fin m) (y : Space m) :
      fderiv ℝ (φ i) y (bm i) = inner ℝ (bm i) (fderiv ℝ G y (bm i)) := by
    have he := (innerSL ℝ (bm i)).hasFDerivAt.comp y (hG.differentiable_one y).hasFDerivAt
    exact congrArg (fun L : Space m →L[ℝ] ℝ ↦ L (bm i)) he.fderiv
  have hterm_int (i : Fin m) :
      Integrable (fun y ↦ columnSignedHeight E H y * fderiv ℝ (φ i) y (bm i)) volume := by
    have hfd_cont : Continuous (fun y ↦ fderiv ℝ (φ i) y (bm i)) :=
      ((hφ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hfd_comp : HasCompactSupport (fun y ↦ fderiv ℝ (φ i) y (bm i)) :=
      (hφc i).of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ (bm i))
    have hfd_int : Integrable (fun y ↦ fderiv ℝ (φ i) y (bm i)) volume :=
      hfd_cont.integrable_of_hasCompactSupport hfd_comp
    refine (hfd_int.norm.const_mul H).mono'
      ((measurable_columnSignedHeight hE H).aestronglyMeasurable.mul hfd_int.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun y ↦ ?_
    rw [norm_mul]
    have habs : ‖columnSignedHeight E H y‖ ≤ H := by
      rw [Real.norm_eq_abs, abs_le]
      exact columnSignedHeight_mem_Icc E hH.le y
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg (fderiv ℝ (φ i) y (bm i)))
  obtain ⟨C, hC⟩ := hGc.exists_bound_of_continuousOn hG.continuous.continuousOn
  have hG_bound (y : Space m) : ‖G y‖ ≤ max C 0 := by
    by_cases hy : y ∈ tsupport G
    · exact (hC y hy).trans (le_max_left _ _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hμ_int (i : Fin m) :
      Integrable (fun x ↦ φ i (horizontal x) * inner ℝ (ν x) (point (bm i) 0)) μ := by
    refine (hν.norm.const_mul (max C 0)).mono'
      (((hφ i).continuous.comp continuous_horizontal).aestronglyMeasurable.mul
        (hν.aestronglyMeasurable.inner aestronglyMeasurable_const)) ?_
    refine Eventually.of_forall fun x ↦ ?_
    rw [norm_mul]
    have h1 : ‖φ i (horizontal x)‖ ≤ max C 0 := by
      calc
        ‖inner ℝ (bm i) (G (horizontal x))‖ ≤ ‖bm i‖ * ‖G (horizontal x)‖ :=
          norm_inner_le_norm _ _
        _ = ‖G (horizontal x)‖ := by rw [bm.norm_eq_one, one_mul]
        _ ≤ max C 0 := hG_bound (horizontal x)
    have h2 : ‖inner ℝ (ν x) (point (bm i) 0)‖ ≤ ‖ν x‖ := by
      rw [inner_point_zero_right]
      calc
        ‖inner ℝ (horizontal (ν x)) (bm i)‖ ≤ ‖horizontal (ν x)‖ * ‖bm i‖ :=
          norm_inner_le_norm _ _
        _ = ‖horizontal (ν x)‖ := by rw [bm.norm_eq_one, mul_one]
        _ ≤ ‖ν x‖ := by
          have hsq : ‖horizontal (ν x)‖ ^ 2 ≤ ‖ν x‖ ^ 2 := by
            nth_rw 2 [← point_horizontal_last (ν x)]
            rw [← real_inner_self_eq_norm_sq (point _ _), inner_point_point,
              real_inner_self_eq_norm_sq]
            nlinarith
          nlinarith [norm_nonneg (horizontal (ν x)), norm_nonneg (ν x)]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_right C 0)
  have hdiv_sum (y : Space m) :
      columnSignedHeight E H y * fieldDivergence bm G y =
        ∑ i : Fin m, columnSignedHeight E H y * fderiv ℝ (φ i) y (bm i) := by
    unfold fieldDivergence
    simp_rw [← hd]
    rw [Finset.mul_sum]
  simp_rw [hdiv_sum]
  rw [integral_finsetSum _ fun i _ ↦ hterm_int i]
  have hstep (i : Fin m) :
      (∫ y, columnSignedHeight E H y * fderiv ℝ (φ i) y (bm i)) =
        ∫ x, φ i (horizontal x) * inner ℝ (ν x) (point (bm i) 0) ∂μ :=
    integral_columnSignedHeight_fderiv_eq b hE hU hH hHH' μ hμcompl hμopen hdist hbot htop
      (hφ i) (hφc i) ((hφs_sub i).trans hGs) (bm i)
  simp_rw [hstep]
  rw [← integral_finsetSum _ fun i _ ↦ hμ_int i]
  apply integral_congr_ae
  refine Eventually.of_forall fun x ↦ ?_
  simp_rw [inner_point_zero_right, φ]
  simpa only [mul_comm, real_inner_comm (bm _)] using
    bm.sum_inner_mul_inner (horizontal (ν x)) (G (horizontal x))

/-- For any unit vector `u` in `Space (m + 1)`, `‖horizontal u‖² ≤ 2 * (1 - ⟪u, e_last⟫)`. -/
theorem norm_horizontal_sq_le_two_mul_one_sub_vertical {m : ℕ} {u : Space (m + 1)}
    (hu : ‖u‖ = 1) :
    ‖horizontal u‖ ^ 2 ≤ 2 * (1 - inner ℝ u (verticalDirection m)) := by
  have hdecomp : ‖horizontal u‖ ^ 2 + (inner ℝ u (verticalDirection m)) ^ 2 = 1 := by
    have h1 : ‖u‖ ^ 2 = 1 := by rw [hu, one_pow]
    nth_rw 1 [← point_horizontal_last u] at h1
    rw [← real_inner_self_eq_norm_sq (point _ _), inner_point_point,
      real_inner_self_eq_norm_sq, ← inner_verticalDirection_right u] at h1
    linarith
  have hcs := abs_real_inner_le_norm u (verticalDirection m)
  rw [hu, norm_verticalDirection, mul_one] at hcs
  have hbounds := abs_le.mp hcs
  nlinarith

/-- Cauchy–Schwarz bound on the horizontal weak divergence of `columnSignedHeight` over any
measurable subset `A ⊆ U` (`GR9.1`). -/
theorem abs_integral_columnSignedHeight_fieldDivergence_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (bm : OrthonormalBasis (Fin m) ℝ (Space m))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U)
    {G : Space m → Space m} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (hGs : tsupport G ⊆ A) (hGunit : ∀ y, ‖G y‖ ≤ 1) :
    |∫ y, columnSignedHeight E H y * fieldDivergence bm G y| ≤
      Real.sqrt (2 * (projectedExcessMeasure μ ν).real A *
        (volume.real A + (projectedExcessMeasure μ ν).real A)) := by
  let : IsFiniteMeasure (projectedExcessMeasure μ ν) := isFiniteMeasure_projectedExcessMeasure μ hν
  have hid := integral_columnSignedHeight_fieldDivergence_eq b bm hE hU hH hHH' μ hμcompl hμopen
    hν hdist hbot htop hG hGc (hGs.trans hAU)
  let S : Set (Space (m + 1)) := horizontal ⁻¹' A
  have hS : MeasurableSet S := hA.preimage continuous_horizontal.measurable
  have hset_eq : (∫ x, inner ℝ (horizontal (ν x)) (G (horizontal x)) ∂μ) =
      ∫ x in S, inner ℝ (horizontal (ν x)) (G (horizontal x)) ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hxS
    have hnot : horizontal x ∉ tsupport G := fun hh ↦ hxS (hGs hh)
    rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right]
  rw [hid, hset_eq]
  have hνh_aesm : AEStronglyMeasurable (fun x ↦ ‖horizontal (ν x)‖) (μ.restrict S) :=
    (horizontalContinuousLinearMap.continuous.comp_aestronglyMeasurable
      hν.aestronglyMeasurable.restrict).norm
  have hνh_sq_int : Integrable (fun x ↦ ‖horizontal (ν x)‖ ^ 2) (μ.restrict S) := by
    refine Integrable.of_bound ((continuous_pow 2).comp_aestronglyMeasurable hνh_aesm) 1 ?_
    filter_upwards [ae_restrict_of_ae hνunit] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hsq : ‖horizontal (ν x)‖ ^ 2 + (inner ℝ (ν x) (verticalDirection m)) ^ 2 = 1 := by
      have h1 : ‖ν x‖ ^ 2 = 1 := by rw [hx, one_pow]
      nth_rw 1 [← point_horizontal_last (ν x)] at h1
      rw [← real_inner_self_eq_norm_sq (point _ _), inner_point_point,
        real_inner_self_eq_norm_sq, ← inner_verticalDirection_right (ν x)] at h1
      linarith
    nlinarith [sq_nonneg (inner ℝ (ν x) (verticalDirection m))]
  have h1_sq_int : Integrable (fun _ : Space (m + 1) ↦ (1 : ℝ) ^ 2) (μ.restrict S) :=
    integrable_const _
  have hprod_int : Integrable (fun x ↦ ‖horizontal (ν x)‖ * (1 : ℝ)) (μ.restrict S) := by
    refine Integrable.of_bound (hνh_aesm.mul aestronglyMeasurable_const) 1 ?_
    filter_upwards [ae_restrict_of_ae hνunit] with x hx
    rw [mul_one, Real.norm_of_nonneg (norm_nonneg _)]
    have hsq : ‖horizontal (ν x)‖ ^ 2 ≤ 1 := by
      have h1 : ‖ν x‖ ^ 2 = 1 := by rw [hx, one_pow]
      nth_rw 1 [← point_horizontal_last (ν x)] at h1
      rw [← real_inner_self_eq_norm_sq (point _ _), inner_point_point,
        real_inner_self_eq_norm_sq] at h1
      nlinarith
    nlinarith [norm_nonneg (horizontal (ν x))]
  have hbound_inner : |∫ x in S, inner ℝ (horizontal (ν x)) (G (horizontal x)) ∂μ| ≤
      ∫ x in S, ‖horizontal (ν x)‖ * 1 ∂μ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hprod_int ?_
    exact Eventually.of_forall fun x ↦ by
      calc
        ‖inner ℝ (horizontal (ν x)) (G (horizontal x))‖
            ≤ ‖horizontal (ν x)‖ * ‖G (horizontal x)‖ := norm_inner_le_norm _ _
        _ ≤ ‖horizontal (ν x)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hGunit (horizontal x)) (norm_nonneg _)
  have hcs := abs_integral_mul_le_sqrt hνh_sq_int h1_sq_int
  have hpos_int : 0 ≤ ∫ x in S, ‖horizontal (ν x)‖ * 1 ∂μ :=
    integral_nonneg fun x ↦ by positivity
  rw [abs_of_nonneg hpos_int] at hcs
  let w : Space (m + 1) → ℝ := fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)
  have hw_aesm : AEStronglyMeasurable w μ :=
    aestronglyMeasurable_const.sub (hν.aestronglyMeasurable.inner aestronglyMeasurable_const)
  have hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x := by
    filter_upwards [hνunit] with x hx
    have hc := real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hc
    dsimp [w]; linarith
  have hw_int : Integrable w (μ.restrict S) := by
    refine Integrable.of_bound hw_aesm.restrict 2 ?_
    filter_upwards [ae_restrict_of_ae hνunit] with x hx
    have hc := abs_real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hc
    rw [Real.norm_eq_abs, abs_le]
    dsimp [w]
    exact ⟨by linarith [(abs_le.mp hc).2], by linarith [(abs_le.mp hc).1]⟩
  have hfirst : (∫ x in S, ‖horizontal (ν x)‖ ^ 2 ∂μ) ≤
      2 * (projectedExcessMeasure μ ν).real A := by
    have hle : (∫ x in S, ‖horizontal (ν x)‖ ^ 2 ∂μ) ≤ ∫ x in S, 2 * w x ∂μ := by
      refine integral_mono_ae hνh_sq_int (hw_int.const_mul 2) ?_
      filter_upwards [ae_restrict_of_ae hνunit] with x hx
      exact norm_horizontal_sq_le_two_mul_one_sub_vertical hx
    rw [integral_const_mul] at hle
    have hexc_eq : (projectedExcessMeasure μ ν).real A = ∫ x in S, w x ∂μ := by
      unfold projectedExcessMeasure Measure.real
      rw [Measure.map_apply continuous_horizontal.measurable hA,
        withDensity_apply _ hS]
      have hlint : (∫⁻ x in S, ENNReal.ofReal (w x) ∂μ) =
          ENNReal.ofReal (∫ x in S, w x ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hw_int (ae_restrict_of_ae hw_nonneg)
      rw [hlint, ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hw_nonneg))]
    rwa [← hexc_eq] at hle
  have hsecond : (∫ _ in S, (1 : ℝ) ^ 2 ∂μ) =
      volume.real A + (projectedExcessMeasure μ ν).real A := by
    simp only [one_pow, integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one]
    have hmapA : (μ S).toReal = (projectedPerimeterMeasure μ).real A := by
      unfold projectedPerimeterMeasure Measure.real
      rw [Measure.map_apply continuous_horizontal.measurable hA]
    rw [hmapA]
    exact projectedPerimeterMeasure_real_apply_eq b hE hU hH hHH' μ hμcompl hμopen hν hνunit
      hdist hbot htop hA hAU
  have hnonneg₁ : 0 ≤ 2 * (projectedExcessMeasure μ ν).real A := by positivity
  calc
    |∫ x in S, inner ℝ (horizontal (ν x)) (G (horizontal x)) ∂μ|
        ≤ ∫ x in S, ‖horizontal (ν x)‖ * 1 ∂μ := hbound_inner
    _ ≤ Real.sqrt (∫ x in S, ‖horizontal (ν x)‖ ^ 2 ∂μ) *
          Real.sqrt (∫ _ in S, (1 : ℝ) ^ 2 ∂μ) := hcs
    _ ≤ Real.sqrt (2 * (projectedExcessMeasure μ ν).real A) *
          Real.sqrt (volume.real A + (projectedExcessMeasure μ ν).real A) :=
      mul_le_mul (Real.sqrt_le_sqrt hfirst) (by rw [hsecond])
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * (projectedExcessMeasure μ ν).real A *
          (volume.real A + (projectedExcessMeasure μ ν).real A)) :=
      (Real.sqrt_mul hnonneg₁ _).symm

/-- Open-ball Cauchy–Schwarz bound on the horizontal weak divergence of `columnSignedHeight`
(`GR9.1`). -/
theorem abs_integral_columnSignedHeight_fieldDivergence_ball_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    (bm : OrthonormalBasis (Fin m) ℝ (Space m))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {y₀ : Space m} {ρ : ℝ} (hball : ball y₀ ρ ⊆ U)
    {G : Space m → Space m} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (hGs : tsupport G ⊆ ball y₀ ρ) (hGunit : ∀ y, ‖G y‖ ≤ 1) :
    |∫ y, columnSignedHeight E H y * fieldDivergence bm G y| ≤
      Real.sqrt (2 * (projectedExcessMeasure μ ν).real (ball y₀ ρ) *
        (volume.real (ball y₀ ρ) + (projectedExcessMeasure μ ν).real (ball y₀ ρ))) :=
  abs_integral_columnSignedHeight_fieldDivergence_le b bm hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop measurableSet_ball hball hG hGc hGs hGunit

/-! ### 4. Single-layer jump-counting bound (`BV14a` & `GR10`) -/

/-- Smooth 1D bump centered at `q` with outer radius `r` and inner radius `r / 2`. -/
def oneDimBump (q : ℝ) {r : ℝ} (hr : 0 < r) : ContDiffBump q where
  rIn := r / 2
  rOut := r
  rIn_pos := half_pos hr
  rIn_lt_rOut := half_lt_self hr

/-- Radius `r_k := 1 / ((k : ℝ) + 1)` for countable 1D jump-counting bump tests. -/
def fourBumpRadius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem fourBumpRadius_pos (k : ℕ) : 0 < fourBumpRadius k := by
  unfold fourBumpRadius
  positivity

/-- Unit-integral smooth 1D bump centered at `q : ℚ` with outer radius `fourBumpRadius k`. -/
def fourBumpKernel (q : ℚ) (k : ℕ) : ℝ → ℝ :=
  (oneDimBump (q : ℝ) (fourBumpRadius_pos k)).normed volume

/-- Derivative profile `η(q₀, r_k) - 2 η(q₁, r_k) + 2 η(q₂, r_k) - η(q₃, r_k)` for the 4-bump
jump-counting test. -/
def fourBumpDeriv (q₀ q₁ q₂ q₃ : ℚ) (k : ℕ) (t : ℝ) : ℝ :=
  fourBumpKernel q₀ k t - 2 * fourBumpKernel q₁ k t +
    2 * fourBumpKernel q₂ k t - fourBumpKernel q₃ k t

/-- Explicit smooth compactly supported 4-bump 1D test `ψ(t) := ∫ s in (-H')..t, ψ'(s)`. -/
def fourBumpTest (H' : ℝ) (q₀ q₁ q₂ q₃ : ℚ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ s in (-H')..t, fourBumpDeriv q₀ q₁ q₂ q₃ k s

private theorem fourBumpKernel_props (q : ℚ) (k : ℕ) :
    let η := fourBumpKernel q k
    let r := fourBumpRadius k
    ContDiff ℝ (⊤ : ℕ∞) η ∧ Integrable η volume ∧ (∫ t, η t) = 1 ∧
      (∀ t, 0 ≤ η t) ∧ (∀ t, η t ≤ 1 / r) ∧
      (∀ t, t ∉ Ioo ((q : ℝ) - r) ((q : ℝ) + r) → η t = 0) := by
  let B := oneDimBump (q : ℝ) (fourBumpRadius_pos k)
  have hr : 0 < fourBumpRadius k := fourBumpRadius_pos k
  dsimp only [fourBumpKernel]
  refine ⟨B.contDiff_normed, B.integrable_normed, B.integral_normed, B.nonneg_normed, ?_, ?_⟩
  · intro t
    have hle := B.normed_le_div_measure_closedBall_rIn volume t
    have hrIn : B.rIn = fourBumpRadius k / 2 := rfl
    have hvol : volume.real (closedBall (q : ℝ) B.rIn) = fourBumpRadius k := by
      rw [hrIn, Real.closedBall_eq_Icc, Measure.real, Real.volume_Icc]
      have hdiff : ((q : ℝ) + fourBumpRadius k / 2) - ((q : ℝ) - fourBumpRadius k / 2) =
          fourBumpRadius k := by ring
      rw [hdiff, ENNReal.toReal_ofReal hr.le]
    rwa [hvol] at hle
  · intro t ht
    by_contra hne
    have hmem : t ∈ Function.support (B.normed volume) := hne
    rw [B.support_normed_eq] at hmem
    have hrOut : B.rOut = fourBumpRadius k := rfl
    rw [hrOut, Real.ball_eq_Ioo] at hmem
    exact ht hmem

private theorem fourBumpKernel_intervalIntegral_props (q : ℚ) (k : ℕ) {H' : ℝ}
    (hlow : -H' ≤ (q : ℝ) - fourBumpRadius k) :
    let η := fourBumpKernel q k
    let r := fourBumpRadius k
    (∀ t, 0 ≤ ∫ s in (-H')..t, η s) ∧
      (∀ t, (∫ s in (-H')..t, η s) ≤ 1) ∧
      (∀ t, t ≤ (q : ℝ) - r → (∫ s in (-H')..t, η s) = 0) ∧
      (∀ t, (q : ℝ) + r ≤ t → (∫ s in (-H')..t, η s) = 1) := by
  obtain ⟨hcd, hint, hint1, hnonneg, -, hsupp⟩ := fourBumpKernel_props q k
  let η := fourBumpKernel q k
  let r := fourBumpRadius k
  have hr : 0 < r := fourBumpRadius_pos k
  have hzero_left : ∀ t ≤ (q : ℝ) - r, (∫ s in (-H')..t, η s) = 0 := by
    intro t ht
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ))]
    · simp
    · intro s hs
      apply hsupp s
      intro hsI
      rcases le_total (-H') t with hHt | htH
      · rw [uIcc_of_le hHt] at hs
        linarith [hs.2, hsI.1]
      · rw [uIcc_of_ge htH] at hs
        linarith [hs.2, hsI.1, hlow]
  have hone_right : ∀ t, (q : ℝ) + r ≤ t → (∫ s in (-H')..t, η s) = 1 := by
    intro t ht
    have hHt : -H' ≤ t := by linarith
    rw [intervalIntegral.integral_of_le hHt, ← hint1, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    refine Eventually.of_forall fun s ↦ ?_
    by_cases hs : s ∈ Ioc (-H') t
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs]
      symm
      apply hsupp s
      intro hsI
      exact hs ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
  refine ⟨?_, ?_, hzero_left, hone_right⟩
  · intro t
    by_cases hHt : -H' ≤ t
    · exact intervalIntegral.integral_nonneg hHt fun s _ ↦ hnonneg s
    · rw [hzero_left t (by linarith)]
  · intro t
    by_cases hHt : -H' ≤ t
    · rw [intervalIntegral.integral_of_le hHt, ← hint1]
      exact setIntegral_le_integral hint (Eventually.of_forall hnonneg)
    · rw [hzero_left t (by linarith)]
      exact zero_le_one

private theorem fourBumpTest_props {H' : ℝ} {q₀ q₁ q₂ q₃ : ℚ} {k : ℕ}
    (h0 : -H' < (q₀ : ℝ) - fourBumpRadius k)
    (h01 : (q₀ : ℝ) + fourBumpRadius k < (q₁ : ℝ) - fourBumpRadius k)
    (h12 : (q₁ : ℝ) + fourBumpRadius k < (q₂ : ℝ) - fourBumpRadius k)
    (h23 : (q₂ : ℝ) + fourBumpRadius k < (q₃ : ℝ) - fourBumpRadius k)
    (h3 : (q₃ : ℝ) + fourBumpRadius k < H') :
    let ψ := fourBumpTest H' q₀ q₁ q₂ q₃ k
    ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo (-H') H' ∧
      (∀ t, |ψ t| ≤ 1) ∧ deriv ψ = fourBumpDeriv q₀ q₁ q₂ q₃ k := by
  let r := fourBumpRadius k
  have hr : 0 < r := fourBumpRadius_pos k
  obtain ⟨hc0, _, _, _, _, _⟩ := fourBumpKernel_props q₀ k
  obtain ⟨hc1, _, _, _, _, _⟩ := fourBumpKernel_props q₁ k
  obtain ⟨hc2, _, _, _, _, _⟩ := fourBumpKernel_props q₂ k
  obtain ⟨hc3, _, _, _, _, _⟩ := fourBumpKernel_props q₃ k
  let ψ' := fourBumpDeriv q₀ q₁ q₂ q₃ k
  have hψ'_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ' := by
    unfold ψ' fourBumpDeriv
    exact ((hc0.sub (contDiff_const.mul hc1)).add (contDiff_const.mul hc2)).sub hc3
  have hψ'_cont : Continuous ψ' := hψ'_smooth.continuous
  let ψ := fourBumpTest H' q₀ q₁ q₂ q₃ k
  have hd (t : ℝ) : HasDerivAt ψ (ψ' t) t :=
    intervalIntegral.integral_hasDerivAt_right (hψ'_cont.intervalIntegrable (-H') t)
      hψ'_cont.stronglyMeasurable.stronglyMeasurableAtFilter hψ'_cont.continuousAt
  have hderiv : deriv ψ = ψ' := funext fun t ↦ (hd t).deriv
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hd t).differentiableAt, hderiv ▸ hψ'_smooth⟩
  obtain ⟨hI0_0, hI0_1, hI0_L, hI0_R⟩ := fourBumpKernel_intervalIntegral_props q₀ k h0.le
  obtain ⟨hI1_0, hI1_1, hI1_L, hI1_R⟩ :=
    fourBumpKernel_intervalIntegral_props q₁ k (by change -H' ≤ (q₁ : ℝ) - r; linarith)
  obtain ⟨hI2_0, hI2_1, hI2_L, hI2_R⟩ :=
    fourBumpKernel_intervalIntegral_props q₂ k (by change -H' ≤ (q₂ : ℝ) - r; linarith)
  obtain ⟨hI3_0, hI3_1, hI3_L, hI3_R⟩ :=
    fourBumpKernel_intervalIntegral_props q₃ k (by change -H' ≤ (q₃ : ℝ) - r; linarith)
  have hψ_split (t : ℝ) : ψ t =
      (∫ s in (-H')..t, fourBumpKernel q₀ k s) -
        2 * (∫ s in (-H')..t, fourBumpKernel q₁ k s) +
        2 * (∫ s in (-H')..t, fourBumpKernel q₂ k s) -
        (∫ s in (-H')..t, fourBumpKernel q₃ k s) := by
    dsimp [ψ, fourBumpTest, fourBumpDeriv]
    have hi0 := hc0.continuous.intervalIntegrable (μ := volume) (-H') t
    have hi1 := hc1.continuous.intervalIntegrable (μ := volume) (-H') t
    have hi2 := hc2.continuous.intervalIntegrable (μ := volume) (-H') t
    have hi3 := hc3.continuous.intervalIntegrable (μ := volume) (-H') t
    rw [intervalIntegral.integral_sub
          ((hi0.sub (hi1.const_mul 2)).add (hi2.const_mul 2)) hi3,
        intervalIntegral.integral_add (hi0.sub (hi1.const_mul 2)) (hi2.const_mul 2),
        intervalIntegral.integral_sub hi0 (hi1.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsupp_sub : Function.support ψ ⊆ Icc ((q₀ : ℝ) - r) ((q₃ : ℝ) + r) := by
    intro t ht
    by_contra hnot
    apply ht
    rw [hψ_split t]
    by_cases hlt : t < (q₀ : ℝ) - r
    · rw [hI0_L t hlt.le, hI1_L t (by linarith), hI2_L t (by linarith), hI3_L t (by linarith)]
      ring
    · have hgt : (q₃ : ℝ) + r < t := lt_of_not_ge fun hle ↦ hnot ⟨not_lt.mp hlt, hle⟩
      rw [hI0_R t (by linarith), hI1_R t (by linarith), hI2_R t (by linarith), hI3_R t hgt.le]
      ring
  have hts_sub : tsupport ψ ⊆ Icc ((q₀ : ℝ) - r) ((q₃ : ℝ) + r) :=
    closure_minimal hsupp_sub isClosed_Icc
  have hcomp : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hts_sub
  have hts_Ioo : tsupport ψ ⊆ Ioo (-H') H' := fun t ht ↦ by
    have hmem := hts_sub ht
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hbound (t : ℝ) : |ψ t| ≤ 1 := by
    rw [hψ_split t, abs_le]
    by_cases ht1 : t ≤ (q₁ : ℝ) - r
    · rw [hI1_L t ht1, hI2_L t (by linarith), hI3_L t (by linarith)]
      exact ⟨by linarith [hI0_0 t], by linarith [hI0_1 t]⟩
    · by_cases ht2 : t ≤ (q₂ : ℝ) - r
      · rw [hI0_R t (by linarith), hI2_L t ht2, hI3_L t (by linarith)]
        exact ⟨by linarith [hI1_1 t], by linarith [hI1_0 t]⟩
      · by_cases ht3 : t ≤ (q₃ : ℝ) - r
        · rw [hI0_R t (by linarith), hI1_R t (by linarith), hI3_L t ht3]
          exact ⟨by linarith [hI2_0 t], by linarith [hI2_1 t]⟩
        · rw [hI0_R t (by linarith), hI1_R t (by linarith), hI2_R t (by linarith)]
          exact ⟨by linarith [hI3_1 t], by linarith [hI3_0 t]⟩
  exact ⟨hψ_smooth.of_le (by simp), hcomp, hts_Ioo, hbound, hderiv⟩

/-- Elementary 4-bump 1D jump-counting lemma (`BV14a` without 1D Jordan decomposition): any `{0, 1}`
profile trapped between `0` below `-H` and `1` above `H` that fails to agree a.e. on `Ioo (-H') H'`
with `(Ioi c).indicator 1` (for its signed height `c`) admits a rational 4-bump test `ψ` in
`C²_c(Ioo (-H') H')` with `|ψ| ≤ 1` and `2 ≤ -(∫ t, χ t * deriv ψ t)`. -/
theorem exists_fourBumpTest_of_not_singleLayer {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ01 : ∀ t, χ t = 0 ∨ χ t = 1)
    (hbot : ∀ᵐ t ∂volume, t ∈ Ioo (-H') (-H) → χ t = 0)
    (htop : ∀ᵐ t ∂volume, t ∈ Ioo H H' → χ t = 1)
    (hnot : ¬(∀ᵐ t ∂volume.restrict (Ioo (-H') H'),
      χ t = (Ioi ((∫ s in Icc (-H) H, (1 - χ s)) - H)).indicator (fun _ ↦ (1 : ℝ)) t)) :
    ∃ (q₀ q₁ q₂ q₃ : ℚ) (k : ℕ),
      -H' < (q₀ : ℝ) ∧ (q₀ : ℝ) < q₁ ∧ (q₁ : ℝ) < q₂ ∧ (q₂ : ℝ) < q₃ ∧ (q₃ : ℝ) < H' ∧
        let ψ := fourBumpTest H' q₀ q₁ q₂ q₃ k
        ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo (-H') H' ∧
          (∀ t, |ψ t| ≤ 1) ∧ 2 ≤ -(∫ t, χ t * deriv ψ t) := by
  let c : ℝ := (∫ s in Icc (-H) H, (1 - χ s)) - H
  have hχ_nonneg (t : ℝ) : 0 ≤ χ t := by rcases hχ01 t with h0 | h1 <;> linarith
  have hχ_le_one (t : ℝ) : χ t ≤ 1 := by rcases hχ01 t with h0 | h1 <;> linarith
  have hIcc_fin : volume (Icc (-H) H) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hc_const : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-H) H) volume := integrableOn_const hIcc_fin
  have hχ_int_Icc : IntegrableOn χ (Icc (-H) H) volume :=
    hc_const.mono' hχ_meas.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (hχ_nonneg t)]
        exact hχ_le_one t)
  have hc_bounds : -H ≤ c ∧ c ≤ H := by
    have hlow : 0 ≤ ∫ s in Icc (-H) H, (1 - χ s) :=
      integral_nonneg fun s ↦ sub_nonneg.mpr (hχ_le_one s)
    have hhigh : (∫ s in Icc (-H) H, (1 - χ s)) ≤ 2 * H := by
      have h1mχ : IntegrableOn (fun s ↦ 1 - χ s) (Icc (-H) H) volume := hc_const.sub hχ_int_Icc
      have hle := integral_mono h1mχ hc_const fun s ↦ sub_le_self 1 (hχ_nonneg s)
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
        sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith)] at hle
      linarith
    exact ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hint_χ_Icc : (∫ s in Icc (-H) H, χ s) = H - c := by
    have hsub := integral_sub hc_const hχ_int_Icc
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
      sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith)] at hsub
    dsimp [c]
    linarith
  let S₁ : Set ℝ := {t ∈ Ioo (-H) c | χ t = 1}
  let S₂ : Set ℝ := {t ∈ Ioo c H | χ t = 0}
  have hS₁_meas : MeasurableSet S₁ :=
    measurableSet_Ioo.inter (hχ_meas (measurableSet_singleton 1))
  have hS₂_meas : MeasurableSet S₂ :=
    measurableSet_Ioo.inter (hχ_meas (measurableSet_singleton 0))
  have hS₁_fin : volume S₁ ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
  have hS₂_fin : volume S₂ ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
  have hS_balance : volume.real S₁ = volume.real S₂ := by
    have hsplit_union : Icc (-H) H = Icc (-H) c ∪ Ioc c H :=
      (Icc_union_Ioc_eq_Icc hc_bounds.1 hc_bounds.2).symm
    have hdisj : Disjoint (Icc (-H) c) (Ioc c H) :=
      disjoint_left.mpr fun t ht1 ht2 ↦ not_lt.mpr ht1.2 ht2.1
    have hint_split : (∫ s in Icc (-H) H, χ s) =
        (∫ s in Icc (-H) c, χ s) + ∫ s in Ioc c H, χ s := by
      rw [hsplit_union, setIntegral_union hdisj measurableSet_Ioc
        (hχ_int_Icc.mono_set (Icc_subset_Icc_right hc_bounds.2))
        (hχ_int_Icc.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hc_bounds.1)))]
    have hleft_eq : (∫ s in Icc (-H) c, χ s) = volume.real S₁ := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      have hind : (Ioo (-H) c).indicator χ = S₁.indicator (fun _ ↦ (1 : ℝ)) := by
        ext t
        by_cases ht : t ∈ Ioo (-H) c
        · rcases hχ01 t with h0 | h1
          · have hnotS : t ∉ S₁ := fun hh ↦ by linarith [hh.2]
            simp [ht, h0, hnotS]
          · have hinS : t ∈ S₁ := ⟨ht, h1⟩
            simp [ht, h1, hinS]
        · have hnotS : t ∉ S₁ := fun hh ↦ ht hh.1
          simp [ht, hnotS]
      rw [← integral_indicator measurableSet_Ioo, hind, integral_indicator_const _ hS₁_meas,
        smul_eq_mul, mul_one]
    have hright_eq : (∫ s in Ioc c H, (1 - χ s)) = volume.real S₂ := by
      rw [← restrict_Ioo_eq_restrict_Ioc]
      have hind : (Ioo c H).indicator (fun s ↦ 1 - χ s) = S₂.indicator (fun _ ↦ (1 : ℝ)) := by
        ext t
        by_cases ht : t ∈ Ioo c H
        · rcases hχ01 t with h0 | h1
          · have hinS : t ∈ S₂ := ⟨ht, h0⟩
            simp [ht, h0, hinS]
          · have hnotS : t ∉ S₂ := fun hh ↦ by linarith [hh.2]
            simp [ht, h1, hnotS]
        · have hnotS : t ∉ S₂ := fun hh ↦ ht hh.1
          simp [ht, hnotS]
      rw [← integral_indicator measurableSet_Ioo, hind, integral_indicator_const _ hS₂_meas,
        smul_eq_mul, mul_one]
    have hIoc_fin : volume (Ioc c H) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hc_Ioc : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc c H) volume := integrableOn_const hIoc_fin
    have hχ_Ioc : IntegrableOn χ (Ioc c H) volume :=
      hχ_int_Icc.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hc_bounds.1))
    have hsub_Ioc := integral_sub hc_Ioc hχ_Ioc
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith [hc_bounds.2]), hright_eq] at hsub_Ioc
    linarith
  have hS_pos : 0 < volume.real S₁ ∧ 0 < volume.real S₂ := by
    by_contra hzero_both
    have hS₁0 : volume S₁ = 0 := by
      by_contra hne1
      have hp1 : 0 < volume.real S₁ := ENNReal.toReal_pos hne1 hS₁_fin
      have hp2 : 0 < volume.real S₂ := by linarith
      exact hzero_both ⟨hp1, hp2⟩
    have hS₂0 : volume S₂ = 0 := by
      have hr1 : volume.real S₁ = 0 := by simp [Measure.real, hS₁0]
      have hr2 : volume.real S₂ = 0 := by linarith
      by_contra hne2
      exact (ENNReal.toReal_pos hne2 hS₂_fin).ne' hr2
    apply hnot
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hmH_ae : ∀ᵐ t : ℝ ∂volume, t ≠ -H :=
      compl_mem_ae_iff.mpr (measure_singleton (μ := volume) (-H))
    have hc_ae : ∀ᵐ t : ℝ ∂volume, t ≠ c :=
      compl_mem_ae_iff.mpr (measure_singleton (μ := volume) c)
    have hH_ae : ∀ᵐ t : ℝ ∂volume, t ≠ H :=
      compl_mem_ae_iff.mpr (measure_singleton (μ := volume) H)
    have hS₁_ae : ∀ᵐ t : ℝ ∂volume, t ∉ S₁ := compl_mem_ae_iff.mpr hS₁0
    have hS₂_ae : ∀ᵐ t : ℝ ∂volume, t ∉ S₂ := compl_mem_ae_iff.mpr hS₂0
    filter_upwards [hbot, htop, hS₁_ae, hS₂_ae, hmH_ae, hc_ae, hH_ae] with
      t htb htt hnS₁ hnS₂ hne_mH hne_c hne_H htI
    by_cases htc : c < t
    · rw [indicator_of_mem (mem_Ioi.mpr htc)]
      rcases lt_or_gt_of_ne hne_H with htH | hHt
      · rcases hχ01 t with h0 | h1
        · exfalso; exact hnS₂ ⟨⟨htc, htH⟩, h0⟩
        · exact h1
      · exact htt ⟨hHt, htI.2⟩
    · rw [indicator_of_notMem (mem_Ioi.not.mpr htc)]
      have htlc : t < c := lt_of_le_of_ne (not_lt.mp htc) hne_c
      rcases lt_or_gt_of_ne hne_mH with htmH | hmHt
      · exact htb ⟨htI.1, htmH⟩
      · rcases hχ01 t with h0 | h1
        · exact h0
        · exfalso; exact hnS₁ ⟨⟨hmHt, htlc⟩, h1⟩
  have hex_dens {S : Set ℝ} (hSm : MeasurableSet S) (hSpos : 0 < volume.real S) :
      ∃ x ∈ S, Tendsto (fun r ↦ volume (S ∩ closedBall x r) / volume (closedBall x r))
        (𝓝[>] 0) (𝓝 1) := by
    have hae := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hSm
    by_contra hnone
    have hsub : S ⊆ {x | ¬Tendsto (fun r ↦ volume (S ∩ closedBall x r) / volume (closedBall x r))
        (𝓝[>] 0) (𝓝 (S.indicator 1 x))} := by
      intro x hxS hlim
      rw [indicator_of_mem hxS, Pi.one_apply] at hlim
      exact hnone ⟨x, hxS, hlim⟩
    have hnull : volume S = 0 := measure_mono_null hsub (ae_iff.mp hae)
    simp [Measure.real, hnull] at hSpos
  obtain ⟨t₁, ht₁S, ht₁_dens⟩ := hex_dens hS₁_meas hS_pos.1
  obtain ⟨t₂, ht₂S, ht₂_dens⟩ := hex_dens hS₂_meas hS_pos.2
  let t₀ : ℝ := (-H' - H) / 2
  let t₃ : ℝ := (H + H') / 2
  have ht₁_Ioo : -H < t₁ ∧ t₁ < c := ht₁S.1
  have ht₂_Ioo : c < t₂ ∧ t₂ < H := ht₂S.1
  have hord : -H' < t₀ ∧ t₀ < -H ∧ -H < t₁ ∧ t₁ < c ∧ c < t₂ ∧ t₂ < H ∧ H < t₃ ∧ t₃ < H' := by
    dsimp [t₀, t₃]
    exact ⟨by linarith, by linarith, ht₁_Ioo.1, ht₁_Ioo.2, ht₂_Ioo.1, ht₂_Ioo.2,
      by linarith, by linarith⟩
  have hcompl_small {S : Set ℝ} {x : ℝ} (hSm : MeasurableSet S)
      (hdens : Tendsto (fun r ↦ volume (S ∩ closedBall x r) / volume (closedBall x r))
        (𝓝[>] 0) (𝓝 1)) :
      ∀ᶠ r in 𝓝[>] (0 : ℝ), volume.real (closedBall x (2 * r) \ S) < r / 5 := by
    have h2r : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝 0) (𝓝 (2 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        exact mem_Ioi.mpr (by positivity)
    have hcomp := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (hdens.comp h2r)
    simp only [ENNReal.toReal_one] at hcomp
    have h1_mem : Ioo (19 / 20 : ℝ) (21 / 20) ∈ 𝓝 (1 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩
    have hmem := hcomp.eventually h1_mem
    filter_upwards [self_mem_nhdsWithin, hmem] with r (hr : 0 < r) hratio
    have hR : 0 < 2 * r := by positivity
    have hvolB : volume.real (closedBall x (2 * r)) = 4 * r := by
      rw [Real.closedBall_eq_Icc, Measure.real, Real.volume_Icc]
      have hd : (x + 2 * r) - (x - 2 * r) = 4 * r := by ring
      rw [hd, ENNReal.toReal_ofReal (by positivity)]
    have hB_ne_zero : volume (closedBall x (2 * r)) ≠ 0 := by
      intro h0
      have : volume.real (closedBall x (2 * r)) = 0 := by simp [Measure.real, h0]
      linarith
    have hB_ne_top : volume (closedBall x (2 * r)) ≠ ⊤ := by
      rw [Real.closedBall_eq_Icc, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hdiv_toReal :
        (volume (S ∩ closedBall x (2 * r)) / volume (closedBall x (2 * r))).toReal =
          volume.real (S ∩ closedBall x (2 * r)) / (4 * r) := by
      rw [ENNReal.toReal_div, ← Measure.real, ← Measure.real, hvolB]
    change (volume (S ∩ closedBall x (2 * r)) / volume (closedBall x (2 * r))).toReal ∈
      Ioo (19 / 20 : ℝ) (21 / 20) at hratio
    rw [hdiv_toReal] at hratio
    have hinter_gt : (19 / 5 : ℝ) * r < volume.real (S ∩ closedBall x (2 * r)) := by
      have h4r : 0 < 4 * r := by positivity
      have := (lt_div_iff₀ h4r).mp hratio.1
      linarith
    have hsdiff_eq : volume.real (closedBall x (2 * r) \ S) =
        volume.real (closedBall x (2 * r)) - volume.real (S ∩ closedBall x (2 * r)) := by
      have hset : closedBall x (2 * r) \ S = closedBall x (2 * r) \ (S ∩ closedBall x (2 * r)) := by
        ext z; simp [and_comm]
      rw [hset]
      exact measureReal_sdiff inter_subset_right (hSm.inter measurableSet_closedBall) hB_ne_top
    linarith
  let δ_gap : ℝ := min ((H' - H) / 8) (min ((t₁ + H) / 4) (min ((t₂ - t₁) / 8) ((H - t₂) / 4)))
  have hδ_pos : 0 < δ_gap := by
    dsimp [δ_gap]
    refine lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hrk_nhds : Tendsto fourBumpRadius atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fourBumpRadius_pos⟩
  have hgap_ev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 δ_gap := Ioo_mem_nhdsGT hδ_pos
  have hev_k := hrk_nhds.eventually
    (hgap_ev.and ((hcompl_small hS₁_meas ht₁_dens).and
      (hcompl_small hS₂_meas ht₂_dens)))
  obtain ⟨k, hk_gap, hk_S₁, hk_S₂⟩ := hev_k.exists
  let r := fourBumpRadius k
  have hr_pos : 0 < r := fourBumpRadius_pos k
  have hr_lt_δ : r < δ_gap := hk_gap.2
  have hr1 : r < (H' - H) / 8 := lt_of_lt_of_le hr_lt_δ (min_le_left _ _)
  have hr2 : r < (t₁ + H) / 4 := lt_of_lt_of_le hr_lt_δ ((min_le_right _ _).trans (min_le_left _ _))
  have hr3 : r < (t₂ - t₁) / 8 :=
    lt_of_lt_of_le hr_lt_δ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr4 : r < (H - t₂) / 4 :=
    lt_of_lt_of_le hr_lt_δ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨q₀, hq₀l, hq₀r⟩ := exists_rat_btwn (show t₀ - r < t₀ + r by linarith)
  obtain ⟨q₁, hq₁l, hq₁r⟩ := exists_rat_btwn (show t₁ - r < t₁ + r by linarith)
  obtain ⟨q₂, hq₂l, hq₂r⟩ := exists_rat_btwn (show t₂ - r < t₂ + r by linarith)
  obtain ⟨q₃, hq₃l, hq₃r⟩ := exists_rat_btwn (show t₃ - r < t₃ + r by linarith)
  have hsep0 : -H' < (q₀ : ℝ) - r := by dsimp [t₀] at hq₀l; linarith
  have hsep0_cap : (q₀ : ℝ) + r < -H := by dsimp [t₀] at hq₀r; linarith
  have hsep01 : (q₀ : ℝ) + r < (q₁ : ℝ) - r := by linarith
  have hsep12 : (q₁ : ℝ) + r < (q₂ : ℝ) - r := by linarith
  have hsep23 : (q₂ : ℝ) + r < (q₃ : ℝ) - r := by dsimp [t₃] at hq₃l; linarith
  have hsep3_cap : H < (q₃ : ℝ) - r := by dsimp [t₃] at hq₃l; linarith
  have hsep3 : (q₃ : ℝ) + r < H' := by dsimp [t₃] at hq₃r; linarith
  obtain ⟨hψ_cd, hψ_comp, hψ_ts, hψ_bd, hψ_deriv⟩ :=
    fourBumpTest_props hsep0 hsep01 hsep12 hsep23 hsep3
  refine ⟨q₀, q₁, q₂, q₃, k, by linarith, ?_, ?_, ?_, by linarith,
    hψ_cd, hψ_comp, hψ_ts, hψ_bd, ?_⟩
  · exact_mod_cast (by linarith : (q₀ : ℝ) < q₁)
  · exact_mod_cast (by linarith : (q₁ : ℝ) < q₂)
  · exact_mod_cast (by linarith : (q₂ : ℝ) < q₃)
  · rw [hψ_deriv]
    obtain ⟨_, hi0, _, _, _, hsupp0⟩ := fourBumpKernel_props q₀ k
    obtain ⟨_, hi1, hint1_eq, hnn1, hub1, hsupp1⟩ := fourBumpKernel_props q₁ k
    obtain ⟨_, hi2, _, hnn2, hub2, hsupp2⟩ := fourBumpKernel_props q₂ k
    obtain ⟨_, hi3, hint3_eq, _, _, hsupp3⟩ := fourBumpKernel_props q₃ k
    have hχ_ker_int (q : ℚ) : Integrable (fun t ↦ χ t * fourBumpKernel q k t) volume := by
      obtain ⟨hcd_q, hi_q, _, hnn_q, _, _⟩ := fourBumpKernel_props q k
      refine hi_q.mono' (hχ_meas.aestronglyMeasurable.mul hcd_q.continuous.aestronglyMeasurable) ?_
      exact Eventually.of_forall fun t ↦ by
        rw [norm_mul, Real.norm_of_nonneg (hχ_nonneg t), Real.norm_of_nonneg (hnn_q t)]
        exact mul_le_of_le_one_left (hnn_q t) (hχ_le_one t)
    have hsplit_int : (∫ t, χ t * fourBumpDeriv q₀ q₁ q₂ q₃ k t) =
        (∫ t, χ t * fourBumpKernel q₀ k t) - 2 * (∫ t, χ t * fourBumpKernel q₁ k t) +
          2 * (∫ t, χ t * fourBumpKernel q₂ k t) - (∫ t, χ t * fourBumpKernel q₃ k t) := by
      have heq (t : ℝ) : χ t * fourBumpDeriv q₀ q₁ q₂ q₃ k t =
          ((χ t * fourBumpKernel q₀ k t - 2 * (χ t * fourBumpKernel q₁ k t)) +
            2 * (χ t * fourBumpKernel q₂ k t)) - χ t * fourBumpKernel q₃ k t := by
        unfold fourBumpDeriv; ring
      simp_rw [heq]
      have i0 := hχ_ker_int q₀
      have i1 : Integrable (fun t ↦ 2 * (χ t * fourBumpKernel q₁ k t)) volume :=
        (hχ_ker_int q₁).const_mul 2
      have i2 : Integrable (fun t ↦ 2 * (χ t * fourBumpKernel q₂ k t)) volume :=
        (hχ_ker_int q₂).const_mul 2
      have i3 := hχ_ker_int q₃
      have i01 : Integrable (fun t ↦ χ t * fourBumpKernel q₀ k t -
          2 * (χ t * fourBumpKernel q₁ k t)) volume := i0.sub i1
      have i012 : Integrable (fun t ↦ χ t * fourBumpKernel q₀ k t -
          2 * (χ t * fourBumpKernel q₁ k t) + 2 * (χ t * fourBumpKernel q₂ k t)) volume :=
        i01.add i2
      rw [integral_sub i012 i3, integral_add i01 i2, integral_sub i0 i1,
        integral_const_mul, integral_const_mul]
    have hJ0 : (∫ t, χ t * fourBumpKernel q₀ k t) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hbot] with t htb
      simp only [Pi.zero_apply]
      by_cases ht : t ∈ Ioo ((q₀ : ℝ) - r) ((q₀ : ℝ) + r)
      · rw [htb ⟨by linarith [ht.1], by linarith [ht.2]⟩, zero_mul]
      · rw [hsupp0 t ht, mul_zero]
    have hJ3 : (∫ t, χ t * fourBumpKernel q₃ k t) = 1 := by
      rw [← hint3_eq]
      apply integral_congr_ae
      filter_upwards [htop] with t htt
      by_cases ht : t ∈ Ioo ((q₃ : ℝ) - r) ((q₃ : ℝ) + r)
      · rw [htt ⟨by linarith [ht.1], by linarith [ht.2]⟩, one_mul]
      · rw [hsupp3 t ht, mul_zero]
    have hJ1 : 4 / 5 ≤ ∫ t, χ t * fourBumpKernel q₁ k t := by
      let E₁ := closedBall t₁ (2 * r) \ S₁
      have hE₁_meas : MeasurableSet E₁ := measurableSet_closedBall.diff hS₁_meas
      have hE₁_fin : volume E₁ ≠ ⊤ :=
        ne_top_of_le_ne_top
          (by rw [Real.closedBall_eq_Icc, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          (measure_mono sdiff_subset)
      have hdom₁ : Integrable (E₁.indicator (fun _ ↦ 1 / r)) volume :=
        (integrableOn_const hE₁_fin).integrable_indicator hE₁_meas
      have herr : (∫ t, (1 - χ t) * fourBumpKernel q₁ k t) ≤
          (1 / r) * volume.real E₁ := by
        have h1mχ_int : Integrable (fun t ↦ (1 - χ t) * fourBumpKernel q₁ k t) volume := by
          have he : (fun t ↦ (1 - χ t) * fourBumpKernel q₁ k t) =
              fun t ↦ fourBumpKernel q₁ k t - χ t * fourBumpKernel q₁ k t := by ext t; ring
          rw [he]
          exact hi1.sub (hχ_ker_int q₁)
        have hle := integral_mono h1mχ_int hdom₁ fun t ↦ by
          by_cases htI : t ∈ Ioo ((q₁ : ℝ) - r) ((q₁ : ℝ) + r)
          · by_cases htS : t ∈ S₁
            · simp [htS.2, E₁, htS]
            · have htB : t ∈ closedBall t₁ (2 * r) := by
                rw [Real.closedBall_eq_Icc]
                exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
              have htE : t ∈ E₁ := ⟨htB, htS⟩
              rw [indicator_of_mem htE]
              exact (mul_le_of_le_one_left (hnn1 t) (by linarith [hχ_nonneg t])).trans (hub1 t)
          · rw [hsupp1 t htI, mul_zero]
            by_cases htE : t ∈ E₁
            · rw [indicator_of_mem htE]; positivity
            · rw [indicator_of_notMem htE]
        rwa [integral_indicator_const _ hE₁_meas, smul_eq_mul, mul_comm] at hle
      have hdiff_eq : 1 - (∫ t, χ t * fourBumpKernel q₁ k t) =
          ∫ t, (1 - χ t) * fourBumpKernel q₁ k t := by
        have he : (fun t ↦ (1 - χ t) * fourBumpKernel q₁ k t) =
            fun t ↦ fourBumpKernel q₁ k t - χ t * fourBumpKernel q₁ k t := by ext t; ring
        rw [he, integral_sub hi1 (hχ_ker_int q₁), hint1_eq]
      have hsmall : (1 / r) * volume.real E₁ < 1 / 5 := by
        have := (div_lt_div_iff_of_pos_right hr_pos).mpr hk_S₁
        have h1 : volume.real E₁ / r = (1 / r) * volume.real E₁ := by ring
        have h2 : (r / 5) / r = 1 / 5 := by field_simp [hr_pos.ne']
        linarith
      linarith
    have hJ2 : (∫ t, χ t * fourBumpKernel q₂ k t) ≤ 1 / 5 := by
      let E₂ := closedBall t₂ (2 * r) \ S₂
      have hE₂_meas : MeasurableSet E₂ := measurableSet_closedBall.diff hS₂_meas
      have hE₂_fin : volume E₂ ≠ ⊤ :=
        ne_top_of_le_ne_top
          (by rw [Real.closedBall_eq_Icc, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          (measure_mono sdiff_subset)
      have hdom₂ : Integrable (E₂.indicator (fun _ ↦ 1 / r)) volume :=
        (integrableOn_const hE₂_fin).integrable_indicator hE₂_meas
      have hle := integral_mono (hχ_ker_int q₂) hdom₂ fun t ↦ by
        by_cases htI : t ∈ Ioo ((q₂ : ℝ) - r) ((q₂ : ℝ) + r)
        · by_cases htS : t ∈ S₂
          · simp [htS.2, E₂, htS]
          · have htB : t ∈ closedBall t₂ (2 * r) := by
              rw [Real.closedBall_eq_Icc]
              exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
            have htE : t ∈ E₂ := ⟨htB, htS⟩
            rw [indicator_of_mem htE]
            exact (mul_le_of_le_one_left (hnn2 t) (hχ_le_one t)).trans (hub2 t)
        · rw [hsupp2 t htI, mul_zero]
          by_cases htE : t ∈ E₂
          · rw [indicator_of_mem htE]; positivity
          · rw [indicator_of_notMem htE]
      rw [integral_indicator_const _ hE₂_meas, smul_eq_mul, mul_comm] at hle
      have hsmall : (1 / r) * volume.real E₂ < 1 / 5 := by
        have := (div_lt_div_iff_of_pos_right hr_pos).mpr hk_S₂
        have h1 : volume.real E₂ / r = (1 / r) * volume.real E₂ := by ring
        have h2 : (r / 5) / r = 1 / 5 := by field_simp [hr_pos.ne']
        linarith
      linarith
    rw [hsplit_int, hJ0, hJ3]
    linarith

/-- Horizontal set of multi-layer columns where `E` fails to agree a.e. on `Ioo (-H') H'` with the
ray `Ioi (columnSignedHeight E H y)` (`BV14a`, `GR10`). -/
def multiLayerColumns {m : ℕ} (E : Set (Space (m + 1))) (U : Set (Space m)) (H H' : ℝ) :
    Set (Space m) :=
  {y ∈ U | ¬(∀ᵐ t ∂volume.restrict (Ioo (-H') H'),
    E.indicator (fun _ ↦ (1 : ℝ)) (point y t) =
      (Ioi (columnSignedHeight E H y)).indicator (fun _ ↦ (1 : ℝ)) t)}

/-- Vertical `L¹` single-layer discrepancy along column `y` over `Ioo (-H') H'`. -/
def columnLayerError {m : ℕ} (E : Set (Space (m + 1))) (H H' : ℝ) (y : Space m) : ℝ :=
  ∫ t in Ioo (-H') H',
    |E.indicator (fun _ ↦ (1 : ℝ)) (point y t) -
      (Ioi (columnSignedHeight E H y)).indicator (fun _ ↦ (1 : ℝ)) t|

theorem measurable_columnLayerError {m : ℕ} {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (H H' : ℝ) :
    Measurable (columnLayerError E H H') := by
  have hg : Measurable (columnSignedHeight E H) := measurable_columnSignedHeight hE H
  have hlt_meas : MeasurableSet {p : Space m × ℝ | columnSignedHeight E H p.1 < p.2} :=
    measurableSet_lt (hg.comp measurable_fst) measurable_snd
  have hind_ray : Measurable (fun p : Space m × ℝ ↦
      (Ioi (columnSignedHeight E H p.1)).indicator (fun _ ↦ (1 : ℝ)) p.2) := by
    have heq : (fun p : Space m × ℝ ↦
        (Ioi (columnSignedHeight E H p.1)).indicator (fun _ ↦ (1 : ℝ)) p.2) =
        {p : Space m × ℝ | columnSignedHeight E H p.1 < p.2}.indicator (fun _ ↦ (1 : ℝ)) := by
      ext p
      by_cases hp : columnSignedHeight E H p.1 < p.2 <;> simp [hp]
    rw [heq]
    exact measurable_const.indicator hlt_meas
  have hmeas_prod : Measurable (fun p : Space m × ℝ ↦
      |E.indicator (fun _ ↦ (1 : ℝ)) (point p.1 p.2) -
        (Ioi (columnSignedHeight E H p.1)).indicator (fun _ ↦ (1 : ℝ)) p.2|) :=
    continuous_abs.measurable.comp
      (((measurable_const.indicator hE).comp pointContinuousLinearMap.continuous.measurable).sub
        hind_ray)
  exact (hmeas_prod.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo (-H') H'))).measurable

theorem columnLayerError_eq_zero_iff {m : ℕ} {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (H H' : ℝ) (y : Space m) :
    columnLayerError E H H' y = 0 ↔
      (∀ᵐ t ∂volume.restrict (Ioo (-H') H'),
        E.indicator (fun _ ↦ (1 : ℝ)) (point y t) =
          (Ioi (columnSignedHeight E H y)).indicator (fun _ ↦ (1 : ℝ)) t) := by
  let d : ℝ → ℝ := fun t ↦
    |E.indicator (fun _ ↦ (1 : ℝ)) (point y t) -
      (Ioi (columnSignedHeight E H y)).indicator (fun _ ↦ (1 : ℝ)) t|
  have hd_meas : Measurable d :=
    continuous_abs.measurable.comp
      (((measurable_const.indicator hE).comp (continuous_point y).measurable).sub
        (measurable_const.indicator measurableSet_Ioi))
  have hfin : volume (Ioo (-H') H') ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hd_int : IntegrableOn d (Ioo (-H') H') volume := by
    refine (integrableOn_const (C := (1 : ℝ)) hfin).mono' hd_meas.aestronglyMeasurable ?_
    refine Eventually.of_forall fun t ↦ ?_
    rw [Real.norm_of_nonneg (abs_nonneg _), abs_le]
    by_cases hx : point y t ∈ E <;> by_cases ht : columnSignedHeight E H y < t <;> simp [hx, ht]
  unfold columnLayerError
  change (∫ t in Ioo (-H') H', d t) = 0 ↔ _
  rw [integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ ↦ abs_nonneg _) hd_int]
  refine ⟨fun h ↦ h.mono fun t ht ↦ sub_eq_zero.mp (abs_eq_zero.mp ht),
    fun h ↦ h.mono fun t ht ↦ by simp [ht]⟩

theorem measurableSet_multiLayerColumns {m : ℕ} {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : MeasurableSet U) (H H' : ℝ) :
    MeasurableSet (multiLayerColumns E U H H') := by
  have heq : multiLayerColumns E U H H' = {y ∈ U | columnLayerError E H H' y ≠ 0} := by
    ext y
    simp [multiLayerColumns, columnLayerError_eq_zero_iff hE H H' y]
  rw [heq]
  exact hU.inter ((measurable_columnLayerError hE H H') (measurableSet_singleton 0).compl)

/-- On any measurable horizontal set `S ⊆ U` where a single smooth vertical test `ψ` (`|ψ| ≤ 1`,
`tsupport ψ ⊆ Ioo (-H') H'`) satisfies `2 ≤ -(∫ t, 1_E(y, t) * ψ'(t))` for every `y ∈ S`, the
projected perimeter satisfies `2 * volume S ≤ projectedPerimeterMeasure μ S`. -/
private theorem two_mul_volume_le_projectedPerimeter_of_vertical_test {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo (-H') H') (hψ_bd : ∀ t, |ψ t| ≤ 1)
    {S : Set (Space m)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hS_jump : ∀ y ∈ S, 2 ≤ -(∫ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * deriv ψ t)) :
    2 * volume S ≤ projectedPerimeterMeasure μ S := by
  let Lψ : Space m → ℝ := fun y ↦ -(∫ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * deriv ψ t)
  have hdψ_cont : Continuous (deriv ψ) := (contDiff_one_iff_deriv.mp hψ).2
  have hdψ_supp : tsupport (deriv ψ) ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro t ht
    by_contra hnot
    apply ht
    have hev : ψ =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hnot] with s hs
      exact image_eq_zero_of_notMem_tsupport hs
    simpa using hev.deriv_eq
  have hdψ_comp : HasCompactSupport (deriv ψ) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) hdψ_supp
  have hdψ_int : Integrable (deriv ψ) volume := hdψ_cont.integrable_of_hasCompactSupport hdψ_comp
  let Cψ : ℝ := ∫ t, ‖deriv ψ t‖
  have hCψ_nonneg : 0 ≤ Cψ := integral_nonneg fun _ ↦ norm_nonneg _
  have hLψ_meas : Measurable Lψ := by
    have hp_meas : Measurable (fun p : Space m × ℝ ↦
        E.indicator (fun _ ↦ (1 : ℝ)) (point p.1 p.2) * deriv ψ p.2) :=
      ((measurable_const.indicator hE).comp pointContinuousLinearMap.continuous.measurable).mul
        (hdψ_cont.measurable.comp measurable_snd)
    exact (hp_meas.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.neg
  have hLψ_bd (y : Space m) : ‖Lψ y‖ ≤ Cψ := by
    dsimp only [Lψ, Cψ]
    rw [norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _) hdψ_int.norm ?_
    exact Eventually.of_forall fun t ↦ by
      by_cases hx : point y t ∈ E <;> simp [hx]
  let σ : Measure (Space m) := projectedPerimeterMeasure μ
  have hsmooth_le : ∀ φ : Space m → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ y, φ y * Lψ y) ≤ ∫ y, |φ y| ∂σ := by
    intro φ hφ hφc hφs
    let F₀ : Space (m + 1) → Space (m + 1) :=
      fun x ↦ (φ (horizontal x) * ψ (x (Fin.last m))) • verticalDirection m
    have hF₀_diff : ContDiff ℝ 1 F₀ :=
      ((hφ.comp horizontalContinuousLinearMap.contDiff).mul
        (hψ.comp (PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).contDiff)).smul contDiff_const
    obtain ⟨hF₀_comp, hF₀_sub⟩ :=
      hasCompactSupport_product_field hφc hφs hψc hψs (verticalDirection m)
    let Fc : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨F₀, hF₀_diff.continuous⟩, hF₀_comp⟩
    have hid := hdist Fc hF₀_diff hF₀_sub
    have hdiv_eq (x : Space (m + 1)) :
        fieldDivergence b Fc x = φ (horizontal x) * deriv ψ (x (Fin.last m)) := by
      change fieldDivergence b F₀ x = _
      dsimp only [F₀]
      rw [fieldDivergence_horizontal_mul_vertical_smul b hφ hψ (verticalDirection m) x]
      simp
    have hg_int : Integrable
        (fun x : Space (m + 1) ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x)
        volume := by
      have hcont := fieldDivergence_continuous b hF₀_diff
      have hdiv_supp : tsupport (fieldDivergence b F₀) ⊆ tsupport F₀ := by
        apply closure_minimal _ (isClosed_tsupport F₀)
        intro x hx
        by_contra hn
        exact hx (fieldDivergence_zero_of_notMem_tsupport b F₀ hn)
      have hdiv_c : HasCompactSupport (fieldDivergence b F₀) :=
        hF₀_comp.of_isClosed_subset (isClosed_tsupport _) hdiv_supp
      have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hdiv_c).indicator hE
      refine hi.congr (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ E <;> simp [hx, Fc]
    have hlhs : -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x) =
        ∫ y, φ y * Lψ y := by
      rw [integral_space_eq_integral_horizontal_vertical hg_int]
      simp_rw [hdiv_eq, horizontal_point, last_point]
      have hpull (y : Space m) :
          (∫ t : ℝ, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * (φ y * deriv ψ t)) =
            -(φ y * Lψ y) := by
        have hf : (fun t : ℝ ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * (φ y * deriv ψ t)) =
            fun t ↦ φ y * (E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * deriv ψ t) := by
          ext t; ring
        rw [hf, integral_const_mul]
        dsimp [Lψ]
        ring
      simp_rw [hpull]
      rw [integral_neg, neg_neg]
    obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuousOn hφ.continuous.continuousOn
    have hφ_abs_int : Integrable (fun x : Space (m + 1) ↦ |φ (horizontal x)|) μ := by
      refine Integrable.of_bound (hφ.continuous.abs.comp continuous_horizontal).aestronglyMeasurable
        (max C 0) (Eventually.of_forall fun x ↦ ?_)
      rw [Real.norm_of_nonneg (abs_nonneg _), ← Real.norm_eq_abs]
      by_cases hy : horizontal x ∈ tsupport φ
      · exact (hC _ hy).trans (le_max_left _ _)
      · simp [image_eq_zero_of_notMem_tsupport hy]
    have hrhs_le : (∫ x, inner ℝ (Fc x) (ν x) ∂μ) ≤ ∫ y, |φ y| ∂σ := by
      have hmap : (∫ y, |φ y| ∂σ) = ∫ x, |φ (horizontal x)| ∂μ :=
        integral_map continuous_horizontal.measurable.aemeasurable
          hφ.continuous.abs.aestronglyMeasurable
      rw [hmap]
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hφ_abs_int ?_
      filter_upwards [hνunit] with x hx
      change ‖inner ℝ ((φ (horizontal x) * ψ (x (Fin.last m))) • verticalDirection m) (ν x)‖ ≤ _
      calc
        ‖inner ℝ ((φ (horizontal x) * ψ (x (Fin.last m))) • verticalDirection m) (ν x)‖
            ≤ ‖(φ (horizontal x) * ψ (x (Fin.last m))) • verticalDirection m‖ * ‖ν x‖ :=
          norm_inner_le_norm _ _
        _ = |φ (horizontal x)| * |ψ (x (Fin.last m))| := by
          rw [hx, mul_one, norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs, abs_mul]
        _ ≤ |φ (horizontal x)| := mul_le_of_le_one_right (abs_nonneg _) (hψ_bd _)
    linarith
  have hcont_le : ∀ χ : Space m → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U →
      (∀ y, χ y ∈ Icc (0 : ℝ) 1) → (∫ y, χ y * Lψ y) ≤ ∫ y, χ y ∂σ := by
    intro χ hχ hχc hχs hχv
    let K₀ := tsupport χ
    have hK₀ : IsCompact K₀ := hχc
    let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
    have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
    have hg_ex (j : ℕ) := hχ.exists_contDiff_approx 1 (ε := fun _ ↦ ε j)
      continuous_const (fun _ ↦ hε j)
    choose g hg hclose hsupp using hg_ex
    have hgs (j : ℕ) : tsupport (g j) ⊆ K₀ := closure_mono (hsupp j)
    have hgc (j : ℕ) : HasCompactSupport (g j) := hK₀.of_isClosed_subset (isClosed_tsupport _) (hgs j)
    have hg1 (j : ℕ) : ContDiff ℝ 1 (g j) := by simpa using hg j
    have hgt (y : Space m) : Tendsto (fun j ↦ g j y) atTop (𝓝 (χ y)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ (hclose j y).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hg_bd (j : ℕ) (y : Space m) : ‖g j y‖ ≤ 2 := by
      have hd := hclose j y
      rw [dist_eq_norm] at hd
      have hε1 : ε j ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
      have htri : ‖g j y‖ ≤ ‖g j y - χ y‖ + ‖χ y‖ := by
        simpa only [sub_add_cancel] using norm_add_le (g j y - χ y) (χ y)
      have hχ1 : ‖χ y‖ ≤ 1 := by rw [Real.norm_of_nonneg (hχv y).1]; exact (hχv y).2
      linarith
    have hlim_L : Tendsto (fun j ↦ ∫ y, g j y * Lψ y) atTop (𝓝 (∫ y, χ y * Lψ y)) := by
      have hdom : Integrable (K₀.indicator (fun _ ↦ 2 * Cψ)) volume :=
        (integrableOn_const hK₀.measure_lt_top.ne).integrable_indicator hK₀.measurableSet
      refine tendsto_integral_of_dominated_convergence (K₀.indicator (fun _ ↦ 2 * Cψ))
        (fun j ↦ ((hg1 j).continuous.aestronglyMeasurable.mul hLψ_meas.aestronglyMeasurable))
        hdom (fun j ↦ Eventually.of_forall fun y ↦ ?_)
        (Eventually.of_forall fun y ↦ (hgt y).mul tendsto_const_nhds)
      by_cases hy : y ∈ K₀
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul (hg_bd j y) (hLψ_bd y) (norm_nonneg _) (by positivity)
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (hgs j hh)),
          zero_mul, norm_zero]
    have hlim_R : Tendsto (fun j ↦ ∫ y, |g j y| ∂σ) atTop (𝓝 (∫ y, χ y ∂σ)) := by
      have hlim_abs : Tendsto (fun j ↦ ∫ y, |g j y| ∂σ) atTop (𝓝 (∫ y, |χ y| ∂σ)) :=
        tendsto_integral_of_dominated_convergence (fun _ ↦ (2 : ℝ))
          (fun j ↦ (hg1 j).continuous.abs.aestronglyMeasurable) (integrable_const 2)
          (fun j ↦ Eventually.of_forall fun y ↦ by
            rw [Real.norm_of_nonneg (abs_nonneg _), ← Real.norm_eq_abs]
            exact hg_bd j y)
          (Eventually.of_forall fun y ↦ (hgt y).abs)
      have habs_eq : (fun y ↦ |χ y|) = χ := funext fun y ↦ abs_of_nonneg (hχv y).1
      rwa [habs_eq] at hlim_abs
    exact le_of_tendsto_of_tendsto hlim_L hlim_R (Eventually.of_forall fun j ↦
      hsmooth_le (g j) (hg1 j) (hgc j) ((hgs j).trans hχs))
  have hU_lt := volume_lt_top_of_slab_trapped b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop
  have hS_ne_top : volume S ≠ ⊤ := (lt_of_le_of_lt (measure_mono hSU) hU_lt).ne
  rw [hS.measure_eq_iSup_isCompact_of_ne_top hS_ne_top, ENNReal.mul_iSup]
  refine iSup_le fun K ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hKS ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hK ↦ ?_
  have hreal_le : 2 * volume.real K ≤ σ.real K := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε : ℝ := δ / (Cψ + 2)
    have hε_pos : 0 < ε := div_pos hδ (by linarith)
    have hε_ne : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε_pos).ne'
    obtain ⟨V₁, hKV₁, hV₁o, _, hV₁_lt⟩ :=
      hK.measurableSet.exists_isOpen_sdiff_lt (μ := volume) hK.measure_lt_top.ne hε_ne
    obtain ⟨V₂, hKV₂, hV₂o, _, hV₂_lt⟩ :=
      hK.measurableSet.exists_isOpen_sdiff_lt (μ := σ) (measure_ne_top σ K) hε_ne
    let V : Set (Space m) := V₁ ∩ V₂ ∩ U
    have hVo : IsOpen V := (hV₁o.inter hV₂o).inter hU
    have hKV : K ⊆ V := fun y hy ↦ ⟨⟨hKV₁ hy, hKV₂ hy⟩, hSU (hKS hy)⟩
    have hVU : V ⊆ U := inter_subset_right
    obtain ⟨χ, hχK, hχc, hχs, hχv⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hVo hKV
    have hcut := hcont_le χ χ.continuous hχc (hχs.trans hVU) hχv
    have hχL_int : Integrable (fun y ↦ χ y * Lψ y) volume := by
      have hdom : Integrable ((tsupport χ).indicator (fun _ ↦ Cψ)) volume :=
        (integrableOn_const hχc.measure_lt_top.ne).integrable_indicator (isClosed_tsupport _).measurableSet
      refine hdom.mono' (χ.continuous.aestronglyMeasurable.mul hLψ_meas.aestronglyMeasurable)
        (Eventually.of_forall fun y ↦ ?_)
      by_cases hy : y ∈ tsupport χ
      · rw [indicator_of_mem hy, norm_mul, Real.norm_of_nonneg (hχv y).1]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hχv y).2).trans (hLψ_bd y)
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, zero_mul, norm_zero]
    have hsplit_V : (∫ y, χ y * Lψ y) =
        (∫ y in K, χ y * Lψ y) + ∫ y in V \ K, χ y * Lψ y := by
      have hsuppV : (∫ y, χ y * Lψ y) = ∫ y in V, χ y * Lψ y := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hyV
        rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hyV (hχs hh)), zero_mul]
      rw [hsuppV, ← setIntegral_union disjoint_sdiff_right (hVo.measurableSet.diff hK.measurableSet)
        hχL_int.integrableOn hχL_int.integrableOn, union_sdiff_cancel hKV]
    have hK_lower : 2 * volume.real K ≤ ∫ y in K, χ y * Lψ y := by
      have hc2 : IntegrableOn (fun _ : Space m ↦ (2 : ℝ)) K volume :=
        integrableOn_const hK.measure_lt_top.ne
      have hle := setIntegral_mono_on hc2 hχL_int.integrableOn hK.measurableSet fun y hy ↦ by
        rw [hχK hy, Pi.one_apply, one_mul]
        exact hS_jump y (hKS hy)
      rwa [setIntegral_const, smul_eq_mul, mul_comm] at hle
    have hVK_fin : volume (V \ K) ≠ ⊤ :=
      ne_top_of_le_ne_top hU_lt.ne (measure_mono (sdiff_subset.trans hVU))
    have hVK_vol_le : volume.real (V \ K) ≤ ε := by
      have hsub1 : V \ K ⊆ V₁ \ K := sdiff_subset_sdiff (inter_subset_left.trans inter_subset_left) Subset.rfl
      have hlt1 := lt_of_le_of_lt (measure_mono hsub1) hV₁_lt
      exact ENNReal.toReal_le_of_le_ofReal hε_pos.le hlt1.le
    have hVK_err : |∫ y in V \ K, χ y * Lψ y| ≤ Cψ * ε := by
      have hcC : IntegrableOn (fun _ : Space m ↦ Cψ) (V \ K) volume := integrableOn_const hVK_fin
      rw [← Real.norm_eq_abs]
      have hle := norm_integral_le_of_norm_le (f := fun y ↦ χ y * Lψ y) hcC
        (Eventually.of_forall fun y ↦ by
          rw [norm_mul, Real.norm_of_nonneg (hχv y).1]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hχv y).2).trans (hLψ_bd y))
      rw [setIntegral_const, smul_eq_mul, mul_comm] at hle
      exact hle.trans (mul_le_mul_of_nonneg_left hVK_vol_le hCψ_nonneg)
    have hσ_upper : (∫ y, χ y ∂σ) ≤ σ.real K + ε := by
      have hsuppσ : (∫ y, χ y ∂σ) = ∫ y in V, χ y ∂σ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hyV
        exact image_eq_zero_of_notMem_tsupport fun hh ↦ hyV (hχs hh)
      have hχσ_int : Integrable χ σ := χ.continuous.integrable_of_hasCompactSupport hχc
      have hleV : (∫ y in V, χ y ∂σ) ≤ σ.real V := by
        have hc1 : IntegrableOn (fun _ : Space m ↦ (1 : ℝ)) V σ :=
          integrableOn_const (measure_ne_top σ V)
        have h1 := integral_mono hχσ_int.integrableOn hc1 fun y ↦ (hχv y).2
        rwa [setIntegral_const, smul_eq_mul, mul_one] at h1
      have hV_split : σ.real V = σ.real K + σ.real (V \ K) := by
        have hu : K ∪ (V \ K) = V := union_sdiff_cancel hKV
        nth_rw 1 [← hu]
        exact measureReal_union disjoint_sdiff_right (hVo.measurableSet.diff hK.measurableSet)
          (measure_ne_top σ _) (measure_ne_top σ _)
      have hσ_VK : σ.real (V \ K) ≤ ε := by
        have hsub2 : V \ K ⊆ V₂ \ K :=
          sdiff_subset_sdiff (inter_subset_left.trans inter_subset_right) Subset.rfl
        exact ENNReal.toReal_le_of_le_ofReal hε_pos.le
          (lt_of_le_of_lt (measure_mono hsub2) hV₂_lt).le
      linarith
    have hcomb : 2 * volume.real K ≤ σ.real K + (Cψ + 1) * ε := by
      linarith [(abs_le.mp hVK_err).1]
    have hε_bound : (Cψ + 1) * ε ≤ δ := by
      dsimp [ε]
      have hpos_den : 0 < Cψ + 2 := by linarith
      rw [mul_div_assoc', div_le_iff₀ hpos_den]
      nlinarith
    linarith
  calc
    2 * volume K = ENNReal.ofReal (2 * volume.real K) := by
      have hof2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
      rw [ENNReal.ofReal_mul (by norm_num), hof2,
        Measure.real, ENNReal.ofReal_toReal hK.measure_lt_top.ne]
    _ ≤ ENNReal.ofReal (σ.real K) := ENNReal.ofReal_le_ofReal hreal_le
    _ = σ K := ENNReal.ofReal_toReal (measure_ne_top σ K)
    _ ≤ σ S := measure_mono hKS

/-- Localized multi-layer column bound: on any measurable horizontal subset `G ⊆ U`, the Lebesgue
measure of `multiLayerColumns E U H H' ∩ G` does not exceed its projected tilt-excess
`projectedExcessMeasure μ ν (multiLayerColumns E U H H' ∩ G)` (`BV14a`, `GR10`). -/
theorem volume_multiLayerColumns_inter_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {G : Set (Space m)} (hG : MeasurableSet G) (hGU : G ⊆ U) :
    volume (multiLayerColumns E U H H' ∩ G) ≤
      projectedExcessMeasure μ ν (multiLayerColumns E U H H' ∩ G) := by
  let Mset := multiLayerColumns E U H H'
  have hMset_meas : MeasurableSet Mset :=
    measurableSet_multiLayerColumns hE hU.measurableSet H H'
  let MG := Mset ∩ G
  have hMG_meas : MeasurableSet MG := hMset_meas.inter hG
  have hMG_U : MG ⊆ U := inter_subset_right.trans hGU
  let seq : ℕ → ℚ × ℚ × ℚ × ℚ × ℕ :=
    fun n ↦ (Encodable.decode (α := ℚ × ℚ × ℚ × ℚ × ℕ) n).getD (0, 0, 0, 0, 0)
  have hseq_surj : Function.Surjective seq :=
    Encodable.surjective_decode_getD (ℚ × ℚ × ℚ × ℚ × ℕ) (0, 0, 0, 0, 0)
  let valid : ℚ × ℚ × ℚ × ℚ × ℕ → Prop := fun p ↦
    let (q₀, q₁, q₂, q₃, k) := p
    ∃ (hcd : ContDiff ℝ 2 (fourBumpTest H' q₀ q₁ q₂ q₃ k)),
      HasCompactSupport (fourBumpTest H' q₀ q₁ q₂ q₃ k) ∧
        tsupport (fourBumpTest H' q₀ q₁ q₂ q₃ k) ⊆ Ioo (-H') H' ∧
        (∀ t, |fourBumpTest H' q₀ q₁ q₂ q₃ k t| ≤ 1)
  classical
  let W : ℕ → Set (Space m) := fun n ↦
    let (q₀, q₁, q₂, q₃, k) := seq n
    if valid (seq n) then
      {y ∈ MG | 2 ≤ -(∫ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
        deriv (fourBumpTest H' q₀ q₁ q₂ q₃ k) t)}
    else ∅
  have hW_meas (n : ℕ) : MeasurableSet (W n) := by
    dsimp only [W]
    split_ifs with hv
    · rcases hseq_eq : seq n with ⟨q₀, q₁, q₂, q₃, k⟩
      rw [hseq_eq] at hv
      dsimp only
      obtain ⟨hcd, -, -, -⟩ := hv
      have hd_cont : Continuous (deriv (fourBumpTest H' q₀ q₁ q₂ q₃ k)) :=
        (contDiff_one_iff_deriv.mp (hcd.of_le (by norm_num))).2
      have hp_meas : Measurable (fun p : Space m × ℝ ↦
          E.indicator (fun _ ↦ (1 : ℝ)) (point p.1 p.2) *
            deriv (fourBumpTest H' q₀ q₁ q₂ q₃ k) p.2) :=
        ((measurable_const.indicator hE).comp pointContinuousLinearMap.continuous.measurable).mul
          (hd_cont.measurable.comp measurable_snd)
      have hfn_meas : Measurable (fun y : Space m ↦
          -(∫ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
            deriv (fourBumpTest H' q₀ q₁ q₂ q₃ k) t)) :=
        (hp_meas.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.neg
      exact hMG_meas.inter (measurableSet_Ici.preimage hfn_meas)
    · exact MeasurableSet.empty
  let Mn : ℕ → Set (Space m) := disjointed W
  have hMn_meas (n : ℕ) : MeasurableSet (Mn n) := MeasurableSet.disjointed hW_meas n
  have hMn_disj : Pairwise (Function.onFun Disjoint Mn) := disjoint_disjointed W
  have hMn_sub_W (n : ℕ) : Mn n ⊆ W n := disjointed_subset W n
  have hW_sub_MG (n : ℕ) : W n ⊆ MG := by
    dsimp only [W]
    split_ifs <;> [exact sep_subset _ _; exact empty_subset _]
  have hMn_piece (n : ℕ) : 2 * volume (Mn n) ≤ projectedPerimeterMeasure μ (Mn n) := by
    by_cases hv : valid (seq n)
    · have hWn : W n =
          let (q₀, q₁, q₂, q₃, k) := seq n
          {y ∈ MG | 2 ≤ -(∫ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
            deriv (fourBumpTest H' q₀ q₁ q₂ q₃ k) t)} := ite_eq_left hv
      rcases hseq_eq : seq n with ⟨q₀, q₁, q₂, q₃, k⟩
      rw [hseq_eq] at hv hWn
      obtain ⟨hcd, hcomp, hts, hbd⟩ := hv
      refine two_mul_volume_le_projectedPerimeter_of_vertical_test b hE hU hH hHH' μ hμcompl
        hμopen hν hνunit hdist hbot htop (hcd.of_le (by norm_num)) hcomp hts hbd
        (hMn_meas n) ((hMn_sub_W n).trans ((hW_sub_MG n).trans hMG_U)) ?_
      intro y hy
      have hyW := hMn_sub_W n hy
      rw [hWn] at hyW
      exact hyW.2
    · have hWn : W n = ∅ := ite_eq_right hv
      have h0 : Mn n = ∅ := subset_eq_empty (hMn_sub_W n) hWn
      simp [h0]
  have hcover_ae : ∀ᵐ y ∂volume, y ∈ MG → y ∈ ⋃ n, Mn n := by
    rw [iUnion_disjointed]
    filter_upwards [ae_vertical_of_ae_volume hbot, ae_vertical_of_ae_volume htop] with
      y hybot hytop hyMG
    have hyU : y ∈ U := hMG_U hyMG
    have hyM : y ∈ Mset := hyMG.1
    have hbot_y : ∀ᵐ t ∂volume, t ∈ Ioo (-H') (-H) → E.indicator (fun _ ↦ (1 : ℝ)) (point y t) = 0 := by
      filter_upwards [hybot] with t ht htI
      simp only [horizontal_point, last_point] at ht
      simp [ht hyU htI]
    have htop_y : ∀ᵐ t ∂volume, t ∈ Ioo H H' → E.indicator (fun _ ↦ (1 : ℝ)) (point y t) = 1 := by
      filter_upwards [hytop] with t ht htI
      simp only [horizontal_point, last_point] at ht
      simp [ht hyU htI]
    have h01 (t : ℝ) : E.indicator (fun _ ↦ (1 : ℝ)) (point y t) = 0 ∨
        E.indicator (fun _ ↦ (1 : ℝ)) (point y t) = 1 := by
      by_cases hx : point y t ∈ E <;> simp [hx]
    obtain ⟨q₀, q₁, q₂, q₃, k, -, -, -, -, -, hcd, hcomp, hts, hbd, hjump⟩ :=
      exists_fourBumpTest_of_not_singleLayer hH hHH'
        ((measurable_const.indicator hE).comp (continuous_point y).measurable)
        h01 hbot_y htop_y hyM.2
    obtain ⟨n, hn⟩ := hseq_surj (q₀, q₁, q₂, q₃, k)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    have hv : valid (seq n) := by
      rw [hn]
      exact ⟨hcd, hcomp, hts, hbd⟩
    dsimp only [W]
    rw [ite_eq_left hv, hn]
    exact ⟨hyMG, hjump⟩
  have hvol_eq : volume MG = volume (⋃ n, Mn n) := by
    apply le_antisymm
    · have hsub : MG ⊆ (⋃ n, Mn n) ∪ {y | ¬(y ∈ MG → y ∈ ⋃ n, Mn n)} := fun y hy ↦ by
        by_cases h : y ∈ ⋃ n, Mn n
        · exact Or.inl h
        · exact Or.inr fun hh ↦ h (hh hy)
      calc
        volume MG ≤ volume ((⋃ n, Mn n) ∪ {y | ¬(y ∈ MG → y ∈ ⋃ n, Mn n)}) := measure_mono hsub
        _ ≤ volume (⋃ n, Mn n) + volume {y | ¬(y ∈ MG → y ∈ ⋃ n, Mn n)} := measure_union_le _ _
        _ = volume (⋃ n, Mn n) := by rw [ae_iff.mp hcover_ae, add_zero]
    · exact measure_mono (iUnion_subset fun n ↦ (hMn_sub_W n).trans (hW_sub_MG n))
  have h2_le : 2 * volume MG ≤ volume MG + projectedExcessMeasure μ ν MG := by
    calc
      2 * volume MG = 2 * volume (⋃ n, Mn n) := by rw [hvol_eq]
      _ = 2 * ∑' n, volume (Mn n) := by rw [measure_iUnion hMn_disj hMn_meas]
      _ = ∑' n, 2 * volume (Mn n) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' n, projectedPerimeterMeasure μ (Mn n) := ENNReal.tsum_le_tsum hMn_piece
      _ = projectedPerimeterMeasure μ (⋃ n, Mn n) :=
          (measure_iUnion hMn_disj hMn_meas).symm
      _ ≤ projectedPerimeterMeasure μ MG :=
          measure_mono (iUnion_subset fun n ↦ (hMn_sub_W n).trans (hW_sub_MG n))
      _ = volume MG + projectedExcessMeasure μ ν MG :=
          projectedPerimeterMeasure_apply_eq b hE hU hH hHH' μ hμcompl hμopen hν hνunit
            hdist hbot htop hMG_meas hMG_U
  have hU_lt := volume_lt_top_of_slab_trapped b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop
  have hMG_ne_top : volume MG ≠ ⊤ := (lt_of_le_of_lt (measure_mono hMG_U) hU_lt).ne
  have htwo_add : volume MG + volume MG = 2 * volume MG := (two_mul _).symm
  rw [← htwo_add] at h2_le
  exact (ENNReal.add_le_add_iff_left hMG_ne_top).mp h2_le

/-- Global multi-layer column measure bound on `U` (`BV14a`, `GR10`). -/
theorem volume_multiLayerColumns_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E) :
    volume (multiLayerColumns E U H H') ≤
      projectedExcessMeasure μ ν (multiLayerColumns E U H H') := by
  have h := volume_multiLayerColumns_inter_le b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop hU.measurableSet Subset.rfl
  have hinter : multiLayerColumns E U H H' ∩ U = multiLayerColumns E U H H' :=
    inter_eq_left.mpr fun _ hy ↦ hy.1
  rwa [hinter] at h

/-- Real-valued multi-layer column bound `volume.real M_set ≤ (projectedExcessMeasure μ ν).real U`
(`GR10`). -/
theorem volume_real_multiLayerColumns_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E) :
    volume.real (multiLayerColumns E U H H') ≤ (projectedExcessMeasure μ ν).real U := by
  let : IsFiniteMeasure (projectedExcessMeasure μ ν) := isFiniteMeasure_projectedExcessMeasure μ hν
  have hle := (volume_multiLayerColumns_le b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop).trans (measure_mono (fun _ hy ↦ hy.1 : multiLayerColumns E U H H' ⊆ U))
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- On any measurable horizontal set `G ⊆ U` where `(projectedExcessMeasure μ ν).restrict G ≤
ENNReal.ofReal c • volume.restrict G` with `c < 1`, the multi-layer set in `G` has Lebesgue
measure zero. -/
theorem volume_multiLayerColumns_inter_eq_zero_of_excess_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {G : Set (Space m)} (hG : MeasurableSet G) (hGU : G ⊆ U)
    {c : ℝ} (hc_lt : c < 1)
    (hexc : (projectedExcessMeasure μ ν).restrict G ≤ ENNReal.ofReal c • volume.restrict G) :
    volume (multiLayerColumns E U H H' ∩ G) = 0 := by
  let MG := multiLayerColumns E U H H' ∩ G
  have hMG_meas : MeasurableSet MG :=
    (measurableSet_multiLayerColumns hE hU.measurableSet H H').inter hG
  have h1 := volume_multiLayerColumns_inter_le b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop hG hGU
  have h2 : projectedExcessMeasure μ ν MG ≤ ENNReal.ofReal c * volume MG := by
    have hr := hexc MG
    have hMGG : MG ∩ G = MG := inter_eq_left.mpr inter_subset_right
    simpa only [Measure.restrict_apply hMG_meas, hMGG,
      Measure.smul_apply, smul_eq_mul] using hr
  have hle : volume MG ≤ ENNReal.ofReal c * volume MG := h1.trans h2
  have hU_lt := volume_lt_top_of_slab_trapped b hE hU hH hHH' μ hμcompl hμopen hν hνunit
    hdist hbot htop
  have hMG_fin : volume MG ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (inter_subset_right.trans hGU)) hU_lt).ne
  by_cases hc0 : c ≤ 0
  · rw [ENNReal.ofReal_eq_zero.mpr hc0, zero_mul] at hle
    exact nonpos_iff_eq_zero.mp hle
  · have hc_pos : 0 < c := lt_of_not_ge hc0
    have hreal : volume.real MG ≤ c * volume.real MG := by
      have htr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMG_fin) hle
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_pos.le] at htr
    have hr0 : volume.real MG ≤ 0 := by nlinarith
    by_contra hne
    exact not_le_of_gt (ENNReal.toReal_pos hne hMG_fin) hr0

/-- Single-layer epigraph identification (`BV14.2`, `GR9`): on any measurable horizontal set `G ⊆ U`
where `(projectedExcessMeasure μ ν).restrict G ≤ ENNReal.ofReal c • volume.restrict G` with
`c < 1`, `E` coincides `volume`-a.e. in `{x ∈ cylinderSet U H' | horizontal x ∈ G}` with
`epigraph (columnSignedHeight E H)`. -/
theorem ae_mem_iff_columnSignedHeight_lt_of_excess_le {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (μ : Measure (Space (m + 1))) [IsFiniteMeasure μ]
    (hμcompl : μ (cylinderSet U H')ᶜ = 0)
    (hμopen : ∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space (m + 1), Space (m + 1)),
      ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
      tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {G : Set (Space m)} (hG : MeasurableSet G) (hGU : G ⊆ U)
    {c : ℝ} (hc_lt : c < 1)
    (hexc : (projectedExcessMeasure μ ν).restrict G ≤ ENNReal.ofReal c • volume.restrict G) :
    ∀ᵐ x ∂volume, x ∈ cylinderSet U H' → horizontal x ∈ G →
      (x ∈ E ↔ columnSignedHeight E H (horizontal x) < x (Fin.last m)) := by
  have hMG0 := volume_multiLayerColumns_inter_eq_zero_of_excess_le b hE hU hH hHH' μ hμcompl
    hμopen hν hνunit hdist hbot htop hG hGU hc_lt hexc
  let S : Set (Space (m + 1)) := {x ∈ cylinderSet U H' | horizontal x ∈ G}
  have hS_meas : MeasurableSet S :=
    (measurableSet_cylinderSet hU.measurableSet H').inter
      (hG.preimage continuous_horizontal.measurable)
  let δ : Space (m + 1) → ℝ := fun x ↦
    |E.indicator (fun _ ↦ (1 : ℝ)) x -
      (epigraph (columnSignedHeight E H)).indicator (fun _ ↦ (1 : ℝ)) x|
  have h_epi_meas : MeasurableSet (epigraph (columnSignedHeight E H)) :=
    measurableSet_lt ((measurable_columnSignedHeight hE H).comp continuous_horizontal.measurable)
      ((PiLp.continuous_apply 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).measurable)
  have hδ_meas : Measurable δ :=
    continuous_abs.measurable.comp
      ((measurable_const.indicator hE).sub (measurable_const.indicator h_epi_meas))
  have hS_fin : volume S ≠ ⊤ := by
    have hU_lt := volume_lt_top_of_slab_trapped b hE hU hH hHH' μ hμcompl hμopen hν hνunit
      hdist hbot htop
    have hmp := measurePreserving_horizontal_last m
    have hsub : S ⊆ (fun x : Space (m + 1) ↦ (horizontal x, x (Fin.last m))) ⁻¹'
        (U ×ˢ Ioo (-H') H') := fun x hx ↦ hx.1
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [hmp.measure_preimage (hU.measurableSet.prod measurableSet_Ioo).nullMeasurableSet,
      Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_ne_top hU_lt.ne ENNReal.ofReal_ne_top
  have hS_int : Integrable (S.indicator δ) volume := by
    refine ((integrableOn_const (C := (1 : ℝ)) hS_fin).integrable_indicator hS_meas).mono'
      (hδ_meas.indicator hS_meas).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, indicator_of_mem hxS, Real.norm_of_nonneg (abs_nonneg _), abs_le]
      by_cases hxE : x ∈ E <;> by_cases hxe : x ∈ epigraph (columnSignedHeight E H) <;>
        simp [hxE, hxe]
    · simp [hxS]
  have hint_zero : (∫ x, S.indicator δ x) = 0 := by
    rw [integral_space_eq_integral_horizontal_vertical hS_int]
    have hMG_ae : ∀ᵐ y : Space m ∂volume, y ∉ multiLayerColumns E U H H' ∩ G :=
      compl_mem_ae_iff.mpr hMG0
    have hae_y : ∀ᵐ y : Space m ∂volume, (∫ t : ℝ, S.indicator δ (point y t)) = 0 := by
      filter_upwards [hMG_ae] with y hy_not_MG
      by_cases hyG : y ∈ G
      · have hyU : y ∈ U := hGU hyG
        have hy_not_M : y ∉ multiLayerColumns E U H H' := fun hm ↦ hy_not_MG ⟨hm, hyG⟩
        have herr0 : columnLayerError E H H' y = 0 := by
          rw [columnLayerError_eq_zero_iff hE H H' y]
          by_contra hnot_ae
          exact hy_not_M ⟨hyU, hnot_ae⟩
        have hslice_eq : (fun t : ℝ ↦ S.indicator δ (point y t)) =
            (Ioo (-H') H').indicator (fun t ↦
              |E.indicator (fun _ ↦ (1 : ℝ)) (point y t) -
                (Ioi (columnSignedHeight E H y)).indicator (fun _ ↦ (1 : ℝ)) t|) := by
          ext t
          by_cases ht : t ∈ Ioo (-H') H'
          · have hpS : point y t ∈ S := ⟨point_mem_cylinderSet.mpr ⟨hyU, ht⟩, by simp [hyG]⟩
            rw [indicator_of_mem hpS, indicator_of_mem ht]
            by_cases hc : columnSignedHeight E H y < t <;> simp [δ, epigraph, hc]
          · have hpS : point y t ∉ S := fun hh ↦ ht (by simpa using hh.1.2)
            rw [indicator_of_notMem hpS, indicator_of_notMem ht]
        rw [hslice_eq, integral_indicator measurableSet_Ioo]
        exact herr0
      · have hslice0 : (fun t : ℝ ↦ S.indicator δ (point y t)) = 0 := by
          ext t
          have hpS : point y t ∉ S := fun hh ↦ hyG (by simpa using hh.2)
          simp [hpS]
        simp [hslice0]
    rw [integral_congr_ae hae_y, integral_zero]
  have hae_zero :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x ↦ indicator_nonneg (fun _ _ ↦ abs_nonneg _) x) hS_int).mp
      hint_zero
  filter_upwards [hae_zero] with x hx0 hxΩ hxG
  have hxS : x ∈ S := ⟨hxΩ, hxG⟩
  rw [indicator_of_mem hxS] at hx0
  have heq := sub_eq_zero.mp (abs_eq_zero.mp hx0)
  by_cases hxE : x ∈ E
  · have h1 : (epigraph (columnSignedHeight E H)).indicator (fun _ ↦ (1 : ℝ)) x = 1 := by
      simp [hxE] at heq; linarith
    have hmem : x ∈ epigraph (columnSignedHeight E H) := by
      by_contra hn; simp [hn] at h1
    simpa [epigraph, hxE] using hmem
  · have h0 : (epigraph (columnSignedHeight E H)).indicator (fun _ ↦ (1 : ℝ)) x = 0 := by
      simp [hxE] at heq; linarith
    have hnmem : x ∉ epigraph (columnSignedHeight E H) := by
      intro hm; simp [hm] at h0
    simpa [epigraph, hxE] using hnmem

end SerrinEpigraph
