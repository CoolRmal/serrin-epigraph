module

public import SerrinEpigraph.ExcessPhaseBand
public import SerrinEpigraph.PerimeterRadonRepresentation
public import SerrinEpigraph.WeakEquation

/-!
# Height estimates for the harmonic approximation (`GR11`)

Setting: a slab-trapped perimeter representation `(μ, ν)` of a local perimeter minimizer `E` on
the cylinder `U × (-H', H')`, with signed height `g = columnSignedHeight E H` and projected excess
`ε = π_# ((1 - ν_n) μ)`.

* `SlabTrappedRepresentation.integral_last_mul_fderiv_horizontal_eq_zero`: the first variation
  with the vertical field `φ(πx) ψ(x_n) e_n` (`ψ ≡ 1` on the slab) gives
  `∫ ν_n Dφ(πx)(πν) dμ = 0`.
* `SlabTrappedRepresentation.integral_columnSignedHeight_mul_laplacian_eq`: the horizontal moment
  formula gives `∫ g Δφ = ∫ Dφ(πx)(πν) dμ`.
* `IsLocalPerimeterMinimizer.abs_integral_columnSignedHeight_mul_laplacian_le`:
  **very weak harmonicity of the height up to the excess**, `|∫ g Δφ| ≤ sup|Dφ| ε(B)`.
* `IsPerimeterRepresentation.integral_mul_last_eq`: the vertical Gauss–Green formula in columns.
* `neg_integral_indicator_mul_deriv_eq`: the one-dimensional column identity behind
  `∫ η (x_n - L)² ν_n dμ = ∫ η(y) ∫_{-H}^{H} 2|t - L(y)| 1[E_y Δ {t > L(y)}] dt dy`
  (`SlabTrappedRepresentation.integral_height_sq_mul_last_eq`).
* `SlabTrappedRepresentation.integral_height_sq_le` (**`GR11.1`, upper bound**): if the boundary
  lies in the band `|t - L| ≤ δ` over `B`, and `E` is the supergraph of `f` over the good set `G`,
  then `∫ η (x_n - L)² dμ ≤ 2 ∫_G η (f - L)² + 4 δ² |B \ G| + δ² ε(B)`.

No graph area formula is used: the vertical flux and the height square are computed directly from
the Gauss–Green formula of the representation.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported Laplacian

namespace SerrinEpigraph

/-! ### Product fields `φ(πx) ψ(x_n)` -/

theorem hasFDerivAt_horizontal_mul_last {m : ℕ} {φ : Space m → ℝ} {ψ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (x : Space (m + 1)) :
    HasFDerivAt (fun z : Space (m + 1) ↦ φ (horizontal z) * ψ (z (Fin.last m)))
      (φ (horizontal x) •
          ((ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ (x (Fin.last m)))).comp
            (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m))) +
        ψ (x (Fin.last m)) • (fderiv ℝ φ (horizontal x)).comp horizontalContinuousLinearMap) x := by
  have h1 : HasFDerivAt (fun z : Space (m + 1) ↦ φ (horizontal z))
      ((fderiv ℝ φ (horizontal x)).comp horizontalContinuousLinearMap) x :=
    (hφ (horizontal x)).hasFDerivAt.comp x horizontalContinuousLinearMap.hasFDerivAt
  have h2 : HasFDerivAt (fun z : Space (m + 1) ↦ ψ (z (Fin.last m)))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ (x (Fin.last m)))).comp
        (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m))) x :=
    ((hψ (x (Fin.last m))).hasDerivAt.hasFDerivAt).comp x
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).hasFDerivAt
  exact h1.mul h2

theorem fderiv_horizontal_mul_last_apply {m : ℕ} {φ : Space m → ℝ} {ψ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (x w : Space (m + 1)) :
    fderiv ℝ (fun z : Space (m + 1) ↦ φ (horizontal z) * ψ (z (Fin.last m))) x w =
      φ (horizontal x) * (deriv ψ (x (Fin.last m)) * w (Fin.last m)) +
        ψ (x (Fin.last m)) * fderiv ℝ φ (horizontal x) (horizontal w) := by
  rw [(hasFDerivAt_horizontal_mul_last hφ hψ x).fderiv]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, horizontalContinuousLinearMap_apply', EuclideanSpace.proj, PiLp.proj_apply]
  ring

/-- A function vanishing unless its horizontal and vertical factors are nonzero has compact support
inside `tsupport φ × tsupport ψ`. -/
theorem tsupport_horizontal_mul_last_subset {m : ℕ} {φ : Space m → ℝ} {ψ : ℝ → ℝ}
    {F : Space (m + 1) → ℝ}
    (hF : ∀ x, F x ≠ 0 → φ (horizontal x) ≠ 0 ∧ ψ (x (Fin.last m)) ≠ 0)
    (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ) :
    HasCompactSupport F ∧
      tsupport F ⊆ {x | horizontal x ∈ tsupport φ ∧ x (Fin.last m) ∈ tsupport ψ} := by
  let K : Set (Space (m + 1)) :=
    (fun p : Space m × ℝ ↦ point p.1 p.2) '' (tsupport φ ×ˢ tsupport ψ)
  have hK : IsCompact K := (hφc.prod hψc).image pointContinuousLinearMap.continuous
  have hsupp : Function.support F ⊆ K := by
    intro x hx
    obtain ⟨h1, h2⟩ := hF x hx
    exact ⟨(horizontal x, x (Fin.last m)), ⟨subset_tsupport φ h1, subset_tsupport ψ h2⟩,
      point_horizontal_last x⟩
  have htsK : tsupport F ⊆ K := closure_minimal hsupp hK.isClosed
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport F) htsK, htsK.trans ?_⟩
  rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
  exact ⟨by simpa [horizontal_point] using hy, by simpa [last_point] using ht⟩

/-! ### The slab cutoff -/

/-- A smooth vertical cutoff, equal to `1` on `Icc (-(H + H') / 2) ((H + H') / 2)` and compactly
supported in `Ioo (-H') H'`. -/
def slabCutoff {H H' : ℝ} (hH : 0 < H) (hHH' : H < H') : ContDiffBump (0 : ℝ) where
  rIn := (H + H') / 2
  rOut := (H + 3 * H') / 4
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem slabCutoff_props {H H' : ℝ} (hH : 0 < H) (hHH' : H < H') :
    ContDiff ℝ 1 (slabCutoff hH hHH' : ℝ → ℝ) ∧ HasCompactSupport (slabCutoff hH hHH' : ℝ → ℝ) ∧
      tsupport (slabCutoff hH hHH' : ℝ → ℝ) ⊆ Ioo (-H') H' ∧
      (∀ t ∈ Ioo (-((H + H') / 2)) ((H + H') / 2), (slabCutoff hH hHH' : ℝ → ℝ) t = 1) ∧
      (∀ t ∈ Ioo (-((H + H') / 2)) ((H + H') / 2), deriv (slabCutoff hH hHH' : ℝ → ℝ) t = 0) := by
  let B := slabCutoff hH hHH'
  have hrIn : B.rIn = (H + H') / 2 := rfl
  have hrOut : B.rOut = (H + 3 * H') / 4 := rfl
  have hone : ∀ t ∈ Ioo (-((H + H') / 2)) ((H + H') / 2), (B : ℝ → ℝ) t = 1 := by
    intro t ht
    apply B.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc, hrIn]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨B.contDiff, B.hasCompactSupport, ?_, hone, ?_⟩
  · rw [B.tsupport_eq]
    intro t ht
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add, mem_Icc, hrOut] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    have hev : (B : ℝ → ℝ) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hone s hs
    simpa using hev.deriv_eq

/-! ### The projected excess as an integral -/

theorem projectedExcessMeasure_real_eq_setIntegral {m : ℕ} {μ : Measure (Space (m + 1))}
    [IsFiniteMeasure μ] {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) {A : Set (Space m)} (hA : MeasurableSet A) :
    (projectedExcessMeasure μ ν).real A =
      ∫ x in horizontal ⁻¹' A, (1 - ν x (Fin.last m)) ∂μ := by
  have hπm : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  have hBm : MeasurableSet (horizontal ⁻¹' A : Set (Space (m + 1))) := hA.preimage hπm
  have hlin : projectedExcessMeasure μ ν A =
      ∫⁻ x in horizontal ⁻¹' A, ENNReal.ofReal (1 - ν x (Fin.last m)) ∂μ := by
    unfold projectedExcessMeasure
    rw [Measure.map_apply hπm hA, withDensity_apply _ hBm]
    simp only [inner_verticalDirection_right]
  have hf_int : Integrable (fun x ↦ 1 - ν x (Fin.last m)) μ := by
    have h : Integrable (fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)) μ :=
      (integrable_const 1).sub (hν.inner_const _)
    simpa only [inner_verticalDirection_right] using h
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ 1 - ν x (Fin.last m) := by
    filter_upwards [hνunit] with x hx
    have h := abs_apply_last_le_norm (ν x)
    rw [hx] at h
    linarith [le_abs_self (ν x (Fin.last m))]
  rw [Measure.real, hlin, integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf_nonneg)
    hf_int.aestronglyMeasurable.restrict]

theorem ae_one_sub_last_nonneg {m : ℕ} {μ : Measure (Space (m + 1))}
    {ν : Space (m + 1) → Space (m + 1)} (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) :
    ∀ᵐ x ∂μ, 0 ≤ 1 - ν x (Fin.last m) ∧ |ν x (Fin.last m)| ≤ 1 ∧ ‖horizontal (ν x)‖ ≤ 1 := by
  filter_upwards [hνunit] with x hx
  have h1 := abs_apply_last_le_norm (ν x)
  have h2 := norm_horizontal_le_norm_of_space (ν x)
  rw [hx] at h1 h2
  exact ⟨by linarith [le_abs_self (ν x (Fin.last m))], h1, h2⟩

/-- A function of the form `x ↦ ⟪π(ν x), Ψ(π x)⟫` with `Ψ` continuous and compactly supported is
`μ`-integrable. -/
theorem integrable_inner_horizontal_comp {m : ℕ} {μ : Measure (Space (m + 1))}
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ) {Ψ : Space m → Space m}
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    Integrable (fun x ↦ inner ℝ (horizontal (ν x)) (Ψ (horizontal x))) μ := by
  obtain ⟨C, hC⟩ := hΨ.bounded_above_of_compact_support hΨc
  have hm : AEStronglyMeasurable (fun x ↦ inner ℝ (horizontal (ν x)) (Ψ (horizontal x))) μ :=
    (continuous_horizontal.comp_aestronglyMeasurable hν.aestronglyMeasurable).inner
      (hΨ.comp continuous_horizontal).aestronglyMeasurable
  refine Integrable.mono' (hν.norm.mul_const C) hm (Eventually.of_forall fun x ↦ ?_)
  calc ‖inner ℝ (horizontal (ν x)) (Ψ (horizontal x))‖
      ≤ ‖horizontal (ν x)‖ * ‖Ψ (horizontal x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖ν x‖ * C := by
        gcongr
        · exact norm_horizontal_le_norm_of_space _
        · exact hC _

/-! ### Very weak harmonicity of the height up to the excess -/

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

theorem restrict_cylinder_eq (hS : SlabTrappedRepresentation b E U H H' μ ν) :
    μ.restrict (cylinderSet U H') = μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS.rep.measure_compl] with x hx
  simpa using hx

/-- **Vertical first variation.** For a minimizer, the vertical field `φ(πx) ψ(x_n) e_n`, with
`ψ ≡ 1` on the slab carrying `μ`, gives `∫ ν_n Dφ(πx)(πν) dμ = 0`. -/
theorem integral_last_mul_fderiv_horizontal_eq_zero (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hcyl : cylinderSet U H' ⊆ Ω)
    {φ : Space m → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ x, ν x (Fin.last m) * fderiv ℝ φ (horizontal x) (horizontal (ν x)) ∂μ = 0 := by
  have hH := hS.pos
  have hHH' := hS.lt
  obtain ⟨hψ, hψc, hψs, hψ1, hψd⟩ := slabCutoff_props hH hHH'
  set ψ : ℝ → ℝ := ⇑(slabCutoff hH hHH') with hψ_def
  set W := cylinderSet U H' with hW_def
  have hW : IsOpen W := isOpen_cylinderSet hS.isOpen H'
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  set f : Space (m + 1) → ℝ := fun z ↦ φ (horizontal z) * ψ (z (Fin.last m)) with hf_def
  have hf : ContDiff ℝ 1 f :=
    (hφ.comp horizontalContinuousLinearMap.contDiff).mul
      (hψ.comp (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff)
  obtain ⟨hfc, hfs⟩ := tsupport_horizontal_mul_last_subset (F := f)
    (fun x hx ↦ ⟨left_ne_zero_of_mul hx, right_ne_zero_of_mul hx⟩) hφc hψc
  set X : Space (m + 1) → Space (m + 1) := fun z ↦ f z • verticalDirection m with hX_def
  have hX : ContDiff ℝ 1 X := hf.smul contDiff_const
  have hXc : HasCompactSupport X :=
    hfc.mono (fun x hx ↦ fun h0 ↦ hx (by simp [X, h0]))
  have hXW : tsupport X ⊆ W :=
    (tsupport_smul_subset_left _ _).trans (hfs.trans fun x hx ↦ ⟨hφU hx.1, hψs hx.2⟩)
  have hminW : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ W ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E W ≤ variationalPerimeter b D W :=
    fun D hD ⟨K, hK, hKW, hED⟩ ↦ hmin.minimizes W D K hW hcyl hD hK hKW hED
  have hrestr := hS.restrict_cylinder_eq
  have hfv := perimeter_first_variation_eq_zero b hS.measurableSet hW hminW μ
    (by rw [hrestr]; exact hS.rep.integrable) (by rw [hrestr]; exact hS.rep.norm_eq_one)
    (by rw [hrestr]; exact hS.rep.dist) hX hXc hXW
  rw [hrestr] at hfv
  have hae : ∀ᵐ x ∂μ, fieldDivergence b X x - inner ℝ (ν x) (fderiv ℝ X x (ν x)) =
      -(ν x (Fin.last m) * fderiv ℝ φ (horizontal x) (horizontal (ν x))) := by
    filter_upwards [hS.ae_abs_last_le] with x hx
    have hxI : x (Fin.last m) ∈ Ioo (-((H + H') / 2)) ((H + H') / 2) := by
      have := abs_le.mp hx.2.2
      constructor <;> linarith
    have hdiv : fieldDivergence b X x = fderiv ℝ f x (verticalDirection m) :=
      fieldDivergence_smul_const b (hf.differentiable one_ne_zero) (verticalDirection m) x
    have hdX : fderiv ℝ X x (ν x) = fderiv ℝ f x (ν x) • verticalDirection m := by
      rw [fderiv_smul_const ((hf.differentiable one_ne_zero) x)]
      rfl
    rw [hdiv, hdX, real_inner_smul_right, inner_verticalDirection_right,
      fderiv_horizontal_mul_last_apply hφd hψdiff, fderiv_horizontal_mul_last_apply hφd hψdiff,
      hψ1 _ hxI, hψd _ hxI]
    simp only [horizontal_verticalDirection, map_zero, last_verticalDirection, mul_zero,
      zero_mul, mul_one, one_mul, add_zero, zero_add]
    ring
  rw [integral_congr_ae hae, integral_neg, neg_eq_zero] at hfv
  exact hfv

/-- **Horizontal moment formula against a Laplacian**: `∫ g Δφ = ∫ Dφ(πx)(πν) dμ`. -/
theorem integral_columnSignedHeight_mul_laplacian_eq
    (hS : SlabTrappedRepresentation b E U H H' μ ν) {φ : Space m → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∫ y, columnSignedHeight E H y * Δ φ y =
      ∫ x, fderiv ℝ φ (horizontal x) (horizontal (ν x)) ∂μ := by
  have := hS.isFiniteMeasure
  set bm := EuclideanSpace.basisFun (Fin m) ℝ with hbm
  have hd1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hGi : ∀ i, ContDiff ℝ 1 (fun y ↦ fderiv ℝ φ y (bm i)) :=
    fun i ↦ hd1.clm_apply contDiff_const
  set G : Fin m → Space m → Space m := fun i y ↦ fderiv ℝ φ y (bm i) • bm i with hG_def
  have hG : ∀ i, ContDiff ℝ 1 (G i) := fun i ↦ (hGi i).smul contDiff_const
  have hGc : ∀ i, HasCompactSupport (G i) := fun i ↦
    (hφc.fderiv_apply ℝ (bm i)).mono (fun y hy ↦ fun h0 ↦ hy (by simp [G, h0]))
  have hGs : ∀ i, tsupport (G i) ⊆ U := fun i ↦
    ((tsupport_smul_subset_left _ _).trans (tsupport_fderiv_apply_subset ℝ (bm i))).trans hφU
  have hmom : ∀ i, (∫ y, columnSignedHeight E H y * fieldDivergence bm (G i) y) =
      ∫ x, inner ℝ (horizontal (ν x)) (G i (horizontal x)) ∂μ := fun i ↦
    integral_columnSignedHeight_fieldDivergence_eq b bm hS.measurableSet hS.isOpen hS.pos hS.lt
      μ hS.rep.measure_compl hS.rep.measure_open hS.rep.integrable hS.rep.dist hS.bot hS.top
      (hG i) (hGc i) (hGs i)
  have hdiv : ∀ i y, fieldDivergence bm (G i) y =
      fderiv ℝ (fun z ↦ fderiv ℝ φ z (bm i)) y (bm i) := fun i y ↦
    fieldDivergence_smul_const bm ((hGi i).differentiable one_ne_zero) (bm i) y
  have hlap : ∀ y, Δ φ y = ∑ i, fieldDivergence bm (G i) y := by
    intro y
    rw [laplacian_eq_sum_fderiv bm ((hd1.differentiable one_ne_zero) y)]
    simp only [hdiv]
  have hgm : AEStronglyMeasurable (columnSignedHeight E H) volume :=
    (measurable_columnSignedHeight hS.measurableSet H).aestronglyMeasurable
  have hint1 : ∀ i, Integrable (fun y ↦ columnSignedHeight E H y * fieldDivergence bm (G i) y) := by
    intro i
    have hcont : Continuous (fieldDivergence bm (G i)) := fieldDivergence_continuous bm (hG i)
    have hsupp : HasCompactSupport (fieldDivergence bm (G i)) := by
      refine (hGc i).mono' ?_
      intro y hy
      by_contra hn
      exact hy (fieldDivergence_zero_of_notMem_tsupport bm (G i) hn)
    exact (hcont.integrable_of_hasCompactSupport hsupp).bdd_mul (c := H) hgm
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs]; exact abs_columnSignedHeight_le E hS.pos.le y)
  have hint2 : ∀ i, Integrable
      (fun x ↦ inner ℝ (horizontal (ν x)) (G i (horizontal x))) μ := fun i ↦
    integrable_inner_horizontal_comp hS.rep.integrable (hG i).continuous (hGc i)
  have hexp : ∀ (L : Space m →L[ℝ] ℝ) (w : Space m),
      ∑ i, inner ℝ w (L (bm i) • bm i) = L w := by
    intro L w
    conv_rhs => rw [← bm.sum_repr' w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul, real_inner_smul_right, real_inner_comm (bm i) w, mul_comm]
  calc ∫ y, columnSignedHeight E H y * Δ φ y
      = ∫ y, ∑ i, columnSignedHeight E H y * fieldDivergence bm (G i) y := by
        congr 1; ext y; rw [hlap, Finset.mul_sum]
    _ = ∑ i, ∫ y, columnSignedHeight E H y * fieldDivergence bm (G i) y :=
        integral_finsetSum _ (fun i _ ↦ hint1 i)
    _ = ∑ i, ∫ x, inner ℝ (horizontal (ν x)) (G i (horizontal x)) ∂μ := by
        congr 1; ext i; exact hmom i
    _ = ∫ x, ∑ i, inner ℝ (horizontal (ν x)) (G i (horizontal x)) ∂μ :=
        (integral_finsetSum _ (fun i _ ↦ hint2 i)).symm
    _ = ∫ x, fderiv ℝ φ (horizontal x) (horizontal (ν x)) ∂μ := by
        congr 1; ext x; exact hexp _ _

end SlabTrappedRepresentation

namespace IsLocalPerimeterMinimizer

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **Very weak harmonicity of the height up to the excess** (`GR11`): for a test function
supported in `B ⊆ U` with `‖Dφ‖ ≤ K`, `|∫ g Δφ| ≤ K ε(B)`. -/
theorem abs_integral_columnSignedHeight_mul_laplacian_le (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hcyl : cylinderSet U H' ⊆ Ω)
    {B : Set (Space m)} (hB : MeasurableSet B) (hBU : B ⊆ U)
    {φ : Space m → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφB : tsupport φ ⊆ B)
    {K : ℝ} (hK : ∀ y, ‖fderiv ℝ φ y‖ ≤ K) :
    |∫ y, columnSignedHeight E H y * Δ φ y| ≤ K * (projectedExcessMeasure μ ν).real B := by
  have := hS.isFiniteMeasure
  have hφU := hφB.trans hBU
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  rw [hS.integral_columnSignedHeight_mul_laplacian_eq hφ hφc hφU]
  have hzero := hS.integral_last_mul_fderiv_horizontal_eq_zero hmin hcyl hφ1 hφc hφU
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hΨ : Continuous (fun y ↦ (fderiv ℝ φ y)) := hφ1.continuous_fderiv one_ne_zero
  have hint1 : Integrable (fun x ↦ fderiv ℝ φ (horizontal x) (horizontal (ν x))) μ := by
    refine Integrable.mono' (hS.rep.integrable.norm.mul_const K) ?_
      (Eventually.of_forall fun x ↦ ?_)
    · have hcF : Continuous (fun p : Space m × Space (m + 1) ↦
          fderiv ℝ φ p.1 (horizontal p.2)) :=
        (hΨ.comp continuous_fst).clm_apply (continuous_horizontal.comp continuous_snd)
      exact hcF.comp_aestronglyMeasurable
        (continuous_horizontal.aestronglyMeasurable.prodMk hS.rep.integrable.aestronglyMeasurable)
    · calc ‖fderiv ℝ φ (horizontal x) (horizontal (ν x))‖
          ≤ ‖fderiv ℝ φ (horizontal x)‖ * ‖horizontal (ν x)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖ν x‖ := by
            gcongr
            · exact hK _
            · exact norm_horizontal_le_norm_of_space _
        _ = ‖ν x‖ * K := mul_comm _ _
  have hint2 : Integrable
      (fun x ↦ ν x (Fin.last m) * fderiv ℝ φ (horizontal x) (horizontal (ν x))) μ := by
    refine hint1.bdd_mul (c := ‖(1 : ℝ)‖ + 0) ?_ ?_
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.comp_aestronglyMeasurable
        hS.rep.integrable.aestronglyMeasurable
    · filter_upwards [ae_one_sub_last_nonneg hS.rep.norm_eq_one] with x hx
      rw [Real.norm_eq_abs]
      simpa using hx.2.1
  have heq : ∫ x, fderiv ℝ φ (horizontal x) (horizontal (ν x)) ∂μ =
      ∫ x, (1 - ν x (Fin.last m)) * fderiv ℝ φ (horizontal x) (horizontal (ν x)) ∂μ := by
    simp_rw [sub_mul, one_mul]
    rw [integral_sub hint1 hint2, hzero, sub_zero]
  rw [heq, projectedExcessMeasure_real_eq_setIntegral hS.rep.integrable hS.rep.norm_eq_one hB]
  have hπB : MeasurableSet (horizontal ⁻¹' B : Set (Space (m + 1))) :=
    hB.preimage continuous_horizontal.measurable
  have hone_int : Integrable (fun x ↦ 1 - ν x (Fin.last m)) μ := by
    have h : Integrable (fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)) μ :=
      (integrable_const 1).sub (hS.rep.integrable.inner_const _)
    simpa only [inner_verticalDirection_right] using h
  rw [← integral_indicator hπB, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x ↦ abs_nonneg _)
    ((hone_int.indicator hπB).const_mul K) ?_)
  filter_upwards [ae_one_sub_last_nonneg hS.rep.norm_eq_one] with x hx
  by_cases hxB : horizontal x ∈ B
  · rw [indicator_of_mem (show x ∈ horizontal ⁻¹' B from hxB), abs_mul, abs_of_nonneg hx.1]
    calc (1 - ν x (Fin.last m)) * |fderiv ℝ φ (horizontal x) (horizontal (ν x))|
        ≤ (1 - ν x (Fin.last m)) * (‖fderiv ℝ φ (horizontal x)‖ * ‖horizontal (ν x)‖) :=
          mul_le_mul_of_nonneg_left (by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _) hx.1
      _ ≤ (1 - ν x (Fin.last m)) * (K * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hK _) hx.2.2 (norm_nonneg _) hK0) hx.1
      _ = K * (1 - ν x (Fin.last m)) := by ring
  · have hnot : horizontal x ∉ tsupport φ := fun h ↦ hxB (hφB h)
    rw [indicator_of_notMem (show x ∉ horizontal ⁻¹' B from hxB), fderiv_of_notMem_tsupport ℝ hnot]
    simp

end IsLocalPerimeterMinimizer

/-! ### The vertical Gauss–Green formula in columns -/

theorem hasDerivAt_comp_point {m : ℕ} {f : Space (m + 1) → ℝ} (hf : Differentiable ℝ f)
    (y : Space m) (t : ℝ) :
    HasDerivAt (fun s ↦ f (point y s)) (fderiv ℝ f (point y t) (verticalDirection m)) t := by
  have hd : HasDerivAt (point y) (verticalDirection m) t := by
    simpa only [point_add_vertical, zero_add, id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const (verticalDirection m)).const_add (point y 0)
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hd

/-- **Vertical Gauss–Green formula in columns.** For a `C¹` function `f` compactly supported in
the representation domain, `∫ f ν_n dμ = -∫_y ∫_t 1_E(y, t) ∂_t f(y, t) dt dy`. -/
theorem IsPerimeterRepresentation.integral_mul_last_eq {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E W : Set (Space (m + 1))}
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (h : IsPerimeterRepresentation b E W μ ν) (hE : MeasurableSet E)
    {f : Space (m + 1) → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfW : tsupport f ⊆ W) :
    ∫ x, f x * ν x (Fin.last m) ∂μ =
      -∫ y : Space m, ∫ t : ℝ, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
        deriv (fun s ↦ f (point y s)) t := by
  set X : Space (m + 1) → Space (m + 1) := fun x ↦ f x • verticalDirection m with hX_def
  have hX : ContDiff ℝ 1 X := hf.smul contDiff_const
  have hXc : HasCompactSupport X := hfc.mono (fun x hx ↦ fun h0 ↦ hx (by simp [X, h0]))
  have hXs : tsupport X ⊆ W := (tsupport_smul_subset_left _ _).trans hfW
  let Fc : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨X, hX.continuous⟩, hXc⟩
  have hid := h.dist Fc hX hXs
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdiv : ∀ x, fieldDivergence b X x = fderiv ℝ f x (verticalDirection m) :=
    fun x ↦ fieldDivergence_smul_const b hfd (verticalDirection m) x
  have hrhs : ∫ x, inner ℝ (Fc x) (ν x) ∂μ = ∫ x, f x * ν x (Fin.last m) ∂μ := by
    congr 1
    ext x
    change inner ℝ (f x • verticalDirection m) (ν x) = _
    rw [real_inner_smul_left, real_inner_comm, inner_verticalDirection_right]
  have hint : Integrable (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Fc x) := by
    have hcont := fieldDivergence_continuous b hX
    have hdiv_c : HasCompactSupport (fieldDivergence b X) := by
      refine hXc.mono' ?_
      intro x hx
      by_contra hn
      exact hx (fieldDivergence_zero_of_notMem_tsupport b X hn)
    have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hdiv_c).indicator hE
    refine hi.congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ E <;> simp [hx, Fc]
  rw [← hrhs, ← hid, integral_space_eq_integral_horizontal_vertical hint]
  congr 1
  congr 1
  ext y
  congr 1
  ext t
  change E.indicator (fun _ ↦ (1 : ℝ)) (point y t) * fieldDivergence b X (point y t) = _
  rw [hdiv, (hasDerivAt_comp_point hfd y t).deriv]

/-! ### The one-dimensional column identity -/

/-- The column defect: `2|t - L|` if `t` lies on the wrong side of the level `L` relative to `S`,
and `0` otherwise. -/
def columnDefect (S : Set ℝ) (L t : ℝ) : ℝ :=
  {s | ¬(s ∈ S ↔ L < s)}.indicator (fun s ↦ 2 * |s - L|) t

theorem columnDefect_nonneg (S : Set ℝ) (L t : ℝ) : 0 ≤ columnDefect S L t :=
  indicator_nonneg (fun _ _ ↦ by positivity) _

theorem columnDefect_of_iff {S : Set ℝ} {L t : ℝ} (h : t ∈ S ↔ L < t) :
    columnDefect S L t = 0 :=
  indicator_of_notMem (fun h' ↦ absurd h h') _

theorem columnDefect_of_not_iff {S : Set ℝ} {L t : ℝ} (h : ¬(t ∈ S ↔ L < t)) :
    columnDefect S L t = 2 * |t - L| :=
  indicator_of_mem h _

theorem columnDefect_eq (S : Set ℝ) (L t : ℝ) :
    columnDefect S L t =
      (Ioi L).indicator (fun s ↦ 2 * (s - L)) t - S.indicator (fun s ↦ 2 * (s - L)) t := by
  by_cases hS : t ∈ S <;> by_cases hL : L < t
  · rw [columnDefect_of_iff (iff_of_true hS hL), indicator_of_mem (show t ∈ Ioi L from hL),
      indicator_of_mem hS, sub_self]
  · rw [columnDefect_of_not_iff (fun h ↦ hL (h.mp hS)),
      indicator_of_notMem (show t ∉ Ioi L from hL), indicator_of_mem hS,
      abs_of_nonpos (by linarith [not_lt.mp hL])]
    ring
  · rw [columnDefect_of_not_iff (fun h ↦ hS (h.mpr hL)),
      indicator_of_mem (show t ∈ Ioi L from hL), indicator_of_notMem hS,
      abs_of_pos (by linarith)]
    ring
  · rw [columnDefect_of_iff (iff_of_false hS hL), indicator_of_notMem (show t ∉ Ioi L from hL),
      indicator_of_notMem hS, sub_self]

theorem hasDerivAt_sub_sq (L x : ℝ) : HasDerivAt (fun s ↦ (s - L) ^ 2) (2 * (x - L)) x := by
  have h := ((hasDerivAt_id x).sub_const L).mul ((hasDerivAt_id x).sub_const L)
  convert h using 1
  · funext s
    simp only [id, sq, Pi.mul_apply]
  · simp only [id]
    ring

/-- **The column identity.** Let `ψ ≡ 1` near `[-H, H]` with compact support in `(-H', H')`, and
let the column `S` be empty below `-H` and full above `H` inside `(-H', H')`. For a level
`|L| ≤ H`, `-∫ 1_S (ψ (t - L)²)' dt = ∫_{-H}^{H} 2|t - L| 1[S Δ {t > L}] dt`. -/
theorem neg_integral_indicator_mul_deriv_eq {S : Set ℝ} (hS : MeasurableSet S) {H H₁ H' L : ℝ}
    (hHH₁ : H < H₁) (hL : |L| ≤ H) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo (-H') H') (hψ1 : ∀ t ∈ Ioo (-H₁) H₁, ψ t = 1)
    (hbot : ∀ᵐ t ∂volume, t ∈ Ioo (-H') (-H) → t ∉ S)
    (htop : ∀ᵐ t ∂volume, t ∈ Ioo H H' → t ∈ S) :
    -∫ t, S.indicator (fun _ ↦ (1 : ℝ)) t * deriv (fun s ↦ ψ s * (s - L) ^ 2) t =
      ∫ t in Icc (-H) H, columnDefect S L t := by
  set h : ℝ → ℝ := fun s ↦ ψ s * (s - L) ^ 2 with hh_def
  have hhc : HasCompactSupport h := hψc.mul_right
  have hh : ContDiff ℝ 1 h := hψ.mul ((contDiff_id.sub contDiff_const).pow 2)
  have hHL := abs_le.mp hL
  have hH0 : 0 ≤ H := le_trans (abs_nonneg L) hL
  have hd_in : ∀ t ∈ Ioo (-H₁) H₁, deriv h t = 2 * (t - L) := by
    intro t ht
    have hev : h =ᶠ[𝓝 t] fun s ↦ (s - L) ^ 2 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      simp only [hh_def, hψ1 s hs, one_mul]
    rw [hev.deriv_eq, (hasDerivAt_sub_sq L t).deriv]
  have hd_out : ∀ t, t ∉ Ioo (-H') H' → deriv h t = 0 := by
    intro t ht
    have hnot : t ∉ tsupport h := fun hs ↦ ht (hψs (tsupport_mul_subset_left hs))
    have hev : h =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hnot] with s hs
      exact image_eq_zero_of_notMem_tsupport hs
    simpa using hev.deriv_eq
  have hg : Continuous (fun s : ℝ ↦ 2 * (s - L)) := by fun_prop
  have hae : (fun t ↦ S.indicator (fun _ ↦ (1 : ℝ)) t * deriv h t) =ᵐ[volume]
      fun t ↦ (Icc (-H) H).indicator (fun s ↦ S.indicator (fun s ↦ 2 * (s - L)) s) t +
        (Ioi H).indicator (deriv h) t := by
    filter_upwards [hbot, htop] with t htb htt
    by_cases ht1 : t ∈ Icc (-H) H
    · have htI : t ∈ Ioo (-H₁) H₁ := ⟨by linarith [ht1.1], by linarith [ht1.2]⟩
      rw [indicator_of_mem ht1,
        indicator_of_notMem (show t ∉ Ioi H from fun h' ↦ not_lt.mpr ht1.2 h'), add_zero,
        hd_in t htI]
      by_cases htS : t ∈ S
      · rw [indicator_of_mem htS, indicator_of_mem htS, one_mul]
      · rw [indicator_of_notMem htS, indicator_of_notMem htS, zero_mul]
    · rw [indicator_of_notMem ht1, zero_add]
      by_cases htH : H < t
      · rw [indicator_of_mem (show t ∈ Ioi H from htH)]
        by_cases htH' : t < H'
        · rw [indicator_of_mem (htt ⟨htH, htH'⟩), one_mul]
        · rw [hd_out t (fun h' ↦ htH' h'.2), mul_zero]
      · rw [indicator_of_notMem (show t ∉ Ioi H from htH)]
        have htlt : t < -H := by
          by_contra hc
          push Not at hc
          exact ht1 ⟨hc, not_lt.mp htH⟩
        by_cases htH' : -H' < t
        · rw [indicator_of_notMem (htb ⟨htH', htlt⟩), zero_mul]
        · rw [hd_out t (fun h' ↦ htH' h'.1), mul_zero]
  have hintS : IntegrableOn (S.indicator (fun s ↦ 2 * (s - L))) (Icc (-H) H) :=
    (hg.integrableOn_Icc).indicator hS
  have hintL : IntegrableOn ((Ioi L).indicator (fun s ↦ 2 * (s - L))) (Icc (-H) H) :=
    (hg.integrableOn_Icc).indicator measurableSet_Ioi
  have hint1 : Integrable
      (fun t ↦ (Icc (-H) H).indicator (fun s ↦ S.indicator (fun s ↦ 2 * (s - L)) s) t) :=
    hintS.integrable_indicator measurableSet_Icc
  have hint2 : Integrable (fun t ↦ (Ioi H).indicator (deriv h) t) :=
    ((hh.continuous_deriv le_rfl).integrable_of_hasCompactSupport hhc.deriv).integrableOn
      |>.integrable_indicator measurableSet_Ioi
  have hhH : h H = (H - L) ^ 2 := by
    simp only [hh_def, hψ1 H ⟨by linarith, hHH₁⟩, one_mul]
  have hsq : ∫ t in Icc (-H) H, (Ioi L).indicator (fun s ↦ 2 * (s - L)) t = (H - L) ^ 2 := by
    rw [setIntegral_indicator measurableSet_Ioi]
    have hset : Icc (-H) H ∩ Ioi L = Ioc L H := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [hset, ← intervalIntegral.integral_of_le hHL.2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_sub_sq L x)
        (hg.intervalIntegrable _ _)]
    ring
  have hcd : ∫ t in Icc (-H) H, columnDefect S L t =
      (H - L) ^ 2 - ∫ t in Icc (-H) H, S.indicator (fun s ↦ 2 * (s - L)) t := by
    simp_rw [columnDefect_eq]
    rw [integral_sub hintL hintS, hsq]
  rw [integral_congr_ae hae, integral_add hint1 hint2, integral_indicator measurableSet_Icc,
    integral_indicator measurableSet_Ioi, hhc.integral_Ioi_deriv_eq hh H, hhH, hcd]
  ring

/-! ### Bounds for the column defect -/

theorem setIntegral_columnDefect_le_of_band {S : Set ℝ} {H L δ : ℝ} (hδ : 0 ≤ δ)
    (hband : ∀ᵐ t ∂volume, t ∈ Icc (-H) H → δ < |t - L| → (t ∈ S ↔ L < t)) :
    ∫ t in Icc (-H) H, columnDefect S L t ≤ 4 * δ ^ 2 := by
  set J := Icc (L - δ) (L + δ) with hJ
  have hJfin : volume J ≠ ⊤ := measure_Icc_lt_top.ne
  have hintJ : Integrable (J.indicator (fun _ ↦ 2 * δ)) :=
    (integrableOn_const hJfin).integrable_indicator measurableSet_Icc
  have hle : ∀ᵐ t ∂(volume.restrict (Icc (-H) H)),
      columnDefect S L t ≤ J.indicator (fun _ ↦ 2 * δ) t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hband] with t ht htI
    by_cases hδt : δ < |t - L|
    · rw [columnDefect_of_iff (ht htI hδt)]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _
    · push Not at hδt
      have hmem : t ∈ J := ⟨by linarith [(abs_le.mp hδt).1], by linarith [(abs_le.mp hδt).2]⟩
      rw [indicator_of_mem hmem]
      by_cases hc : (t ∈ S ↔ L < t)
      · rw [columnDefect_of_iff hc]
        positivity
      · rw [columnDefect_of_not_iff hc]
        linarith
  calc ∫ t in Icc (-H) H, columnDefect S L t
      ≤ ∫ t in Icc (-H) H, J.indicator (fun _ ↦ 2 * δ) t :=
        integral_mono_of_nonneg (Eventually.of_forall (columnDefect_nonneg S L))
          hintJ.integrableOn hle
    _ ≤ ∫ t, J.indicator (fun _ ↦ 2 * δ) t :=
        setIntegral_le_integral hintJ
          (Eventually.of_forall fun _ ↦ indicator_nonneg (fun _ _ ↦ by positivity) _)
    _ = 4 * δ ^ 2 := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, measureReal_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring

theorem setIntegral_columnDefect_le_of_graph {S : Set ℝ} {H H' L f : ℝ} (hHH' : H < H')
    (hf : |f| ≤ H) (hS : ∀ᵐ t ∂volume, t ∈ Ioo (-H') H' → (t ∈ S ↔ f < t)) :
    ∫ t in Icc (-H) H, columnDefect S L t ≤ 2 * (f - L) ^ 2 := by
  set J := Ioc (min f L) (max f L) with hJ
  have hJfin : volume J ≠ ⊤ := measure_Ioc_lt_top.ne
  have hintJ : Integrable (J.indicator (fun _ ↦ 2 * |f - L|)) :=
    (integrableOn_const hJfin).integrable_indicator measurableSet_Ioc
  have hH0 : 0 ≤ H := le_trans (abs_nonneg f) hf
  have hle : ∀ᵐ t ∂(volume.restrict (Icc (-H) H)),
      columnDefect S L t ≤ J.indicator (fun _ ↦ 2 * |f - L|) t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hS] with t ht htI
    have htS := ht ⟨by linarith [htI.1], by linarith [htI.2]⟩
    by_cases hc : (t ∈ S ↔ L < t)
    · rw [columnDefect_of_iff hc]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _
    · rw [columnDefect_of_not_iff hc]
      rw [htS] at hc
      have hbetween : t ∈ J := by
        by_cases hft : f < t
        · have hLt : ¬ L < t := fun h' ↦ hc (iff_of_true hft h')
          push Not at hLt
          exact ⟨lt_of_le_of_lt (min_le_left _ _) hft, le_trans hLt (le_max_right _ _)⟩
        · have hLt : L < t := by
            by_contra h'
            exact hc (iff_of_false hft h')
          push Not at hft
          exact ⟨lt_of_le_of_lt (min_le_right _ _) hLt, le_trans hft (le_max_left _ _)⟩
      rw [indicator_of_mem hbetween]
      have habs : |t - L| ≤ |f - L| := by
        rcases le_total f L with hfL | hfL
        · have h1 : min f L = f := min_eq_left hfL
          have h2 : max f L = L := max_eq_right hfL
          have hb := hbetween
          rw [hJ, h1, h2] at hb
          rw [abs_of_nonpos (by linarith [hb.2]), abs_of_nonpos (by linarith)]
          linarith [hb.1]
        · have h1 : min f L = L := min_eq_right hfL
          have h2 : max f L = f := max_eq_left hfL
          have hb := hbetween
          rw [hJ, h1, h2] at hb
          rw [abs_of_pos (by linarith [hb.1]), abs_of_nonneg (by linarith)]
          linarith [hb.2]
      linarith
  have hlen : max f L - min f L = |f - L| := by
    rcases le_total f L with hfL | hfL
    · rw [max_eq_right hfL, min_eq_left hfL, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left hfL, min_eq_right hfL, abs_of_nonneg (by linarith)]
  calc ∫ t in Icc (-H) H, columnDefect S L t
      ≤ ∫ t in Icc (-H) H, J.indicator (fun _ ↦ 2 * |f - L|) t :=
        integral_mono_of_nonneg (Eventually.of_forall (columnDefect_nonneg S L))
          hintJ.integrableOn hle
    _ ≤ ∫ t, J.indicator (fun _ ↦ 2 * |f - L|) t :=
        setIntegral_le_integral hintJ
          (Eventually.of_forall fun _ ↦ indicator_nonneg (fun _ _ ↦ by positivity) _)
    _ = 2 * (f - L) ^ 2 := by
        rw [integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, measureReal_def,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [min_le_max (a := f) (b := L)]),
          hlen, ← sq_abs (f - L)]
        ring

/-! ### The height square on the perimeter measure (`GR11.1`) -/

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- The cut-off height square `η(πx) ψ(x_n) (x_n - L(πx))²`. -/
theorem contDiff_cutoff_height_sq {η L : Space m → ℝ} {ψ : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hψ : ContDiff ℝ 1 ψ) (hL : ContDiff ℝ 1 L) :
    ContDiff ℝ 1 (fun x : Space (m + 1) ↦ η (horizontal x) *
      (ψ (x (Fin.last m)) * (x (Fin.last m) - L (horizontal x)) ^ 2)) := by
  have hπ : ContDiff ℝ 1 (horizontal : Space (m + 1) → Space m) :=
    horizontalContinuousLinearMap.contDiff
  have hlast : ContDiff ℝ 1 (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff
  exact (hη.comp hπ).mul ((hψ.comp hlast).mul ((hlast.sub (hL.comp hπ)).pow 2))

/-- **The height square in columns.** For a level `L` with `|L| ≤ H` on `tsupport η`,
`∫ η (x_n - L)² ν_n dμ = ∫ η(y) ∫_{-H}^{H} columnDefect E_y (L y) dt dy`. -/
theorem integral_height_sq_mul_last_eq (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {η : Space m → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) {L : Space m → ℝ} (hL : ContDiff ℝ 1 L)
    (hLH : ∀ y ∈ tsupport η, |L y| ≤ H) :
    ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 * ν x (Fin.last m) ∂μ =
      ∫ y, η y * ∫ t in Icc (-H) H, columnDefect {s | point y s ∈ E} (L y) t := by
  have hH := hS.pos
  have hHH' := hS.lt
  obtain ⟨hψ, hψc, hψs, hψ1, -⟩ := slabCutoff_props hH hHH'
  set ψ : ℝ → ℝ := ⇑(slabCutoff hH hHH') with hψ_def
  set f : Space (m + 1) → ℝ := fun x ↦ η (horizontal x) *
    (ψ (x (Fin.last m)) * (x (Fin.last m) - L (horizontal x)) ^ 2) with hf_def
  have hf : ContDiff ℝ 1 f := contDiff_cutoff_height_sq hη hψ hL
  obtain ⟨hfc, hfs⟩ := tsupport_horizontal_mul_last_subset (φ := η) (ψ := ψ) (F := f)
    (fun x hx ↦ ⟨left_ne_zero_of_mul hx, left_ne_zero_of_mul (right_ne_zero_of_mul hx)⟩)
    hηc hψc
  have hfW : tsupport f ⊆ cylinderSet U H' := hfs.trans fun x hx ↦ ⟨hηU hx.1, hψs hx.2⟩
  have hGG := hS.rep.integral_mul_last_eq hS.measurableSet hf hfc hfW
  have hlhs : ∫ x, f x * ν x (Fin.last m) ∂μ =
      ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 * ν x (Fin.last m) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hS.ae_abs_last_le] with x hx
    have hxI : x (Fin.last m) ∈ Ioo (-((H + H') / 2)) ((H + H') / 2) := by
      have := abs_le.mp hx.2.2
      constructor <;> linarith
    simp only [f, hψ1 _ hxI, one_mul]
  rw [← hlhs, hGG]
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hcol : ∀ y t, deriv (fun s ↦ f (point y s)) t =
      η y * deriv (fun s ↦ ψ s * (s - L y) ^ 2) t := by
    intro y t
    have hfun : (fun s ↦ f (point y s)) = fun s ↦ η y * (ψ s * (s - L y) ^ 2) := by
      funext s
      simp only [f, horizontal_point, last_point]
    rw [hfun]
    exact deriv_const_mul _ ((hψd t).mul ((differentiableAt_id.sub_const (L y)).pow 2))
  have hbot_slice := ae_vertical_of_ae_volume hS.bot
  have htop_slice := ae_vertical_of_ae_volume hS.top
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hbot_slice, htop_slice] with y hyb hyt
  simp_rw [hcol]
  by_cases hy : η y = 0
  · simp [hy]
  have hyU : y ∈ U := hηU (subset_tsupport η hy)
  have hLy := hLH y (subset_tsupport η hy)
  have hind : ∀ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) =
      {s | point y s ∈ E}.indicator (fun _ ↦ (1 : ℝ)) t := fun t ↦ rfl
  have hfac : (fun t ↦ E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
      (η y * deriv (fun s ↦ ψ s * (s - L y) ^ 2) t)) =
      fun t ↦ η y * ({s | point y s ∈ E}.indicator (fun _ ↦ (1 : ℝ)) t *
        deriv (fun s ↦ ψ s * (s - L y) ^ 2) t) := by
    funext t
    rw [hind t]
    ring
  rw [hfac, integral_const_mul, ← mul_neg]
  congr 1
  refine neg_integral_indicator_mul_deriv_eq
    (hS.measurableSet.preimage (continuous_point y).measurable) (H₁ := (H + H') / 2)
    (by linarith) hLy hψ hψc hψs hψ1 ?_ ?_
  · filter_upwards [hyb] with t ht hmem
    exact ht (by simpa [horizontal_point] using hyU) (by simpa [last_point] using hmem)
  · filter_upwards [hyt] with t ht hmem
    exact ht (by simpa [horizontal_point] using hyU) (by simpa [last_point] using hmem)

/-- The height square `η(πx) (x_n - L(πx))²` is `μ`-integrable. -/
theorem integrable_height_sq (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {η : Space m → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    {L : Space m → ℝ} (hL : ContDiff ℝ 1 L) :
    Integrable (fun x ↦ η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2) μ := by
  have := hS.isFiniteMeasure
  have hH := hS.pos
  have hHH' := hS.lt
  obtain ⟨hψ, hψc, -, hψ1, -⟩ := slabCutoff_props hH hHH'
  set ψ : ℝ → ℝ := ⇑(slabCutoff hH hHH') with hψ_def
  set f : Space (m + 1) → ℝ := fun x ↦ η (horizontal x) *
    (ψ (x (Fin.last m)) * (x (Fin.last m) - L (horizontal x)) ^ 2) with hf_def
  have hf : ContDiff ℝ 1 f := contDiff_cutoff_height_sq hη hψ hL
  obtain ⟨hfc, -⟩ := tsupport_horizontal_mul_last_subset (φ := η) (ψ := ψ) (F := f)
    (fun x hx ↦ ⟨left_ne_zero_of_mul hx, left_ne_zero_of_mul (right_ne_zero_of_mul hx)⟩)
    hηc hψc
  refine (hf.continuous.integrable_of_hasCompactSupport hfc).congr ?_
  filter_upwards [hS.ae_abs_last_le] with x hx
  have hxI : x (Fin.last m) ∈ Ioo (-((H + H') / 2)) ((H + H') / 2) := by
    have := abs_le.mp hx.2.2
    constructor <;> linarith
  simp only [f, hψ1 _ hxI, one_mul]

/-- **`GR11.1`, upper bound.** Suppose that over `B` the boundary lies in the band
`|t - L(y)| ≤ δ` (`μ`-a.e.), that outside the band the phase is the correct half-space, and that
over the good set `G` the phase is the supergraph of `f`. Then
`∫ η (x_n - L)² dμ ≤ 2 ∫_G η (f - L)² + 4 δ² |B \ G| + δ² ε(B)` for `0 ≤ η ≤ 1` supported in
`B`. -/
theorem integral_height_sq_le (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {B : Set (Space m)} (hBm : MeasurableSet B) (hBfin : volume B ≠ ⊤) (hBU : B ⊆ U)
    {η : Space m → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηB : tsupport η ⊆ B)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    {L : Space m → ℝ} (hL : ContDiff ℝ 1 L) (hLH : ∀ y ∈ B, |L y| ≤ H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbandμ : ∀ᵐ x ∂μ, horizontal x ∈ B → |x (Fin.last m) - L (horizontal x)| ≤ δ)
    (hbandE : ∀ᵐ x ∂volume, horizontal x ∈ B → |x (Fin.last m)| < H' →
      δ < |x (Fin.last m) - L (horizontal x)| → (x ∈ E ↔ L (horizontal x) < x (Fin.last m)))
    {G : Set (Space m)} (hGm : MeasurableSet G) {f : Space m → ℝ} (hfm : Measurable f)
    (hfH : ∀ y, |f y| ≤ H)
    (hfE : ∀ᵐ x ∂volume, x ∈ cylinderSet U H' → horizontal x ∈ G →
      (x ∈ E ↔ f (horizontal x) < x (Fin.last m))) :
    ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 ∂μ ≤
      2 * (∫ y in G, η y * (f y - L y) ^ 2) + 4 * δ ^ 2 * volume.real (B \ G) +
        δ ^ 2 * (projectedExcessMeasure μ ν).real B := by
  have := hS.isFiniteMeasure
  have hH := hS.pos
  have hHH' := hS.lt
  have hηU : tsupport η ⊆ U := hηB.trans hBU
  set q : Space (m + 1) → ℝ := fun x ↦ η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2
    with hq_def
  have hqint : Integrable q μ := hS.integrable_height_sq hη hηc hL
  have hνn : AEStronglyMeasurable (fun x ↦ ν x (Fin.last m)) μ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.comp_aestronglyMeasurable
      hS.rep.integrable.aestronglyMeasurable
  have hunit := ae_one_sub_last_nonneg hS.rep.norm_eq_one
  have hint_a : Integrable (fun x ↦ q x * ν x (Fin.last m)) μ := by
    have h := hqint.bdd_mul (c := 1) hνn (by
      filter_upwards [hunit] with x hx
      rw [Real.norm_eq_abs]
      exact hx.2.1)
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    ring
  have hone_int : Integrable (fun x ↦ 1 - ν x (Fin.last m)) μ := by
    have h : Integrable (fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)) μ :=
      (integrable_const 1).sub (hS.rep.integrable.inner_const _)
    simpa only [inner_verticalDirection_right] using h
  have hint_b : Integrable (fun x ↦ q x * (1 - ν x (Fin.last m))) μ := by
    have h := hqint.bdd_mul (c := 2) hone_int.aestronglyMeasurable (by
      filter_upwards [hunit] with x hx
      rw [Real.norm_eq_abs]
      have := abs_le.mp hx.2.1
      rw [abs_le]
      constructor <;> linarith)
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    ring
  have hsplit : ∫ x, q x ∂μ = ∫ x, q x * ν x (Fin.last m) ∂μ +
      ∫ x, q x * (1 - ν x (Fin.last m)) ∂μ := by
    rw [← integral_add hint_a hint_b]
    congr 1
    ext x
    ring
  -- the excess part
  have hπB : MeasurableSet (horizontal ⁻¹' B : Set (Space (m + 1))) :=
    hBm.preimage continuous_horizontal.measurable
  have hpart_b : ∫ x, q x * (1 - ν x (Fin.last m)) ∂μ ≤
      δ ^ 2 * (projectedExcessMeasure μ ν).real B := by
    rw [projectedExcessMeasure_real_eq_setIntegral hS.rep.integrable hS.rep.norm_eq_one hBm,
      ← integral_indicator hπB, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((hone_int.indicator hπB).const_mul _) ?_
    · filter_upwards [hunit] with x hx
      exact mul_nonneg (mul_nonneg (hη0 _) (sq_nonneg _)) hx.1
    · filter_upwards [hunit, hbandμ] with x hx hxb
      by_cases hxB : horizontal x ∈ B
      · rw [indicator_of_mem (show x ∈ horizontal ⁻¹' B from hxB)]
        have hsq : (x (Fin.last m) - L (horizontal x)) ^ 2 ≤ δ ^ 2 := by
          have := hxb hxB
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        calc q x * (1 - ν x (Fin.last m))
            = η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 *
                (1 - ν x (Fin.last m)) := rfl
          _ ≤ 1 * δ ^ 2 * (1 - ν x (Fin.last m)) := by
              gcongr
              · exact hx.1
              · exact hη1 _
          _ = δ ^ 2 * (1 - ν x (Fin.last m)) := by ring
      · have hη0' : η (horizontal x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h ↦ hxB (hηB h))
        rw [indicator_of_notMem (show x ∉ horizontal ⁻¹' B from hxB)]
        simp [q, hη0']
  -- the vertical part, via columns
  have hLH' : ∀ y ∈ tsupport η, |L y| ≤ H := fun y hy ↦ hLH y (hηB hy)
  have hcol := hS.integral_height_sq_mul_last_eq hη hηc hηU hL hLH'
  have hbandE_slice := ae_vertical_of_ae_volume hbandE
  have hfE_slice := ae_vertical_of_ae_volume hfE
  set Φ : Space m → ℝ := fun y ↦ ∫ t in Icc (-H) H, columnDefect {s | point y s ∈ E} (L y) t
    with hΦ_def
  have hΦ0 : ∀ y, 0 ≤ Φ y := fun y ↦
    setIntegral_nonneg measurableSet_Icc (fun t _ ↦ columnDefect_nonneg _ _ _)
  have hηfL : Integrable (fun y ↦ η y * (f y - L y) ^ 2) := by
    refine Integrable.mono' ((integrableOn_const hBfin).integrable_indicator hBm
      (f := fun _ ↦ 4 * H ^ 2)) ?_ (Eventually.of_forall fun y ↦ ?_)
    · exact (hη.continuous.measurable.mul
        ((hfm.sub hL.continuous.measurable).pow_const 2)).aestronglyMeasurable
    · by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (hη0 y) (sq_nonneg _))]
        have h1 := abs_le.mp (hfH y)
        have h2 := abs_le.mp (hLH y hyB)
        have hsq : (f y - L y) ^ 2 ≤ 4 * H ^ 2 := by nlinarith
        calc η y * (f y - L y) ^ 2 ≤ 1 * (4 * H ^ 2) := by
              gcongr
              · exact hη1 y
          _ = 4 * H ^ 2 := one_mul _
      · have hη0' : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hyB (hηB h))
        rw [indicator_of_notMem hyB, hη0']
        simp
  have hBGfin : volume (B \ G) ≠ ⊤ :=
    ((measure_mono sdiff_subset).trans_lt hBfin.lt_top).ne
  have hint_r1 : Integrable (G.indicator (fun y ↦ 2 * (η y * (f y - L y) ^ 2))) :=
    (hηfL.const_mul 2).indicator hGm
  have hint_r2 : Integrable ((B \ G).indicator (fun _ ↦ 4 * δ ^ 2)) :=
    (integrableOn_const hBGfin).integrable_indicator (hBm.diff hGm)
  have hpart_a : ∫ y, η y * Φ y ≤
      2 * (∫ y in G, η y * (f y - L y) ^ 2) + 4 * δ ^ 2 * volume.real (B \ G) := by
    have hle : ∀ᵐ y ∂volume, η y * Φ y ≤
        G.indicator (fun y ↦ 2 * (η y * (f y - L y) ^ 2)) y +
          (B \ G).indicator (fun _ ↦ 4 * δ ^ 2) y := by
      filter_upwards [hbandE_slice, hfE_slice] with y hyb hyf
      have hr1 : 0 ≤ G.indicator (fun y ↦ 2 * (η y * (f y - L y) ^ 2)) y :=
        indicator_nonneg (fun y _ ↦ by have := hη0 y; positivity) _
      have hr2 : 0 ≤ (B \ G).indicator (fun _ ↦ 4 * δ ^ 2) y :=
        indicator_nonneg (fun _ _ ↦ by positivity) _
      by_cases hyB : y ∈ B
      · by_cases hyG : y ∈ G
        · have hgraph : ∀ᵐ t ∂volume, t ∈ Ioo (-H') H' →
              (t ∈ {s | point y s ∈ E} ↔ f y < t) := by
            filter_upwards [hyf] with t ht htI
            have h := ht (point_mem_cylinderSet.mpr ⟨hBU hyB, htI⟩)
              (by simpa [horizontal_point] using hyG)
            simpa [horizontal_point, last_point] using h
          have hΦy := setIntegral_columnDefect_le_of_graph (L := L y) hHH' (hfH y) hgraph
          rw [indicator_of_mem hyG]
          calc η y * Φ y ≤ η y * (2 * (f y - L y) ^ 2) :=
                mul_le_mul_of_nonneg_left hΦy (hη0 y)
            _ = 2 * (η y * (f y - L y) ^ 2) := by ring
            _ ≤ 2 * (η y * (f y - L y) ^ 2) + (B \ G).indicator (fun _ ↦ 4 * δ ^ 2) y :=
                le_add_of_nonneg_right hr2
        · have hband1 : ∀ᵐ t ∂volume, t ∈ Icc (-H) H → δ < |t - L y| →
              (t ∈ {s | point y s ∈ E} ↔ L y < t) := by
            filter_upwards [hyb] with t ht htI hδt
            have htH : |t| < H' := by
              rw [abs_lt]
              constructor <;> linarith [htI.1, htI.2]
            have h := ht (by simpa [horizontal_point] using hyB)
              (by simpa [last_point] using htH) (by simpa [horizontal_point, last_point] using hδt)
            simpa [horizontal_point, last_point] using h
          have hΦy := setIntegral_columnDefect_le_of_band hδ hband1
          rw [indicator_of_notMem hyG, zero_add,
            indicator_of_mem (show y ∈ B \ G from ⟨hyB, hyG⟩)]
          calc η y * Φ y ≤ 1 * Φ y := mul_le_mul_of_nonneg_right (hη1 y) (hΦ0 y)
            _ ≤ 4 * δ ^ 2 := by rw [one_mul]; exact hΦy
      · have hη0' : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hyB (hηB h))
        rw [hη0', zero_mul]
        exact add_nonneg hr1 hr2
    calc ∫ y, η y * Φ y
        ≤ ∫ y, (G.indicator (fun y ↦ 2 * (η y * (f y - L y) ^ 2)) y +
            (B \ G).indicator (fun _ ↦ 4 * δ ^ 2) y) :=
          integral_mono_of_nonneg (Eventually.of_forall fun y ↦ mul_nonneg (hη0 y) (hΦ0 y))
            (hint_r1.add hint_r2) hle
      _ = 2 * (∫ y in G, η y * (f y - L y) ^ 2) + 4 * δ ^ 2 * volume.real (B \ G) := by
          rw [integral_add hint_r1 hint_r2, integral_indicator hGm, integral_indicator (hBm.diff hGm),
            setIntegral_const, smul_eq_mul, integral_const_mul]
          ring
  calc ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 ∂μ
      = ∫ x, q x ∂μ := rfl
    _ = ∫ x, q x * ν x (Fin.last m) ∂μ + ∫ x, q x * (1 - ν x (Fin.last m)) ∂μ := hsplit
    _ ≤ (2 * (∫ y in G, η y * (f y - L y) ^ 2) + 4 * δ ^ 2 * volume.real (B \ G)) +
          δ ^ 2 * (projectedExcessMeasure μ ν).real B := by
        gcongr
        exact (le_of_eq hcol).trans hpart_a

end SlabTrappedRepresentation

end SerrinEpigraph
