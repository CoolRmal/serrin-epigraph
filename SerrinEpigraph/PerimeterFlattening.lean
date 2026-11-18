module

public import SerrinEpigraph.PerimeterFlatteningAux

/-!
# Directed reverse Poincaré inequality for perimeter minimizers by flattening (`GR8`)

This module implements `GR8` of `docs/rigidity-proof/gmt-regularity.md` for an arbitrary
measurable local perimeter minimizer whose boundary inside the cylinder
`cylinderSet U H' = U × (-H', H')` is trapped in the slab `|t| ≤ H` (empty phase below, full phase
above). No graph structure of the boundary is assumed.

## The competitor

Fix a horizontal cutoff `0 ≤ η ≤ 1` (`C²`, compactly supported in `U`), a level `λ`, and
`H < H₁ < H₂ < H'`. Put `s = 1 - η²`. The competitor `flattenedPhase E U η λ H₁ H₂` is defined
column by column (`flattenedColumn`):
* in the *core* `{η = 1}` the band `[-H₁, H₁]` is collapsed to the level `λ`, so the new phase is
  exactly the half-space `{t > λ}` there (all reverse layers are removed);
* in the *annulus* `{η < 1}` the band is mapped by the invertible affine compression
  `t ↦ λ + s (t - λ)`;
* above the compressed band the column is filled, below it is emptied, and the set is unchanged
  outside `[-H₂, H₂]` and outside `U`.
It agrees with `E` almost everywhere off a compact subset of the cylinder
(`ae_mem_flattenedPhase_iff`), so local minimality applies.

## The perimeter of the competitor (no gluing perimeter)

Column by column the competitor is obtained from `E` by the vertical shear
`F x = x - θ x • e_n`, `θ(y, t) = η(y)² ψ(t)`, `ψ(t) = (t - λ) χ(t)` (invertible over the annulus,
collapsing the band to `λ` over the core). For every test field `X` supported in the cylinder,
the one-dimensional column change of variables (`integral_flattenedColumn_eq`: affine
substitution on the band, `C¹` substitution with a *continuous* integrand in the transition
layer, slab trapping elsewhere) and the pointwise Piola identity
`div (cof(DF)ᵀ X ∘ F) = det DF · (div X) ∘ F` (`fieldDivergence_shearPiolaField`, a differential
identity valid for every `C²` map) give
`∫_{E♭} div X = ∫_E div Z = -∫ ⟪Z, ν⟫ dμ` for one single `C¹` field `Z` on the whole cylinder
(`integral_flattenedPhase_fieldDivergence_eq`). Core and annulus are therefore tested by the
same field, and the resulting bound
`P(E♭, cylinder) ≤ |{η = 1}| + ∫_{π⁻¹{η < 1}} |cof DF ν| dμ`
contains no term on the interface `∂{η = 1}`: this is the zero gluing cost that the blueprint
derives from the cylinder-trace (cut-off and lower semicontinuity) argument, obtained here
without traces.

The perimeter of the core is *not* computed from a cofactor/area formula (the map is not
injective there): on the core the pairing reduces to `∫ X_n(y, λ) ν_n dμ`, and the net vertical
flux identity `π_# (ν_n μ) = dy` (`integral_indicator_horizontal_mul_vertical_eq`) turns it into
`∫_{core} X_n(y, λ) dy`, bounded by the horizontal area of the core (one horizontal sheet). In
the annulus the pairing is bounded pointwise by `GR8.1` (`flattening_pointwise_bound`).

## Main results

* `IsLocalPerimeterMinimizer.flattening_excess_le`: for every cutoff `η` and every level `λ`
  `ℰ({η = 1}) + ¼ ∫_{η < 1} η² |ν_h|² dμ ≤ 6 ∫ (t - λ)² |∇η|² dμ`.
* `IsLocalPerimeterMinimizer.flattening_excess_closedBall_le` (`GR8.2`): for
  `closedBall y₀ R ⊆ U` and `0 ≤ r < R`,
  `ℰ(closedBall y₀ r) ≤ flatteningConstant / (R - r)² ∫_{π⁻¹(ball y₀ R)} (t - λ)² dμ`,
  with a universal constant.
Here `ℰ = projectedExcessMeasure μ ν = π_# ((1 - ν_n) μ)` is the directed excess of `BV13–BV14`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported

namespace SerrinEpigraph

/-! ### 1. Horizontal/vertical decomposition -/

theorem inner_eq_inner_horizontal_add_mul_last {m : ℕ} (u v : Space (m + 1)) :
    inner ℝ u v = inner ℝ (horizontal u) (horizontal v) + u (Fin.last m) * v (Fin.last m) := by
  nth_rw 1 [← point_horizontal_last u, ← point_horizontal_last v]
  rw [inner_point_point]

theorem norm_sq_eq_norm_horizontal_sq_add {m : ℕ} (u : Space (m + 1)) :
    ‖u‖ ^ 2 = ‖horizontal u‖ ^ 2 + u (Fin.last m) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_inner_horizontal_add_mul_last,
    real_inner_self_eq_norm_sq]
  ring

theorem point_sub_smul_verticalDirection {m : ℕ} (y : Space m) (t c : ℝ) :
    point y t - c • verticalDirection m = point y (t - c) := by
  rw [sub_eq_add_neg, ← neg_smul, point_add_vertical, sub_eq_add_neg]

theorem horizontal_sub_smul_verticalDirection {m : ℕ} (x : Space (m + 1)) (c : ℝ) :
    horizontal (x - c • verticalDirection m) = horizontal x := by
  nth_rw 1 [← point_horizontal_last x]
  rw [point_sub_smul_verticalDirection, horizontal_point]

theorem last_sub_smul_verticalDirection {m : ℕ} (x : Space (m + 1)) (c : ℝ) :
    (x - c • verticalDirection m) (Fin.last m) = x (Fin.last m) - c := by
  nth_rw 1 [← point_horizontal_last x]
  rw [point_sub_smul_verticalDirection, last_point]

theorem horizontalContinuousLinearMap_apply' {m : ℕ} (x : Space (m + 1)) :
    horizontalContinuousLinearMap x = horizontal x := rfl

/-! ### 2. The height function of the vertical compression -/

/-- Height of the GR8 vertical compression: `θ(y, t) = η(y)² ψ(t)`; the compression is
`x ↦ x - θ x • e_n`. -/
def flatteningHeight {m : ℕ} (η : Space m → ℝ) (ψ : ℝ → ℝ) (x : Space (m + 1)) : ℝ :=
  η (horizontal x) ^ 2 * ψ (x (Fin.last m))

theorem contDiff_flatteningHeight {m : ℕ} {η : Space m → ℝ} {ψ : ℝ → ℝ} {n : ℕ∞}
    (hη : ContDiff ℝ n η) (hψ : ContDiff ℝ n ψ) : ContDiff ℝ n (flatteningHeight η ψ) := by
  have hlast : ContDiff ℝ n (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff
  have hhor : ContDiff ℝ n (fun x : Space (m + 1) ↦ horizontal x) :=
    horizontalContinuousLinearMap.contDiff
  exact ((hη.comp hhor).pow 2).mul (hψ.comp hlast)

theorem hasFDerivAt_flatteningHeight {m : ℕ} {η : Space m → ℝ} {ψ : ℝ → ℝ}
    (hη : Differentiable ℝ η) (hψ : Differentiable ℝ ψ) (x : Space (m + 1)) :
    HasFDerivAt (flatteningHeight η ψ)
      ((η (horizontal x) ^ 2) • ((deriv ψ (x (Fin.last m))) •
          (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m) : Space (m + 1) →L[ℝ] ℝ)) +
        (ψ (x (Fin.last m))) • ((2 * η (horizontal x)) •
          (fderiv ℝ η (horizontal x)).comp horizontalContinuousLinearMap)) x := by
  have hηx : HasFDerivAt (fun z : Space (m + 1) ↦ η (horizontal z))
      ((fderiv ℝ η (horizontal x)).comp horizontalContinuousLinearMap) x :=
    (hη (horizontal x)).hasFDerivAt.comp x horizontalContinuousLinearMap.hasFDerivAt
  have hη2 : HasFDerivAt (fun z : Space (m + 1) ↦ η (horizontal z) ^ 2)
      ((2 * η (horizontal x)) • (fderiv ℝ η (horizontal x)).comp horizontalContinuousLinearMap)
      x := by
    simpa [pow_one] using hηx.pow 2
  have hψx : HasFDerivAt (fun z : Space (m + 1) ↦ ψ (z (Fin.last m)))
      ((deriv ψ (x (Fin.last m))) •
        (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m) : Space (m + 1) →L[ℝ] ℝ)) x :=
    (hψ (x (Fin.last m))).hasDerivAt.comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).hasFDerivAt
  exact hη2.mul hψx

/-- Explicit derivative of the compression height. -/
theorem fderiv_flatteningHeight_apply {m : ℕ} {η : Space m → ℝ} {ψ : ℝ → ℝ}
    (hη : Differentiable ℝ η) (hψ : Differentiable ℝ ψ) (x v : Space (m + 1)) :
    fderiv ℝ (flatteningHeight η ψ) x v =
      η (horizontal x) ^ 2 * deriv ψ (x (Fin.last m)) * v (Fin.last m) +
        2 * η (horizontal x) * ψ (x (Fin.last m)) * fderiv ℝ η (horizontal x) (horizontal v) := by
  rw [(hasFDerivAt_flatteningHeight hη hψ x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, smul_eq_mul, EuclideanSpace.coe_proj, horizontalContinuousLinearMap_apply']
  ring

/-- The vertical derivative of the compression height. -/
theorem fderiv_flatteningHeight_verticalDirection {m : ℕ} {η : Space m → ℝ} {ψ : ℝ → ℝ}
    (hη : Differentiable ℝ η) (hψ : Differentiable ℝ ψ) (x : Space (m + 1)) :
    fderiv ℝ (flatteningHeight η ψ) x (verticalDirection m) =
      η (horizontal x) ^ 2 * deriv ψ (x (Fin.last m)) := by
  rw [fderiv_flatteningHeight_apply hη hψ, horizontal_verticalDirection, map_zero,
    last_verticalDirection]
  ring

theorem flatteningHeight_point {m : ℕ} (η : Space m → ℝ) (ψ : ℝ → ℝ) (y : Space m) (t : ℝ) :
    flatteningHeight η ψ (point y t) = η y ^ 2 * ψ t := by
  simp [flatteningHeight]

/-- The compression height is bounded once `0 ≤ η ≤ 1` and `ψ` is bounded. -/
theorem abs_flatteningHeight_le {m : ℕ} {η : Space m → ℝ} {ψ : ℝ → ℝ}
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1) {M : ℝ} (hψ : ∀ t, |ψ t| ≤ M)
    (x : Space (m + 1)) : |flatteningHeight η ψ x| ≤ M := by
  have h0 := hη0 (horizontal x)
  have h1 := hη1 (horizontal x)
  have hsq : η (horizontal x) ^ 2 ≤ 1 := by nlinarith
  rw [flatteningHeight, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    η (horizontal x) ^ 2 * |ψ (x (Fin.last m))| ≤ 1 * M :=
      mul_le_mul hsq (hψ _) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

/-! ### 3. The flattened competitor -/

/-- The GR8 flattening competitor: over `U` every vertical column is replaced by its
`flattenedColumn` with compression factor `1 - η²` (core `{η = 1}`: half-space `{t > λ}`;
annulus `{η < 1}`: invertible affine compression of the band); outside `U` the set is
unchanged. -/
def flattenedPhase {m : ℕ} (E : Set (Space (m + 1))) (U : Set (Space m)) (η : Space m → ℝ)
    (lam H₁ H₂ : ℝ) : Set (Space (m + 1)) :=
  {x | (horizontal x ∈ U → x (Fin.last m) ∈ flattenedColumn {t | point (horizontal x) t ∈ E}
      lam (1 - η (horizontal x) ^ 2) H₁ H₂) ∧ (horizontal x ∉ U → x ∈ E)}

theorem point_mem_flattenedPhase_of_mem {m : ℕ} {E : Set (Space (m + 1))}
    {U : Set (Space m)} {η : Space m → ℝ} {lam H₁ H₂ : ℝ} {y : Space m} (hy : y ∈ U) (t : ℝ) :
    point y t ∈ flattenedPhase E U η lam H₁ H₂ ↔
      t ∈ flattenedColumn {t | point y t ∈ E} lam (1 - η y ^ 2) H₁ H₂ := by
  simp [flattenedPhase, hy]

theorem point_mem_flattenedPhase_of_notMem {m : ℕ} {E : Set (Space (m + 1))}
    {U : Set (Space m)} {η : Space m → ℝ} {lam H₁ H₂ : ℝ} {y : Space m} (hy : y ∉ U)
    (t : ℝ) : point y t ∈ flattenedPhase E U η lam H₁ H₂ ↔ point y t ∈ E := by
  simp [flattenedPhase, hy]

theorem measurableSet_flattenedPhase {m : ℕ} {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : MeasurableSet U) {η : Space m → ℝ} (hη : Measurable η)
    (lam H₁ H₂ : ℝ) : MeasurableSet (flattenedPhase E U η lam H₁ H₂) := by
  have hπ : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  have hlast : Measurable (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.measurable
  have hs : Measurable (fun x : Space (m + 1) ↦ 1 - η (horizontal x) ^ 2) :=
    measurable_const.sub ((hη.comp hπ).pow_const 2)
  have hG : Measurable (fun x : Space (m + 1) ↦ point (horizontal x)
      (lam + (x (Fin.last m) - lam) / (1 - η (horizontal x) ^ 2))) := by
    have hpt : Measurable (fun p : Space m × ℝ ↦ point p.1 p.2) :=
      pointContinuousLinearMap.continuous.measurable
    exact hpt.comp (hπ.prodMk (measurable_const.add ((hlast.sub measurable_const).div hs)))
  have hb : Measurable (fun x : Space (m + 1) ↦ lam + (1 - η (horizontal x) ^ 2) * (H₁ - lam)) :=
    measurable_const.add (hs.mul measurable_const)
  have ha : Measurable (fun x : Space (m + 1) ↦ lam - (1 - η (horizontal x) ^ 2) * (H₁ + lam)) :=
    measurable_const.sub (hs.mul measurable_const)
  have heq : flattenedPhase E U η lam H₁ H₂ =
      (horizontal ⁻¹' U ∩ (({x | |x (Fin.last m)| ≤ H₂} ∩
        ({x | lam + (1 - η (horizontal x) ^ 2) * (H₁ - lam) < x (Fin.last m)} ∪
          ({x | lam - (1 - η (horizontal x) ^ 2) * (H₁ + lam) ≤ x (Fin.last m)} ∩
            {x | x (Fin.last m) ≤ lam + (1 - η (horizontal x) ^ 2) * (H₁ - lam)} ∩
            (fun x ↦ point (horizontal x)
              (lam + (x (Fin.last m) - lam) / (1 - η (horizontal x) ^ 2))) ⁻¹' E))) ∪
        ({x | |x (Fin.last m)| ≤ H₂}ᶜ ∩ E))) ∪ ((horizontal ⁻¹' U)ᶜ ∩ E) := by
    ext x
    by_cases hxU : horizontal x ∈ U <;> by_cases hx2 : |x (Fin.last m)| ≤ H₂ <;>
      simp [flattenedPhase, flattenedColumn, hxU, hx2, and_assoc]
  rw [heq]
  have hB : MeasurableSet {x : Space (m + 1) | |x (Fin.last m)| ≤ H₂} :=
    measurableSet_le (continuous_abs.measurable.comp hlast) measurable_const
  refine ((hU.preimage hπ).inter ((hB.inter ((measurableSet_lt hb hlast).union
    (((measurableSet_le ha hlast).inter (measurableSet_le hlast hb)).inter
      (hE.preimage hG)))).union (hB.compl.inter hE))).union ((hU.preimage hπ).compl.inter hE)

/-- The compact set outside of which the competitor agrees with `E` almost everywhere. -/
def flatteningSupport {m : ℕ} (η : Space m → ℝ) (H₂ : ℝ) : Set (Space (m + 1)) :=
  (fun p : Space m × ℝ ↦ point p.1 p.2) '' (tsupport η ×ˢ Icc (-H₂) H₂)

theorem isCompact_flatteningSupport {m : ℕ} {η : Space m → ℝ} (hηc : HasCompactSupport η)
    (H₂ : ℝ) : IsCompact (flatteningSupport η H₂) :=
  (hηc.isCompact.prod isCompact_Icc).image pointContinuousLinearMap.continuous

theorem flatteningSupport_subset_cylinderSet {m : ℕ} {η : Space m → ℝ} {U : Set (Space m)}
    (hηU : tsupport η ⊆ U) {H₂ H' : ℝ} (h3 : H₂ < H') :
    flatteningSupport η H₂ ⊆ cylinderSet U H' := by
  rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
  rw [point_mem_cylinderSet]
  exact ⟨hηU hy, by linarith [ht.1], by linarith [ht.2]⟩

/-- The competitor agrees with `E` almost everywhere off `flatteningSupport η H₂`: there the
compression factor is `1` and the slab trapping identifies the filled and emptied layers. -/
theorem ae_mem_flattenedPhase_iff {m : ℕ} {E : Set (Space (m + 1))} {U : Set (Space m)}
    {H H₁ H₂ H' lam : ℝ} (h1 : H < H₁) (h3 : H₂ < H')
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    (η : Space m → ℝ) :
    ∀ᵐ x ∂volume, x ∉ flatteningSupport η H₂ →
      (x ∈ E ↔ x ∈ flattenedPhase E U η lam H₁ H₂) := by
  filter_upwards [hbot, htop] with x hxb hxt hxK
  by_cases hxU : horizontal x ∈ U
  · by_cases hx2 : |x (Fin.last m)| ≤ H₂
    · have hη0 : η (horizontal x) = 0 := by
        by_contra hne
        apply hxK
        exact ⟨(horizontal x, x (Fin.last m)), ⟨subset_tsupport η hne, abs_le.mp hx2⟩,
          point_horizontal_last x⟩
      have hmem : x ∈ flattenedPhase E U η lam H₁ H₂ ↔
          (H₁ < x (Fin.last m) ∨ (-H₁ ≤ x (Fin.last m) ∧ x (Fin.last m) ≤ H₁ ∧ x ∈ E)) := by
        simp only [flattenedPhase, hxU, flattenedColumn, mem_ofPred_eq, hx2, hη0, ite_true,
          not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
        norm_num
      rw [hmem]
      rcases lt_or_ge H₁ (x (Fin.last m)) with hgt | hle
      · have hxE : x ∈ E := hxt hxU ⟨by linarith, by linarith [(abs_le.mp hx2).2]⟩
        exact ⟨fun _ ↦ Or.inl hgt, fun _ ↦ hxE⟩
      · rcases lt_or_ge (x (Fin.last m)) (-H₁) with hlt | hge
        · have hxE : x ∉ E := hxb hxU ⟨by linarith [(abs_le.mp hx2).1], by linarith⟩
          constructor
          · exact fun h ↦ absurd h hxE
          · rintro (h | ⟨h, -, -⟩)
            · linarith
            · linarith
        · constructor
          · exact fun h ↦ Or.inr ⟨hge, hle, h⟩
          · rintro (h | ⟨-, -, h⟩)
            · linarith
            · exact h
    · simp [flattenedPhase, flattenedColumn, hxU, hx2]
  · simp [flattenedPhase, hxU]

/-! ### 4. The divergence identity for the competitor -/

theorem hasCompactSupport_fieldDivergence {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {F : Space d → Space d} (hc : HasCompactSupport F) :
    HasCompactSupport (fieldDivergence b F) := by
  have hs : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  exact hc.of_isClosed_subset (isClosed_tsupport _) hs

/-- The GR8 compression height attached to the cutoff `η` and the level `λ`. -/
abbrev flatteningShearHeight {m : ℕ} (η : Space m → ℝ) (lam H₁ H₂ : ℝ) :
    Space (m + 1) → ℝ :=
  flatteningHeight η (verticalFlatteningProfile lam H₁ H₂)

/-- The shear Piola field of a test field `X` for the GR8 compression. -/
abbrev flatteningPiolaField {m : ℕ} (η : Space m → ℝ) (lam H₁ H₂ : ℝ)
    (X : Space (m + 1) → Space (m + 1)) : Space (m + 1) → Space (m + 1) :=
  shearPiolaField (flatteningShearHeight η lam H₁ H₂) (verticalDirection m) X

theorem contDiff_flatteningShearHeight {m : ℕ} {η : Space m → ℝ} (hη : ContDiff ℝ 2 η)
    (lam H₁ H₂ : ℝ) : ContDiff ℝ 2 (flatteningShearHeight η lam H₁ H₂) :=
  contDiff_flatteningHeight hη (contDiff_verticalFlatteningProfile lam H₁ H₂)

theorem abs_flatteningShearHeight_le {m : ℕ} {η : Space m → ℝ} (hη0 : ∀ y, 0 ≤ η y)
    (hη1 : ∀ y, η y ≤ 1) {lam H₁ H₂ : ℝ} (hH₁ : 0 ≤ H₁) (h2 : H₁ < H₂) (x : Space (m + 1)) :
    |flatteningShearHeight η lam H₁ H₂ x| ≤ H₂ + |lam| :=
  abs_flatteningHeight_le hη0 hη1 (abs_verticalFlatteningProfile_le hH₁ h2) x

/-- The compression maps the complement of the cylinder to itself. -/
theorem sub_flatteningShearHeight_notMem_cylinderSet {m : ℕ} {η : Space m → ℝ}
    {U : Set (Space m)} {lam H₁ H₂ H' : ℝ} (hH₁ : 0 ≤ H₁) (h2 : H₁ < H₂) (h3 : H₂ < H')
    {x : Space (m + 1)} (hx : x ∉ cylinderSet U H') :
    x - flatteningShearHeight η lam H₁ H₂ x • verticalDirection m ∉ cylinderSet U H' := by
  intro hmem
  rw [mem_cylinderSet, horizontal_sub_smul_verticalDirection,
    last_sub_smul_verticalDirection] at hmem
  apply hx
  refine ⟨hmem.1, ?_⟩
  by_contra hn
  have hge : H' ≤ |x (Fin.last m)| := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hn
    rcases hn with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact h
  have h0 : verticalFlatteningProfile lam H₁ H₂ (x (Fin.last m)) = 0 :=
    (verticalFlatteningProfile_out hH₁ h2 (by linarith)).1
  have hθ0 : flatteningShearHeight η lam H₁ H₂ x = 0 := by
    simp [flatteningShearHeight, flatteningHeight, h0]
  rw [hθ0, sub_zero] at hmem
  exact hn hmem.2

/-- The Piola field of a test field supported in the cylinder is a compactly supported `C¹`
test field supported in the cylinder. -/
theorem flatteningPiolaField_test {m : ℕ} {η : Space m → ℝ} (hη : ContDiff ℝ 2 η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1) {U : Set (Space m)} {lam H₁ H₂ H' : ℝ}
    (hH₁ : 0 ≤ H₁) (h2 : H₁ < H₂) (h3 : H₂ < H')
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXs : tsupport X ⊆ cylinderSet U H') :
    ContDiff ℝ 1 (flatteningPiolaField η lam H₁ H₂ X) ∧
      HasCompactSupport (flatteningPiolaField η lam H₁ H₂ X) ∧
      tsupport (flatteningPiolaField η lam H₁ H₂ X) ⊆ cylinderSet U H' := by
  have hθ := contDiff_flatteningShearHeight hη lam H₁ H₂
  have hsub := tsupport_shearPiolaField_subset hθ.continuous (verticalDirection m) X
  refine ⟨contDiff_shearPiolaField hθ hX _, ?_, ?_⟩
  · exact (isCompact_preimage_shear hθ.continuous
      (abs_flatteningShearHeight_le hη0 hη1 hH₁ h2) (verticalDirection m) hXc).of_isClosed_subset
        (isClosed_tsupport _) hsub
  · intro x hx
    by_contra hn
    exact sub_flatteningShearHeight_notMem_cylinderSet hH₁ h2 h3 hn (hXs (hsub hx))

/-- Divergence identity for the competitor (`GR8`): for every `C¹` test field `X` supported in
the cylinder, `∫_{E♭} div X = ∫_E div Z`, where `Z` is the Piola pull-back of `X` along the
compression. It is proved column by column from `integral_flattenedColumn_eq` and the Piola
identity; core, annulus and their interface are all handled by the same field `Z`. -/
theorem integral_flattenedPhase_fieldDivergence_eq {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E) {U : Set (Space m)} (hU : MeasurableSet U)
    {H H₁ H₂ H' lam : ℝ} (h1 : H < H₁) (h2 : H₁ < H₂) (h3 : H₂ < H') (hlam : |lam| ≤ H₁)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {η : Space m → ℝ} (hη : ContDiff ℝ 2 η) (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    (hηU : ∀ y, y ∉ U → η y = 0)
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXs : tsupport X ⊆ cylinderSet U H') :
    ∫ x, (flattenedPhase E U η lam H₁ H₂).indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence b X x =
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence b (flatteningPiolaField η lam H₁ H₂ X) x := by
  have hH₁ : 0 ≤ H₁ := (abs_nonneg lam).trans hlam
  set ψ := verticalFlatteningProfile lam H₁ H₂ with hψ_def
  set θ := flatteningShearHeight η lam H₁ H₂ with hθ_def
  have hψ2 : ContDiff ℝ 2 ψ := contDiff_verticalFlatteningProfile lam H₁ H₂
  have hθ2 : ContDiff ℝ 2 θ := contDiff_flatteningShearHeight hη lam H₁ H₂
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ2.differentiable (by norm_num)
  obtain ⟨hZ1, hZc, -⟩ := flatteningPiolaField_test hη hη0 hη1 hH₁ h2 h3 hX hXc hXs
  have hdivZ : ∀ x, fieldDivergence b (flatteningPiolaField η lam H₁ H₂ X) x =
      (1 - fderiv ℝ θ x (verticalDirection m)) *
        fieldDivergence b X (x - θ x • verticalDirection m) :=
    fieldDivergence_shearPiolaField b hθ2 hX (verticalDirection m)
  have hdivX_cont : Continuous (fieldDivergence b X) := fieldDivergence_continuous b hX
  have hE''m : MeasurableSet (flattenedPhase E U η lam H₁ H₂) :=
    measurableSet_flattenedPhase hE hU hη.continuous.measurable lam H₁ H₂
  rw [integral_space_eq_integral_horizontal_vertical
      (integrable_indicator_divergence b hE''m hX hXc),
    integral_space_eq_integral_horizontal_vertical (integrable_indicator_divergence b hE hZ1 hZc)]
  apply integral_congr_ae
  filter_upwards [ae_vertical_of_ae_volume hbot, ae_vertical_of_ae_volume htop] with y hyb hyt
  have hcol : ∀ t, point y t - θ (point y t) • verticalDirection m =
      point y (t - η y ^ 2 * ψ t) := by
    intro t
    rw [hθ_def, flatteningShearHeight, flatteningHeight_point,
      point_sub_smul_verticalDirection]
  have hcolD : ∀ t, fderiv ℝ θ (point y t) (verticalDirection m) = η y ^ 2 * deriv ψ t := by
    intro t
    rw [hθ_def, flatteningShearHeight, fderiv_flatteningHeight_verticalDirection hηd hψd,
      horizontal_point, last_point]
  have hRpt : ∀ t, E.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
      fieldDivergence b (flatteningPiolaField η lam H₁ H₂ X) (point y t) =
        {t | point y t ∈ E}.indicator (fun _ ↦ (1 : ℝ)) t *
          ((1 - η y ^ 2 * deriv ψ t) * fieldDivergence b X (point y (t - η y ^ 2 * ψ t))) := by
    intro t
    rw [hdivZ, hcolD, hcol]
    rfl
  simp_rw [hRpt]
  by_cases hy : y ∈ U
  · have hS : MeasurableSet {t | point y t ∈ E} :=
      hE.preimage (continuous_point y).measurable
    have hgc : Continuous (fun τ ↦ fieldDivergence b X (point y τ)) :=
      hdivX_cont.comp (continuous_point y)
    have hg0 : ∀ τ, H' ≤ |τ| → fieldDivergence b X (point y τ) = 0 := by
      intro τ hτ
      apply fieldDivergence_zero_of_notMem_tsupport
      intro hmem
      have hI := (hXs hmem).2
      rw [last_point] at hI
      have := abs_lt.mpr hI
      linarith
    have hbotS : ∀ᵐ t, t ∈ Ioo (-H') (-H) → t ∉ {t | point y t ∈ E} := by
      filter_upwards [hyb] with t ht hmem
      exact ht (by rw [horizontal_point]; exact hy) (by rw [last_point]; exact hmem)
    have htopS : ∀ᵐ t, t ∈ Ioo H H' → t ∈ {t | point y t ∈ E} := by
      filter_upwards [hyt] with t ht hmem
      exact ht (by rw [horizontal_point]; exact hy) (by rw [last_point]; exact hmem)
    have hη2 : 0 ≤ η y ^ 2 := sq_nonneg _
    have hη21 : η y ^ 2 ≤ 1 := by nlinarith [hη0 y, hη1 y]
    have hcolumn := integral_flattenedColumn_eq hS hgc h1 h2 h3 hlam hη2 hη21 hg0
      (hψ2.of_le (by norm_num))
      (fun t ht ↦ (verticalFlatteningProfile_band hH₁ h2 ht).1)
      (fun t ht ↦ (verticalFlatteningProfile_band hH₁ h2 ht).2)
      (fun t ht ↦ (verticalFlatteningProfile_out hH₁ h2 ht).1)
      (fun t ht ↦ (verticalFlatteningProfile_out hH₁ h2 ht).2) hbotS htopS
    have hLpt : ∀ t, (flattenedPhase E U η lam H₁ H₂).indicator (fun _ ↦ (1 : ℝ)) (point y t) *
        fieldDivergence b X (point y t) =
          (flattenedColumn {t | point y t ∈ E} lam (1 - η y ^ 2) H₁ H₂).indicator
            (fun _ ↦ (1 : ℝ)) t * fieldDivergence b X (point y t) := by
      intro t
      congr 1
      by_cases ht : t ∈ flattenedColumn {t | point y t ∈ E} lam (1 - η y ^ 2) H₁ H₂
      · rw [indicator_of_mem ((point_mem_flattenedPhase_of_mem hy t).mpr ht),
          indicator_of_mem ht]
      · rw [indicator_of_notMem (fun h ↦ ht ((point_mem_flattenedPhase_of_mem hy t).mp h)),
          indicator_of_notMem ht]
    simp_rw [hLpt]
    exact hcolumn
  · have hηy : η y = 0 := hηU y hy
    congr 1
    funext t
    have hmem : point y t ∈ flattenedPhase E U η lam H₁ H₂ ↔ t ∈ {t | point y t ∈ E} :=
      point_mem_flattenedPhase_of_notMem hy t
    rw [hηy]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero,
      one_mul]
    congr 1
    by_cases ht : t ∈ {t | point y t ∈ E}
    · rw [indicator_of_mem (hmem.mpr ht), indicator_of_mem ht]
    · rw [indicator_of_notMem (fun h ↦ ht (hmem.mp h)), indicator_of_notMem ht]

/-! ### 5. Net vertical flux against bounded horizontal weights -/

theorem abs_apply_last_le_norm {m : ℕ} (x : Space (m + 1)) : |x (Fin.last m)| ≤ ‖x‖ := by
  have h := norm_sq_eq_norm_horizontal_sq_add x
  have hsq : |x (Fin.last m)| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [sq_abs, h]
    nlinarith [sq_nonneg ‖horizontal x‖]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem norm_horizontal_le_norm_of_space {m : ℕ} (x : Space (m + 1)) :
    ‖horizontal x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_norm_horizontal_sq_add x
  have hsq : ‖horizontal x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg (x (Fin.last m))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Net vertical flux identity `π_# (ν_n μ) = dy` on `U`, tested against bounded measurable
horizontal weights supported in a measurable `A ⊆ U` (`BV13.2`, `GR8`). -/
theorem integral_indicator_horizontal_mul_vertical_eq {m : ℕ}
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
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U)
    {φ : Space m → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ y, |φ y| ≤ C) :
    ∫ x, A.indicator φ (horizontal x) * inner ℝ (ν x) (verticalDirection m) ∂μ =
      ∫ y in A, φ y := by
  set f : Space m → ℝ := A.indicator φ with hf_def
  have hfm : Measurable f := hφ.indicator hA
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hφC 0)
  have hfb : ∀ y, ‖f y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ A
    · rw [hf_def, indicator_of_mem hy, Real.norm_eq_abs]
      exact hφC y
    · rw [hf_def, indicator_of_notMem hy, norm_zero]
      exact hC0
  have hfU : U.indicator f = f := by
    funext y
    by_cases hy : y ∈ U
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, hf_def, indicator_of_notMem (fun h ↦ hy (hAU h))]
  let : IsFiniteMeasure (projectedExcessMeasure μ ν) :=
    isFiniteMeasure_projectedExcessMeasure μ hν
  have hres := projectedPerimeterMeasure_restrict_eq b hE hU hH hHH' μ hμcompl hμopen hν
    hνunit hdist hbot htop
  have hUfin : volume U < ⊤ := volume_lt_top_of_slab_trapped b hE hU hH hHH' μ hμcompl hμopen
    hν hνunit hdist hbot htop
  have hπm : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  -- integrability of the weight against the relevant finite measures
  have hf_exc : Integrable f (projectedExcessMeasure μ ν) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall hfb)
  have hf_vol : Integrable f volume := by
    have hAfin : volume A < ⊤ := (measure_mono hAU).trans_lt hUfin
    have hon : IntegrableOn φ A volume := by
      refine IntegrableOn.of_bound hAfin hφ.aestronglyMeasurable C
        (Eventually.of_forall fun y ↦ ?_)
      rw [Real.norm_eq_abs]
      exact hφC y
    exact (integrable_indicator_iff hA).mpr hon
  have hfπ : Integrable (fun x ↦ f (horizontal x)) μ :=
    Integrable.of_bound (hfm.comp hπm).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ hfb _)
  -- the excess density
  set w : Space (m + 1) → ℝ := fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m) with hw_def
  have hw_aesm : AEStronglyMeasurable w μ :=
    aestronglyMeasurable_const.sub (hν.aestronglyMeasurable.inner aestronglyMeasurable_const)
  have hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x := by
    filter_upwards [hνunit] with x hx
    have hcs := real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hcs
    simp only [hw_def]
    linarith
  have hw_lt_top : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ :=
    Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hmap_exc : (∫ y, f y ∂projectedExcessMeasure μ ν) =
      ∫ x, f (horizontal x) * w x ∂μ := by
    unfold projectedExcessMeasure
    rw [integral_map hπm.aemeasurable hfm.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hw_aesm.aemeasurable.ennreal_ofReal
        hw_lt_top]
    apply integral_congr_ae
    filter_upwards [hw_nonneg] with x hwx
    rw [ENNReal.toReal_ofReal hwx, smul_eq_mul, mul_comm]
  have hmap_perim : (∫ y, f y ∂projectedPerimeterMeasure μ) = ∫ x, f (horizontal x) ∂μ :=
    integral_map hπm.aemeasurable hfm.aestronglyMeasurable
  have hfw_int : Integrable (fun x ↦ f (horizontal x) * w x) μ := by
    refine Integrable.of_bound ((hfm.comp hπm).aestronglyMeasurable.mul hw_aesm) (2 * C) ?_
    filter_upwards [hνunit] with x hx
    have hcs := abs_real_inner_le_norm (ν x) (verticalDirection m)
    rw [hx, norm_verticalDirection, mul_one] at hcs
    have hw2 : |w x| ≤ 2 := by
      simp only [hw_def]
      rw [abs_le] at hcs ⊢
      constructor <;> linarith
    rw [norm_mul, Real.norm_eq_abs]
    calc
      ‖f (horizontal x)‖ * |w x| ≤ C * 2 :=
        mul_le_mul (hfb _) hw2 (abs_nonneg _) hC0
      _ = 2 * C := by ring
  -- the restricted measure identity integrated against `f`
  have hperim_eq : (∫ y, f y ∂projectedPerimeterMeasure μ) =
      (∫ y, f y) + ∫ y, f y ∂projectedExcessMeasure μ ν := by
    calc
      (∫ y, f y ∂projectedPerimeterMeasure μ) = ∫ y, U.indicator f y ∂projectedPerimeterMeasure μ :=
        by rw [hfU]
      _ = ∫ y in U, f y ∂projectedPerimeterMeasure μ := integral_indicator hU.measurableSet
      _ = ∫ y in U, f y ∂(volume + projectedExcessMeasure μ ν) := by rw [hres]
      _ = ∫ y, U.indicator f y ∂(volume + projectedExcessMeasure μ ν) :=
        (integral_indicator hU.measurableSet).symm
      _ = ∫ y, f y ∂(volume + projectedExcessMeasure μ ν) := by rw [hfU]
      _ = (∫ y, f y) + ∫ y, f y ∂projectedExcessMeasure μ ν :=
        integral_add_measure hf_vol hf_exc
  have hsplit : (fun x ↦ A.indicator φ (horizontal x) * inner ℝ (ν x) (verticalDirection m)) =
      fun x ↦ f (horizontal x) - f (horizontal x) * w x := by
    funext x
    simp only [hw_def, hf_def]
    ring
  rw [hsplit, integral_sub hfπ hfw_int, ← hmap_perim, ← hmap_exc, hperim_eq, add_sub_cancel_right,
    hf_def, integral_indicator hA]

/-! ### 6. The Piola field on the band -/

/-- The point of the compressed band attached to `x`: `(y, λ + (1 - η(y)²) (t - λ))`. -/
abbrev flatteningBandPoint {m : ℕ} (η : Space m → ℝ) (lam : ℝ) (x : Space (m + 1)) :
    Space (m + 1) :=
  point (horizontal x) (lam + (1 - η (horizontal x) ^ 2) * (x (Fin.last m) - lam))

/-- Cofactor formula for the Piola field at a band point (`|t| ≤ H₁`). -/
theorem inner_flatteningPiolaField_band {m : ℕ} {η : Space m → ℝ} (hη : ContDiff ℝ 2 η)
    {lam H₁ H₂ : ℝ} (hH₁ : 0 ≤ H₁) (h2 : H₁ < H₂) (X : Space (m + 1) → Space (m + 1))
    {x : Space (m + 1)} (hx : |x (Fin.last m)| ≤ H₁) (v : Space (m + 1)) :
    inner ℝ (flatteningPiolaField η lam H₁ H₂ X x) v =
      (1 - η (horizontal x) ^ 2) * inner ℝ (X (flatteningBandPoint η lam x)) v +
        (2 * η (horizontal x) * fderiv ℝ η (horizontal x)
            (horizontal (X (flatteningBandPoint η lam x))) * (x (Fin.last m) - lam) +
          η (horizontal x) ^ 2 * X (flatteningBandPoint η lam x) (Fin.last m)) *
          v (Fin.last m) := by
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hψd : Differentiable ℝ (verticalFlatteningProfile lam H₁ H₂) :=
    (contDiff_verticalFlatteningProfile lam H₁ H₂ (n := 1)).differentiable one_ne_zero
  obtain ⟨hψx, hψ'x⟩ := verticalFlatteningProfile_band (lam := lam) hH₁ h2 hx
  have hpt : x - flatteningShearHeight η lam H₁ H₂ x • verticalDirection m =
      flatteningBandPoint η lam x := by
    nth_rw 1 [← point_horizontal_last x]
    rw [point_sub_smul_verticalDirection]
    simp only [flatteningShearHeight, flatteningHeight, hψx]
    congr 1
    ring
  have hD : ∀ u, fderiv ℝ (flatteningShearHeight η lam H₁ H₂) x u =
      η (horizontal x) ^ 2 * u (Fin.last m) +
        2 * η (horizontal x) * (x (Fin.last m) - lam) *
          fderiv ℝ η (horizontal x) (horizontal u) := by
    intro u
    rw [flatteningShearHeight, fderiv_flatteningHeight_apply hηd hψd, hψx, hψ'x]
    ring
  rw [flatteningPiolaField, inner_shearPiolaField, hpt, hD, hD, horizontal_verticalDirection,
    map_zero, last_verticalDirection, real_inner_comm v (verticalDirection m),
    inner_verticalDirection_right]
  ring

/-- `GR8.1` at a band point: the pairing of the Piola field of a unit-bounded test field with a
unit vector `n` is at most `1 - η² |n_h|² / 4 + 6 (t - λ)² |∇η|²`. -/
theorem abs_inner_flatteningPiolaField_le {m : ℕ} {η : Space m → ℝ} (hη : ContDiff ℝ 2 η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1) {lam H₁ H₂ : ℝ} (hH₁ : 0 ≤ H₁) (h2 : H₁ < H₂)
    {X : Space (m + 1) → Space (m + 1)} (hXb : ∀ x, ‖X x‖ ≤ 1)
    {x : Space (m + 1)} (hx : |x (Fin.last m)| ≤ H₁) {n : Space (m + 1)} (hn : ‖n‖ = 1) :
    |inner ℝ (flatteningPiolaField η lam H₁ H₂ X x) n| ≤
      1 - η (horizontal x) ^ 2 * ‖horizontal n‖ ^ 2 / 4 +
        6 * ((x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2) := by
  rw [inner_flatteningPiolaField_band hη hH₁ h2 X hx n,
    inner_eq_inner_horizontal_add_mul_last (X (flatteningBandPoint η lam x)) n]
  set X' := X (flatteningBandPoint η lam x)
  have hX' : ‖horizontal X'‖ ^ 2 + X' (Fin.last m) ^ 2 ≤ 1 := by
    rw [← norm_sq_eq_norm_horizontal_sq_add]
    have := hXb (flatteningBandPoint η lam x)
    nlinarith [norm_nonneg X']
  have hn' : ‖horizontal n‖ ^ 2 + n (Fin.last m) ^ 2 = 1 := by
    rw [← norm_sq_eq_norm_horizontal_sq_add, hn, one_pow]
  have h := flattening_pointwise_bound (L := fderiv ℝ η (horizontal x))
    (w := x (Fin.last m) - lam) hX' hn' (hη0 (horizontal x)) (hη1 (horizontal x))
  calc
    _ ≤ 1 - η (horizontal x) ^ 2 * ‖horizontal n‖ ^ 2 / 4 +
        6 * (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 := h
    _ = _ := by ring

/-- In the core `{η = 1}` the Piola field only sees the vertical component of `X` at the level
`λ`: the pairing is `X_n(y, λ) ν_n`. -/
theorem inner_flatteningPiolaField_core {m : ℕ} {η : Space m → ℝ} (hη : ContDiff ℝ 2 η)
    (hη1 : ∀ y, η y ≤ 1) {lam H₁ H₂ : ℝ} (hH₁ : 0 ≤ H₁) (h2 : H₁ < H₂)
    (X : Space (m + 1) → Space (m + 1)) {x : Space (m + 1)} (hx : |x (Fin.last m)| ≤ H₁)
    (hηx : η (horizontal x) = 1) (v : Space (m + 1)) :
    inner ℝ (flatteningPiolaField η lam H₁ H₂ X x) v =
      X (point (horizontal x) lam) (Fin.last m) * v (Fin.last m) := by
  have hmax : IsLocalMax η (horizontal x) :=
    Filter.Eventually.of_forall fun z ↦ by rw [hηx]; exact hη1 z
  have hDη : fderiv ℝ η (horizontal x) = 0 := hmax.fderiv_eq_zero
  have hpt : flatteningBandPoint η lam x = point (horizontal x) lam := by
    simp [flatteningBandPoint, hηx]
  rw [inner_flatteningPiolaField_band hη hH₁ h2 X hx v, hpt, hDη, hηx]
  simp

/-! ### 7. The perimeter of the competitor -/

/-- The weighted height integrand of `GR8` is integrable against a slab-concentrated finite
measure. -/
theorem integrable_sq_last_sub_mul_norm_fderiv_sq {m : ℕ} (μ : Measure (Space (m + 1)))
    [IsFiniteMeasure μ] {H : ℝ} (hslab : ∀ᵐ x ∂μ, |x (Fin.last m)| ≤ H) {η : Space m → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (c : ℝ) :
    Integrable (fun x ↦ (x (Fin.last m) - c) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2) μ := by
  have hηDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hlastc : Continuous (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous
  obtain ⟨Cη, hCη⟩ := (hηc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hηDc
  refine Integrable.of_bound (((hlastc.sub continuous_const).pow 2).mul
    ((hηDc.comp continuous_horizontal).norm.pow 2)).aestronglyMeasurable
    ((H + |c|) ^ 2 * Cη ^ 2) ?_
  filter_upwards [hslab] with x hx
  have hxH : |x (Fin.last m) - c| ≤ H + |c| := (abs_sub _ _).trans (add_le_add hx le_rfl)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ha : (x (Fin.last m) - c) ^ 2 ≤ (H + |c|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hxH 2
  have hb : ‖fderiv ℝ η (horizontal x)‖ ^ 2 ≤ Cη ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hCη _) 2
  exact mul_le_mul ha hb (by positivity) (by positivity)

/-- Clamping the level into the slab does not increase the squared height deviation. -/
theorem sq_sub_clamp_le {t lam H : ℝ} (ht : |t| ≤ H) :
    (t - max (-H) (min lam H)) ^ 2 ≤ (t - lam) ^ 2 := by
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  rcases le_total lam (-H) with h | h
  · have hc : max (-H) (min lam H) = -H := by
      rw [min_eq_left (by linarith)]
      exact max_eq_left h
    rw [hc]
    nlinarith
  · rcases le_total lam H with h' | h'
    · rw [min_eq_left h', max_eq_right h]
    · have hc : max (-H) (min lam H) = H := by
        rw [min_eq_right h']
        exact max_eq_right (by linarith)
      rw [hc]
      nlinarith

/-- The pointwise `GR8.1` majorant `1 - η² |ν_h|² / 4 + 6 (t - λ)² |∇η|²` of the pairing of
the Piola field with the unit normal. -/
def flatteningMajorant {m : ℕ} (η : Space m → ℝ) (ν : Space (m + 1) → Space (m + 1))
    (lam : ℝ) (x : Space (m + 1)) : ℝ :=
  1 - η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 / 4 +
    6 * ((x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2)

theorem integrable_horizontal_normal_weight {m : ℕ} (μ : Measure (Space (m + 1)))
    [IsFiniteMeasure μ] {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) {η : Space m → ℝ} (hηc : Continuous η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1) :
    Integrable (fun x ↦ η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2) μ := by
  refine Integrable.of_bound (((hηc.comp continuous_horizontal).pow 2
    ).aestronglyMeasurable.mul
      ((continuous_horizontal.comp_aestronglyMeasurable hν.aestronglyMeasurable).norm.pow 2))
    1 ?_
  filter_upwards [hνunit] with x hx
  have hh := norm_horizontal_le_norm_of_space (ν x)
  rw [hx] at hh
  have he0 := hη0 (horizontal x)
  have he1 := hη1 (horizontal x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh2 : ‖horizontal (ν x)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (horizontal (ν x))]
  have he2 : η (horizontal x) ^ 2 ≤ 1 := by nlinarith
  calc
    η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ≤ 1 * 1 :=
      mul_le_mul he2 hh2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

theorem integrable_flatteningMajorant {m : ℕ} (μ : Measure (Space (m + 1)))
    [IsFiniteMeasure μ] {H : ℝ} (hslab : ∀ᵐ x ∂μ, |x (Fin.last m)| ≤ H)
    {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) {η : Space m → ℝ} (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1) (lam : ℝ) :
    Integrable (flatteningMajorant η ν lam) μ :=
  ((integrable_const 1).sub ((integrable_horizontal_normal_weight μ hν hνunit hη.continuous
    hη0 hη1).div_const 4)).add
    ((integrable_sq_last_sub_mul_norm_fderiv_sq μ hslab hη hηc lam).const_mul 6)

/-- **Perimeter of the flattened competitor** (`GR8`, no minimality used): in the cylinder, the
competitor has perimeter at most the horizontal area of the core `{η = 1}` (one horizontal
sheet at height `λ`) plus the integral over the annulus of the `GR8.1` majorant of the cofactor
term. There is no contribution of the interface `∂{η = 1}` (zero gluing cost). -/
theorem variationalPerimeter_flattenedPhase_le {m : ℕ}
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
    {η : Space m → ℝ} (hη : ContDiff ℝ 2 η) (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    {lam H₁ H₂ : ℝ} (h1 : H < H₁) (h2 : H₁ < H₂) (h3 : H₂ < H') (hlam : |lam| ≤ H₁) :
    variationalPerimeter b (flattenedPhase E U η lam H₁ H₂) (cylinderSet U H') ≤
      ENNReal.ofReal (volume.real {y | η y = 1} +
        ∫ x in (horizontal ⁻¹' {y | η y = 1})ᶜ, flatteningMajorant η ν lam x ∂μ) := by
  have hH₁0 : 0 ≤ H₁ := (abs_nonneg lam).trans hlam
  have hηU' : ∀ y, y ∉ U → η y = 0 :=
    fun y hy ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hηU h))
  have hπm : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  have hlastc : Continuous (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous
  set K₁ : Set (Space m) := {y | η y = 1} with hK₁_def
  have hK₁m : MeasurableSet K₁ := (isClosed_eq hη.continuous continuous_const).measurableSet
  have hK₁η : K₁ ⊆ tsupport η := by
    intro y hy
    apply subset_tsupport η
    rw [Function.mem_support, show η y = 1 from hy]
    exact one_ne_zero
  have hK₁U : K₁ ⊆ U := hK₁η.trans hηU
  have hK₁vol : volume K₁ < ⊤ := (measure_mono hK₁η).trans_lt hηc.isCompact.measure_lt_top
  set P : Set (Space (m + 1)) := horizontal ⁻¹' K₁ with hP_def
  have hPm : MeasurableSet P := hK₁m.preimage hπm
  have hslab := ae_mem_slab_of_slab_trapped b hU hH hHH' μ hμcompl hμopen hbot htop
  have hslab' : ∀ᵐ x ∂μ, |x (Fin.last m)| ≤ H := by
    filter_upwards [hslab] with x hx
    exact abs_le.mpr hx.2
  have hRint : Integrable (flatteningMajorant η ν lam) μ :=
    integrable_flatteningMajorant μ hslab' hν hνunit (hη.of_le (by norm_num)) hηc hη0 hη1 lam
  refine iSup_le fun X ↦ iSup_le fun hX ↦ iSup_le fun hXc ↦ iSup_le fun hXs ↦
    iSup_le fun hXb ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨hZ1, hZc, hZs⟩ := flatteningPiolaField_test hη hη0 hη1 hH₁0 h2 h3 hX hXc hXs
  set Z := flatteningPiolaField η lam H₁ H₂ X with hZ_def
  let Zc : C_c(Space (m + 1), Space (m + 1)) := ⟨⟨Z, hZ1.continuous⟩, hZc⟩
  have hd : -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Z x) =
      ∫ x, inner ℝ (Z x) (ν x) ∂μ := hdist Zc hZ1 hZs
  have hid := integral_flattenedPhase_fieldDivergence_eq b hE hU.measurableSet h1 h2 h3 hlam
    hbot htop hη hη0 hη1 hηU' hX hXc hXs
  rw [hid, ← neg_neg (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Z x), hd,
    norm_neg, Real.norm_eq_abs]
  -- Integrability of the pairing.
  obtain ⟨CZ, hCZ⟩ := hZc.exists_bound_of_continuous hZ1.continuous
  have hpair_int : Integrable (fun x ↦ inner ℝ (Z x) (ν x)) μ := by
    refine (hν.norm.const_mul CZ).mono'
      (hZ1.continuous.aestronglyMeasurable.inner hν.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hCZ x) (norm_nonneg _))
  rw [← integral_add_compl hPm hpair_int]
  -- Core: exact cancellation through the net vertical flux.
  set φ : Space m → ℝ := fun y ↦ X (point y lam) (Fin.last m) with hφ_def
  have hφm : Measurable φ :=
    (hlastc.comp (hX.continuous.comp (pointContinuousLinearMap.continuous.comp
      (continuous_id.prodMk continuous_const)))).measurable
  have hφb : ∀ y, |φ y| ≤ 1 := fun y ↦ (abs_apply_last_le_norm _).trans (hXb _)
  have hcore : ∫ x in P, inner ℝ (Z x) (ν x) ∂μ = ∫ y in K₁, φ y := by
    rw [← integral_indicator hPm]
    rw [← integral_indicator_horizontal_mul_vertical_eq b hE hU hH hHH' μ
      hμcompl hμopen hν hνunit hdist hbot htop hK₁m hK₁U hφm hφb]
    apply integral_congr_ae
    filter_upwards [hslab] with x hx
    by_cases hxP : x ∈ P
    · have hηx : η (horizontal x) = 1 := hxP
      have hxH : |x (Fin.last m)| ≤ H₁ :=
        abs_le.mpr ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
      rw [indicator_of_mem hxP, indicator_of_mem (show horizontal x ∈ K₁ from hxP),
        inner_flatteningPiolaField_core hη hη1 hH₁0 h2 X hxH hηx, inner_verticalDirection_right]
    · rw [indicator_of_notMem hxP, indicator_of_notMem (show horizontal x ∉ K₁ from hxP),
        zero_mul]
  have hcore_le : |∫ x in P, inner ℝ (Z x) (ν x) ∂μ| ≤ volume.real K₁ := by
    rw [hcore, ← Real.norm_eq_abs]
    have := norm_setIntegral_le_of_norm_le_const hK₁vol
      (fun y _ ↦ (show ‖φ y‖ ≤ 1 by rw [Real.norm_eq_abs]; exact hφb y))
    linarith
  -- Annulus: the pointwise bound `GR8.1`.
  have hann_le : |∫ x in Pᶜ, inner ℝ (Z x) (ν x) ∂μ| ≤
      ∫ x in Pᶜ, flatteningMajorant η ν lam x ∂μ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hRint.integrableOn (ae_restrict_of_ae ?_)
    filter_upwards [hslab, hνunit] with x hx hxν
    have hxH : |x (Fin.last m)| ≤ H₁ :=
      abs_le.mpr ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
    rw [Real.norm_eq_abs]
    exact abs_inner_flatteningPiolaField_le hη hη0 hη1 (lam := lam) hH₁0 h2 hXb hxH hxν
  calc
    |∫ x in P, inner ℝ (Z x) (ν x) ∂μ + ∫ x in Pᶜ, inner ℝ (Z x) (ν x) ∂μ|
        ≤ |∫ x in P, inner ℝ (Z x) (ν x) ∂μ| + |∫ x in Pᶜ, inner ℝ (Z x) (ν x) ∂μ| :=
      abs_add_le _ _
    _ ≤ volume.real K₁ + ∫ x in Pᶜ, flatteningMajorant η ν lam x ∂μ :=
      add_le_add hcore_le hann_le

/-! ### 8. The directed reverse Poincaré inequality (`GR8`) -/

/-- `GR8` with a level `λ` inside the trapping slab. See
`IsLocalPerimeterMinimizer.flattening_excess_le` for arbitrary `λ`. -/
theorem IsLocalPerimeterMinimizer.flattening_excess_le_of_abs_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (hcyl : cylinderSet U H' ⊆ Ω)
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
    {η : Space m → ℝ} (hη : ContDiff ℝ 2 η) (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) {lam : ℝ} (hlam : |lam| ≤ H) :
    (projectedExcessMeasure μ ν).real {y | η y = 1} +
        (1 / 4) * ∫ x in horizontal ⁻¹' {y | η y < 1},
          η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ∂μ ≤
      6 * ∫ x, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ := by
  -- Parameters of the competitor.
  set H₁ : ℝ := (2 * H + H') / 3 with hH₁_def
  set H₂ : ℝ := (H + 2 * H') / 3 with hH₂_def
  have h1 : H < H₁ := by rw [hH₁_def]; linarith
  have h2 : H₁ < H₂ := by rw [hH₁_def, hH₂_def]; linarith
  have h3 : H₂ < H' := by rw [hH₂_def]; linarith
  have hlam₁ : |lam| ≤ H₁ := hlam.trans h1.le
  have hπm : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  have hWo : IsOpen (cylinderSet U H') := isOpen_cylinderSet hU H'
  set K₁ : Set (Space m) := {y | η y = 1} with hK₁_def
  have hK₁m : MeasurableSet K₁ := (isClosed_eq hη.continuous continuous_const).measurableSet
  have hK₁U : K₁ ⊆ U := by
    intro y hy
    apply hηU
    apply subset_tsupport η
    rw [Function.mem_support, show η y = 1 from hy]
    exact one_ne_zero
  set P : Set (Space (m + 1)) := horizontal ⁻¹' K₁ with hP_def
  have hPm : MeasurableSet P := hK₁m.preimage hπm
  have hslab := ae_mem_slab_of_slab_trapped b hU hH hHH' μ hμcompl hμopen hbot htop
  have hslab' : ∀ᵐ x ∂μ, |x (Fin.last m)| ≤ H := by
    filter_upwards [hslab] with x hx
    exact abs_le.mpr hx.2
  have hη1' : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hI₁int := integrable_horizontal_normal_weight μ hν hνunit hη.continuous hη0 hη1
  have hI₂int := integrable_sq_last_sub_mul_norm_fderiv_sq μ hslab' hη1' hηc lam
  -- Perimeter of the competitor, and minimality.
  set B : ℝ := volume.real K₁ + ∫ x in Pᶜ, flatteningMajorant η ν lam x ∂μ with hB_def
  have hPE'' := variationalPerimeter_flattenedPhase_le b hmin.measurableSet hU hH hHH' μ hμcompl
    hμopen hν hνunit hdist hbot htop hη hη0 hη1 hηc hηU h1 h2 h3 hlam₁
  have hle : variationalPerimeter b E (cylinderSet U H') ≤
      variationalPerimeter b (flattenedPhase E U η lam H₁ H₂) (cylinderSet U H') :=
    hmin.minimizes (cylinderSet U H') (flattenedPhase E U η lam H₁ H₂) (flatteningSupport η H₂)
      hWo hcyl (measurableSet_flattenedPhase hmin.measurableSet hU.measurableSet
        hη.continuous.measurable lam H₁ H₂)
      (isCompact_flatteningSupport hηc H₂) (flatteningSupport_subset_cylinderSet hηU h3)
      (ae_mem_flattenedPhase_iff h1 h3 hbot htop η)
  have hB0 : 0 ≤ B := by
    have hK : 0 ≤ volume.real K₁ := measureReal_nonneg
    have hR : 0 ≤ ∫ x in Pᶜ, flatteningMajorant η ν lam x ∂μ := by
      refine setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae ?_)
      filter_upwards [hνunit] with x hx
      show (0 : ℝ) ≤ flatteningMajorant η ν lam x
      have hh := norm_horizontal_le_norm_of_space (ν x)
      rw [hx] at hh
      have he1 := hη1 (horizontal x)
      have he0 := hη0 (horizontal x)
      have hh2 : ‖horizontal (ν x)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (horizontal (ν x))]
      have he2 : η (horizontal x) ^ 2 ≤ 1 := by nlinarith
      have hprod : η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ≤ 1 :=
        (mul_le_mul he2 hh2 (by positivity) zero_le_one).trans (by norm_num)
      have hpos : 0 ≤ 6 * ((x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2) := by
        positivity
      simp only [flatteningMajorant]
      linarith
    linarith
  have hμW : μ (cylinderSet U H') = variationalPerimeter b E (cylinderSet U H') :=
    hμopen _ hWo subset_rfl
  have hμuniv : μ univ = μ (cylinderSet U H') := by
    rw [← measure_add_measure_compl hWo.measurableSet, hμcompl, add_zero]
  have hμle : μ univ ≤ ENNReal.ofReal B := by
    rw [hμuniv, hμW]
    exact hle.trans hPE''
  have hμreal : μ.real univ ≤ B := ENNReal.toReal_le_of_le_ofReal hB0 hμle
  -- Bookkeeping.
  have hsplit : μ.real P + μ.real Pᶜ = μ.real univ := measureReal_add_measureReal_compl hPm
  have hPproj : μ.real P = (projectedPerimeterMeasure μ).real K₁ := by
    simp only [Measure.real, projectedPerimeterMeasure, Measure.map_apply hπm hK₁m, hP_def]
  have hPexc := projectedPerimeterMeasure_real_apply_eq b hmin.measurableSet hU hH hHH' μ
    hμcompl hμopen hν hνunit hdist hbot htop hK₁m hK₁U
  have hPc : ∫ x in Pᶜ, (1 : ℝ) ∂μ = μ.real Pᶜ := by
    rw [setIntegral_const, smul_eq_mul, mul_one]
  have hRsplit : ∫ x in Pᶜ, flatteningMajorant η ν lam x ∂μ =
      μ.real Pᶜ - (∫ x in Pᶜ, η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ∂μ) / 4 +
        6 * ∫ x in Pᶜ, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ := by
    have hA : IntegrableOn
        (fun x ↦ (1 : ℝ) - η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 / 4) Pᶜ μ :=
      ((integrable_const 1).sub (hI₁int.div_const 4)).integrableOn
    have hB' : IntegrableOn (fun x ↦ 6 * ((x (Fin.last m) - lam) ^ 2 *
        ‖fderiv ℝ η (horizontal x)‖ ^ 2)) Pᶜ μ := (hI₂int.const_mul 6).integrableOn
    have hC : IntegrableOn (fun x ↦ η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 / 4) Pᶜ μ :=
      (hI₁int.div_const 4).integrableOn
    calc
      ∫ x in Pᶜ, flatteningMajorant η ν lam x ∂μ =
          ∫ x in Pᶜ, ((1 - η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 / 4) +
            6 * ((x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2)) ∂μ := rfl
      _ = (∫ x in Pᶜ, (1 - η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 / 4) ∂μ) +
          ∫ x in Pᶜ, 6 * ((x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2) ∂μ :=
        integral_add hA hB'
      _ = ((∫ x in Pᶜ, (1 : ℝ) ∂μ) -
            ∫ x in Pᶜ, η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 / 4 ∂μ) +
          ∫ x in Pᶜ, 6 * ((x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2) ∂μ := by
        rw [integral_sub (integrable_const 1).integrableOn hC]
      _ = _ := by rw [integral_const_mul, integral_div, hPc]
  have hI₂le : ∫ x in Pᶜ, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ ≤
      ∫ x, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ :=
    setIntegral_le_integral hI₂int (Eventually.of_forall fun x ↦ by positivity)
  have hPc_eq : Pᶜ = horizontal ⁻¹' {y | η y < 1} := by
    ext x
    simp only [hP_def, hK₁_def, mem_compl_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun h ↦ lt_of_le_of_ne (hη1 _) h, fun h ↦ ne_of_lt h⟩
  rw [← hPc_eq]
  linarith

/-- **Directed reverse Poincaré inequality (`GR8`).** Let `E` be a local perimeter minimizer in
`Ω ⊇ cylinderSet U H'` whose reduced boundary in the cylinder is trapped in the slab `|t| ≤ H`
(empty phase below, full phase above), with perimeter measure `μ` (restricted to the cylinder)
and inner unit normal `ν`. For every `C²` cutoff `0 ≤ η ≤ 1` with compact support in `U` and
every level `λ`,
`ℰ({η = 1}) + ¼ ∫_{π⁻¹{η < 1}} η² |ν_h|² dμ ≤ 6 ∫ (t - λ)² |∇η|² dμ`,
where `ℰ = projectedExcessMeasure μ ν` is the directed (oriented) excess. -/
theorem IsLocalPerimeterMinimizer.flattening_excess_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (hcyl : cylinderSet U H' ⊆ Ω)
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
    {η : Space m → ℝ} (hη : ContDiff ℝ 2 η) (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) (lam : ℝ) :
    (projectedExcessMeasure μ ν).real {y | η y = 1} +
        (1 / 4) * ∫ x in horizontal ⁻¹' {y | η y < 1},
          η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ∂μ ≤
      6 * ∫ x, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ := by
  set lam' : ℝ := max (-H) (min lam H) with hlam'_def
  have hlam' : |lam'| ≤ H :=
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have h := hmin.flattening_excess_le_of_abs_le hU hH hHH' hcyl μ hμcompl hμopen hν hνunit
    hdist hbot htop hη hη0 hη1 hηc hηU hlam'
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hslab := ae_mem_slab_of_slab_trapped b hU hH hHH' μ hμcompl hμopen hbot htop
  have hslab' : ∀ᵐ x ∂μ, |x (Fin.last m)| ≤ H := by
    filter_upwards [hslab] with x hx
    exact abs_le.mpr hx.2
  have hη1' : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  refine integral_mono_ae (integrable_sq_last_sub_mul_norm_fderiv_sq μ hslab' hη1' hηc lam')
    (integrable_sq_last_sub_mul_norm_fderiv_sq μ hslab' hη1' hηc lam) ?_
  filter_upwards [hslab'] with x hx
  exact mul_le_mul_of_nonneg_right (sq_sub_clamp_le hx) (sq_nonneg _)

/-! ### 9. The ball form `GR8.2` -/

/-- The universal constant of `GR8.2`: `24 B²` with `B` a bound for `Real.smoothTransition'`. -/
def flatteningConstant : ℝ := 24 * smoothTransitionDerivBound ^ 2

theorem flatteningConstant_pos : 0 < flatteningConstant := by
  have := smoothTransitionDerivBound_pos
  unfold flatteningConstant
  positivity

/-- **`GR8.2`.** For `closedBall y₀ R ⊆ U` and `0 ≤ r < R`, the directed excess over the
smaller closed ball is bounded by the squared height deviation from any level `λ` over the
larger ball:
`ℰ(closedBall y₀ r) ≤ C / (R - r)² ∫_{π⁻¹(ball y₀ R)} (t - λ)² dμ`
with the universal constant `C = flatteningConstant`. -/
theorem IsLocalPerimeterMinimizer.flattening_excess_closedBall_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (hcyl : cylinderSet U H' ⊆ Ω)
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
    (y₀ : Space m) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hball : closedBall y₀ R ⊆ U)
    (lam : ℝ) :
    (projectedExcessMeasure μ ν).real (closedBall y₀ r) ≤
      flatteningConstant / (R - r) ^ 2 *
        ∫ x in horizontal ⁻¹' ball y₀ R, (x (Fin.last m) - lam) ^ 2 ∂μ := by
  set η : Space m → ℝ := radialFlatteningCutoff y₀ r R with hη_def
  have hη : ContDiff ℝ 2 η := contDiff_radialFlatteningCutoff y₀ r R
  have hηc : HasCompactSupport η := hasCompactSupport_radialFlatteningCutoff hr hrR
  have hηU : tsupport η ⊆ U := (tsupport_radialFlatteningCutoff_subset hr hrR).trans hball
  have hmain := hmin.flattening_excess_le hU hH hHH' hcyl μ hμcompl hμopen hν hνunit hdist hbot
    htop hη (radialFlatteningCutoff_nonneg y₀ r R) (radialFlatteningCutoff_le_one y₀ r R) hηc
    hηU lam
  let : IsFiniteMeasure (projectedExcessMeasure μ ν) :=
    isFiniteMeasure_projectedExcessMeasure μ hν
  have hmono : (projectedExcessMeasure μ ν).real (closedBall y₀ r) ≤
      (projectedExcessMeasure μ ν).real {y | η y = 1} :=
    measureReal_mono (fun y hy ↦ radialFlatteningCutoff_eq_one hr hrR hy)
  have hI₁ : 0 ≤ ∫ x in horizontal ⁻¹' {y | η y < 1},
      η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ∂μ :=
    setIntegral_nonneg_of_ae (Eventually.of_forall fun x ↦ by positivity)
  have hslab := ae_mem_slab_of_slab_trapped b hU hH hHH' μ hμcompl hμopen hbot htop
  have hslab' : ∀ᵐ x ∂μ, |x (Fin.last m)| ≤ H := by
    filter_upwards [hslab] with x hx
    exact abs_le.mpr hx.2
  have hRr : 0 < R - r := by linarith
  set c : ℝ := 2 * smoothTransitionDerivBound / (R - r) with hc_def
  have hc0 : 0 ≤ c := by
    have := smoothTransitionDerivBound_pos
    positivity
  have hBm : MeasurableSet (horizontal ⁻¹' ball y₀ R : Set (Space (m + 1))) :=
    measurableSet_ball.preimage continuous_horizontal.measurable
  have hlastc : Continuous (fun x : Space (m + 1) ↦ x (Fin.last m)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous
  have hsq_int : Integrable (fun x : Space (m + 1) ↦ (x (Fin.last m) - lam) ^ 2) μ := by
    refine Integrable.of_bound ((hlastc.sub continuous_const).pow 2).aestronglyMeasurable
      ((H + |lam|) ^ 2) ?_
    filter_upwards [hslab'] with x hx
    have hxH : |x (Fin.last m) - lam| ≤ H + |lam| := (abs_sub _ _).trans (add_le_add hx le_rfl)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hxH 2
  have hgrad : ∫ x, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ ≤
      c ^ 2 * ∫ x in horizontal ⁻¹' ball y₀ R, (x (Fin.last m) - lam) ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_indicator hBm]
    refine integral_mono_ae (integrable_sq_last_sub_mul_norm_fderiv_sq μ hslab'
      (hη.of_le (by norm_num)) hηc lam) ((hsq_int.const_mul (c ^ 2)).indicator hBm) ?_
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ horizontal ⁻¹' ball y₀ R
    · rw [indicator_of_mem hx]
      have hD : ‖fderiv ℝ η (horizontal x)‖ ^ 2 ≤ c ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_radialFlatteningCutoff_le hr hrR _) 2
      calc
        (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ≤
            (x (Fin.last m) - lam) ^ 2 * c ^ 2 :=
          mul_le_mul_of_nonneg_left hD (sq_nonneg _)
        _ = c ^ 2 * (x (Fin.last m) - lam) ^ 2 := mul_comm _ _
    · rw [indicator_of_notMem hx]
      have hfar : R ≤ ‖horizontal x - y₀‖ := by
        rw [mem_preimage, mem_ball, dist_eq_norm, not_lt] at hx
        exact hx
      have hz : fderiv ℝ η (horizontal x) = 0 := fderiv_radialFlatteningCutoff_eq_zero hr hrR hfar
      show (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ≤ 0
      rw [hz, norm_zero]
      simp
  have hconst : 6 * c ^ 2 = flatteningConstant / (R - r) ^ 2 := by
    rw [hc_def, flatteningConstant]
    field_simp
    ring
  calc
    (projectedExcessMeasure μ ν).real (closedBall y₀ r)
        ≤ (projectedExcessMeasure μ ν).real {y | η y = 1} +
          (1 / 4) * ∫ x in horizontal ⁻¹' {y | η y < 1},
            η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ∂μ := by
      have : 0 ≤ (1 / 4 : ℝ) * ∫ x in horizontal ⁻¹' {y | η y < 1},
          η (horizontal x) ^ 2 * ‖horizontal (ν x)‖ ^ 2 ∂μ := by positivity
      linarith
    _ ≤ 6 * ∫ x, (x (Fin.last m) - lam) ^ 2 * ‖fderiv ℝ η (horizontal x)‖ ^ 2 ∂μ := hmain
    _ ≤ 6 * (c ^ 2 * ∫ x in horizontal ⁻¹' ball y₀ R, (x (Fin.last m) - lam) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hgrad (by norm_num)
    _ = flatteningConstant / (R - r) ^ 2 *
          ∫ x in horizontal ⁻¹' ball y₀ R, (x (Fin.last m) - lam) ^ 2 ∂μ := by
      rw [← mul_assoc, hconst]

/-! ### 10. Existence of the cylinder perimeter measure -/

/-- A finite-perimeter cylinder carries the finite perimeter measure and unit polar vector used
in the hypotheses of `IsLocalPerimeterMinimizer.flattening_excess_le`. -/
theorem exists_cylinder_perimeter_polar_measure {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) {U : Set (Space m)} (hU : IsOpen U) {H' : ℝ}
    (hP : variationalPerimeter b E (cylinderSet U H') ≠ ⊤) :
    ∃ (μ : Measure (Space (m + 1))) (ν : Space (m + 1) → Space (m + 1)),
      IsFiniteMeasure μ ∧ μ (cylinderSet U H')ᶜ = 0 ∧
      (∀ V, IsOpen V → V ⊆ cylinderSet U H' → μ V = variationalPerimeter b E V) ∧
      Integrable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ F : C_c(Space (m + 1), Space (m + 1)),
        ContDiff ℝ 1 (F : Space (m + 1) → Space (m + 1)) →
        tsupport (F : Space (m + 1) → Space (m + 1)) ⊆ cylinderSet U H' →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν x) ∂μ := by
  obtain ⟨μ, ν, hfin, -, huniv, hopen, hν, hunit, hdist⟩ :=
    exists_localized_perimeter_polar_measure b hE hP
  have hWo : IsOpen (cylinderSet U H') := isOpen_cylinderSet hU H'
  have hW : μ (cylinderSet U H') = μ univ := by
    rw [hopen _ hWo subset_rfl, huniv]
  have hcompl : μ (cylinderSet U H')ᶜ = 0 := by
    have hsum := measure_add_measure_compl (μ := μ) hWo.measurableSet
    rw [hW] at hsum
    have hfin' : μ univ ≠ ⊤ := measure_ne_top μ univ
    exact (ENNReal.add_right_inj hfin').mp (hsum.trans (add_zero _).symm)
  exact ⟨μ, ν, hfin, hcompl, hopen, hν, hunit, hdist⟩

/-- For a local minimizer, a cylinder contained in a ball whose closure lies in the domain has
finite perimeter. -/
theorem IsLocalPerimeterMinimizer.variationalPerimeter_cylinderSet_ne_top {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    {U : Set (Space m)} {H' : ℝ} {x₀ : Space (m + 1)} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall x₀ ρ ⊆ Ω) (hsub : cylinderSet U H' ⊆ ball x₀ ρ) :
    variationalPerimeter b E (cylinderSet U H') ≠ ⊤ :=
  ne_top_of_le_ne_top (hmin.perimeter_ball_ne_top x₀ ρ hρ hball)
    (variationalPerimeter_mono b E hsub)

end SerrinEpigraph
