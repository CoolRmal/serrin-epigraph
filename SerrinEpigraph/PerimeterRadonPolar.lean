module

public import SerrinEpigraph.PerimeterRadonVector
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Polar decomposition of Euclidean vector measures

Coordinate Radon–Nikodym derivatives construct the vector density. Equality of variation
measures then proves that the density has Euclidean norm one almost everywhere.
-/

public section

open MeasureTheory
open scoped Topology CompactlySupported

namespace SerrinEpigraph

/-- Project a Euclidean vector measure onto one fixed vector. -/
@[expose] noncomputable def vectorMeasureCoordinate {d : ℕ} {X : Type*}
    [MeasurableSpace X] (σ : VectorMeasure X (Space d)) (v : Space d) : SignedMeasure X :=
  σ.mapRange (innerSL ℝ v).toAddMonoidHom (innerSL ℝ v).continuous

/-- Every coordinate measure is absolutely continuous with respect to Euclidean variation. -/
theorem vectorMeasureCoordinate_absolutelyContinuous {d : ℕ} {X : Type*}
    [MeasurableSpace X] (σ : VectorMeasure X (Space d)) (v : Space d) :
    vectorMeasureCoordinate σ v ≪ᵥ σ.variation.toENNRealVectorMeasure := by
  intro s hs
  have hz : σ s = 0 := σ.absolutelyContinuous hs
  change inner ℝ v (σ s) = 0
  rw [hz, inner_zero_right]

/-- The vector density assembled from the coordinate Radon–Nikodym derivatives. -/
@[expose] noncomputable def vectorPolarDensity {d : ℕ} {X : Type*}
    [MeasurableSpace X] (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (σ : VectorMeasure X (Space d)) (x : X) : Space d :=
  ∑ i, (vectorMeasureCoordinate σ (b i)).rnDeriv σ.variation x • b i

theorem integrable_vectorPolarDensity {d : ℕ} {X : Type*} [MeasurableSpace X]
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (σ : VectorMeasure X (Space d)) :
    Integrable (vectorPolarDensity b σ) σ.variation := by
  apply integrable_finsetSum
  intro i _
  exact ((vectorMeasureCoordinate σ (b i)).integrable_rnDeriv σ.variation).smul_const (b i)

/-- The constructed density represents the original vector measure on every measurable set. -/
theorem withDensity_vectorPolarDensity {d : ℕ} {X : Type*} [MeasurableSpace X]
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (σ : VectorMeasure X (Space d))
    [SigmaFinite σ.variation] : σ.variation.withDensityᵥ (vectorPolarDensity b σ) = σ := by
  ext1 s hs
  rw [withDensityᵥ_apply (integrable_vectorPolarDensity b σ) hs]
  change (∫ x in s, ∑ i,
    (vectorMeasureCoordinate σ (b i)).rnDeriv σ.variation x • b i ∂σ.variation) = σ s
  rw [integral_finsetSum]
  · have hcoord (i : Fin d) :
        (∫ x in s, (vectorMeasureCoordinate σ (b i)).rnDeriv σ.variation x ∂σ.variation) =
          inner ℝ (b i) (σ s) := by
      have he := congrArg (fun τ : SignedMeasure X ↦ τ s)
        ((vectorMeasureCoordinate σ (b i)).withDensityᵥ_rnDeriv_eq σ.variation
          (vectorMeasureCoordinate_absolutelyContinuous σ (b i)))
      rw [withDensityᵥ_apply
        ((vectorMeasureCoordinate σ (b i)).integrable_rnDeriv σ.variation) hs] at he
      exact he
    simp_rw [integral_smul_const, hcoord]
    exact b.sum_repr' (σ s)
  · intro i _
    exact (((vectorMeasureCoordinate σ (b i)).integrable_rnDeriv σ.variation).smul_const
      (b i)).integrableOn

/-- Euclidean polar density has norm exactly one almost everywhere for the variation measure. -/
theorem norm_vectorPolarDensity_ae {d : ℕ} {X : Type*} [MeasurableSpace X]
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (σ : VectorMeasure X (Space d))
    [SigmaFinite σ.variation] : ∀ᵐ x ∂σ.variation, ‖vectorPolarDensity b σ x‖ = 1 := by
  have hi := integrable_vectorPolarDensity b σ
  have hm : σ.variation.withDensity (fun x ↦ ‖vectorPolarDensity b σ x‖ₑ) =
      σ.variation.withDensity 1 := by
    rw [← Measure.variation_withDensityᵥ hi, withDensity_vectorPolarDensity b σ, withDensity_one]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hi.aestronglyMeasurable.enorm aemeasurable_const).mp hm
  filter_upwards [hae] with x hx
  simpa using congrArg ENNReal.toReal hx

/-- The bounded-test density formula only needs an almost-everywhere bound on the density. -/
theorem integral_withDensity_inner_of_ae_bounded {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} [IsFiniteMeasure μ] {w f : Y → Space d}
    (hw : Integrable w μ) (hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x, ‖f x‖ ≤ C) :
    (∫ᵛ x, f x ∂[innerSL ℝ; μ.withDensityᵥ w]) = ∫ x, inner ℝ (f x) (w x) ∂μ := by
  classical
  let g : Y → Space d := fun x ↦ if ‖w x‖ ≤ 1 then w x else 0
  have hgw : g =ᵐ[μ] w := by
    filter_upwards [hwb] with x hx
    simp [g, hx]
  have hg : Integrable g μ := hw.congr hgw.symm
  have hgb (x : Y) : ‖g x‖ ≤ 1 := by
    dsimp [g]
    split_ifs with h <;> simp_all
  have he := integral_withDensity_inner_of_bounded hg hgb hf hC hfb
  rw [WithDensityᵥEq.congr_ae hgw] at he
  refine he.trans (integral_congr_ae ?_)
  filter_upwards [hgw] with x hx
  rw [hx]

/-- Finite variational perimeter has a finite regular perimeter measure and a unit polar vector,
with the full distributional integration-by-parts identity. -/
theorem exists_perimeter_polar_measure {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hP : variationalPerimeter b E Ω ≠ ⊤) :
    ∃ (μ : Measure (Space d)) (ν : Space d → Space d),
      IsFiniteMeasure μ ∧ μ.Regular ∧ μ Set.univ = variationalPerimeter b E Ω ∧
      Integrable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ Ω →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν x) ∂μ := by
  obtain ⟨σ, hmass, hdist⟩ := exists_perimeter_vector_measure b hE hP
  let : IsFiniteMeasure σ.variation := ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hP⟩
  have hi := integrable_vectorPolarDensity b σ
  have hn := norm_vectorPolarDensity_ae b σ
  refine ⟨σ.variation, vectorPolarDensity b σ, inferInstance, inferInstance, hmass, hi, hn, ?_⟩
  intro F hF hs
  refine (hdist F hF hs).trans ?_
  nth_rw 1 [← withDensity_vectorPolarDensity b σ]
  exact integral_withDensity_inner_of_ae_bounded hi (hn.mono fun _ h ↦ h.le)
    F.continuous.measurable (norm_nonneg F.toBoundedContinuousFunction)
    F.toBoundedContinuousFunction.norm_coe_le_norm

end SerrinEpigraph
