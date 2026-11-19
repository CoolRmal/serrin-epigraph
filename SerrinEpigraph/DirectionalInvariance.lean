module

public import SerrinEpigraph.MollificationDuality
public import SerrinEpigraph.SmoothBoundaryChart
public import SerrinEpigraph.PerimeterInvariance
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Translation invariance from a vanishing directional derivative

If `∫_E ∂_v φ = 0` for every smooth compactly supported `φ`, then `E` is a.e. invariant under the
translations `x ↦ x + t v` (`ae_mem_iff_add_smul_mem_of_integral_fderiv_eq_zero`). The smooth
averages of `1_E` have vanishing derivative in the direction `v` (move the averaging to the test
functions and integrate by parts), hence are invariant under these translations, and they converge
to `1_E` almost everywhere.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace SerrinEpigraph

/-- The divergence of `φ v` for a constant vector `v` is the directional derivative `Dφ(v)`. -/
theorem fieldDivergence_smul_const_eq_fderiv {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {φ : Space d → ℝ} {x : Space d} (hφ : DifferentiableAt ℝ φ x) (v : Space d) :
    fieldDivergence b (fun z ↦ φ z • v) x = fderiv ℝ φ x v := by
  rw [fieldDivergence_eq_trace, (hφ.hasFDerivAt.smul_const v).fderiv, trace_clm_smulRight]

/-- **A vanishing directional distributional derivative gives translation invariance.** If
`∫_E ∂_v φ = 0` for every smooth compactly supported `φ`, then `E` is a.e. invariant under the
translations by the multiples of `v`. -/
theorem ae_mem_iff_add_smul_mem_of_integral_fderiv_eq_zero {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) (v : Space d)
    (h : ∀ φ : Space d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ φ x v = 0) (t : ℝ) :
    ∀ᵐ x ∂volume, x ∈ E ↔ x + t • v ∈ E := by
  set χ : Space d → ℝ := E.indicator (fun _ ↦ (1 : ℝ)) with hχ
  have hloc : LocallyIntegrable χ volume := locallyIntegrable_phaseIndicator hE
  have hχm : Measurable χ := measurable_const.indicator hE
  have hχB : ∀ x, ‖χ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ E <;> simp [hχ, hx]
  have hsmooth : ∀ n, ContDiff ℝ ∞ (mollify χ n) := fun n ↦
    mollify_contDiff_of_locallyIntegrable hloc n
  -- the smooth averages are weakly invariant
  have hweak : ∀ (n : ℕ) (ψ : Space d → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, mollify χ n x * fderiv ℝ ψ x v = 0 := by
    intro n ψ hψ hψc
    have hψ' : Continuous fun x ↦ fderiv ℝ ψ x v :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψ'c : HasCompactSupport fun x ↦ fderiv ℝ ψ x v := hψc.fderiv_apply (𝕜 := ℝ) v
    rw [integral_mollify_mul_eq_average_tests hχm hχB hψ' hψ'c n]
    have hinner : ∀ y, ∫ x, χ x * fderiv ℝ ψ (x + y) v = 0 := by
      intro y
      have h1 := h (fun x ↦ ψ (x + y)) (hψ.comp (contDiff_id.add contDiff_const))
        (hψc.comp_homeomorph (Homeomorph.addRight y))
      simpa [fderiv_comp_add_right] using h1
    simp [hinner]
  -- hence they have vanishing derivative along `v`
  have hderiv0 : ∀ n x, fderiv ℝ (mollify χ n) x v = 0 := by
    intro n
    have hcont : Continuous fun x ↦ fderiv ℝ (mollify χ n) x v :=
      ((hsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    have hzero : ∀ᵐ x ∂volume, fderiv ℝ (mollify χ n) x v = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
        fun ψ hψ hψc ↦ ?_
      have hibp := integral_mul_fieldDivergence_eq_neg (EuclideanSpace.basisFun (Fin d) ℝ)
        (X := fun x ↦ ψ x • v) isOpen_univ ((hsmooth n).of_le (by simp)).contDiffOn
        ((hψ.of_le (by simp)).smul contDiff_const) (hasCompactSupport_smul_left' hψc fun _ ↦ v)
        (subset_univ _)
      have h1 : ∫ x, mollify χ n x *
          fieldDivergence (EuclideanSpace.basisFun (Fin d) ℝ) (fun x ↦ ψ x • v) x = 0 := by
        rw [← hweak n ψ hψ hψc]
        congr 1
        funext x
        rw [fieldDivergence_smul_const_eq_fderiv _ ((hψ.differentiable (by simp)) x)]
      rw [h1] at hibp
      have h2 : ∫ x, fderiv ℝ (mollify χ n) x (ψ x • v) = 0 := by linarith
      simpa [map_smul, smul_eq_mul] using h2
    have := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hzero
    intro x
    exact congrFun this x
  -- hence they are invariant along `v`
  have hinv : ∀ n x, mollify χ n (x + t • v) = mollify χ n x := by
    intro n x
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ mollify χ n (x + s • v)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ ↦ x + s • v) v s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_add x
      have h2 := ((hsmooth n).differentiable (by simp) (x + s • v)).hasFDerivAt.comp_hasDerivAt s h1
      rwa [hderiv0 n] at h2
    have := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv) t 0
    simpa using this
  -- pass to the limit
  have hlim := mollify_tendsto_ae_of_locallyIntegrable hloc
  have hlim' : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ mollify χ n (x + t • v)) atTop (𝓝 (χ (x + t • v))) :=
    (measurePreserving_add_right volume (t • v)).quasiMeasurePreserving.ae hlim
  filter_upwards [hlim, hlim'] with x hx hx'
  have heq : χ (x + t • v) = χ x := by
    refine tendsto_nhds_unique hx' ?_
    simpa [hinv] using hx
  simp only [hχ] at heq
  by_cases hxE : x ∈ E <;> by_cases hxtE : x + t • v ∈ E <;> simp_all

end SerrinEpigraph
