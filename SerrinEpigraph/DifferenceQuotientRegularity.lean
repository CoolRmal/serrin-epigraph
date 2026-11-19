module

public import SerrinEpigraph.SobolevBallCompactness
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Difference quotients and `W^{2,2}_loc` regularity of Lipschitz weak solutions

This is the first step of the Schauder bootstrap for nonlinear divergence-form equations
`div 𝒜(∇u) = 0` (blueprint `gmt-regularity.md`, GR14). Throughout, `u : Space d → ℝ` is globally
`L`-Lipschitz, the flux `𝒜` is `C¹`, uniformly elliptic with constant `λ > 0` and has derivative
bounded by `Λ` on the ball `‖p‖ ≤ L` (`IsEllipticFlux 𝒜 L λ Λ`), and the equation holds for all
`C¹` test functions compactly supported in `ball x₀ R` (`IsWeakSolution 𝒜 u (ball x₀ R)`).
Gradients of Lipschitz functions are the almost-everywhere gradients given by Rademacher's theorem.

## Main results

* `HasWeakGradientOn U w G`: `∫ w ∂ₑφ = -∫ ⟪G, e⟫ φ` for `φ ∈ C¹_c(U)`;
  `HasWeakGradientOn.ae_eq` (uniqueness a.e. on open sets), `hasWeakGradientOn_of_contDiffOn`
  and `hasWeakGradientOn_of_lipschitz` (consistency with classical and a.e. gradients),
  `HasWeakGradientOn.of_orthonormalBasis` (coordinate directions suffice).
* `exists_inner_eq_of_abs_le` (Hahn–Banach + Riesz) and the resulting `L²` criteria
  `exists_weakDeriv_of_abs_integral_le`, `exists_hasWeakGradientOn_of_abs_integral_le`.
* `integral_inner_gradient_eq_zero_of_lipschitz_test`,
  `IsWeakSolution.integral_eq_zero_of_lipschitz`: the weak equation (and its translates) for
  Lipschitz test functions.
* `IsWeakSolution.integral_norm_gradient_sub_sq_le`: Caccioppoli inequality for differences,
  `∫_{B_r} ‖∇u(y + z) - ∇u(y)‖² ≤ 4 (Λ/λ)² (L ‖z‖)² |B̄_ρ| / (ρ - r)²` for `ρ + ‖z‖ < R`.
* `diffQuot u v h = (u (· + h v) - u) / h`; `IsWeakSolution.integral_fderiv_diffQuot_sq_le`
  (uniform `L²(B_r)` bound for `∇ D_h^v u`); `IsWeakSolution.integral_inner_avgFluxDeriv_eq_zero`
  (`D_h^v u` solves `div (A_h ∇ D_h^v u) = 0` with the averaged coefficient
  `A_h = ∫₀¹ D𝒜(∇u + t (∇u(· + h v) - ∇u)) dt`, which is measurable, bounded by `Λ` and elliptic
  with constant `λ`).
* `IsWeakSolution.exists_hasWeakGradientOn_fderiv`: `∂ᵥu` has a weak gradient `G ∈ L²(B_r)` on
  `B_r` for every `r < R`, with `∫_{B_r} ‖G‖² ≤ d · 16 (Λ/λ)² L² ‖v‖² |B̄_{(r+R)/2}| / (R - r)²`.
* `IsWeakSolution.integral_inner_fderiv_flux_eq_zero`: `∂ᵥu` solves the linearized equation
  `∫ ⟪D𝒜(∇u) G, ∇φ⟫ = 0` for `φ ∈ C¹_c(B_r)`;
  `IsWeakSolution.exists_hasWeakGradientOn_fderiv_linearized`
  combines both.
* `minimalSurfaceFlux p = p / √(1 + ‖p‖²)`: `isEllipticFlux_minimalSurfaceFlux` (constants
  `λ = (1 + L²)^{-3/2}`, `Λ = 2`), `exists_hasWeakGradientOn_fderiv_of_minimalSurface`,
  `integral_linearized_minimalSurface_eq_zero`.

The Caccioppoli inequality is proved directly from the monotonicity and Lipschitz bounds
`λ ‖q - p‖² ≤ ⟪𝒜 q - 𝒜 p, q - p⟫`, `‖𝒜 q - 𝒜 p‖ ≤ Λ ‖q - p‖` on `‖p‖, ‖q‖ ≤ L`
(`IsEllipticFlux.inner_sub_ge`, `IsEllipticFlux.norm_sub_le`), testing with
`η² (u(· + z) - u)` for the piecewise linear cutoff `η = linearCutoff x₀ r ρ`. The weak gradient
is obtained from the uniform bounds by Riesz representation in `L²(B_r)`, and the linearized
equation by passing to the limit in the difference equation (weak convergence of `∇ D_h^v u`,
via density of `C¹_c(B_r)` in `L²(B_r)`, plus a uniform first-order Taylor estimate for `𝒜`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric ContinuousLinearMap InnerProductSpace
open scoped Topology Convolution

namespace SerrinEpigraph

/-! ### Weak gradients -/

/-- `G` is a weak gradient of `w` on `U`: both are locally integrable on `U`, and
`∫ w ∂ₑφ = -∫ ⟪G, e⟫ φ` for every direction `e` and every `C¹` test function `φ` compactly
supported in `U`. (Equivalently `∫ w ∂ᵢφ = -∫ Gᵢ φ` for the coordinate directions; see
`HasWeakGradientOn.of_orthonormalBasis`.) -/
def HasWeakGradientOn {d : ℕ} (U : Set (Space d)) (w : Space d → ℝ)
    (G : Space d → Space d) : Prop :=
  LocallyIntegrableOn w U ∧ LocallyIntegrableOn G U ∧
    ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ e : Space d, ∫ y, w y * fderiv ℝ φ y e = -∫ y, inner ℝ (G y) e * φ y

/-- A locally integrable function times a continuous test function compactly supported in the
domain of local integrability is integrable. -/
private theorem integrable_mul_of_locallyIntegrableOn {d : ℕ} {U : Set (Space d)} {f φ : Space d → ℝ}
    (hf : LocallyIntegrableOn f U) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) : Integrable (fun y ↦ f y * φ y) := by
  have hK : IntegrableOn f (tsupport φ) := hf.integrableOn_compact_subset hsub hφc
  have hKφ : IntegrableOn (fun y ↦ f y * φ y) (tsupport φ) :=
    hK.mul_continuousOn hφ.continuousOn hφc
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hKφ
  exact (Function.support_mul_subset_right _ _).trans (subset_tsupport φ)

/-- A component of a locally integrable vector field is locally integrable. -/
theorem locallyIntegrableOn_inner_const {d : ℕ} {U : Set (Space d)} {G : Space d → Space d}
    (hG : LocallyIntegrableOn G U) (e : Space d) :
    LocallyIntegrableOn (fun y ↦ inner ℝ (G y) e) U := by
  intro x hx
  obtain ⟨t, ht, hGt⟩ := hG x hx
  refine ⟨t, ht, ((innerSL ℝ e).integrable_comp hGt).congr ?_⟩
  filter_upwards with y
  simp only [innerSL_apply_apply, real_inner_comm]

/-- Testing a function against a `C¹` test function compactly supported in a set where the
function is locally integrable produces an integrable integrand. -/
theorem integrable_mul_fderiv_of_locallyIntegrableOn {d : ℕ} {U : Set (Space d)}
    {f φ : Space d → ℝ} (hf : LocallyIntegrableOn f U) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ U) (e : Space d) :
    Integrable (fun y ↦ f y * fderiv ℝ φ y e) :=
  integrable_mul_of_locallyIntegrableOn hf
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ e) ((tsupport_fderiv_apply_subset ℝ e).trans hsub)

namespace HasWeakGradientOn

variable {d : ℕ} {U V : Set (Space d)} {w : Space d → ℝ} {G G' : Space d → Space d}

theorem locallyIntegrableOn (h : HasWeakGradientOn U w G) : LocallyIntegrableOn w U := h.1

theorem locallyIntegrableOn_gradient (h : HasWeakGradientOn U w G) :
    LocallyIntegrableOn G U := h.2.1

theorem integral_eq (h : HasWeakGradientOn U w G) {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ U) (e : Space d) :
    ∫ y, w y * fderiv ℝ φ y e = -∫ y, inner ℝ (G y) e * φ y :=
  h.2.2 φ hφ hφc hsub e

/-- Weak gradients restrict to smaller sets. -/
theorem mono (h : HasWeakGradientOn U w G) (hVU : V ⊆ U) : HasWeakGradientOn V w G :=
  ⟨h.1.mono_set hVU, h.2.1.mono_set hVU,
    fun φ hφ hφc hsub e ↦ h.2.2 φ hφ hφc (hsub.trans hVU) e⟩

/-- It suffices to test the directions of an orthonormal basis, e.g. the coordinate directions
`EuclideanSpace.single i 1`. -/
theorem of_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Space d))
    (hw : LocallyIntegrableOn w U) (hG : LocallyIntegrableOn G U)
    (hb : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ i, ∫ y, w y * fderiv ℝ φ y (b i) = -∫ y, inner ℝ (G y) (b i) * φ y) :
    HasWeakGradientOn U w G := by
  refine ⟨hw, hG, fun φ hφ hφc hsub e ↦ ?_⟩
  have he : e = ∑ i, inner ℝ (b i) e • b i := (b.sum_repr' e).symm
  have hl : ∀ y, w y * fderiv ℝ φ y e = ∑ i, inner ℝ (b i) e * (w y * fderiv ℝ φ y (b i)) := by
    intro y
    conv_lhs => rw [he]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hr : ∀ y, inner ℝ (G y) e * φ y =
      ∑ i, inner ℝ (b i) e * (inner ℝ (G y) (b i) * φ y) := by
    intro y
    conv_lhs => rw [he]
    simp only [inner_sum, inner_smul_right, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hli : ∀ i, Integrable (fun y ↦ inner ℝ (b i) e * (w y * fderiv ℝ φ y (b i))) :=
    fun i ↦ (integrable_mul_fderiv_of_locallyIntegrableOn hw hφ hφc hsub (b i)).const_mul _
  have hri : ∀ i, Integrable (fun y ↦ inner ℝ (b i) e * (inner ℝ (G y) (b i) * φ y)) :=
    fun i ↦ (integrable_mul_of_locallyIntegrableOn (locallyIntegrableOn_inner_const hG (b i))
      hφ.continuous hφc hsub).const_mul _
  simp_rw [hl, hr]
  rw [integral_finsetSum _ (fun i _ ↦ hli i), integral_finsetSum _ (fun i _ ↦ hri i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul, hb φ hφ hφc hsub i, mul_neg]

/-- **Uniqueness of weak gradients**: on an open set two weak gradients of the same function
agree almost everywhere. -/
theorem ae_eq (hU : IsOpen U) (h : HasWeakGradientOn U w G) (h' : HasWeakGradientOn U w G') :
    ∀ᵐ y, y ∈ U → G y = G' y := by
  let b := stdOrthonormalBasis ℝ (Space d)
  have hi : ∀ i, ∀ᵐ y, y ∈ U → inner ℝ (G y) (b i) - inner ℝ (G' y) (b i) = 0 := by
    intro i
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrableOn_inner_const h.locallyIntegrableOn_gradient (b i)).sub
        (locallyIntegrableOn_inner_const h'.locallyIntegrableOn_gradient (b i)))
    intro g hg hgc hgs
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
    have h1 := h.integral_eq hg1 hgc hgs (b i)
    have h2 := h'.integral_eq hg1 hgc hgs (b i)
    have hi1 := integrable_mul_of_locallyIntegrableOn
      (locallyIntegrableOn_inner_const h.locallyIntegrableOn_gradient (b i)) hg.continuous hgc hgs
    have hi2 := integrable_mul_of_locallyIntegrableOn
      (locallyIntegrableOn_inner_const h'.locallyIntegrableOn_gradient (b i)) hg.continuous hgc hgs
    have hfun : (fun y ↦ g y • ((fun y ↦ inner ℝ (G y) (b i)) - fun y ↦ inner ℝ (G' y) (b i)) y) =
        fun y ↦ inner ℝ (G y) (b i) * g y - inner ℝ (G' y) (b i) * g y := by
      funext y
      simp only [Pi.sub_apply, smul_eq_mul]
      ring
    rw [hfun, integral_sub hi1 hi2]
    linarith
  rw [← ae_all_iff] at hi
  filter_upwards [hi] with y hy hyU
  rw [← b.sum_repr' (G y), ← b.sum_repr' (G' y)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm, real_inner_comm (G' y), sub_eq_zero.mp (hy i hyU)]

/-- A weak gradient can be modified on a null subset of `U`. -/
theorem congr_ae (h : HasWeakGradientOn U w G) (hU : MeasurableSet U)
    (hGG' : ∀ᵐ y, y ∈ U → G y = G' y) : HasWeakGradientOn U w G' := by
  have hae : G =ᵐ[volume.restrict U] G' := (ae_restrict_iff' hU).mpr hGG'
  refine ⟨h.locallyIntegrableOn, LocallyIntegrableOn.congr hae h.locallyIntegrableOn_gradient,
    fun φ hφ hφc hsub e ↦ ?_⟩
  rw [h.integral_eq hφ hφc hsub e]
  congr 1
  apply integral_congr_ae
  filter_upwards [hGG'] with y hy
  by_cases hyU : y ∈ U
  · rw [hy hyU]
  · have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h' ↦ hyU (hsub h'))
    rw [hφy, mul_zero, mul_zero]

end HasWeakGradientOn

/-- The gradient of a globally Lipschitz function is bounded by the Lipschitz constant. -/
private theorem norm_gradient_le_of_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (y : Space d) : ‖gradient f y‖ ≤ K := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using norm_fderiv_le_of_lipschitz ℝ hf

/-- The gradient of a globally Lipschitz function is locally integrable. -/
private theorem locallyIntegrable_gradient_of_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : LocallyIntegrable (gradient f) volume := by
  rw [locallyIntegrable_iff]
  intro S hS
  have hi : IntegrableOn (fun _ : Space d ↦ (K : ℝ)) S :=
    continuousOn_const.integrableOn_compact hS
  exact hi.mono' (measurable_gradient f).aestronglyMeasurable
    (Eventually.of_forall (fun y ↦ norm_gradient_le_of_lipschitz hf y))

/-- **Consistency for Lipschitz functions**: the almost-everywhere gradient of a globally
Lipschitz function is its weak gradient on every set. -/
theorem hasWeakGradientOn_of_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (U : Set (Space d)) : HasWeakGradientOn U f (gradient f) := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn U,
    (locallyIntegrable_gradient_of_lipschitz hf).locallyIntegrableOn U,
    fun φ hφ hφc _ e ↦ ?_⟩
  simp only [gradient, toDual_symm_apply]
  rw [integral_fderiv_apply_mul_eq_neg_of_lipschitz hf hφ hφc, neg_neg]

/-- **Consistency for `C¹` functions**: the classical gradient of a function that is `C¹` on an
open set is its weak gradient there. -/
theorem hasWeakGradientOn_of_contDiffOn {d : ℕ} {f : Space d → ℝ} {U : Set (Space d)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : HasWeakGradientOn U f (gradient f) := by
  have hcont : ContinuousOn (gradient f) U :=
    (toDual ℝ (Space d)).symm.continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  refine ⟨hf.continuousOn.locallyIntegrableOn hU.measurableSet,
    hcont.locallyIntegrableOn hU.measurableSet, fun φ hφ hφc hsub e ↦ ?_⟩
  rw [integral_mul_fderiv_eq_neg_of_hasCompactSupport hU hf hφ hφc hsub]
  simp only [gradient, toDual_symm_apply]

/-! ### Riesz representation of bounded functionals on test functions -/

/-- A linear functional on an abstract space of test functions which is bounded by the norm of
a linear map into a real Hilbert space is represented by an element of that Hilbert space of
norm at most the bound (Hahn–Banach followed by the Riesz representation theorem). -/
theorem exists_inner_eq_of_abs_le {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : V →ₗ[ℝ] H) (ℓ : V →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, |ℓ v| ≤ C * ‖T v‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ v, ℓ v = inner ℝ g (T v) := by
  have hker : LinearMap.ker T ≤ LinearMap.ker ℓ := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h := hb v
    rw [hv, norm_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  let ℓ₀ : LinearMap.range T →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T).liftQ ℓ hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ v, ℓ₀ ⟨T v, LinearMap.mem_range_self T v⟩ = ℓ v := by
    intro v
    simp only [ℓ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hbd : ∀ y : LinearMap.range T, ‖ℓ₀ y‖ ≤ C * ‖y‖ := by
    rintro ⟨y, v, rfl⟩
    rw [hℓ₀ v, Real.norm_eq_abs]
    exact hb v
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq (LinearMap.range T) (ℓ₀.mkContinuous C hbd)
  refine ⟨(toDual ℝ H).symm g, ?_, fun v ↦ ?_⟩
  · rw [LinearIsometryEquiv.norm_map, hgn]
    exact LinearMap.mkContinuous_norm_le _ hC hbd
  · rw [toDual_symm_apply, hg ⟨T v, LinearMap.mem_range_self T v⟩,
      LinearMap.mkContinuous_apply, hℓ₀]

/-! ### Structure conditions on the flux -/

/-- Structure conditions on a flux `𝒜` on the ball `‖p‖ ≤ L`: it is `C¹`, uniformly elliptic
with constant `lam > 0`, and its derivative is bounded by `Λ`. -/
structure IsEllipticFlux {d : ℕ} (𝒜 : Space d → Space d) (L lam Λ : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 𝒜
  pos : 0 < lam
  elliptic : ∀ p, ‖p‖ ≤ L → ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ 𝒜 p ξ) ξ
  bounded : ∀ p, ‖p‖ ≤ L → ‖fderiv ℝ 𝒜 p‖ ≤ Λ

/-- `u` is a weak solution of `div 𝒜(∇u) = 0` in `U`: `∫ ⟪𝒜(∇u), ∇φ⟫ = 0` for every `C¹` test
function compactly supported in `U`. -/
def IsWeakSolution {d : ℕ} (𝒜 : Space d → Space d) (u : Space d → ℝ) (U : Set (Space d)) :
    Prop :=
  ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ y, inner ℝ (𝒜 (gradient u y)) (gradient φ y) = 0

/-- Points of a segment between two points of a closed ball centered at the origin. -/
private theorem norm_add_smul_sub_le {d : ℕ} {L : ℝ} {p q : Space d} (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖p + t • (q - p)‖ ≤ L := by
  have he : p + t • (q - p) = (1 - t) • p + t • q := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [he]
  calc ‖(1 - t) • p + t • q‖ ≤ ‖(1 - t) • p‖ + ‖t • q‖ := norm_add_le _ _
    _ = (1 - t) * ‖p‖ + t * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
          Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * L + t * L := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hp (by linarith [ht.2])
        · exact mul_le_mul_of_nonneg_left hq ht.1
    _ = L := by ring

namespace IsEllipticFlux

variable {d : ℕ} {𝒜 : Space d → Space d} {L lam Λ : ℝ}

/-- The flux is `Λ`-Lipschitz on the ball `‖p‖ ≤ L`. -/
theorem norm_sub_le (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {p q : Space d} (hp : ‖p‖ ≤ L)
    (hq : ‖q‖ ≤ L) : ‖𝒜 q - 𝒜 p‖ ≤ Λ * ‖q - p‖ := by
  have hp' : p ∈ closedBall (0 : Space d) L := by simpa using hp
  have hq' : q ∈ closedBall (0 : Space d) L := by simpa using hq
  refine (convex_closedBall (0 : Space d) L).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ h𝒜.contDiff.differentiable one_ne_zero x) (fun x hx ↦ h𝒜.bounded x ?_) hp' hq'
  simpa using hx

/-- The flux is strongly monotone on the ball `‖p‖ ≤ L`. -/
theorem inner_sub_ge (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {p q : Space d} (hp : ‖p‖ ≤ L)
    (hq : ‖q‖ ≤ L) : lam * ‖q - p‖ ^ 2 ≤ inner ℝ (𝒜 q - 𝒜 p) (q - p) := by
  set ξ := q - p with hξ
  let g : ℝ → ℝ := fun t ↦ inner ℝ (𝒜 (p + t • ξ)) ξ - lam * t * ‖ξ‖ ^ 2
  have hderiv : ∀ t, HasDerivAt g (inner ℝ (fderiv ℝ 𝒜 (p + t • ξ) ξ) ξ - lam * ‖ξ‖ ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ ↦ p + t • ξ) ξ t := by
      simpa using ((hasDerivAt_id t).smul_const ξ).const_add p
    have h2 : HasDerivAt (fun t ↦ 𝒜 (p + t • ξ)) (fderiv ℝ 𝒜 (p + t • ξ) ξ) t :=
      (h𝒜.contDiff.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t ↦ inner ℝ (𝒜 (p + t • ξ)) ξ)
        (inner ℝ (fderiv ℝ 𝒜 (p + t • ξ) ξ) ξ) t := by
      simpa using h2.inner ℝ (hasDerivAt_const t ξ)
    have h4 : HasDerivAt (fun t ↦ lam * t * ‖ξ‖ ^ 2) (lam * ‖ξ‖ ^ 2) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).mul_const (‖ξ‖ ^ 2)
    exact h3.sub h4
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ ↦ (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have := h𝒜.elliptic _ (norm_add_smul_sub_le hp hq (Set.Ioo_subset_Icc_self ht)) ξ
      linarith
  have h01 := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    zero_le_one
  simp only [g, zero_smul, add_zero, one_smul, mul_zero, zero_mul, sub_zero, mul_one] at h01
  have hpq : p + ξ = q := by rw [hξ]; abel
  rw [hpq] at h01
  rw [inner_sub_left]
  linarith

/-- The flux is bounded on the ball `‖p‖ ≤ L`. -/
theorem exists_bound (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) :
    ∃ M, 0 ≤ M ∧ ∀ p, ‖p‖ ≤ L → ‖𝒜 p‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space d) L).exists_bound_of_continuousOn
    h𝒜.contDiff.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun p hp ↦ (hM p ?_).trans (le_max_left _ _)⟩
  simpa using hp

end IsEllipticFlux

/-! ### Lipschitz test functions -/

/-- Smooth averages of a Lipschitz function are Lipschitz with the same constant. -/
private theorem lipschitzWith_mollify {d : ℕ} {v : Space d → ℝ} {K : NNReal}
    (hv : LipschitzWith K v) (n : ℕ) : LipschitzWith K (mollify v n) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  apply mollify_dist_le hv.continuous n y z
  intro t _
  have hd := hv.dist_le_mul (y - t) (z - t)
  rwa [dist_sub_right] at hd

/-- Smoothing at scale `1 / (n + 1)` enlarges the support by at most that scale. -/
private theorem tsupport_mollify_subset_cthickening {d : ℕ} (φ : Space d → ℝ) (n : ℕ) :
    tsupport (mollify φ n) ⊆ cthickening (1 / ((n : ℝ) + 1)) (tsupport φ) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  by_contra hnot
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards with t
  change (averagingBump d n).normed volume t * φ (x - t) = 0
  by_cases hk : (averagingBump d n).normed volume t = 0
  · rw [hk, zero_mul]
  · have ht : t ∈ ball (0 : Space d) (averagingBump d n).rOut := by
      rw [← (averagingBump d n).support_normed_eq (μ := volume)]
      exact hk
    have hr : (averagingBump d n).rOut = 1 / ((n : ℝ) + 1) := rfl
    have ht' : ‖t‖ < 1 / ((n : ℝ) + 1) := by
      rw [← hr]
      simpa only [mem_ball, dist_zero_right] using ht
    have hφ : φ (x - t) = 0 := by
      by_contra hne
      apply hnot
      apply thickening_subset_cthickening
      rw [mem_thickening_iff]
      refine ⟨x - t, subset_tsupport φ hne, ?_⟩
      rw [dist_eq_norm, sub_sub_cancel]
      exact ht'
    rw [hφ, mul_zero]

/-- A bounded measurable function vanishing outside a ball is integrable. -/
private theorem integrable_of_norm_le_of_eq_zero {d : ℕ} {F : Space d → ℝ} (hF : AEStronglyMeasurable F)
    {B : ℝ} (hB : ∀ y, ‖F y‖ ≤ B) {x : Space d} {ρ : ℝ} (h0 : ∀ y ∉ closedBall x ρ, F y = 0) :
    Integrable F := by
  have hon : IntegrableOn F (closedBall x ρ) :=
    Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne hF
      (Eventually.of_forall (fun y ↦ hB y))
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro y hy
  by_contra hn
  exact hy (h0 y hn)

/-- **Lipschitz test functions.** If a bounded measurable vector field `F` satisfies
`∫ ⟪F, ∇φ⟫ = 0` for every `C¹` test function compactly supported in an open set `U`, then the
same holds for every Lipschitz test function compactly supported in `U`. -/
theorem integral_inner_gradient_eq_zero_of_lipschitz_test {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    {F : Space d → Space d} (hFm : AEStronglyMeasurable F) {M : ℝ} (hFM : ∀ y, ‖F y‖ ≤ M)
    (hF : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ y, inner ℝ (F y) (gradient φ y) = 0)
    {φ : Space d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) :
    ∫ y, inner ℝ (F y) (gradient φ y) = 0 := by
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open hU hsub
  set S := cthickening δ (tsupport φ) with hS
  have hSc : IsCompact S := hφc.isCompact.cthickening
  have hM : 0 ≤ M := (norm_nonneg _).trans (hFM 0)
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hδ)).mono
      (fun n hn ↦ hn)
  have hsupp : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ δ → tsupport (mollify φ n) ⊆ S :=
    fun n hn ↦ (tsupport_mollify_subset_cthickening φ n).trans (cthickening_mono hn _)
  have hzero : ∀ᶠ n : ℕ in atTop, ∫ y, inner ℝ (F y) (gradient (mollify φ n) y) = 0 := by
    filter_upwards [hev] with n hn
    exact hF _ ((mollify_contDiff hφ.continuous n).of_le (by simp))
      (hSc.of_isClosed_subset (isClosed_tsupport _) (hsupp n hn)) ((hsupp n hn).trans hδU)
  have hgrad0 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ δ → ∀ y ∉ S, gradient (mollify φ n) y = 0 := by
    intro n hn y hy
    have hf : fderiv ℝ (mollify φ n) y = 0 := by
      by_contra hne
      exact hy (hsupp n hn (support_fderiv_subset ℝ hne))
    simp only [gradient, hf, map_zero]
  have hlim : Tendsto (fun n ↦ ∫ y, inner ℝ (F y) (gradient (mollify φ n) y)) atTop
      (𝓝 (∫ y, inner ℝ (F y) (gradient φ y))) := by
    apply tendsto_integral_filter_of_dominated_convergence (S.indicator (fun _ ↦ M * K))
    · exact Eventually.of_forall (fun n ↦ hFm.inner (measurable_gradient _).aestronglyMeasurable)
    · filter_upwards [hev] with n hn
      apply Eventually.of_forall
      intro y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        refine (norm_inner_le_norm _ _).trans (mul_le_mul (hFM y) ?_ (norm_nonneg _) hM)
        exact norm_gradient_le_of_lipschitz (lipschitzWith_mollify hφ n) y
      · rw [Set.indicator_of_notMem hy, hgrad0 n hn y hy, inner_zero_right, norm_zero]
    · exact (integrableOn_const hSc.measure_lt_top.ne).integrable_indicator
        hSc.isClosed.measurableSet
    · filter_upwards [mollify_fderiv_tendsto_ae_of_lipschitz hφ] with y hy
      have hg : Tendsto (fun n ↦ gradient (mollify φ n) y) atTop (𝓝 (gradient φ y)) :=
        ((toDual ℝ (Space d)).symm.continuous.tendsto _).comp hy
      exact tendsto_const_nhds.inner hg
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun n hn ↦ hn.symm))

/-- **Translating the weak equation.** If `∫ ⟪F, ∇φ⟫ = 0` for all `C¹` tests compactly supported
in `U`, the translated field `F (· + z)` satisfies the same identity for tests compactly supported
in `(· + z) ⁻¹' U`. -/
theorem integral_inner_gradient_comp_add_eq_zero {d : ℕ} {U : Set (Space d)}
    {F : Space d → Space d}
    (hF : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ y, inner ℝ (F y) (gradient φ y) = 0) (z : Space d)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ (· + z) ⁻¹' U) :
    ∫ y, inner ℝ (F (y + z)) (gradient φ y) = 0 := by
  let ψ : Space d → ℝ := φ ∘ (Homeomorph.addRight (-z))
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph _
  have hψs : tsupport ψ ⊆ U := by
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have h := hsub hy
    simpa using h
  have hgrad : ∀ y, gradient ψ y = gradient φ (y - z) := by
    intro y
    have hfun : ψ = fun y ↦ φ (y + -z) := rfl
    simp only [gradient, hfun, fderiv_comp_add_right, sub_eq_add_neg]
  have h0 := hF ψ hψ hψc hψs
  simp_rw [hgrad] at h0
  have he := integral_add_right_eq_self (μ := volume)
    (fun y ↦ inner ℝ (F y) (gradient φ (y - z))) z
  simp only [add_sub_cancel_right] at he
  rw [he]
  exact h0

/-- A weak solution, tested with Lipschitz test functions. -/
theorem IsWeakSolution.integral_eq_zero_of_lipschitz {d : ℕ} {𝒜 : Space d → Space d}
    {L lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ} {Lu : NNReal}
    (hu : LipschitzWith Lu u) (hL : (Lu : ℝ) ≤ L) {U : Set (Space d)} (hU : IsOpen U)
    (hweak : IsWeakSolution 𝒜 u U) (z : Space d)
    {φ : Space d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ (· + z) ⁻¹' U) :
    ∫ y, inner ℝ (𝒜 (gradient u (y + z))) (gradient φ y) = 0 := by
  obtain ⟨M, _, hM⟩ := h𝒜.exists_bound
  have hgu : ∀ y, ‖gradient u y‖ ≤ L := fun y ↦ (norm_gradient_le_of_lipschitz hu y).trans hL
  have hm : AEStronglyMeasurable (fun y ↦ 𝒜 (gradient u (y + z))) :=
    (h𝒜.contDiff.continuous.measurable.comp
      ((measurable_gradient u).comp (measurable_add_const z))).aestronglyMeasurable
  exact integral_inner_gradient_eq_zero_of_lipschitz_test (F := fun y ↦ 𝒜 (gradient u (y + z)))
    (hU.preimage (continuous_id.add continuous_const)) hm (fun y ↦ hM _ (hgu _))
    (fun ψ hψ hψc hψs ↦ integral_inner_gradient_comp_add_eq_zero hweak z hψ hψc hψs)
    hφ hφc hsub

/-! ### A Lipschitz cutoff and the Caccioppoli inequality for differences -/

/-- The piecewise linear cutoff, equal to `1` on `closedBall x r` and to `0` outside
`ball x ρ`, with slope `1 / (ρ - r)`. -/
def linearCutoff {d : ℕ} (x : Space d) (r ρ : ℝ) (y : Space d) : ℝ :=
  min 1 (max 0 ((ρ - dist y x) / (ρ - r)))

section linearCutoff

variable {d : ℕ} {x : Space d} {r ρ : ℝ}

theorem linearCutoff_nonneg (y : Space d) : 0 ≤ linearCutoff x r ρ y :=
  le_min zero_le_one (le_max_left _ _)

theorem linearCutoff_le_one (y : Space d) : linearCutoff x r ρ y ≤ 1 :=
  min_le_left _ _

theorem linearCutoff_eq_one (hrρ : r < ρ) {y : Space d} (hy : dist y x ≤ r) :
    linearCutoff x r ρ y = 1 := by
  have h1 : 1 ≤ (ρ - dist y x) / (ρ - r) := by
    rw [le_div_iff₀ (sub_pos.mpr hrρ)]
    linarith
  exact min_eq_left (h1.trans (le_max_right _ _))

theorem linearCutoff_eq_zero (hrρ : r < ρ) {y : Space d} (hy : ρ ≤ dist y x) :
    linearCutoff x r ρ y = 0 := by
  have h1 : (ρ - dist y x) / (ρ - r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hrρ).le
  rw [linearCutoff, max_eq_left h1]
  exact min_eq_right zero_le_one

theorem lipschitzWith_linearCutoff (hrρ : r < ρ) :
    LipschitzWith (Real.toNNReal (ρ - r)⁻¹) (linearCutoff x r ρ) := by
  have hpos : 0 < ρ - r := sub_pos.mpr hrρ
  have hlin : LipschitzWith (Real.toNNReal (ρ - r)⁻¹)
      (fun y : Space d ↦ (ρ - dist y x) / (ρ - r)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.mpr hpos.le), ← sub_div, abs_div,
      abs_of_pos hpos, div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
    have h := abs_dist_sub_le y z x
    rw [abs_sub_comm] at h
    calc |ρ - dist y x - (ρ - dist z x)| = |dist z x - dist y x| := by ring_nf
      _ ≤ dist y z := by rw [abs_sub_comm]; exact abs_dist_sub_le y z x
  exact (hlin.const_max 0).const_min 1

theorem tsupport_linearCutoff_subset (hrρ : r < ρ) :
    tsupport (linearCutoff x r ρ) ⊆ closedBall x ρ := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra hn
  apply hy
  apply linearCutoff_eq_zero hrρ
  rw [mem_closedBall, not_le] at hn
  exact hn.le

theorem hasCompactSupport_linearCutoff (hrρ : r < ρ) :
    HasCompactSupport (linearCutoff x r ρ) :=
  (isCompact_closedBall x ρ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_linearCutoff_subset hrρ)

theorem norm_gradient_linearCutoff_le (hrρ : r < ρ) (y : Space d) :
    ‖gradient (linearCutoff x r ρ) y‖ ≤ (ρ - r)⁻¹ := by
  have h := norm_gradient_le_of_lipschitz (lipschitzWith_linearCutoff (x := x) hrρ) y
  rwa [Real.coe_toNNReal _ (inv_nonneg.mpr (sub_pos.mpr hrρ).le)] at h

end linearCutoff

/-- The gradient of a function vanishes off its topological support. -/
private theorem gradient_eq_zero_of_notMem_tsupport {d : ℕ} {f : Space d → ℝ} {y : Space d}
    (hy : y ∉ tsupport f) : gradient f y = 0 := by
  have hf : fderiv ℝ f y = 0 := by
    by_contra hne
    exact hy (support_fderiv_subset ℝ hne)
  simp only [gradient, hf, map_zero]

/-- A product of bounded Lipschitz functions is Lipschitz. -/
private theorem exists_lipschitzWith_mul {d : ℕ} {f g : Space d → ℝ} {Kf Kg : NNReal}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) {A B : ℝ} (hA : ∀ y, |f y| ≤ A)
    (hB : ∀ y, |g y| ≤ B) : ∃ K, LipschitzWith K (fun y ↦ f y * g y) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨Real.toNNReal (A * Kg + B * Kf), LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have h1 := hf.dist_le_mul y z
  have h2 := hg.dist_le_mul y z
  rw [Real.dist_eq] at h1 h2
  have he : f y * g y - f z * g z = f y * (g y - g z) + g z * (f y - f z) := by ring
  rw [he]
  calc |f y * (g y - g z) + g z * (f y - f z)|
      ≤ |f y * (g y - g z)| + |g z * (f y - f z)| := abs_add_le _ _
    _ = |f y| * |g y - g z| + |g z| * |f y - f z| := by rw [abs_mul, abs_mul]
    _ ≤ A * (Kg * dist y z) + B * (Kf * dist y z) :=
        add_le_add (mul_le_mul (hA y) h2 (abs_nonneg _) hA0)
          (mul_le_mul (hB z) h1 (abs_nonneg _) hB0)
    _ = (A * Kg + B * Kf) * dist y z := by ring

/-- The gradient of `η² (u(· + z) - u)` at a point where `η`, `u` and `u(· + z)` are
differentiable, paired with a vector `a`. -/
private theorem inner_gradient_sq_mul_sub {d : ℕ} {u η : Space d → ℝ} {z y : Space d}
    (hu0 : DifferentiableAt ℝ u y) (hu1 : DifferentiableAt ℝ u (y + z))
    (hη : DifferentiableAt ℝ η y) (a : Space d) :
    inner ℝ a (gradient (fun y ↦ η y * η y * (u (y + z) - u y)) y) =
      η y * η y * inner ℝ a (gradient u (y + z) - gradient u y) +
        2 * η y * (u (y + z) - u y) * inner ℝ a (gradient η y) := by
  have h1 : HasFDerivAt (fun y ↦ u (y + z)) (fderiv ℝ u (y + z)) y :=
    (hasFDerivAt_comp_add_right z).2 hu1.hasFDerivAt
  have hδ : HasFDerivAt (fun y ↦ u (y + z) - u y) (fderiv ℝ u (y + z) - fderiv ℝ u y) y :=
    h1.sub hu0.hasFDerivAt
  have hηη : HasFDerivAt (fun y ↦ η y * η y) (η y • fderiv ℝ η y + η y • fderiv ℝ η y) y :=
    hη.hasFDerivAt.mul hη.hasFDerivAt
  have hfd : fderiv ℝ (fun y ↦ η y * η y * (u (y + z) - u y)) y =
      (η y * η y) • (fderiv ℝ u (y + z) - fderiv ℝ u y) +
        (u (y + z) - u y) • (η y • fderiv ℝ η y + η y • fderiv ℝ η y) :=
    (hηη.mul hδ).fderiv
  rw [real_inner_comm, gradient, toDual_symm_apply, hfd]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, smul_eq_mul,
    inner_sub_right]
  rw [real_inner_comm (gradient u (y + z)) a, real_inner_comm (gradient u y) a,
    real_inner_comm (gradient η y) a]
  simp only [gradient, toDual_symm_apply]
  ring

/-- The pointwise algebra behind the Caccioppoli inequality. -/
private theorem caccioppoli_difference_pointwise {d : ℕ} {lam Λ η δ : ℝ} (hlam : 0 < lam) (hη : 0 ≤ η)
    {a ξ g : Space d} (hmono : lam * ‖ξ‖ ^ 2 ≤ inner ℝ a ξ) (hlip : ‖a‖ ≤ Λ * ‖ξ‖) :
    lam / 2 * (η * η * ‖ξ‖ ^ 2) ≤
      (η * η * inner ℝ a ξ + 2 * η * δ * inner ℝ a g) +
        2 * Λ ^ 2 / lam * (δ ^ 2 * ‖g‖ ^ 2) := by
  have hΛ : 0 ≤ Λ * ‖ξ‖ := (norm_nonneg a).trans hlip
  have h1 : lam * (η * η * ‖ξ‖ ^ 2) ≤ η * η * inner ℝ a ξ := by
    have := mul_le_mul_of_nonneg_left hmono (mul_nonneg hη hη)
    linarith
  have h2 : |inner ℝ a g| ≤ Λ * ‖ξ‖ * ‖g‖ :=
    (abs_real_inner_le_norm a g).trans (mul_le_mul_of_nonneg_right hlip (norm_nonneg g))
  have h3 : |2 * η * δ * inner ℝ a g| ≤ 2 * (η * ‖ξ‖) * (Λ * |δ| * ‖g‖) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hη]
    calc 2 * η * |δ| * |inner ℝ a g| ≤ 2 * η * |δ| * (Λ * ‖ξ‖ * ‖g‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * (η * ‖ξ‖) * (Λ * |δ| * ‖g‖) := by ring
  have h4 : 2 * (η * ‖ξ‖) * (Λ * |δ| * ‖g‖) ≤
      lam / 2 * (η * ‖ξ‖) ^ 2 + 2 / lam * (Λ * |δ| * ‖g‖) ^ 2 := by
    have key : lam / 2 * (η * ‖ξ‖) ^ 2 + 2 / lam * (Λ * |δ| * ‖g‖) ^ 2 -
        2 * (η * ‖ξ‖) * (Λ * |δ| * ‖g‖) =
        (lam * (η * ‖ξ‖) - 2 * (Λ * |δ| * ‖g‖)) ^ 2 / (2 * lam) := by
      field_simp
      ring
    have hk : 0 ≤ (lam * (η * ‖ξ‖) - 2 * (Λ * |δ| * ‖g‖)) ^ 2 / (2 * lam) := by positivity
    linarith
  have h5 : 2 / lam * (Λ * |δ| * ‖g‖) ^ 2 = 2 * Λ ^ 2 / lam * (δ ^ 2 * ‖g‖ ^ 2) := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have h6 : lam / 2 * (η * ‖ξ‖) ^ 2 = lam / 2 * (η * η * ‖ξ‖ ^ 2) := by ring
  have h7 := neg_abs_le (2 * η * δ * inner ℝ a g)
  linarith

/-- **Caccioppoli inequality for differences.** Let `u` be an `L`-Lipschitz weak solution of
`div 𝒜(∇u) = 0` in `ball x₀ R`. If `r < ρ` and `ρ + ‖z‖ < R`, then
`∫_{B_r} ‖∇u(y + z) - ∇u(y)‖² ≤ 4 (Λ/λ)² (L ‖z‖)² |B̄_ρ| / (ρ - r)²`. -/
theorem IsWeakSolution.integral_norm_gradient_sub_sq_le {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ} (hweak : IsWeakSolution 𝒜 u (ball x₀ R))
    {r ρ : ℝ} (hrρ : r < ρ) {z : Space d} (hz : ρ + ‖z‖ < R) :
    ∫ y in ball x₀ r, ‖gradient u (y + z) - gradient u y‖ ^ 2 ≤
      4 * (Λ / lam) ^ 2 * ((L : ℝ) * ‖z‖) ^ 2 * volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2 := by
  have hlam := h𝒜.pos
  have hρr : 0 < ρ - r := sub_pos.mpr hrρ
  set η := linearCutoff x₀ r ρ with hη_def
  set δ : Space d → ℝ := fun y ↦ u (y + z) - u y with hδ_def
  set φ : Space d → ℝ := fun y ↦ η y * η y * δ y with hφ_def
  -- elementary bounds
  have hgu : ∀ y, ‖gradient u y‖ ≤ L := norm_gradient_le_of_lipschitz hu
  have hδb : ∀ y, |δ y| ≤ L * ‖z‖ := by
    intro y
    have h := hu.dist_le_mul (y + z) y
    rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h
  have hηlip : LipschitzWith (Real.toNNReal (ρ - r)⁻¹) η := lipschitzWith_linearCutoff hrρ
  have hη0 : ∀ y, 0 ≤ η y := linearCutoff_nonneg
  have hη1 : ∀ y, η y ≤ 1 := linearCutoff_le_one
  have hηabs : ∀ y, |η y| ≤ 1 := fun y ↦ by rw [abs_of_nonneg (hη0 y)]; exact hη1 y
  have hηηabs : ∀ y, |η y * η y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (mul_nonneg (hη0 y) (hη0 y))]
    nlinarith [hη0 y, hη1 y]
  have hδlip : LipschitzWith (L + L) δ := by
    have h1 : LipschitzWith L (fun y ↦ u (y + z)) := LipschitzWith.of_dist_le_mul fun y y' ↦ by
      simpa only [dist_add_right] using hu.dist_le_mul (y + z) (y' + z)
    exact h1.sub hu
  obtain ⟨K₁, hK₁⟩ := exists_lipschitzWith_mul hηlip hηlip hηabs hηabs
  obtain ⟨Kφ, hφlip⟩ := exists_lipschitzWith_mul hK₁ hδlip hηηabs hδb
  -- support of the test function
  have hη0out : ∀ y ∉ closedBall x₀ ρ, η y = 0 := by
    intro y hy
    rw [mem_closedBall, not_le] at hy
    exact linearCutoff_eq_zero hrρ hy.le
  have hφ0 : ∀ y ∉ closedBall x₀ ρ, φ y = 0 := by
    intro y hy
    simp only [φ, hη0out y hy, zero_mul]
  have hφts : tsupport φ ⊆ closedBall x₀ ρ := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra hn
    exact hy (hφ0 y hn)
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall x₀ ρ).of_isClosed_subset (isClosed_tsupport _) hφts
  have hφgrad0 : ∀ y ∉ closedBall x₀ ρ, gradient φ y = 0 :=
    fun y hy ↦ gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hφts h))
  have hηgrad0 : ∀ y ∉ closedBall x₀ ρ, gradient η y = 0 :=
    fun y hy ↦ gradient_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (tsupport_linearCutoff_subset hrρ h))
  -- the equation and its translate, tested with `φ`
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hsubz : tsupport φ ⊆ (· + z) ⁻¹' ball x₀ R := by
    intro y hy
    have hy' := hφts hy
    rw [mem_closedBall] at hy'
    change dist (y + z) x₀ < R
    calc dist (y + z) x₀ ≤ dist (y + z) y + dist y x₀ := dist_triangle _ _ _
      _ = ‖z‖ + dist y x₀ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ < R := by linarith
  have hsub0 : tsupport φ ⊆ (· + 0) ⁻¹' ball x₀ R := by
    intro y hy
    have hy' := hφts hy
    rw [mem_closedBall] at hy'
    change dist (y + 0) x₀ < R
    rw [add_zero]
    linarith
  have heq1 : ∫ y, inner ℝ (𝒜 (gradient u (y + z))) (gradient φ y) = 0 :=
    IsWeakSolution.integral_eq_zero_of_lipschitz h𝒜 hu le_rfl isOpen_ball hweak z
      hφlip hφc hsubz
  have heq0' : ∫ y, inner ℝ (𝒜 (gradient u (y + 0))) (gradient φ y) = 0 :=
    IsWeakSolution.integral_eq_zero_of_lipschitz h𝒜 hu le_rfl isOpen_ball hweak 0
      hφlip hφc hsub0
  have heq0 : ∫ y, inner ℝ (𝒜 (gradient u y)) (gradient φ y) = 0 := by
    simpa only [add_zero] using heq0'
  obtain ⟨M, hM0, hM⟩ := h𝒜.exists_bound
  have hφgb : ∀ y, ‖gradient φ y‖ ≤ Kφ := norm_gradient_le_of_lipschitz hφlip
  have hint : ∀ w : Space d,
      Integrable (fun y ↦ inner ℝ (𝒜 (gradient u (y + w))) (gradient φ y)) := by
    intro w
    refine integrable_of_norm_le_of_eq_zero (B := M * Kφ) (x := x₀) (ρ := ρ) ?_ ?_ ?_
    · exact ((h𝒜.contDiff.continuous.measurable.comp ((measurable_gradient u).comp
        (measurable_add_const w))).aestronglyMeasurable).inner
        (measurable_gradient φ).aestronglyMeasurable
    · intro y
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hM _ (hgu _)) (hφgb y) (norm_nonneg _) hM0)
    · intro y hy
      rw [hφgrad0 y hy, inner_zero_right]
  have hint0 := hint 0
  simp only [add_zero] at hint0
  set I : Space d → ℝ := fun y ↦
    inner ℝ (𝒜 (gradient u (y + z)) - 𝒜 (gradient u y)) (gradient φ y) with hI_def
  have hIfun : I = fun y ↦ inner ℝ (𝒜 (gradient u (y + z))) (gradient φ y) -
      inner ℝ (𝒜 (gradient u y)) (gradient φ y) := by
    funext y
    simp only [I, inner_sub_left]
  have hIi : Integrable I := by
    rw [hIfun]
    exact (hint z).sub hint0
  have hIint : ∫ y, I y = 0 := by
    rw [hIfun, integral_sub (hint z) hint0, heq1, heq0, sub_zero]
  -- the almost-everywhere identity
  have hae : ∀ᵐ y, I y = η y * η y * inner ℝ (𝒜 (gradient u (y + z)) - 𝒜 (gradient u y))
      (gradient u (y + z) - gradient u y) +
      2 * η y * δ y * inner ℝ (𝒜 (gradient u (y + z)) - 𝒜 (gradient u y)) (gradient η y) := by
    have h0 := hu.ae_differentiableAt (μ := volume)
    have h1 : ∀ᵐ y, DifferentiableAt ℝ u (y + z) :=
      (measurePreserving_add_right volume z).quasiMeasurePreserving.ae h0
    have h2 := hηlip.ae_differentiableAt (μ := volume)
    filter_upwards [h0, h1, h2] with y hy0 hy1 hy2
    exact inner_gradient_sq_mul_sub hy0 hy1 hy2 _
  -- the energy quantities
  set J : Space d → ℝ := fun y ↦ η y * η y * ‖gradient u (y + z) - gradient u y‖ ^ 2
    with hJ_def
  set E : Space d → ℝ := fun y ↦ δ y ^ 2 * ‖gradient η y‖ ^ 2 with hE_def
  have hJ0 : ∀ y, 0 ≤ J y := fun y ↦ mul_nonneg (mul_nonneg (hη0 y) (hη0 y)) (sq_nonneg _)
  have hJi : Integrable J := by
    refine integrable_of_norm_le_of_eq_zero (B := (2 * L) ^ 2) (x := x₀) (ρ := ρ) ?_ ?_ ?_
    · exact ((hηlip.continuous.mul hηlip.continuous).measurable.mul
        ((((measurable_gradient u).comp (measurable_add_const z)).sub
          (measurable_gradient u)).norm.pow_const 2)).aestronglyMeasurable
    · intro y
      rw [Real.norm_of_nonneg (hJ0 y)]
      have hd : ‖gradient u (y + z) - gradient u y‖ ≤ 2 * L :=
        (norm_sub_le _ _).trans (by linarith [hgu (y + z), hgu y])
      have hd2 : ‖gradient u (y + z) - gradient u y‖ ^ 2 ≤ (2 * L) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd 2
      have hηη : η y * η y ≤ 1 := by nlinarith [hη0 y, hη1 y]
      calc η y * η y * ‖gradient u (y + z) - gradient u y‖ ^ 2
          ≤ 1 * (2 * L) ^ 2 := mul_le_mul hηη hd2 (sq_nonneg _) zero_le_one
        _ = (2 * L) ^ 2 := one_mul _
    · intro y hy
      simp only [J, hη0out y hy, zero_mul]
  have hE0 : ∀ y, 0 ≤ E y := fun y ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hEb : ∀ y, E y ≤ ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2 := by
    intro y
    have h1 : δ y ^ 2 ≤ ((L : ℝ) * ‖z‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hδb y) 2
    have h2 : ‖gradient η y‖ ^ 2 ≤ ((ρ - r)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_linearCutoff_le hrρ y) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  have hEi : Integrable E := by
    refine integrable_of_norm_le_of_eq_zero (B := ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2)
      (x := x₀) (ρ := ρ) ?_ ?_ ?_
    · exact ((hδlip.continuous.measurable.pow_const 2).mul
        ((measurable_gradient η).norm.pow_const 2)).aestronglyMeasurable
    · intro y
      rw [Real.norm_of_nonneg (hE0 y)]
      exact hEb y
    · intro y hy
      simp only [E, hηgrad0 y hy, norm_zero]
      ring
  -- the pointwise inequality
  have hpt : ∀ᵐ y, lam / 2 * J y ≤ I y + 2 * Λ ^ 2 / lam * E y := by
    filter_upwards [hae] with y hy
    rw [hy]
    exact caccioppoli_difference_pointwise hlam (hη0 y) (h𝒜.inner_sub_ge (hgu y) (hgu (y + z)))
      (h𝒜.norm_sub_le (hgu y) (hgu (y + z)))
  have hmain : lam / 2 * ∫ y, J y ≤ 2 * Λ ^ 2 / lam * ∫ y, E y := by
    have hIE : Integrable (fun y ↦ I y + 2 * Λ ^ 2 / lam * E y) := hIi.add (hEi.const_mul _)
    have h : ∫ y, lam / 2 * J y ≤ ∫ y, (I y + 2 * Λ ^ 2 / lam * E y) :=
      integral_mono_ae (hJi.const_mul (lam / 2)) hIE hpt
    rw [integral_const_mul, integral_add hIi (hEi.const_mul _), integral_const_mul, hIint,
      zero_add] at h
    exact h
  have hJE : ∫ y, J y ≤ 4 * (Λ / lam) ^ 2 * ∫ y, E y := by
    have h := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 2 / lam)
    have e1 : 2 / lam * (lam / 2 * ∫ y, J y) = ∫ y, J y := by
      field_simp
    have e2 : 2 / lam * (2 * Λ ^ 2 / lam * ∫ y, E y) = 4 * (Λ / lam) ^ 2 * ∫ y, E y := by
      field_simp
      ring
    rw [e1, e2] at h
    exact h
  have hEint : ∫ y, E y ≤ ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2 *
      volume.real (closedBall x₀ ρ) := by
    have hind : Integrable ((closedBall x₀ ρ).indicator
        (fun _ ↦ ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2)) :=
      (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    have hle : ∀ y, E y ≤ (closedBall x₀ ρ).indicator
        (fun _ ↦ ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2) y := by
      intro y
      by_cases hy : y ∈ closedBall x₀ ρ
      · rw [Set.indicator_of_mem hy]
        exact hEb y
      · rw [Set.indicator_of_notMem hy]
        simp only [E, hηgrad0 y hy, norm_zero]
        ring_nf
        exact le_rfl
    calc ∫ y, E y ≤ ∫ y, (closedBall x₀ ρ).indicator
          (fun _ ↦ ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2) y := integral_mono hEi hind hle
      _ = volume.real (closedBall x₀ ρ) • (((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2) :=
          integral_indicator_const _ measurableSet_closedBall
      _ = ((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2 * volume.real (closedBall x₀ ρ) := by
          rw [smul_eq_mul, mul_comm]
  have hJr : ∫ y in ball x₀ r, ‖gradient u (y + z) - gradient u y‖ ^ 2 ≤ ∫ y, J y := by
    calc ∫ y in ball x₀ r, ‖gradient u (y + z) - gradient u y‖ ^ 2
        = ∫ y in ball x₀ r, J y := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          have h1 : η y = 1 := linearCutoff_eq_one hrρ (le_of_lt hy)
          simp only [J, h1, one_mul]
      _ ≤ ∫ y, J y := setIntegral_le_integral hJi (Eventually.of_forall hJ0)
  calc ∫ y in ball x₀ r, ‖gradient u (y + z) - gradient u y‖ ^ 2 ≤ ∫ y, J y := hJr
    _ ≤ 4 * (Λ / lam) ^ 2 * ∫ y, E y := hJE
    _ ≤ 4 * (Λ / lam) ^ 2 * (((L : ℝ) * ‖z‖) ^ 2 * ((ρ - r)⁻¹) ^ 2 *
        volume.real (closedBall x₀ ρ)) := mul_le_mul_of_nonneg_left hEint (by positivity)
    _ = 4 * (Λ / lam) ^ 2 * ((L : ℝ) * ‖z‖) ^ 2 * volume.real (closedBall x₀ ρ) /
        (ρ - r) ^ 2 := by
        field_simp

/-! ### `L²` bookkeeping -/

section L2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The squared norm of an element of `L²` is the integral of its square. -/
private theorem norm_sq_Lp_two_eq_integral (G : Lp ℝ 2 μ) : ‖G‖ ^ 2 = ∫ x, G x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The `L²` norm of a square-integrable function. -/
private theorem norm_toLp_two_eq_sqrt {f : X → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_Lp_two_eq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- The `L²` pairing of an `L²` class with a square-integrable function. -/
private theorem inner_toLp_two_eq_integral (g : Lp ℝ 2 μ) {f : X → ℝ} (hf : MemLp f 2 μ) :
    inner ℝ g (hf.toLp f) = ∫ x, g x * f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The Cauchy–Schwarz inequality in `L²`. -/
private theorem abs_integral_mul_le_sqrt_mul_sqrt {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [inner_toLp_two_eq_integral, norm_toLp_two_eq_sqrt, norm_toLp_two_eq_sqrt] at h
  have he : ∫ x, (hf.toLp f : X → ℝ) x * g x ∂μ = ∫ x, f x * g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rwa [he] at h

end L2

/-! ### Weak derivatives from `L²` bounds -/

/-- `C¹` test functions compactly supported in `U`, as a real vector space. -/
def testFunctions {d : ℕ} (U : Set (Space d)) : Submodule ℝ (Space d → ℝ) where
  carrier := {φ | ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    exact ⟨h1.add k1, h2.add k2, (tsupport_add φ ψ).trans (Set.union_subset h3 k3)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3⟩
    exact ⟨contDiff_const.smul h1, h2.smul_left (f := fun _ ↦ c),
      (tsupport_smul_subset_right (fun _ ↦ c) φ).trans h3⟩

theorem memLp_two_of_mem_testFunctions {d : ℕ} {U : Set (Space d)} (φ : testFunctions U) :
    MemLp (φ : Space d → ℝ) 2 (volume.restrict U) :=
  φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1

/-- The `L²(U)` class of a test function, as a linear map. -/
def testToLp {d : ℕ} (U : Set (Space d)) : testFunctions U →ₗ[ℝ] Lp ℝ 2 (volume.restrict U) where
  toFun φ := (memLp_two_of_mem_testFunctions φ).toLp (φ : Space d → ℝ)
  map_add' φ ψ := by
    have hφ := memLp_two_of_mem_testFunctions φ
    have hψ := memLp_two_of_mem_testFunctions ψ
    have hφψ := memLp_two_of_mem_testFunctions (φ + ψ)
    apply Lp.ext
    filter_upwards [hφψ.coeFn_toLp, Lp.coeFn_add (hφ.toLp (φ : Space d → ℝ))
      (hψ.toLp (ψ : Space d → ℝ)), hφ.coeFn_toLp, hψ.coeFn_toLp] with y h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    rfl
  map_smul' c φ := by
    have hφ := memLp_two_of_mem_testFunctions φ
    have hcφ := memLp_two_of_mem_testFunctions (c • φ)
    apply Lp.ext
    filter_upwards [hcφ.coeFn_toLp, Lp.coeFn_smul c (hφ.toLp (φ : Space d → ℝ)),
      hφ.coeFn_toLp] with y h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3]
    rfl

theorem testToLp_apply {d : ℕ} {U : Set (Space d)} (φ : testFunctions U) :
    testToLp U φ = (memLp_two_of_mem_testFunctions φ).toLp (φ : Space d → ℝ) := rfl

/-- Pairing with the derivative of test functions in a fixed direction, as a linear map. -/
def testDerivPairing {d : ℕ} {U : Set (Space d)} {a : Space d → ℝ}
    (ha : LocallyIntegrableOn a U) (e : Space d) : testFunctions U →ₗ[ℝ] ℝ where
  toFun φ := ∫ y, a y * fderiv ℝ (φ : Space d → ℝ) y e
  map_add' φ ψ := by
    have hφ := integrable_mul_fderiv_of_locallyIntegrableOn ha φ.2.1 φ.2.2.1 φ.2.2.2 e
    have hψ := integrable_mul_fderiv_of_locallyIntegrableOn ha ψ.2.1 ψ.2.2.1 ψ.2.2.2 e
    have hfun : (fun y ↦ a y * fderiv ℝ ((φ + ψ : testFunctions U) : Space d → ℝ) y e) =
        fun y ↦ a y * fderiv ℝ (φ : Space d → ℝ) y e + a y * fderiv ℝ (ψ : Space d → ℝ) y e := by
      funext y
      rw [Submodule.coe_add, fderiv_add (φ.2.1.differentiable one_ne_zero y)
        (ψ.2.1.differentiable one_ne_zero y)]
      simp only [_root_.add_apply]
      ring
    rw [hfun, integral_add hφ hψ]
  map_smul' c φ := by
    have hfun : (fun y ↦ a y * fderiv ℝ ((c • φ : testFunctions U) : Space d → ℝ) y e) =
        fun y ↦ c * (a y * fderiv ℝ (φ : Space d → ℝ) y e) := by
      funext y
      rw [Submodule.coe_smul, fderiv_const_smul (φ.2.1.differentiable one_ne_zero y)]
      simp only [_root_.smul_apply, smul_eq_mul]
      ring
    rw [hfun, integral_const_mul]
    rfl

theorem testDerivPairing_apply {d : ℕ} {U : Set (Space d)} {a : Space d → ℝ}
    (ha : LocallyIntegrableOn a U) (e : Space d) (φ : testFunctions U) :
    testDerivPairing ha e φ = ∫ y, a y * fderiv ℝ (φ : Space d → ℝ) y e := rfl

/-- **An `L²` criterion for weak directional derivatives.** If `|∫ a ∂ₑφ| ≤ C ‖φ‖_{L²(U)}` for
all `C¹` test functions compactly supported in `U`, then there is `g ∈ L²(U)` with
`‖g‖_{L²(U)} ≤ C` and `∫ a ∂ₑφ = -∫_U g φ`. -/
theorem exists_weakDeriv_of_abs_integral_le {d : ℕ} {U : Set (Space d)}
    {a : Space d → ℝ} (ha : LocallyIntegrableOn a U) (e : Space d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      |∫ y, a y * fderiv ℝ φ y e| ≤ C * Real.sqrt (∫ y in U, φ y ^ 2)) :
    ∃ g : Space d → ℝ, MemLp g 2 (volume.restrict U) ∧ ∫ y in U, g y ^ 2 ≤ C ^ 2 ∧
      ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ y, a y * fderiv ℝ φ y e = -∫ y in U, g y * φ y := by
  have hbound : ∀ φ : testFunctions U, |(-testDerivPairing ha e) φ| ≤ C * ‖testToLp U φ‖ := by
    intro φ
    rw [LinearMap.neg_apply, testDerivPairing_apply, testToLp_apply, abs_neg,
      norm_toLp_two_eq_sqrt]
    exact hb φ φ.2.1 φ.2.2.1 φ.2.2.2
  obtain ⟨w, hw, hrep⟩ := exists_inner_eq_of_abs_le (testToLp U) (-testDerivPairing ha e) hC hbound
  refine ⟨w, Lp.memLp w, ?_, fun φ hφ hφc hsub ↦ ?_⟩
  · rw [← norm_sq_Lp_two_eq_integral]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  · have h := hrep ⟨φ, hφ, hφc, hsub⟩
    rw [LinearMap.neg_apply, testDerivPairing_apply, testToLp_apply,
      inner_toLp_two_eq_integral] at h
    have h' : ∫ y, a y * fderiv ℝ φ y e = -∫ y in U, w y * φ y := by
      rw [← h, neg_neg]
    exact h'

/-- **An `L²` criterion for weak gradients.** If `|∫ a ∂ₑφ| ≤ C ‖e‖ ‖φ‖_{L²(U)}` for all
directions `e` and all `C¹` test functions compactly supported in the set `U` of finite measure,
then `a` has a weak gradient `G ∈ L²(U)` on `U` with `∫_U ‖G‖² ≤ d C²`. -/
theorem exists_hasWeakGradientOn_of_abs_integral_le {d : ℕ} {U : Set (Space d)}
    (hUf : volume U ≠ ⊤) {a : Space d → ℝ} (ha : LocallyIntegrableOn a U) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ e : Space d, |∫ y, a y * fderiv ℝ φ y e| ≤ C * ‖e‖ * Real.sqrt (∫ y in U, φ y ^ 2)) :
    ∃ G : Space d → Space d, HasWeakGradientOn U a G ∧ MemLp G 2 (volume.restrict U) ∧
      ∫ y in U, ‖G y‖ ^ 2 ≤ d * C ^ 2 := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hUf
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hb' : ∀ i, ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      |∫ y, a y * fderiv ℝ φ y (b i)| ≤ C * Real.sqrt (∫ y in U, φ y ^ 2) := by
    intro i φ hφ hφc hsub
    have h := hb φ hφ hφc hsub (b i)
    rwa [b.norm_eq_one, mul_one] at h
  choose g hg hg2 hgeq using fun i ↦ exists_weakDeriv_of_abs_integral_le ha (b i) hC (hb' i)
  let G : Space d → Space d := fun y ↦ ∑ i, g i y • b i
  have hGi : ∀ y i, inner ℝ (G y) (b i) = g i y := by
    intro y i
    have h := b.orthonormal.inner_left_sum (fun j ↦ g j y) (Finset.mem_univ i)
    simpa only [conj_trivial] using h
  have hGnorm : ∀ y, ‖G y‖ ^ 2 = ∑ i, g i y ^ 2 := by
    intro y
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner (G y) (G y)]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (G y) (b i), hGi, sq]
  have hGm : MemLp G 2 (volume.restrict U) := by
    have hfun : G = ∑ i, fun y ↦ g i y • b i := by
      funext y
      simp only [G, Finset.sum_apply]
    rw [hfun]
    apply memLp_finsetSum'
    intro i _
    refine (hg i).of_le ((hg i).aestronglyMeasurable.smul_const (b i))
      (Eventually.of_forall (fun y ↦ ?_))
    rw [norm_smul, b.norm_eq_one, mul_one]
  have hGint : IntegrableOn G U := hGm.integrable one_le_two
  refine ⟨G, ?_, hGm, ?_⟩
  · refine HasWeakGradientOn.of_orthonormalBasis b ha hGint.locallyIntegrableOn
      (fun φ hφ hφc hsub i ↦ ?_)
    rw [hgeq i φ hφ hφc hsub]
    congr 1
    simp_rw [hGi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsub h)), mul_zero]
  · simp_rw [hGnorm]
    rw [integral_finsetSum _ (fun i _ ↦ (hg i).integrable_sq)]
    calc ∑ i, ∫ y in U, g i y ^ 2 ≤ ∑ _i : Fin d, C ^ 2 :=
          Finset.sum_le_sum (fun i _ ↦ hg2 i)
      _ = d * C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Difference quotients -/

/-- The difference quotient `D_h^v u (y) = (u (y + h v) - u y) / h`. -/
def diffQuot {d : ℕ} (u : Space d → ℝ) (v : Space d) (h : ℝ) (y : Space d) : ℝ :=
  (u (y + h • v) - u y) / h

section diffQuot

variable {d : ℕ} {u : Space d → ℝ} {L : NNReal}

/-- Difference quotients of an `L`-Lipschitz function are bounded by `L ‖v‖`. -/
theorem abs_diffQuot_le (hu : LipschitzWith L u) (v : Space d) {h : ℝ} (hh : h ≠ 0)
    (y : Space d) : |diffQuot u v h y| ≤ L * ‖v‖ := by
  have hd := hu.dist_le_mul (y + h • v) y
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hd
  rw [diffQuot, abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  calc |u (y + h • v) - u y| ≤ L * (|h| * ‖v‖) := hd
    _ = L * ‖v‖ * |h| := by ring

/-- Difference quotients of a Lipschitz function are Lipschitz (with a constant depending on
`h`). -/
theorem lipschitzWith_diffQuot (hu : LipschitzWith L u) (v : Space d) (h : ℝ) :
    LipschitzWith (Real.toNNReal (|h|⁻¹ * (2 * L))) (diffQuot u v h) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, diffQuot, diffQuot, ← sub_div,
    abs_div]
  have h1 := hu.dist_le_mul (y + h • v) (y' + h • v)
  have h2 := hu.dist_le_mul y y'
  rw [dist_add_right] at h1
  rw [Real.dist_eq] at h1 h2
  have h3 : |u (y + h • v) - u y - (u (y' + h • v) - u y')| ≤ 2 * L * dist y y' := by
    have he : u (y + h • v) - u y - (u (y' + h • v) - u y') =
        (u (y + h • v) - u (y' + h • v)) - (u y - u y') := by ring
    rw [he]
    calc |(u (y + h • v) - u (y' + h • v)) - (u y - u y')|
        ≤ |u (y + h • v) - u (y' + h • v)| + |u y - u y'| := abs_sub _ _
      _ ≤ L * dist y y' + L * dist y y' := add_le_add h1 h2
      _ = 2 * L * dist y y' := by ring
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [abs_zero, div_zero, inv_zero, zero_mul]
    exact le_rfl
  · rw [div_le_iff₀ (abs_pos.mpr hh)]
    calc |u (y + h • v) - u y - (u (y' + h • v) - u y')| ≤ 2 * L * dist y y' := h3
      _ = |h|⁻¹ * (2 * L) * dist y y' * |h| := by
          field_simp

/-- The derivative of a difference quotient at a point where `u` is differentiable at both
ends. -/
theorem fderiv_diffQuot_apply {v y : Space d} {h : ℝ} (hu0 : DifferentiableAt ℝ u y)
    (hu1 : DifferentiableAt ℝ u (y + h • v)) (e : Space d) :
    fderiv ℝ (diffQuot u v h) y e = inner ℝ (gradient u (y + h • v) - gradient u y) e / h := by
  have h1 : HasFDerivAt (fun y ↦ u (y + h • v)) (fderiv ℝ u (y + h • v)) y :=
    (hasFDerivAt_comp_add_right (h • v)).2 hu1.hasFDerivAt
  have h2 : HasFDerivAt (fun y ↦ (u (y + h • v) - u y) * h⁻¹)
      (h⁻¹ • (fderiv ℝ u (y + h • v) - fderiv ℝ u y)) y :=
    (h1.sub hu0.hasFDerivAt).mul_const h⁻¹
  have hfun : diffQuot u v h = fun y ↦ (u (y + h • v) - u y) * h⁻¹ := by
    funext y
    rw [diffQuot, div_eq_mul_inv]
  rw [hfun, h2.fderiv, inner_sub_left]
  simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul, gradient, toDual_symm_apply]
  rw [div_eq_inv_mul]

/-- Difference quotients converge to the directional derivative at points of
differentiability. -/
theorem tendsto_diffQuot {y : Space d} (hu : DifferentiableAt ℝ u y) (v : Space d) :
    Tendsto (fun h ↦ diffQuot u v h y) (𝓝[≠] 0) (𝓝 (fderiv ℝ u y v)) := by
  have hl : HasDerivAt (fun t : ℝ ↦ y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd : HasDerivAt (fun t : ℝ ↦ u (y + t • v)) (fderiv ℝ u y v) 0 :=
    hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  refine hd.tendsto_slope_zero.congr (fun t ↦ ?_)
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, diffQuot]
  rw [div_eq_inv_mul]

end diffQuot

/-! ### `W^{2,2}_loc` regularity -/

/-- The directional derivative of a Lipschitz function is locally integrable. -/
private theorem locallyIntegrable_fderiv_apply_of_lipschitz {d : ℕ} {u : Space d → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (v : Space d) :
    LocallyIntegrable (fun y ↦ fderiv ℝ u y v) volume := by
  rw [locallyIntegrable_iff]
  intro S hS
  have hi : IntegrableOn (fun _ : Space d ↦ (L : ℝ) * ‖v‖) S :=
    continuousOn_const.integrableOn_compact hS
  refine hi.mono' (measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable
    (Eventually.of_forall (fun y ↦ ?_))
  exact ((fderiv ℝ u y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))

/-- **Uniform `L²` bound for derivatives of difference quotients.** For `r < ρ`, `h ≠ 0` and
`ρ + |h| ‖v‖ < R`, `∫_{B_r} (∂ₑ D_h^v u)² ≤ ‖e‖² · 4 (Λ/λ)² L² ‖v‖² |B̄_ρ| / (ρ - r)²`. -/
theorem IsWeakSolution.integral_fderiv_diffQuot_sq_le {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ} (hweak : IsWeakSolution 𝒜 u (ball x₀ R))
    {r ρ : ℝ} (hrρ : r < ρ) (v : Space d) {h : ℝ} (hh : h ≠ 0) (hhv : ρ + |h| * ‖v‖ < R)
    (e : Space d) :
    ∫ y in ball x₀ r, (fderiv ℝ (diffQuot u v h) y e) ^ 2 ≤
      ‖e‖ ^ 2 * (4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * volume.real (closedBall x₀ ρ) /
        (ρ - r) ^ 2) := by
  have hz : ρ + ‖h • v‖ < R := by rwa [norm_smul, Real.norm_eq_abs]
  have hcac := IsWeakSolution.integral_norm_gradient_sub_sq_le h𝒜 hu hweak hrρ hz
  have h0 := hu.ae_differentiableAt (μ := volume)
  have h1 : ∀ᵐ y, DifferentiableAt ℝ u (y + h • v) :=
    (measurePreserving_add_right volume (h • v)).quasiMeasurePreserving.ae h0
  have hpt : ∀ᵐ y, (fderiv ℝ (diffQuot u v h) y e) ^ 2 ≤
      ‖e‖ ^ 2 / h ^ 2 * ‖gradient u (y + h • v) - gradient u y‖ ^ 2 := by
    filter_upwards [h0, h1] with y hy0 hy1
    rw [fderiv_diffQuot_apply hy0 hy1]
    have hcs := abs_real_inner_le_norm (gradient u (y + h • v) - gradient u y) e
    have hsq : (inner ℝ (gradient u (y + h • v) - gradient u y) e) ^ 2 ≤
        (‖gradient u (y + h • v) - gradient u y‖ * ‖e‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
    calc (inner ℝ (gradient u (y + h • v) - gradient u y) e / h) ^ 2
        = (inner ℝ (gradient u (y + h • v) - gradient u y) e) ^ 2 / h ^ 2 := div_pow _ _ _
      _ ≤ (‖gradient u (y + h • v) - gradient u y‖ * ‖e‖) ^ 2 / h ^ 2 :=
          div_le_div_of_nonneg_right hsq (sq_nonneg h)
      _ = ‖e‖ ^ 2 / h ^ 2 * ‖gradient u (y + h • v) - gradient u y‖ ^ 2 := by ring
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hlip := lipschitzWith_diffQuot hu v h
  have hfi : IntegrableOn (fun y ↦ (fderiv ℝ (diffQuot u v h) y e) ^ 2) (ball x₀ r) := by
    refine Measure.integrableOn_of_bounded (M := ((Real.toNNReal (|h|⁻¹ * (2 * L)) : ℝ) *
      ‖e‖) ^ 2) measure_ball_lt_top.ne
      ((measurable_fderiv_apply_const ℝ _ e).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact ((fderiv ℝ (diffQuot u v h) y).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hlip) (norm_nonneg _))
  have hgi : IntegrableOn (fun y ↦ ‖gradient u (y + h • v) - gradient u y‖ ^ 2) (ball x₀ r) := by
    refine Measure.integrableOn_of_bounded (M := (2 * L) ^ 2) measure_ball_lt_top.ne
      ((((measurable_gradient u).comp (measurable_add_const _)).sub
        (measurable_gradient u)).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have g1 := norm_gradient_le_of_lipschitz hu (y + h • v)
    have g2 := norm_gradient_le_of_lipschitz hu y
    exact (norm_sub_le _ _).trans (by linarith)
  calc ∫ y in ball x₀ r, (fderiv ℝ (diffQuot u v h) y e) ^ 2
      ≤ ∫ y in ball x₀ r, ‖e‖ ^ 2 / h ^ 2 * ‖gradient u (y + h • v) - gradient u y‖ ^ 2 :=
        setIntegral_mono_ae_restrict hfi (hgi.const_mul _) (ae_restrict_of_ae hpt)
    _ = ‖e‖ ^ 2 / h ^ 2 * ∫ y in ball x₀ r, ‖gradient u (y + h • v) - gradient u y‖ ^ 2 :=
        integral_const_mul _ _
    _ ≤ ‖e‖ ^ 2 / h ^ 2 * (4 * (Λ / lam) ^ 2 * ((L : ℝ) * ‖h • v‖) ^ 2 *
        volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2) :=
        mul_le_mul_of_nonneg_left hcac (by positivity)
    _ = ‖e‖ ^ 2 * (4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2) := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
        field_simp

/-- **Uniform bound for the pairing of difference quotients with test functions.** -/
theorem IsWeakSolution.abs_integral_diffQuot_mul_fderiv_le {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ} (hweak : IsWeakSolution 𝒜 u (ball x₀ R))
    {r ρ : ℝ} (hrρ : r < ρ) (v : Space d) {h : ℝ} (hh : h ≠ 0) (hhv : ρ + |h| * ‖v‖ < R)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ ball x₀ r) (e : Space d) :
    |∫ y, diffQuot u v h y * fderiv ℝ φ y e| ≤
      ‖e‖ * Real.sqrt (4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2) * Real.sqrt (∫ y in ball x₀ r, φ y ^ 2) := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hlip := lipschitzWith_diffQuot hu v h
  have hibp := integral_fderiv_apply_mul_eq_neg_of_lipschitz hlip hφ hφc e
  have hre : ∫ y, diffQuot u v h y * fderiv ℝ φ y e =
      -∫ y, fderiv ℝ (diffQuot u v h) y e * φ y := by
    rw [hibp, neg_neg]
  have hset : ∫ y in ball x₀ r, fderiv ℝ (diffQuot u v h) y e * φ y =
      ∫ y, fderiv ℝ (diffQuot u v h) y e * φ y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hsub h')), mul_zero]
  rw [hre, abs_neg, ← hset]
  have hfm : MemLp (fun y ↦ fderiv ℝ (diffQuot u v h) y e) 2 (volume.restrict (ball x₀ r)) := by
    refine MemLp.of_bound (measurable_fderiv_apply_const ℝ _ e).aestronglyMeasurable
      ((Real.toNNReal (|h|⁻¹ * (2 * L)) : ℝ) * ‖e‖) (Eventually.of_forall (fun y ↦ ?_))
    exact ((fderiv ℝ (diffQuot u v h) y).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hlip) (norm_nonneg _))
  have hφm : MemLp φ 2 (volume.restrict (ball x₀ r)) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  refine (abs_integral_mul_le_sqrt_mul_sqrt hfm hφm).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hb := IsWeakSolution.integral_fderiv_diffQuot_sq_le h𝒜 hu hweak hrρ v hh hhv e
  calc Real.sqrt (∫ y in ball x₀ r, (fderiv ℝ (diffQuot u v h) y e) ^ 2)
      ≤ Real.sqrt (‖e‖ ^ 2 * (4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2)) := Real.sqrt_le_sqrt hb
    _ = ‖e‖ * Real.sqrt (4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Pairings of difference quotients with derivatives of test functions converge to the pairing
of the directional derivative. -/
theorem tendsto_integral_diffQuot_mul {d : ℕ} {u : Space d → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (v : Space d) {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (e : Space d) :
    Tendsto (fun h ↦ ∫ y, diffQuot u v h y * fderiv ℝ φ y e) (𝓝[≠] 0)
      (𝓝 (∫ y, fderiv ℝ u y v * fderiv ℝ φ y e)) := by
  have hφe : Continuous (fun y ↦ fderiv ℝ φ y e) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφi : Integrable (fun y ↦ fderiv ℝ φ y e) :=
    hφe.integrable_of_hasCompactSupport (hφc.fderiv_apply ℝ e)
  apply tendsto_integral_filter_of_dominated_convergence (fun y ↦ L * ‖v‖ * |fderiv ℝ φ y e|)
  · apply Eventually.of_forall
    intro h
    have hc : Continuous (diffQuot u v h) :=
      ((hu.continuous.comp (continuous_id.add continuous_const)).sub hu.continuous).div_const h
    exact (hc.mul hφe).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    apply Eventually.of_forall
    intro y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_diffQuot_le hu v hh y) (abs_nonneg _)
  · exact hφi.abs.const_mul _
  · filter_upwards [hu.ae_differentiableAt (μ := volume)] with y hy
    exact (tendsto_diffQuot hy v).mul_const _

/-- **`W^{2,2}_loc` regularity (first Schauder step).** Let `u` be an `L`-Lipschitz weak solution
of `div 𝒜(∇u) = 0` in `ball x₀ R`, where `𝒜` is `C¹`, uniformly elliptic with constant `lam`
and has derivative bounded by `Λ` on `‖p‖ ≤ L`. Then for every direction `v` and every `r < R`,
the directional derivative `∂ᵥu` has a weak gradient `G ∈ L²(B_r)` on `B_r` with
`∫_{B_r} ‖G‖² ≤ d · 16 (Λ/λ)² L² ‖v‖² |B̄_{(r+R)/2}| / (R - r)²`. -/
theorem IsWeakSolution.exists_hasWeakGradientOn_fderiv {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ} (hweak : IsWeakSolution 𝒜 u (ball x₀ R))
    {r : ℝ} (hrR : r < R) (v : Space d) :
    ∃ G : Space d → Space d, HasWeakGradientOn (ball x₀ r) (fun y ↦ fderiv ℝ u y v) G ∧
      MemLp G 2 (volume.restrict (ball x₀ r)) ∧
      ∫ y in ball x₀ r, ‖G y‖ ^ 2 ≤ d * (16 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ((r + R) / 2)) / (R - r) ^ 2) := by
  set ρ := (r + R) / 2 with hρ
  have hrρ : r < ρ := by rw [hρ]; linarith
  have hρR : ρ < R := by rw [hρ]; linarith
  set C2 := 4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * volume.real (closedBall x₀ ρ) /
    (ρ - r) ^ 2 with hC2
  have hC2nn : 0 ≤ C2 := by positivity
  have hC2eq : C2 = 16 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
      volume.real (closedBall x₀ ρ) / (R - r) ^ 2 := by
    have hρr : ρ - r = (R - r) / 2 := by rw [hρ]; ring
    have hRr : R - r ≠ 0 := by linarith
    rw [hC2, hρr, div_pow]
    field_simp
    ring
  have hb : ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball x₀ r →
      ∀ e : Space d, |∫ y, fderiv ℝ u y v * fderiv ℝ φ y e| ≤
        Real.sqrt C2 * ‖e‖ * Real.sqrt (∫ y in ball x₀ r, φ y ^ 2) := by
    intro φ hφ hφc hsub e
    have hlim := (tendsto_integral_diffQuot_mul hu v hφ hφc e).abs
    apply le_of_tendsto hlim
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0, ρ + |h| * ‖v‖ < R := by
      have hc : Continuous (fun h : ℝ ↦ ρ + |h| * ‖v‖) :=
        continuous_const.add (continuous_abs.mul continuous_const)
      have h0 : ρ + |(0 : ℝ)| * ‖v‖ < R := by simpa using hρR
      exact hc.continuousAt.eventually (gt_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with h hhv hh
    have hbd := IsWeakSolution.abs_integral_diffQuot_mul_fderiv_le h𝒜 hu hweak hrρ v hh hhv
      hφ hφc hsub e
    calc |∫ y, diffQuot u v h y * fderiv ℝ φ y e|
        ≤ ‖e‖ * Real.sqrt C2 * Real.sqrt (∫ y in ball x₀ r, φ y ^ 2) := hbd
      _ = Real.sqrt C2 * ‖e‖ * Real.sqrt (∫ y in ball x₀ r, φ y ^ 2) := by ring
  obtain ⟨G, hG, hGm, hGb⟩ := exists_hasWeakGradientOn_of_abs_integral_le
    measure_ball_lt_top.ne
    ((locallyIntegrable_fderiv_apply_of_lipschitz hu v).locallyIntegrableOn _)
    (Real.sqrt_nonneg C2) hb
  refine ⟨G, hG, hGm, ?_⟩
  rw [Real.sq_sqrt hC2nn, hC2eq] at hGb
  exact hGb

/-! ### The minimal surface operator -/

/-- The flux of the minimal surface (mean curvature) operator, `𝒜(p) = p / √(1 + ‖p‖²)`. -/
def minimalSurfaceFlux {d : ℕ} (p : Space d) : Space d :=
  (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • p

section minimalSurfaceFlux

variable {d : ℕ}

theorem hasFDerivAt_inv_sqrt_one_add_norm_sq (p : Space d) :
    HasFDerivAt (fun q : Space d ↦ (Real.sqrt (1 + ‖q‖ ^ 2))⁻¹)
      (-(Real.sqrt (1 + ‖p‖ ^ 2) ^ 3)⁻¹ • innerSL ℝ p) p := by
  have hpos : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have hW : 0 < Real.sqrt (1 + ‖p‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have h1 : HasFDerivAt (fun q : Space d ↦ 1 + ‖q‖ ^ 2) (2 • innerSL ℝ p) p := by
    simpa using ((hasFDerivAt_id p).norm_sq).const_add 1
  have h2 := h1.sqrt hpos.ne'
  have h3 := (hasFDerivAt_inv hW.ne').comp p h2
  refine h3.congr_fderiv ?_
  ext ξ
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, _root_.smul_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

theorem hasFDerivAt_minimalSurfaceFlux (p : Space d) :
    HasFDerivAt minimalSurfaceFlux
      ((Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • ContinuousLinearMap.id ℝ (Space d) +
        (-(Real.sqrt (1 + ‖p‖ ^ 2) ^ 3)⁻¹ • innerSL ℝ p).smulRight p) p :=
  (hasFDerivAt_inv_sqrt_one_add_norm_sq p).smul (hasFDerivAt_id p)

theorem fderiv_minimalSurfaceFlux_apply (p ξ : Space d) :
    fderiv ℝ minimalSurfaceFlux p ξ =
      (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • ξ - ((Real.sqrt (1 + ‖p‖ ^ 2) ^ 3)⁻¹ * inner ℝ p ξ) • p := by
  rw [(hasFDerivAt_minimalSurfaceFlux p).fderiv, _root_.add_apply,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, neg_mul, neg_smul,
    sub_eq_add_neg]

theorem contDiff_minimalSurfaceFlux : ContDiff ℝ 1 (minimalSurfaceFlux (d := d)) := by
  have h1 : ContDiff ℝ 1 (fun q : Space d ↦ 1 + ‖q‖ ^ 2) := contDiff_const.add (contDiff_norm_sq ℝ)
  have h2 : ContDiff ℝ 1 (fun q : Space d ↦ Real.sqrt (1 + ‖q‖ ^ 2)) :=
    h1.sqrt (fun q ↦ (by positivity : (0 : ℝ) < 1 + ‖q‖ ^ 2).ne')
  have h3 : ContDiff ℝ 1 (fun q : Space d ↦ (Real.sqrt (1 + ‖q‖ ^ 2))⁻¹) :=
    h2.inv (fun q ↦ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + ‖q‖ ^ 2)).ne')
  exact h3.smul contDiff_id

/-- The minimal surface flux is elliptic with constant `(1 + ‖p‖²)^{-3/2}`. -/
theorem inner_fderiv_minimalSurfaceFlux_ge (p ξ : Space d) :
    (Real.sqrt (1 + ‖p‖ ^ 2) ^ 3)⁻¹ * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ minimalSurfaceFlux p ξ) ξ := by
  rw [fderiv_minimalSurfaceFlux_apply, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  set W := Real.sqrt (1 + ‖p‖ ^ 2) with hW_def
  have hpos : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have hW : 0 < W := Real.sqrt_pos.mpr hpos
  have hW2 : W ^ 2 = 1 + ‖p‖ ^ 2 := Real.sq_sqrt hpos.le
  have hcs : inner ℝ p ξ ^ 2 ≤ ‖p‖ ^ 2 * ‖ξ‖ ^ 2 := by
    calc inner ℝ p ξ ^ 2 = |inner ℝ p ξ| ^ 2 := (sq_abs _).symm
      _ ≤ (‖p‖ * ‖ξ‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm p ξ) 2
      _ = ‖p‖ ^ 2 * ‖ξ‖ ^ 2 := mul_pow _ _ _
  have hinv : W⁻¹ = W ^ 2 * (W ^ 3)⁻¹ := by
    field_simp
  have key : W⁻¹ * ‖ξ‖ ^ 2 - (W ^ 3)⁻¹ * inner ℝ p ξ * inner ℝ p ξ -
      (W ^ 3)⁻¹ * ‖ξ‖ ^ 2 = (W ^ 3)⁻¹ * (‖p‖ ^ 2 * ‖ξ‖ ^ 2 - inner ℝ p ξ ^ 2) := by
    rw [hinv, hW2]
    ring
  have hnn : 0 ≤ (W ^ 3)⁻¹ * (‖p‖ ^ 2 * ‖ξ‖ ^ 2 - inner ℝ p ξ ^ 2) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- The derivative of the minimal surface flux has operator norm at most `2`. -/
theorem norm_fderiv_minimalSurfaceFlux_le (p : Space d) :
    ‖fderiv ℝ minimalSurfaceFlux p‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_two (fun ξ ↦ ?_)
  rw [fderiv_minimalSurfaceFlux_apply]
  set W := Real.sqrt (1 + ‖p‖ ^ 2) with hW_def
  have hpos : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have hW1 : 1 ≤ W := by
    rw [hW_def, Real.one_le_sqrt]
    nlinarith [norm_nonneg p]
  have hW : 0 < W := lt_of_lt_of_le zero_lt_one hW1
  have hW2 : W ^ 2 = 1 + ‖p‖ ^ 2 := Real.sq_sqrt hpos.le
  have h1 : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have h2 : (W ^ 3)⁻¹ * ‖p‖ ^ 2 ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    have hW3 : W ^ 2 ≤ W ^ 3 := pow_le_pow_right₀ hW1 (by norm_num)
    nlinarith
  calc ‖W⁻¹ • ξ - ((W ^ 3)⁻¹ * inner ℝ p ξ) • p‖
      ≤ ‖W⁻¹ • ξ‖ + ‖((W ^ 3)⁻¹ * inner ℝ p ξ) • p‖ := norm_sub_le _ _
    _ = W⁻¹ * ‖ξ‖ + (W ^ 3)⁻¹ * |inner ℝ p ξ| * ‖p‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_of_pos (inv_pos.mpr hW), abs_of_pos (inv_pos.mpr (pow_pos hW 3))]
    _ ≤ 1 * ‖ξ‖ + (W ^ 3)⁻¹ * (‖p‖ * ‖ξ‖) * ‖p‖ := by
        gcongr
        exact abs_real_inner_le_norm p ξ
    _ = 1 * ‖ξ‖ + ((W ^ 3)⁻¹ * ‖p‖ ^ 2) * ‖ξ‖ := by ring
    _ ≤ 1 * ‖ξ‖ + 1 * ‖ξ‖ := by gcongr
    _ = 2 * ‖ξ‖ := by ring

/-- The minimal surface flux satisfies the structure conditions on `‖p‖ ≤ L` with ellipticity
constant `(1 + L²)^{-3/2}` and derivative bound `2`. -/
theorem isEllipticFlux_minimalSurfaceFlux (L : ℝ) :
    IsEllipticFlux (minimalSurfaceFlux (d := d)) L (Real.sqrt (1 + L ^ 2) ^ 3)⁻¹ 2 where
  contDiff := contDiff_minimalSurfaceFlux
  pos := by positivity
  elliptic := by
    intro p hp ξ
    refine le_trans ?_ (inner_fderiv_minimalSurfaceFlux_ge p ξ)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    have h := pow_le_pow_left₀ (norm_nonneg p) hp 2
    linarith
  bounded := fun p _ ↦ norm_fderiv_minimalSurfaceFlux_le p

end minimalSurfaceFlux

/-- **`W^{2,2}_loc` regularity for the minimal surface equation.** A globally `L`-Lipschitz weak
solution of `div (∇u / √(1 + |∇u|²)) = 0` in `ball x₀ R` has, for every direction `v` and every
`r < R`, a weak gradient of `∂ᵥu` in `L²(B_r)` with
`∫_{B_r} ‖G‖² ≤ d · 64 (1 + L²)³ L² ‖v‖² |B̄_{(r+R)/2}| / (R - r)²`. -/
theorem exists_hasWeakGradientOn_fderiv_of_minimalSurface {d : ℕ} {u : Space d → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ}
    (hweak : IsWeakSolution minimalSurfaceFlux u (ball x₀ R)) {r : ℝ} (hrR : r < R)
    (v : Space d) :
    ∃ G : Space d → Space d, HasWeakGradientOn (ball x₀ r) (fun y ↦ fderiv ℝ u y v) G ∧
      MemLp G 2 (volume.restrict (ball x₀ r)) ∧
      ∫ y in ball x₀ r, ‖G y‖ ^ 2 ≤ d * (64 * (1 + (L : ℝ) ^ 2) ^ 3 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ((r + R) / 2)) / (R - r) ^ 2) := by
  obtain ⟨G, hG, hGm, hGb⟩ := IsWeakSolution.exists_hasWeakGradientOn_fderiv
    (isEllipticFlux_minimalSurfaceFlux (L : ℝ)) hu hweak hrR v
  refine ⟨G, hG, hGm, hGb.trans_eq ?_⟩
  have hpos : (0 : ℝ) < 1 + (L : ℝ) ^ 2 := by positivity
  have hs : Real.sqrt (1 + (L : ℝ) ^ 2) ^ 2 = 1 + (L : ℝ) ^ 2 := Real.sq_sqrt hpos.le
  have hc : (2 / (Real.sqrt (1 + (L : ℝ) ^ 2) ^ 3)⁻¹) ^ 2 = 4 * (1 + (L : ℝ) ^ 2) ^ 3 := by
    rw [div_inv_eq_mul, mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hs]
    norm_num
  rw [hc]
  ring

/-! ### The linearized equation -/

/-- A real-valued function converges along a filter if it can be approximated, up to any
`η > 0` eventually, by functions converging to values `η`-close to the target. -/
private theorem tendsto_of_forall_approx {ι : Type*} {l : Filter ι} {F : ι → ℝ} {a : ℝ}
    (h : ∀ η > 0, ∃ F' : ι → ℝ, ∃ a' : ℝ, Tendsto F' l (𝓝 a') ∧
      (∀ᶠ i in l, |F i - F' i| ≤ η) ∧ |a - a'| ≤ η) :
    Tendsto F l (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F', a', hF', hFF', ha⟩ := h (ε / 4) (by positivity)
  have h1 := (Metric.tendsto_nhds.mp hF') (ε / 4) (by positivity)
  filter_upwards [h1, hFF'] with i hi hi'
  rw [Real.dist_eq] at hi ⊢
  have e1 := abs_sub_le (F i) (F' i) a
  have e2 := abs_sub_le (F' i) a' a
  rw [abs_sub_comm a' a] at e2
  linarith

/-- `C¹` functions compactly supported in a ball are dense in `L²` of the ball. -/
theorem exists_contDiff_setIntegral_sq_sub_lt {d : ℕ} {x : Space d} {r : ℝ}
    {f : Space d → ℝ} (hf : MemLp f 2 (volume.restrict (ball x r))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Space d → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball x r ∧
      ∫ y in ball x r, (f y - ψ y) ^ 2 < ε := by
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hf0 : MemLp ((ball x r).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).2 hf
  have hf0' : MemLp ((ball x r).indicator f) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact hf0
  obtain ⟨g, -, hgi, hgcont, hgm⟩ :=
    hf0'.exists_hasCompactSupport_integral_rpow_sub_le (p := 2) two_pos
      (ε := ε / 8) (by positivity)
  rw [ENNReal.ofReal_ofNat] at hgm
  obtain ⟨ψ, hψ, hψc, hψs, hψi⟩ := exists_contDiff_tsupport_subset_ball_sq_integral_lt
    (lt_add_one r) (x := x) hgcont.continuousOn (η := ε / 8) (by positivity)
  refine ⟨ψ, hψ, hψc, hψs, ?_⟩
  have hint0 : Integrable (fun y ↦ ((ball x r).indicator f y - g y) ^ 2) :=
    (hf0.sub hgm).integrable_sq
  have h1 : ∫ y in ball x r, (f y - g y) ^ 2 ≤ ε / 8 := by
    calc ∫ y in ball x r, (f y - g y) ^ 2
        = ∫ y in ball x r, ((ball x r).indicator f y - g y) ^ 2 := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          simp only [Set.indicator_of_mem hy]
      _ ≤ ∫ y, ((ball x r).indicator f y - g y) ^ 2 :=
          setIntegral_le_integral hint0 (Eventually.of_forall (fun _ ↦ sq_nonneg _))
      _ = ∫ y, ‖(ball x r).indicator f y - g y‖ ^ (2 : ℝ) := by
          congr 1
          funext y
          rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      _ ≤ ε / 8 := hgi
  have hgr : MemLp g 2 (volume.restrict (ball x r)) := hgm.restrict _
  have hψr : MemLp ψ 2 (volume.restrict (ball x r)) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hi1 : Integrable (fun y ↦ 2 * (f y - g y) ^ 2) (volume.restrict (ball x r)) :=
    (hf.sub hgr).integrable_sq.const_mul 2
  have hi2 : Integrable (fun y ↦ 2 * (g y - ψ y) ^ 2) (volume.restrict (ball x r)) :=
    (hgr.sub hψr).integrable_sq.const_mul 2
  have hle : ∫ y in ball x r, (f y - ψ y) ^ 2 ≤
      ∫ y in ball x r, (2 * (f y - g y) ^ 2 + 2 * (g y - ψ y) ^ 2) := by
    refine integral_mono (hf.sub hψr).integrable_sq (hi1.add hi2) (fun y ↦ ?_)
    nlinarith [sq_nonneg (f y - 2 * g y + ψ y)]
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at hle
  linarith

/-- **Uniform first-order Taylor estimate** for a flux on the ball `‖p‖ ≤ L`: for every `η > 0`
there is `δ > 0` with `‖𝒜 q - 𝒜 p - D𝒜(p)(q - p)‖ ≤ η ‖q - p‖ + (2Λ/δ) ‖q - p‖²`. -/
theorem IsEllipticFlux.exists_taylor {d : ℕ} {𝒜 : Space d → Space d} {L lam Λ : ℝ}
    (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ p q : Space d, ‖p‖ ≤ L → ‖q‖ ≤ L →
      ‖𝒜 q - 𝒜 p - fderiv ℝ 𝒜 p (q - p)‖ ≤ η * ‖q - p‖ + 2 * Λ / δ * ‖q - p‖ ^ 2 := by
  have hcont : Continuous (fderiv ℝ 𝒜) := h𝒜.contDiff.continuous_fderiv one_ne_zero
  have huc := (isCompact_closedBall (0 : Space d) L).uniformContinuousOn_of_continuous
    hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc η hη
  refine ⟨δ, hδ, fun p q hp hq ↦ ?_⟩
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (h𝒜.bounded p hp)
  have hp0 : p ∈ closedBall (0 : Space d) L := by simpa using hp
  have hq0 : q ∈ closedBall (0 : Space d) L := by simpa using hq
  by_cases hpq : ‖q - p‖ < δ
  · set s := closedBall (0 : Space d) L ∩ closedBall p ‖q - p‖ with hs_def
    have hs : Convex ℝ s := (convex_closedBall _ _).inter (convex_closedBall _ _)
    have hps : p ∈ s := ⟨hp0, mem_closedBall_self (norm_nonneg _)⟩
    have hqs : q ∈ s := ⟨hq0, by rw [mem_closedBall, dist_eq_norm]⟩
    have hgd : ∀ x, HasFDerivAt (fun x ↦ 𝒜 x - fderiv ℝ 𝒜 p x)
        (fderiv ℝ 𝒜 x - fderiv ℝ 𝒜 p) x := fun x ↦
      (h𝒜.contDiff.differentiable one_ne_zero x).hasFDerivAt.sub (fderiv ℝ 𝒜 p).hasFDerivAt
    have hbound : ∀ x ∈ s, ‖fderiv ℝ (fun x ↦ 𝒜 x - fderiv ℝ 𝒜 p x) x‖ ≤ η := by
      intro x hx
      rw [(hgd x).fderiv, ← dist_eq_norm]
      have hxp : dist x p < δ := lt_of_le_of_lt hx.2 hpq
      exact (hδ' x hx.1 p hp0 hxp).le
    have hmvt := hs.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ (hgd x).differentiableAt)
      hbound hps hqs
    have hgqp : (𝒜 q - fderiv ℝ 𝒜 p q) - (𝒜 p - fderiv ℝ 𝒜 p p) =
        𝒜 q - 𝒜 p - fderiv ℝ 𝒜 p (q - p) := by
      rw [map_sub]
      abel
    rw [hgqp] at hmvt
    exact hmvt.trans (le_add_of_nonneg_right (by positivity))
  · rw [not_lt] at hpq
    have h1 := h𝒜.norm_sub_le hp hq
    have h2 : ‖fderiv ℝ 𝒜 p (q - p)‖ ≤ Λ * ‖q - p‖ :=
      ((fderiv ℝ 𝒜 p).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (h𝒜.bounded p hp) (norm_nonneg _))
    have h3 : ‖q - p‖ ≤ ‖q - p‖ ^ 2 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith [norm_nonneg (q - p)]
    calc ‖𝒜 q - 𝒜 p - fderiv ℝ 𝒜 p (q - p)‖
        ≤ ‖𝒜 q - 𝒜 p‖ + ‖fderiv ℝ 𝒜 p (q - p)‖ := _root_.norm_sub_le _ _
      _ ≤ 2 * Λ * ‖q - p‖ := by linarith
      _ ≤ 2 * Λ * (‖q - p‖ ^ 2 / δ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * Λ / δ * ‖q - p‖ ^ 2 := by ring
      _ ≤ η * ‖q - p‖ + 2 * Λ / δ * ‖q - p‖ ^ 2 :=
          le_add_of_nonneg_left (by positivity)

/-- Difference of two set integrals of products with a common factor. -/
private theorem setIntegral_mul_sub_mul {d : ℕ} {S : Set (Space d)} {D f g : Space d → ℝ}
    (h1 : Integrable (fun y ↦ D y * f y) (volume.restrict S))
    (h2 : Integrable (fun y ↦ D y * g y) (volume.restrict S)) :
    ∫ y in S, D y * (f y - g y) = (∫ y in S, D y * f y) - ∫ y in S, D y * g y := by
  have hfun : (fun y ↦ D y * (f y - g y)) = fun y ↦ D y * f y - D y * g y := by
    funext y
    ring
  rw [hfun, integral_sub h1 h2]

/-- Derivatives of difference quotients are square integrable on a ball. -/
theorem memLp_fderiv_diffQuot {d : ℕ} {u : Space d → ℝ} {L : NNReal} (hu : LipschitzWith L u)
    (v : Space d) (h : ℝ) (e : Space d) (S : Set (Space d)) (hS : volume S ≠ ⊤) :
    MemLp (fun y ↦ fderiv ℝ (diffQuot u v h) y e) 2 (volume.restrict S) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS
  refine MemLp.of_bound (measurable_fderiv_apply_const ℝ _ e).aestronglyMeasurable
    ((Real.toNNReal (|h|⁻¹ * (2 * L)) : ℝ) * ‖e‖) (Eventually.of_forall (fun y ↦ ?_))
  exact ((fderiv ℝ (diffQuot u v h) y).le_opNorm e).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_diffQuot hu v h))
      (norm_nonneg _))

/-- **Weak convergence of derivatives of difference quotients.** If `G ∈ L²(B_r)` is a weak
gradient of `∂ᵥu` on `B_r`, then `∫_{B_r} ∂ₑ(D_h^v u) f → ∫_{B_r} ⟪G, e⟫ f` as `h → 0`, for
every `f ∈ L²(B_r)`. -/
theorem IsWeakSolution.tendsto_setIntegral_fderiv_diffQuot_mul {d : ℕ}
    {𝒜 : Space d → Space d} {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ)
    {u : Space d → ℝ} (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ}
    (hweak : IsWeakSolution 𝒜 u (ball x₀ R)) {r : ℝ} (hrR : r < R) (v : Space d)
    {G : Space d → Space d} (hG : HasWeakGradientOn (ball x₀ r) (fun y ↦ fderiv ℝ u y v) G)
    (hGm : MemLp G 2 (volume.restrict (ball x₀ r))) {f : Space d → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball x₀ r))) (e : Space d) :
    Tendsto (fun h ↦ ∫ y in ball x₀ r, fderiv ℝ (diffQuot u v h) y e * f y) (𝓝[≠] 0)
      (𝓝 (∫ y in ball x₀ r, inner ℝ (G y) e * f y)) := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set ρ := (r + R) / 2 with hρ
  have hrρ : r < ρ := by rw [hρ]; linarith
  have hρR : ρ < R := by rw [hρ]; linarith
  set C2 := 4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * volume.real (closedBall x₀ ρ) /
    (ρ - r) ^ 2 with hC2
  have hGe : MemLp (fun y ↦ inner ℝ (G y) e) 2 (volume.restrict (ball x₀ r)) :=
    hGm.inner_const e
  apply tendsto_of_forall_approx
  intro η hη
  set A := ‖e‖ * Real.sqrt C2 with hA_def
  set B := Real.sqrt (∫ y in ball x₀ r, inner ℝ (G y) e ^ 2) with hB_def
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  set δ := η / (A + B + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hAδ : A * δ ≤ η := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hBδ : B * δ ≤ η := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨ψ, hψ, hψc, hψs, hψi⟩ := exists_contDiff_setIntegral_sq_sub_lt hf
    (ε := δ ^ 2) (by positivity)
  have hfψ : Real.sqrt (∫ y in ball x₀ r, (f y - ψ y) ^ 2) ≤ δ := by
    rw [← Real.sqrt_sq hδpos.le]
    exact Real.sqrt_le_sqrt hψi.le
  have hψm : MemLp ψ 2 (volume.restrict (ball x₀ r)) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hzero : ∀ (k : Space d → ℝ), ∀ y ∉ ball x₀ r, k y * ψ y = 0 := by
    intro k y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hψs h')), mul_zero]
  refine ⟨fun h ↦ ∫ y in ball x₀ r, fderiv ℝ (diffQuot u v h) y e * ψ y,
    ∫ y in ball x₀ r, inner ℝ (G y) e * ψ y, ?_, ?_, ?_⟩
  · have hl : ∀ h, ∫ y in ball x₀ r, fderiv ℝ (diffQuot u v h) y e * ψ y =
        -∫ y, diffQuot u v h y * fderiv ℝ ψ y e := by
      intro h
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero _),
        integral_fderiv_apply_mul_eq_neg_of_lipschitz (lipschitzWith_diffQuot hu v h) hψ hψc e]
    have hr : ∫ y in ball x₀ r, inner ℝ (G y) e * ψ y =
        -∫ y, fderiv ℝ u y v * fderiv ℝ ψ y e := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero _),
        hG.integral_eq hψ hψc hψs e, neg_neg]
    simp_rw [hl]
    rw [hr]
    exact (tendsto_integral_diffQuot_mul hu v hψ hψc e).neg
  · have hsmall : ∀ᶠ h : ℝ in 𝓝 0, ρ + |h| * ‖v‖ < R := by
      have hc : Continuous (fun h : ℝ ↦ ρ + |h| * ‖v‖) :=
        continuous_const.add (continuous_abs.mul continuous_const)
      have h0 : ρ + |(0 : ℝ)| * ‖v‖ < R := by simpa using hρR
      exact hc.continuousAt.eventually (gt_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with h hhv hh
    have hbd := IsWeakSolution.integral_fderiv_diffQuot_sq_le h𝒜 hu hweak hrρ v hh hhv e
    have hDm := memLp_fderiv_diffQuot hu v h e (ball x₀ r) measure_ball_lt_top.ne
    have hi1 : Integrable (fun y ↦ fderiv ℝ (diffQuot u v h) y e * f y)
        (volume.restrict (ball x₀ r)) := hDm.integrable_mul hf
    have hi2 : Integrable (fun y ↦ fderiv ℝ (diffQuot u v h) y e * ψ y)
        (volume.restrict (ball x₀ r)) := hDm.integrable_mul hψm
    have he := setIntegral_mul_sub_mul hi1 hi2
    have hcs := abs_integral_mul_le_sqrt_mul_sqrt hDm (hf.sub hψm)
    have hsq : Real.sqrt (∫ y in ball x₀ r, (fderiv ℝ (diffQuot u v h) y e) ^ 2) ≤ A := by
      rw [hA_def, ← Real.sqrt_sq (norm_nonneg e), ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt hbd
    have hfin : |∫ y in ball x₀ r, fderiv ℝ (diffQuot u v h) y e * (f y - ψ y)| ≤ η := by
      refine hcs.trans ?_
      exact (mul_le_mul hsq hfψ (Real.sqrt_nonneg _) hA).trans hAδ
    rw [he] at hfin
    exact hfin
  · have hi1 : Integrable (fun y ↦ inner ℝ (G y) e * f y) (volume.restrict (ball x₀ r)) :=
      hGe.integrable_mul hf
    have hi2 : Integrable (fun y ↦ inner ℝ (G y) e * ψ y) (volume.restrict (ball x₀ r)) :=
      hGe.integrable_mul hψm
    have he := setIntegral_mul_sub_mul hi1 hi2
    have hcs := abs_integral_mul_le_sqrt_mul_sqrt hGe (hf.sub hψm)
    have hfin : |∫ y in ball x₀ r, inner ℝ (G y) e * (f y - ψ y)| ≤ η :=
      hcs.trans ((mul_le_mul le_rfl hfψ (Real.sqrt_nonneg _) hB).trans hBδ)
    rw [he] at hfin
    exact hfin

/-- A bounded measurable function vanishing outside a compact set is integrable. -/
private theorem integrable_of_norm_le_of_eq_zero_of_isCompact {d : ℕ} {F : Space d → ℝ}
    (hF : AEStronglyMeasurable F) {B : ℝ} (hB : ∀ y, ‖F y‖ ≤ B) {K : Set (Space d)}
    (hK : IsCompact K) (h0 : ∀ y ∉ K, F y = 0) : Integrable F := by
  have hon : IntegrableOn F K :=
    Measure.integrableOn_of_bounded hK.measure_lt_top.ne hF (Eventually.of_forall (fun y ↦ hB y))
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro y hy
  by_contra hn
  exact hy (h0 y hn)

/-- The gradient of a `C¹` compactly supported function is bounded. -/
private theorem exists_bound_norm_gradient {d : ℕ} {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) : ∃ M, 0 ≤ M ∧ ∀ y, ‖gradient φ y‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hφc.fderiv ℝ).exists_bound_of_continuous (hφ.continuous_fderiv one_ne_zero)
  refine ⟨max M 0, le_max_right _ _, fun y ↦ ?_⟩
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact (hM y).trans (le_max_left _ _)

/-- **The difference equation**: the weak equation and its translate by `z`, tested with the
same `C¹` function. -/
theorem IsWeakSolution.integral_inner_flux_sub_eq_zero {d : ℕ} {𝒜 : Space d → Space d}
    {L lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ} {Lu : NNReal}
    (hu : LipschitzWith Lu u) (hL : (Lu : ℝ) ≤ L) {U : Set (Space d)}
    (hweak : IsWeakSolution 𝒜 u U) (z : Space d) {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hsub : tsupport φ ⊆ U)
    (hsubz : tsupport φ ⊆ (· + z) ⁻¹' U) :
    ∫ y, inner ℝ (𝒜 (gradient u (y + z)) - 𝒜 (gradient u y)) (gradient φ y) = 0 := by
  obtain ⟨M, hM0, hM⟩ := h𝒜.exists_bound
  obtain ⟨Mφ, hMφ0, hMφ⟩ := exists_bound_norm_gradient hφ hφc
  have hgu : ∀ y, ‖gradient u y‖ ≤ L := fun y ↦ (norm_gradient_le_of_lipschitz hu y).trans hL
  have hint : ∀ w : Space d,
      Integrable (fun y ↦ inner ℝ (𝒜 (gradient u (y + w))) (gradient φ y)) := by
    intro w
    refine integrable_of_norm_le_of_eq_zero_of_isCompact (B := M * Mφ) ?_ (fun y ↦ ?_) hφc
      (fun y hy ↦ ?_)
    · exact ((h𝒜.contDiff.continuous.measurable.comp ((measurable_gradient u).comp
        (measurable_add_const w))).aestronglyMeasurable).inner
        (measurable_gradient φ).aestronglyMeasurable
    · exact (norm_inner_le_norm _ _).trans (mul_le_mul (hM _ (hgu _)) (hMφ y) (norm_nonneg _) hM0)
    · rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right]
  have h1 := integral_inner_gradient_comp_add_eq_zero hweak z hφ hφc hsubz
  have h0 := hweak φ hφ hφc hsub
  have hint0 := hint 0
  simp only [add_zero] at hint0
  have hfun : (fun y ↦ inner ℝ (𝒜 (gradient u (y + z)) - 𝒜 (gradient u y)) (gradient φ y)) =
      fun y ↦ inner ℝ (𝒜 (gradient u (y + z))) (gradient φ y) -
        inner ℝ (𝒜 (gradient u y)) (gradient φ y) := by
    funext y
    rw [inner_sub_left]
  rw [hfun, integral_sub (hint z) hint0, h1, h0, sub_zero]

/-- **The remainder of the linearization is small**: with `η, δ` from the uniform Taylor
estimate, the remainder of the first-order expansion of `𝒜(∇u(· + h v)) - 𝒜(∇u)`, tested against
`∇φ`, is `O(|h| (η + |h| / δ))`. -/
theorem IsWeakSolution.abs_integral_inner_remainder_le {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ} (hweak : IsWeakSolution 𝒜 u (ball x₀ R))
    {r ρ : ℝ} (hrρ : r < ρ) {φ : Space d → ℝ} (hsub : tsupport φ ⊆ ball x₀ r)
    {Mφ : ℝ} (hMφ0 : 0 ≤ Mφ) (hMφ : ∀ y, ‖gradient φ y‖ ≤ Mφ) {η δ : ℝ} (hη : 0 < η)
    (hδ : 0 < δ)
    (htaylor : ∀ p q : Space d, ‖p‖ ≤ L → ‖q‖ ≤ L →
      ‖𝒜 q - 𝒜 p - fderiv ℝ 𝒜 p (q - p)‖ ≤ η * ‖q - p‖ + 2 * Λ / δ * ‖q - p‖ ^ 2)
    (v : Space d) {h : ℝ} (hh : h ≠ 0) (hhv : ρ + |h| * ‖v‖ < R) :
    |∫ y, inner ℝ (𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y) -
        fderiv ℝ 𝒜 (gradient u y) (gradient u (y + h • v) - gradient u y)) (gradient φ y)| ≤
      Mφ * |h| * (η * (volume.real (ball x₀ r) +
        4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * volume.real (closedBall x₀ ρ) /
          (ρ - r) ^ 2) / 2 +
        2 * Λ / δ * |h| * (4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
          volume.real (closedBall x₀ ρ) / (ρ - r) ^ 2)) := by
  set C2 := 4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * volume.real (closedBall x₀ ρ) /
    (ρ - r) ^ 2 with hC2
  set V := volume.real (ball x₀ r) with hV
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (h𝒜.bounded 0 (by simp))
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hgu : ∀ y, ‖gradient u y‖ ≤ L := norm_gradient_le_of_lipschitz hu
  have habs : 0 < |h| := abs_pos.mpr hh
  have hz : ρ + ‖h • v‖ < R := by rwa [norm_smul, Real.norm_eq_abs]
  have hcac := IsWeakSolution.integral_norm_gradient_sub_sq_le h𝒜 hu hweak hrρ hz
  have hcac' : ∫ y in ball x₀ r, ‖gradient u (y + h • v) - gradient u y‖ ^ 2 ≤ |h| ^ 2 * C2 := by
    refine hcac.trans (le_of_eq ?_)
    rw [hC2, norm_smul, Real.norm_eq_abs, mul_pow, mul_pow]
    ring
  set Rem : Space d → Space d := fun y ↦ 𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y) -
    fderiv ℝ 𝒜 (gradient u y) (gradient u (y + h • v) - gradient u y) with hRem
  set N : Space d → ℝ := fun y ↦ ‖gradient u (y + h • v) - gradient u y‖ with hN
  set c1 := Mφ * η * |h| / 2 with hc1
  set c2 := Mφ * η / (2 * |h|) + Mφ * (2 * Λ / δ) with hc2
  have hpt : ∀ y, |inner ℝ (Rem y) (gradient φ y)| ≤ c1 + c2 * N y ^ 2 := by
    intro y
    have ht := htaylor _ _ (hgu y) (hgu (y + h • v))
    have hN0 : 0 ≤ N y := norm_nonneg _
    have hamgm : N y ≤ (|h| ^ 2 + N y ^ 2) / (2 * |h|) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (N y - |h|)]
    calc |inner ℝ (Rem y) (gradient φ y)| ≤ ‖Rem y‖ * ‖gradient φ y‖ := abs_real_inner_le_norm _ _
      _ ≤ (η * N y + 2 * Λ / δ * N y ^ 2) * Mφ :=
          mul_le_mul ht (hMφ y) (norm_nonneg _) (by positivity)
      _ ≤ (η * ((|h| ^ 2 + N y ^ 2) / (2 * |h|)) + 2 * Λ / δ * N y ^ 2) * Mφ := by
          apply mul_le_mul_of_nonneg_right _ hMφ0
          have := mul_le_mul_of_nonneg_left hamgm hη.le
          linarith
      _ = c1 + c2 * N y ^ 2 := by
          rw [hc1, hc2]
          field_simp
          ring
  have hΦ : Continuous (fun pq : Space d × Space d ↦ fderiv ℝ 𝒜 pq.1 pq.2) :=
    ((h𝒜.contDiff.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd
  have hQm : Measurable (fun y ↦ gradient u (y + h • v)) :=
    (measurable_gradient u).comp (measurable_add_const _)
  have hRm : Measurable Rem :=
    ((h𝒜.contDiff.continuous.measurable.comp hQm).sub
      (h𝒜.contDiff.continuous.measurable.comp (measurable_gradient u))).sub
      (hΦ.measurable.comp ((measurable_gradient u).prodMk (hQm.sub (measurable_gradient u))))
  have hIm : Measurable (fun y ↦ inner ℝ (Rem y) (gradient φ y)) :=
    hRm.inner (measurable_gradient φ)
  have hNm : Measurable N := (hQm.sub (measurable_gradient u)).norm
  have hNb : ∀ y, N y ^ 2 ≤ (2 * L) ^ 2 := by
    intro y
    apply pow_le_pow_left₀ (norm_nonneg _)
    have g1 := hgu (y + h • v)
    have g2 := hgu y
    exact (_root_.norm_sub_le _ _).trans (by linarith)
  have hNi : IntegrableOn (fun y ↦ N y ^ 2) (ball x₀ r) :=
    Measure.integrableOn_of_bounded (M := (2 * L) ^ 2) measure_ball_lt_top.ne
      (hNm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hNb y))
  have hrhs : IntegrableOn (fun y ↦ c1 + c2 * N y ^ 2) (ball x₀ r) :=
    (integrable_const c1).add (hNi.const_mul c2)
  have hlhs : IntegrableOn (fun y ↦ |inner ℝ (Rem y) (gradient φ y)|) (ball x₀ r) :=
    Measure.integrableOn_of_bounded (M := c1 + c2 * (2 * L) ^ 2) measure_ball_lt_top.ne
      (continuous_abs.measurable.comp hIm).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ by
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        exact (hpt y).trans (by
          have hc2nn : 0 ≤ c2 := by positivity
          have := mul_le_mul_of_nonneg_left (hNb y) hc2nn
          linarith)))
  have hset : ∫ y in ball x₀ r, inner ℝ (Rem y) (gradient φ y) =
      ∫ y, inner ℝ (Rem y) (gradient φ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [gradient_eq_zero_of_notMem_tsupport (fun h' ↦ hy (hsub h')), inner_zero_right]
  change |∫ y, inner ℝ (Rem y) (gradient φ y)| ≤ _
  rw [← hset]
  calc |∫ y in ball x₀ r, inner ℝ (Rem y) (gradient φ y)|
      ≤ ∫ y in ball x₀ r, |inner ℝ (Rem y) (gradient φ y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in ball x₀ r, (c1 + c2 * N y ^ 2) := integral_mono hlhs hrhs hpt
    _ = c1 * V + c2 * ∫ y in ball x₀ r, N y ^ 2 := by
        rw [integral_add (integrable_const c1) (hNi.const_mul c2), integral_const_mul,
          setIntegral_const, smul_eq_mul, mul_comm (volume.real (ball x₀ r)) c1]
    _ ≤ c1 * V + c2 * (|h| ^ 2 * C2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcac' (by positivity))
    _ = Mφ * |h| * (η * (V + C2) / 2 + 2 * Λ / δ * |h| * C2) := by
        rw [hc1, hc2]
        field_simp
        ring

/-- **The linearized equation.** Let `u` be an `L`-Lipschitz weak solution of `div 𝒜(∇u) = 0` in
`ball x₀ R`, `r < R`, and let `G ∈ L²(B_r)` be a weak gradient of `w = ∂ᵥu` on `B_r` (one exists by
`IsWeakSolution.exists_hasWeakGradientOn_fderiv`). Then `w` is a weak solution in `B_r` of the
linearized equation `div (D𝒜(∇u) ∇w) = 0`:
`∫ ⟪D𝒜(∇u) G, ∇φ⟫ = 0` for every `C¹` test function `φ` compactly supported in `B_r`. -/
theorem IsWeakSolution.integral_inner_fderiv_flux_eq_zero {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ} (hweak : IsWeakSolution 𝒜 u (ball x₀ R))
    {r : ℝ} (hrR : r < R) (v : Space d) {G : Space d → Space d}
    (hG : HasWeakGradientOn (ball x₀ r) (fun y ↦ fderiv ℝ u y v) G)
    (hGm : MemLp G 2 (volume.restrict (ball x₀ r)))
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ ball x₀ r) :
    ∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y) (G y)) (gradient φ y) = 0 := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set ρ := (r + R) / 2 with hρ
  have hrρ : r < ρ := by rw [hρ]; linarith
  have hρR : ρ < R := by rw [hρ]; linarith
  set C2 := 4 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * volume.real (closedBall x₀ ρ) /
    (ρ - r) ^ 2 with hC2
  set V := volume.real (ball x₀ r) with hV
  have hlam := h𝒜.pos
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (h𝒜.bounded 0 (by simp))
  have hC2nn : 0 ≤ C2 := by positivity
  have hVnn : 0 ≤ V := measureReal_nonneg
  obtain ⟨Mφ, hMφ0, hMφ⟩ := exists_bound_norm_gradient hφ hφc
  obtain ⟨M, hM0, hM⟩ := h𝒜.exists_bound
  have hgφ0 : ∀ y ∉ ball x₀ r, gradient φ y = 0 :=
    fun y hy ↦ gradient_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsub h))
  have hgu : ∀ y, ‖gradient u y‖ ≤ L := norm_gradient_le_of_lipschitz hu
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hΦ : Continuous (fun pq : Space d × Space d ↦ fderiv ℝ 𝒜 pq.1 pq.2) :=
    ((h𝒜.contDiff.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd
  set f : Fin d → Space d → ℝ :=
    fun i y ↦ inner ℝ (fderiv ℝ 𝒜 (gradient u y) (b i)) (gradient φ y) with hf_def
  have hfm : ∀ i, MemLp (f i) 2 (volume.restrict (ball x₀ r)) := by
    intro i
    refine MemLp.of_bound ?_ (Λ * Mφ) (Eventually.of_forall (fun y ↦ ?_))
    · exact ((hΦ.measurable.comp ((measurable_gradient u).prodMk measurable_const)).inner
        (measurable_gradient φ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul ?_ (hMφ y) (norm_nonneg _) hΛ)
      calc ‖fderiv ℝ 𝒜 (gradient u y) (b i)‖ ≤ ‖fderiv ℝ 𝒜 (gradient u y)‖ * ‖b i‖ :=
            le_opNorm _ _
        _ ≤ Λ * 1 := mul_le_mul (h𝒜.bounded _ (hgu y)) (b.norm_eq_one i).le (norm_nonneg _) hΛ
        _ = Λ := mul_one Λ
  have hdec : ∀ y (X : Space d), inner ℝ (fderiv ℝ 𝒜 (gradient u y) X) (gradient φ y) =
      ∑ i, inner ℝ X (b i) * f i y := by
    intro y X
    conv_lhs => rw [← b.sum_repr' X]
    rw [map_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, real_inner_smul_left, real_inner_comm X (b i)]
  set T1 : ℝ → ℝ := fun h ↦ ∑ i, ∫ y in ball x₀ r, fderiv ℝ (diffQuot u v h) y (b i) * f i y
    with hT1
  have hT1lim : Tendsto T1 (𝓝[≠] 0)
      (𝓝 (∑ i, ∫ y in ball x₀ r, inner ℝ (G y) (b i) * f i y)) :=
    tendsto_finsetSum _ (fun i _ ↦ IsWeakSolution.tendsto_setIntegral_fderiv_diffQuot_mul
      h𝒜 hu hweak hrR v hG hGm (hfm i) (b i))
  have htarget : ∑ i, ∫ y in ball x₀ r, inner ℝ (G y) (b i) * f i y =
      ∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y) (G y)) (gradient φ y) := by
    have h1 : ∑ i, ∫ y in ball x₀ r, inner ℝ (G y) (b i) * f i y =
        ∫ y in ball x₀ r, ∑ i, inner ℝ (G y) (b i) * f i y :=
      (integral_finsetSum (μ := volume.restrict (ball x₀ r)) Finset.univ
        (f := fun i y ↦ inner ℝ (G y) (b i) * f i y)
        (fun i _ ↦ (hGm.inner_const (b i)).integrable_mul (hfm i))).symm
    have h2 : ∫ y in ball x₀ r, ∑ i, inner ℝ (G y) (b i) * f i y =
        ∫ y in ball x₀ r, inner ℝ (fderiv ℝ 𝒜 (gradient u y) (G y)) (gradient φ y) :=
      setIntegral_congr_fun measurableSet_ball (fun y _ ↦ (hdec y (G y)).symm)
    have h3 : ∫ y in ball x₀ r, inner ℝ (fderiv ℝ 𝒜 (gradient u y) (G y)) (gradient φ y) =
        ∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y) (G y)) (gradient φ y) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by rw [hgφ0 y hy, inner_zero_right])
    rw [h1, h2, h3]
  have hT1zero : Tendsto T1 (𝓝[≠] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set X := Mφ * (V + C2) with hX_def
    have hX : 0 ≤ X := by positivity
    set η := ε / (2 * (X + 1)) with hη_def
    have hη : 0 < η := by positivity
    have hkey : Mφ * η * (V + C2) / 2 < ε / 2 := by
      have he : Mφ * η * (V + C2) / 2 = ε * X / (4 * (X + 1)) := by
        rw [hη_def, hX_def]
        field_simp
        ring
      rw [he, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    obtain ⟨δ, hδ, htaylor⟩ := h𝒜.exists_taylor hη
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0,
        ρ + |h| * ‖v‖ < R ∧ Mφ * (2 * Λ / δ * |h| * C2) < ε / 2 := by
      have hc1 : Continuous (fun h : ℝ ↦ ρ + |h| * ‖v‖) :=
        continuous_const.add (continuous_abs.mul continuous_const)
      have hc2 : Continuous (fun h : ℝ ↦ Mφ * (2 * Λ / δ * |h| * C2)) :=
        continuous_const.mul ((continuous_const.mul continuous_abs).mul continuous_const)
      have h01 : ρ + |(0 : ℝ)| * ‖v‖ < R := by simpa using hρR
      have h02 : Mφ * (2 * Λ / δ * |(0 : ℝ)| * C2) < ε / 2 := by
        simpa using half_pos hε
      exact (hc1.continuousAt.eventually (gt_mem_nhds h01)).and
        (hc2.continuousAt.eventually (gt_mem_nhds h02))
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with h hsm hh
    obtain ⟨hhv, hh2⟩ := hsm
    have hh' : h ≠ 0 := hh
    have habs : 0 < |h| := abs_pos.mpr hh'
    rw [Real.dist_eq, sub_zero]
    -- `T1 h` is the linearized difference quotient
    have hQm : Measurable (fun y ↦ gradient u (y + h • v)) :=
      (measurable_gradient u).comp (measurable_add_const _)
    have hIB : Integrable (fun y ↦ inner ℝ (fderiv ℝ 𝒜 (gradient u y)
        (gradient u (y + h • v) - gradient u y)) (gradient φ y)) := by
      refine integrable_of_norm_le_of_eq_zero_of_isCompact (B := Λ * (2 * L) * Mφ) ?_
        (fun y ↦ ?_) hφc (fun y hy ↦ ?_)
      · exact ((hΦ.measurable.comp ((measurable_gradient u).prodMk
          (hQm.sub (measurable_gradient u)))).inner (measurable_gradient φ)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans (mul_le_mul ?_ (hMφ y) (norm_nonneg _)
          (by positivity))
        have g1 := hgu (y + h • v)
        have g2 := hgu y
        calc ‖fderiv ℝ 𝒜 (gradient u y) (gradient u (y + h • v) - gradient u y)‖
            ≤ ‖fderiv ℝ 𝒜 (gradient u y)‖ * ‖gradient u (y + h • v) - gradient u y‖ :=
              le_opNorm _ _
          _ ≤ Λ * (2 * L) := mul_le_mul (h𝒜.bounded _ (hgu y))
              ((_root_.norm_sub_le _ _).trans (by linarith)) (norm_nonneg _) hΛ
      · rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right]
    have hIA : Integrable (fun y ↦ inner ℝ (𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y))
        (gradient φ y)) := by
      refine integrable_of_norm_le_of_eq_zero_of_isCompact (B := 2 * M * Mφ) ?_
        (fun y ↦ ?_) hφc (fun y hy ↦ ?_)
      · exact (((h𝒜.contDiff.continuous.measurable.comp hQm).sub
          (h𝒜.contDiff.continuous.measurable.comp (measurable_gradient u))).inner
          (measurable_gradient φ)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans (mul_le_mul ?_ (hMφ y) (norm_nonneg _)
          (by positivity))
        have g1 := hM _ (hgu (y + h • v))
        have g2 := hM _ (hgu y)
        exact (_root_.norm_sub_le _ _).trans (by linarith)
      · rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right]
    have hsubz : tsupport φ ⊆ (· + h • v) ⁻¹' ball x₀ R := by
      intro y hy
      have hy' := hsub hy
      rw [mem_ball] at hy'
      change dist (y + h • v) x₀ < R
      calc dist (y + h • v) x₀ ≤ dist (y + h • v) y + dist y x₀ := dist_triangle _ _ _
        _ = |h| * ‖v‖ + dist y x₀ := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        _ < R := by linarith
    have hdiff := IsWeakSolution.integral_inner_flux_sub_eq_zero h𝒜 hu le_rfl hweak (h • v) hφ
      hφc (hsub.trans (ball_subset_ball hrR.le)) hsubz
    have hremeq : ∫ y, inner ℝ (𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y) -
        fderiv ℝ 𝒜 (gradient u y) (gradient u (y + h • v) - gradient u y)) (gradient φ y) =
        -∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y)
          (gradient u (y + h • v) - gradient u y)) (gradient φ y) := by
      have hfun : (fun y ↦ inner ℝ (𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y) -
          fderiv ℝ 𝒜 (gradient u y) (gradient u (y + h • v) - gradient u y)) (gradient φ y)) =
          fun y ↦ inner ℝ (𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y)) (gradient φ y) -
            inner ℝ (fderiv ℝ 𝒜 (gradient u y)
              (gradient u (y + h • v) - gradient u y)) (gradient φ y) := by
        funext y
        rw [inner_sub_left]
      rw [hfun, integral_sub hIA hIB, hdiff, zero_sub]
    have hT1eq : T1 h = h⁻¹ * ∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y)
        (gradient u (y + h • v) - gradient u y)) (gradient φ y) := by
      have hint : ∀ i, Integrable (fun y ↦ fderiv ℝ (diffQuot u v h) y (b i) * f i y)
          (volume.restrict (ball x₀ r)) := fun i ↦
        (memLp_fderiv_diffQuot hu v h (b i) (ball x₀ r) measure_ball_lt_top.ne).integrable_mul
          (hfm i)
      have h0 := hu.ae_differentiableAt (μ := volume)
      have h1 : ∀ᵐ y, DifferentiableAt ℝ u (y + h • v) :=
        (measurePreserving_add_right volume (h • v)).quasiMeasurePreserving.ae h0
      have hpt : ∀ᵐ y ∂(volume.restrict (ball x₀ r)),
          ∑ i, fderiv ℝ (diffQuot u v h) y (b i) * f i y =
            h⁻¹ * inner ℝ (fderiv ℝ 𝒜 (gradient u y)
              (gradient u (y + h • v) - gradient u y)) (gradient φ y) := by
        refine ae_restrict_of_ae ?_
        filter_upwards [h0, h1] with y hy0 hy1
        rw [← real_inner_smul_left, ← map_smul, hdec]
        apply Finset.sum_congr rfl
        intro i _
        rw [fderiv_diffQuot_apply hy0 hy1, real_inner_smul_left, div_eq_inv_mul]
      have e1 : T1 h = ∫ y in ball x₀ r, ∑ i, fderiv ℝ (diffQuot u v h) y (b i) * f i y :=
        (integral_finsetSum (μ := volume.restrict (ball x₀ r)) Finset.univ
          (f := fun i y ↦ fderiv ℝ (diffQuot u v h) y (b i) * f i y) (fun i _ ↦ hint i)).symm
      have e2 : ∫ y in ball x₀ r, inner ℝ (fderiv ℝ 𝒜 (gradient u y)
          (gradient u (y + h • v) - gradient u y)) (gradient φ y) =
          ∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y)
            (gradient u (y + h • v) - gradient u y)) (gradient φ y) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy ↦ by rw [hgφ0 y hy, inner_zero_right])
      rw [e1, integral_congr_ae hpt, integral_const_mul, e2]
    have hrem := IsWeakSolution.abs_integral_inner_remainder_le h𝒜 hu hweak hrρ hsub hMφ0 hMφ
      hη hδ htaylor v hh' hhv
    rw [hremeq, abs_neg] at hrem
    rw [hT1eq, abs_mul, abs_inv]
    calc |h|⁻¹ * |∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y)
          (gradient u (y + h • v) - gradient u y)) (gradient φ y)|
        ≤ |h|⁻¹ * (Mφ * |h| * (η * (V + C2) / 2 + 2 * Λ / δ * |h| * C2)) :=
          mul_le_mul_of_nonneg_left hrem (by positivity)
      _ = Mφ * η * (V + C2) / 2 + Mφ * (2 * Λ / δ * |h| * C2) := by
          field_simp
      _ < ε := by linarith
  rw [← htarget]
  exact tendsto_nhds_unique hT1lim hT1zero

/-- **First Schauder step, combined.** An `L`-Lipschitz weak solution of `div 𝒜(∇u) = 0` in
`ball x₀ R` has, for every direction `v` and every `r < R`, a weak gradient `G ∈ L²(B_r)` of
`∂ᵥu` on `B_r` with the explicit bound of `IsWeakSolution.exists_hasWeakGradientOn_fderiv`, and
`∂ᵥu` solves the linearized equation `div (D𝒜(∇u) G) = 0` weakly in `B_r`. -/
theorem IsWeakSolution.exists_hasWeakGradientOn_fderiv_linearized {d : ℕ}
    {𝒜 : Space d → Space d} {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ)
    {u : Space d → ℝ} (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ}
    (hweak : IsWeakSolution 𝒜 u (ball x₀ R)) {r : ℝ} (hrR : r < R) (v : Space d) :
    ∃ G : Space d → Space d, HasWeakGradientOn (ball x₀ r) (fun y ↦ fderiv ℝ u y v) G ∧
      MemLp G 2 (volume.restrict (ball x₀ r)) ∧
      ∫ y in ball x₀ r, ‖G y‖ ^ 2 ≤ d * (16 * (Λ / lam) ^ 2 * (L : ℝ) ^ 2 * ‖v‖ ^ 2 *
        volume.real (closedBall x₀ ((r + R) / 2)) / (R - r) ^ 2) ∧
      ∀ φ : Space d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball x₀ r →
        ∫ y, inner ℝ (fderiv ℝ 𝒜 (gradient u y) (G y)) (gradient φ y) = 0 := by
  obtain ⟨G, hG, hGm, hGb⟩ := IsWeakSolution.exists_hasWeakGradientOn_fderiv h𝒜 hu hweak hrR v
  exact ⟨G, hG, hGm, hGb, fun φ hφ hφc hsub ↦
    IsWeakSolution.integral_inner_fderiv_flux_eq_zero h𝒜 hu hweak hrR v hG hGm hφ hφc hsub⟩

/-- **The linearized minimal surface equation.** For a globally `L`-Lipschitz weak solution of the
minimal surface equation in `ball x₀ R` and a weak gradient `G ∈ L²(B_r)` of `w = ∂ᵥu` on `B_r`,
`r < R`, writing `W = √(1 + ‖∇u‖²)`,
`∫ (W⁻¹ ⟪G, ∇φ⟫ - W⁻³ ⟪∇u, G⟫ ⟪∇u, ∇φ⟫) = 0` for every `C¹` test `φ` compactly supported in
`B_r`. -/
theorem integral_linearized_minimalSurface_eq_zero {d : ℕ} {u : Space d → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) {x₀ : Space d} {R : ℝ}
    (hweak : IsWeakSolution minimalSurfaceFlux u (ball x₀ R)) {r : ℝ} (hrR : r < R)
    (v : Space d) {G : Space d → Space d}
    (hG : HasWeakGradientOn (ball x₀ r) (fun y ↦ fderiv ℝ u y v) G)
    (hGm : MemLp G 2 (volume.restrict (ball x₀ r)))
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ ball x₀ r) :
    ∫ y, ((Real.sqrt (1 + ‖gradient u y‖ ^ 2))⁻¹ * inner ℝ (G y) (gradient φ y) -
      (Real.sqrt (1 + ‖gradient u y‖ ^ 2) ^ 3)⁻¹ * inner ℝ (gradient u y) (G y) *
        inner ℝ (gradient u y) (gradient φ y)) = 0 := by
  have h := IsWeakSolution.integral_inner_fderiv_flux_eq_zero
    (isEllipticFlux_minimalSurfaceFlux (L : ℝ)) hu hweak hrR v hG hGm hφ hφc hsub
  rw [← h]
  congr 1
  funext y
  rw [fderiv_minimalSurfaceFlux_apply, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, mul_assoc]

/-! ### The linear equation solved by difference quotients -/

/-- The averaged coefficient `∫₀¹ D𝒜(p + t (q - p)) dt`. -/
def avgFluxDeriv {d : ℕ} (𝒜 : Space d → Space d) (p q : Space d) : Space d →L[ℝ] Space d :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ 𝒜 (p + t • (q - p))

namespace IsEllipticFlux

variable {d : ℕ} {𝒜 : Space d → Space d} {L lam Λ : ℝ}

theorem continuous_fderiv_segment (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) (p q : Space d) :
    Continuous (fun t : ℝ ↦ fderiv ℝ 𝒜 (p + t • (q - p))) :=
  (h𝒜.contDiff.continuous_fderiv one_ne_zero).comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- The fundamental theorem of calculus along a segment:
`𝒜 q - 𝒜 p = (∫₀¹ D𝒜(p + t (q - p)) dt) (q - p)`. -/
theorem sub_eq_avgFluxDeriv_apply (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) (p q : Space d) :
    𝒜 q - 𝒜 p = avgFluxDeriv 𝒜 p q (q - p) := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ 𝒜 (p + t • (q - p))) volume 0 1 :=
    (h𝒜.continuous_fderiv_segment p q).intervalIntegrable 0 1
  rw [avgFluxDeriv, ContinuousLinearMap.intervalIntegral_apply hint]
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ 𝒜 (p + t • (q - p)))
      (fderiv ℝ 𝒜 (p + t • (q - p)) (q - p)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ ↦ p + t • (q - p)) (q - p) t := by
      simpa using ((hasDerivAt_id t).smul_const (q - p)).const_add p
    exact (h𝒜.contDiff.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous (fun t : ℝ ↦ fderiv ℝ 𝒜 (p + t • (q - p)) (q - p)) :=
    (h𝒜.continuous_fderiv_segment p q).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (hcont.intervalIntegrable 0 1)]
  simp

/-- The averaged coefficient is uniformly elliptic on the ball `‖p‖ ≤ L`. -/
theorem inner_avgFluxDeriv_ge (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {p q : Space d}
    (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L) (ξ : Space d) :
    lam * ‖ξ‖ ^ 2 ≤ inner ℝ (avgFluxDeriv 𝒜 p q ξ) ξ := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ 𝒜 (p + t • (q - p))) volume 0 1 :=
    (h𝒜.continuous_fderiv_segment p q).intervalIntegrable 0 1
  have hcont : Continuous (fun t : ℝ ↦ fderiv ℝ 𝒜 (p + t • (q - p)) ξ) :=
    (h𝒜.continuous_fderiv_segment p q).clm_apply continuous_const
  rw [avgFluxDeriv, ContinuousLinearMap.intervalIntegral_apply hint, real_inner_comm,
    ← innerSL_apply_apply ℝ ξ,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hcont.intervalIntegrable 0 1)]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (f := fun _ : ℝ ↦ lam * ‖ξ‖ ^ 2)
    (g := fun t ↦ innerSL ℝ ξ (fderiv ℝ 𝒜 (p + t • (q - p)) ξ))
    intervalIntegrable_const
    (((innerSL ℝ ξ).continuous.comp hcont).intervalIntegrable 0 1)
    (fun t ht ↦ by
      rw [innerSL_apply_apply, real_inner_comm]
      exact h𝒜.elliptic _ (norm_add_smul_sub_le hp hq ht) ξ)
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at hmono
  exact hmono

/-- The averaged coefficient is bounded by `Λ` on the ball `‖p‖ ≤ L`. -/
theorem norm_avgFluxDeriv_le (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {p q : Space d}
    (hp : ‖p‖ ≤ L) (hq : ‖q‖ ≤ L) : ‖avgFluxDeriv 𝒜 p q‖ ≤ Λ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := Λ)
    (f := fun t : ℝ ↦ fderiv ℝ 𝒜 (p + t • (q - p))) (fun t ht ↦ by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact h𝒜.bounded _ (norm_add_smul_sub_le hp hq (Set.Ioc_subset_Icc_self ht)))
  rwa [sub_zero, abs_one, mul_one] at h

/-- The averaged coefficient depends continuously on its endpoints. -/
theorem continuous_avgFluxDeriv (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) :
    Continuous (fun pq : Space d × Space d ↦ avgFluxDeriv 𝒜 pq.1 pq.2) := by
  have hc : Continuous (Function.uncurry
      (fun (pq : Space d × Space d) (t : ℝ) ↦ fderiv ℝ 𝒜 (pq.1 + t • (pq.2 - pq.1)))) :=
    (h𝒜.contDiff.continuous_fderiv one_ne_zero).comp
      ((continuous_fst.comp continuous_fst).add (continuous_snd.smul
        ((continuous_snd.comp continuous_fst).sub (continuous_fst.comp continuous_fst))))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1

end IsEllipticFlux

/-- The gradient of a difference quotient, at a point where `u` is differentiable at both
ends. -/
theorem gradient_diffQuot {d : ℕ} {u : Space d → ℝ} {v y : Space d} {h : ℝ}
    (hu0 : DifferentiableAt ℝ u y) (hu1 : DifferentiableAt ℝ u (y + h • v)) :
    gradient (diffQuot u v h) y = h⁻¹ • (gradient u (y + h • v) - gradient u y) := by
  apply ext_inner_right ℝ
  intro e
  rw [real_inner_smul_left, gradient, toDual_symm_apply, fderiv_diffQuot_apply hu0 hu1,
    div_eq_inv_mul]

/-- **Difference quotients solve a linear equation.** For `h ≠ 0`, the difference quotient
`w = D_h^v u` is a weak solution of the linear equation `div (A_h ∇w) = 0`, whose coefficient
`A_h(y) = ∫₀¹ D𝒜(∇u(y) + t (∇u(y + h v) - ∇u(y))) dt` is measurable, bounded by `Λ` and
uniformly elliptic with constant `λ` (`IsEllipticFlux.continuous_avgFluxDeriv`,
`IsEllipticFlux.norm_avgFluxDeriv_le`, `IsEllipticFlux.inner_avgFluxDeriv_ge`). -/
theorem IsWeakSolution.integral_inner_avgFluxDeriv_eq_zero {d : ℕ} {𝒜 : Space d → Space d}
    {L : NNReal} {lam Λ : ℝ} (h𝒜 : IsEllipticFlux 𝒜 L lam Λ) {u : Space d → ℝ}
    (hu : LipschitzWith L u) {U : Set (Space d)} (hweak : IsWeakSolution 𝒜 u U) (v : Space d)
    {h : ℝ} {φ : Space d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) (hsubh : tsupport φ ⊆ (· + h • v) ⁻¹' U) :
    ∫ y, inner ℝ (avgFluxDeriv 𝒜 (gradient u y) (gradient u (y + h • v))
      (gradient (diffQuot u v h) y)) (gradient φ y) = 0 := by
  have hdiff := IsWeakSolution.integral_inner_flux_sub_eq_zero h𝒜 hu le_rfl hweak (h • v) hφ
    hφc hsub hsubh
  have h0 := hu.ae_differentiableAt (μ := volume)
  have h1 : ∀ᵐ y, DifferentiableAt ℝ u (y + h • v) :=
    (measurePreserving_add_right volume (h • v)).quasiMeasurePreserving.ae h0
  have hpt : ∀ᵐ y, inner ℝ (avgFluxDeriv 𝒜 (gradient u y) (gradient u (y + h • v))
      (gradient (diffQuot u v h) y)) (gradient φ y) =
      h⁻¹ * inner ℝ (𝒜 (gradient u (y + h • v)) - 𝒜 (gradient u y)) (gradient φ y) := by
    filter_upwards [h0, h1] with y hy0 hy1
    rw [gradient_diffQuot hy0 hy1, map_smul, ← h𝒜.sub_eq_avgFluxDeriv_apply,
      real_inner_smul_left]
  rw [integral_congr_ae hpt, integral_const_mul, hdiff, mul_zero]

end SerrinEpigraph
