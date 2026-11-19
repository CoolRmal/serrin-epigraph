module

public import SerrinEpigraph.WeakEquation
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weyl's lemma and interior estimates for harmonic functions

All statements are on `Space d = EuclideanSpace ℝ (Fin d)` for an arbitrary dimension `d`
(including `d = 0`). "Harmonic" means `C²` on an open set `U` with `Δ h = 0` on `U`; no higher
regularity is assumed. "Smooth" means `ContDiff ℝ (⊤ : ℕ∞)`, i.e. `C^∞` (not analytic).

* `integral_fderiv_mul_radial_eq_zero`: for a radial weight `g (‖z‖ ^ 2)` vanishing outside the
  unit ball, `∫ ∇h(x + s z) · z g(‖z‖²) dz = 0`. The proof writes `z g(‖z‖²) = ∇R(z)` for the
  compactly supported radial potential `R = radialPotential g` and integrates by parts.
* `harmonic_integral_comp_mul_radial`: the radial mollifier identity
  `∫ h (x + s • z) * g (‖z‖ ^ 2) dz = h x * ∫ g (‖z‖ ^ 2) dz` for `0 ≤ s ≤ r`, obtained by
  differentiating in `s` under the integral.
* `harmonic_eq_integral_radial` (item 2): `h x = ∫ h (x + s • z) * ρ z dz` for every continuous
  radial `ρ` supported in the closed unit ball with `∫ ρ = 1`.
* `harmonicKernel`, `scaledHarmonicKernel`: an explicit smooth radial mollifier (Mathlib's
  `ContDiffBump.normed` is not provably radial) and `harmonic_eq_convolution`,
  `h x = (h ⋆ ρ_r) x`.
* `norm_fderiv_le_of_harmonic`, `norm_iteratedFDeriv_two_le_of_harmonic`,
  `norm_iteratedFDeriv_two_le_of_harmonic_grad` (item 5): interior estimates with the
  constants `harmonicGradConst d`, `harmonicHessConst d`.
* `harmonic_fderiv_excess_le`, `harmonic_taylor_excess_le` and their unit-ball versions
  (item 6): excess decay with the constants `harmonicGradExcessConst d`,
  `harmonicTaylorExcessConst d`.
* `IsVeryWeaklyHarmonicOn` (item 1) and `weyl_lemma` (item 4): a very weakly harmonic
  function agrees a.e. with a smooth harmonic function. The proof shows that the
  mollifications `h ⋆ ρ_ε` are harmonic, do not depend on `ε` (by the mollifier identity and
  associativity of convolution) and converge to `h` almost everywhere (Lebesgue
  differentiation), then glues the local representatives.
* `harmonic_eq_average_ball` (item 3): the mean value property on balls, from the radial
  identity with continuous profiles increasing to the indicator of the unit ball.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian ContDiff Convolution

namespace SerrinEpigraph

/-! ### The radial potential of a radial profile -/

/-- The primitive, in the squared radius, of a radial profile `g`, normalized at `1`. -/
def radialPrimitive (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  (∫ t in (1 : ℝ)..u, g t) / 2

theorem hasDerivAt_radialPrimitive {g : ℝ → ℝ} (hg : Continuous g) (u : ℝ) :
    HasDerivAt (radialPrimitive g) (g u / 2) u := by
  have h := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 1 u)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  exact h.div_const 2

theorem contDiff_radialPrimitive {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (radialPrimitive g) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u ↦ (hasDerivAt_radialPrimitive hg u).differentiableAt, ?_⟩
  have hd : deriv (radialPrimitive g) = fun u ↦ g u / 2 :=
    funext fun u ↦ (hasDerivAt_radialPrimitive hg u).deriv
  rw [hd]
  exact hg.div_const 2

theorem radialPrimitive_eq_zero {g : ℝ → ℝ} (hg0 : ∀ t, 1 < t → g t = 0) {u : ℝ}
    (hu : 1 ≤ u) : radialPrimitive g u = 0 := by
  have hi : ∫ t in (1 : ℝ)..u, g t = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le hu] at ht
    exact hg0 t ht.1
  simp [radialPrimitive, hi]

variable {d : ℕ}

/-- The radial potential `z ↦ G (‖z‖ ^ 2)` of a profile `g`; its gradient is `g (‖z‖ ^ 2) • z`. -/
def radialPotential (g : ℝ → ℝ) (z : Space d) : ℝ :=
  radialPrimitive g (‖z‖ ^ 2)

theorem hasFDerivAt_radialPotential {g : ℝ → ℝ} (hg : Continuous g) (z : Space d) :
    HasFDerivAt (radialPotential g) (g (‖z‖ ^ 2) • innerSL ℝ z) z := by
  have h1 := hasDerivAt_radialPrimitive hg (‖z‖ ^ 2)
  have h2 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h3 := h1.comp_hasFDerivAt z h2
  have hL : (g (‖z‖ ^ 2) / 2) • ((2 : ℕ) • innerSL ℝ z : Space d →L[ℝ] ℝ) =
      g (‖z‖ ^ 2) • innerSL ℝ z := by
    rw [two_nsmul, smul_add, ← add_smul]
    congr 1
    ring
  rw [hL] at h3
  exact h3

theorem fderiv_radialPotential_apply {g : ℝ → ℝ} (hg : Continuous g) (z v : Space d) :
    fderiv ℝ (radialPotential g) z v = g (‖z‖ ^ 2) * inner ℝ z v := by
  rw [(hasFDerivAt_radialPotential hg z).fderiv]
  simp

theorem contDiff_radialPotential {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (radialPotential (d := d) g) :=
  (contDiff_radialPrimitive hg).comp (contDiff_norm_sq ℝ)

theorem radialPotential_eq_zero {g : ℝ → ℝ} (hg0 : ∀ t, 1 < t → g t = 0) {z : Space d}
    (hz : 1 ≤ ‖z‖) : radialPotential g z = 0 :=
  radialPrimitive_eq_zero hg0 (one_le_pow₀ hz)

theorem hasCompactSupport_radialPotential {g : ℝ → ℝ} (hg0 : ∀ t, 1 < t → g t = 0) :
    HasCompactSupport (radialPotential (d := d) g) :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz ↦
    radialPotential_eq_zero hg0 (by
      simp only [mem_closedBall, dist_zero_right, not_le] at hz
      exact hz.le)

/-! ### The vanishing radial moment of the gradient -/

/-- Change of variables `y = x + s • z` in a full integral. -/
private theorem integral_comp_add_smul (F : Space d → ℝ) (x : Space d) {s : ℝ} (hs : 0 < s) :
    ∫ z, F (x + s • z) = (s ^ d)⁻¹ * ∫ y, F y := by
  have h1 := Measure.integral_comp_smul (volume : Measure (Space d)) (fun y ↦ F (x + y)) s
  have h2 := integral_add_left_eq_self (μ := (volume : Measure (Space d))) F x
  simp only [finrank_euclideanSpace_fin] at h1
  rw [h1, h2, smul_eq_mul, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hs.le d))]

theorem integral_fderiv_mul_radial_eq_zero {h : Space d → ℝ} {x : Space d} {s : ℝ}
    (hh : ContDiff ℝ 2 h) (hΔ : ∀ y ∈ closedBall x s, Δ h y = 0) (hs : 0 < s)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 1 < t → g t = 0) :
    ∫ z, fderiv ℝ h (x + s • z) z * g (‖z‖ ^ 2) = 0 := by
  set R : Space d → ℝ := radialPotential g with hRdef
  let A : Space d → Space d := fun y ↦ s⁻¹ • (y - x)
  let φ : Space d → ℝ := fun y ↦ R (A y)
  have hA : ∀ y, HasFDerivAt A (s⁻¹ • ContinuousLinearMap.id ℝ (Space d)) y := fun y ↦ by
    exact ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x).const_smul s⁻¹
  have hφd : ∀ y, HasFDerivAt φ ((g (‖A y‖ ^ 2) • innerSL ℝ (A y)).comp
      (s⁻¹ • ContinuousLinearMap.id ℝ (Space d))) y := fun y ↦
    (hasFDerivAt_radialPotential hg (A y)).comp y (hA y)
  have hAc : ContDiff ℝ 1 A := (contDiff_id.sub contDiff_const).const_smul s⁻¹
  have hφ : ContDiff ℝ 1 φ := (contDiff_radialPotential hg).comp hAc
  have hφs : ∀ y, φ y ≠ 0 → y ∈ closedBall x s := by
    intro y hy
    by_contra hyx
    apply hy
    apply radialPotential_eq_zero hg0
    simp only [mem_closedBall, dist_eq_norm, not_le] at hyx
    simp only [A, norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
    rw [le_inv_mul_iff₀ hs]
    linarith
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x s) fun y hy ↦ by
      by_contra hne
      exact hy (hφs y hne)
  have green := integral_inner_gradient_eq_neg_laplacian_mul (μ := volume) isOpen_univ
    hh.contDiffOn hφ hφc (subset_univ _)
  have hrhs : (fun y ↦ (Δ h) y * φ y) = fun _ ↦ 0 := by
    funext y
    by_cases hy : φ y = 0
    · simp [hy]
    · simp [hΔ y (hφs y hy)]
  rw [hrhs, integral_zero, neg_zero] at green
  have hpt : ∀ y, inner ℝ (gradient h y) (gradient φ y) =
      s⁻¹ * (g (‖A y‖ ^ 2) * fderiv ℝ h y (A y)) := by
    intro y
    rw [inner_gradient_right, (hφd y).fderiv, conj_trivial]
    change g (‖A y‖ ^ 2) * inner ℝ (A y) (s⁻¹ • gradient h y) = _
    rw [real_inner_smul_right, real_inner_comm, inner_gradient_left]
    ring
  simp_rw [hpt, integral_const_mul] at green
  have hF : ∫ y, g (‖A y‖ ^ 2) * fderiv ℝ h y (A y) = 0 := by
    rcases mul_eq_zero.mp green with h0 | h0
    · exact absurd h0 (inv_ne_zero hs.ne')
    · exact h0
  have hcv := integral_comp_add_smul (fun y ↦ g (‖A y‖ ^ 2) * fderiv ℝ h y (A y)) x hs
  rw [hF, mul_zero] at hcv
  have hAz : ∀ z : Space d, A (x + s • z) = z := fun z ↦ by
    simp [A, smul_smul, inv_mul_cancel₀ hs.ne']
  simp_rw [hAz] at hcv
  rw [← hcv]
  apply integral_congr_ae
  filter_upwards with z
  ring


/-- The radial mollifier identity for a globally `C²` function harmonic on a closed ball. -/
theorem integral_comp_mul_radial_of_contDiff {h : Space d → ℝ} {x : Space d} {r : ℝ}
    (hh : ContDiff ℝ 2 h) (hΔ : ∀ y ∈ closedBall x r, Δ h y = 0)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 1 < t → g t = 0) {s : ℝ}
    (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    ∫ z, h (x + s • z) * g (‖z‖ ^ 2) = h x * ∫ z : Space d, g (‖z‖ ^ 2) := by
  set ρ : Space d → ℝ := fun z ↦ g (‖z‖ ^ 2) with hρdef
  have hρc : Continuous ρ := hg.comp (continuous_norm.pow 2)
  have hρ0 : ∀ z : Space d, 1 < ‖z‖ → ρ z = 0 := fun z hz ↦
    hg0 _ (by nlinarith [norm_nonneg z])
  have hρs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz ↦ hρ0 z (by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hz)
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hdh : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdf : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  let M : ℝ → ℝ := fun t ↦ ∫ z, h (x + t • z) * ρ z
  let M' : ℝ → ℝ := fun t ↦ ∫ z, fderiv ℝ h (x + t • z) z * ρ z
  have hline : ∀ (z : Space d) (t : ℝ), HasDerivAt (fun t : ℝ ↦ x + t • z) z t :=
    fun z t ↦ by simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have hderiv : ∀ t₀, HasDerivAt M (M' t₀) t₀ := by
    intro t₀
    obtain ⟨C, hC⟩ := (isCompact_closedBall x (|t₀| + 1)).exists_bound_of_continuousOn
      hdf.continuousOn
    have hcont : ∀ t : ℝ, Continuous fun z : Space d ↦ x + t • z := fun t ↦ by fun_prop
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun t z ↦ h (x + t • z) * ρ z) (F' := fun t z ↦ fderiv ℝ h (x + t • z) z * ρ z)
      (x₀ := t₀) (bound := fun z ↦ C * |ρ z|) (ball_mem_nhds t₀ one_pos)
      (Eventually.of_forall fun t ↦
        ((hh.continuous.comp (hcont t)).mul hρc).aestronglyMeasurable)
      (((hh.continuous.comp (hcont t₀)).mul hρc).integrable_of_hasCompactSupport
        hρs.mul_left)
      (((hdf.comp (hcont t₀)).clm_apply continuous_id).mul hρc).aestronglyMeasurable
      ?_ (hρi.abs.const_mul C) ?_
    · exact key.2
    · filter_upwards with z t ht
      by_cases hz : ρ z = 0
      · simp [hz]
      · have hz1 : ‖z‖ ≤ 1 := by
          by_contra hcon
          exact hz (hρ0 z (lt_of_not_ge hcon))
        have ht' : |t| ≤ |t₀| + 1 := by
          have h1 := mem_ball.mp ht
          rw [Real.dist_eq] at h1
          have h2 := abs_sub_abs_le_abs_sub t t₀
          linarith
        have hmem : x + t • z ∈ closedBall x (|t₀| + 1) := by
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          calc |t| * ‖z‖ ≤ |t| * 1 := by gcongr
            _ ≤ |t₀| + 1 := by linarith
        have hb : ‖fderiv ℝ h (x + t • z) z‖ ≤ C :=
          calc ‖fderiv ℝ h (x + t • z) z‖ ≤ ‖fderiv ℝ h (x + t • z)‖ * ‖z‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ C * 1 := mul_le_mul (hC _ hmem) hz1 (norm_nonneg _)
                ((norm_nonneg _).trans (hC _ hmem))
            _ = C := mul_one C
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    · filter_upwards with z t _
      exact ((hdh (x + t • z)).hasFDerivAt.comp_hasDerivAt t (hline z t)).mul_const (ρ z)
  rcases hs0.eq_or_lt with rfl | hspos
  · simp only [zero_smul, add_zero, integral_const_mul]
    rfl
  · obtain ⟨c, hc, hcM⟩ := exists_hasDerivAt_eq_slope M M' hspos
      (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt) (fun t _ ↦ hderiv t)
    have hM'c : M' c = 0 := integral_fderiv_mul_radial_eq_zero hh
      (fun y hy ↦ hΔ y (closedBall_subset_closedBall (hc.2.le.trans hsr) hy)) hc.1 hg hg0
    rw [hM'c, eq_comm, div_eq_zero_iff, sub_zero] at hcM
    have hMs : M s = M 0 := by
      rcases hcM with h1 | h1
      · linarith
      · exact absurd h1 hspos.ne'
    change M s = _
    rw [hMs]
    simp only [M, zero_smul, add_zero, integral_const_mul]

/-- A function that is `C^n` on an open set coincides, on a ball slightly larger than a
given closed ball inside the set, with a globally `C^n` function. -/
theorem exists_contDiff_eqOn_ball_of_contDiffOn {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} {n : ℕ∞} (hh : ContDiffOn ℝ n h U) {x : Space d} {r : ℝ} (hr : 0 ≤ r)
    (hxr : closedBall x r ⊆ U) :
    ∃ r' > r, ∃ h' : Space d → ℝ, ContDiff ℝ n h' ∧ EqOn h' h (ball x r') ∧
      closedBall x r' ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU hxr
  rw [cthickening_closedBall hδ.le hr] at hδU
  let χ : ContDiffBump x := ⟨r + δ / 2, δ + r, by positivity, by linarith⟩
  have hχt : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    exact hδU
  refine ⟨r + δ / 2, by linarith, fun y ↦ h y * χ y, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (hh.contDiffAt (hU.mem_nhds hy)).mul χ.contDiff.contDiffAt
    · have hev : χ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp fun hy' ↦ hy (hχt hy')
      apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hev] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
  · intro y hy
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [h1]
  · exact (closedBall_subset_closedBall (by linarith)).trans hδU

/-- **Radial mollifier identity.** A `C²` function harmonic on an open set containing
`closedBall x r` satisfies `∫ h (x + s • z) * g (‖z‖ ^ 2) dz = h x * ∫ g (‖z‖ ^ 2) dz` for every
continuous profile `g` vanishing on `(1, ∞)` and every `0 ≤ s ≤ r`. -/
theorem harmonic_integral_comp_mul_radial {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t, 1 < t → g t = 0) {s : ℝ} (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    ∫ z, h (x + s • z) * g (‖z‖ ^ 2) = h x * ∫ z : Space d, g (‖z‖ ^ 2) := by
  obtain ⟨r', hr', h', hh', heq, hsub⟩ :=
    exists_contDiff_eqOn_ball_of_contDiffOn hU (n := 2) hh (hs0.trans hsr) hxr
  have hΔ' : ∀ y ∈ closedBall x r, Δ h' y = 0 := by
    intro y hy
    have hyb : y ∈ ball x r' := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hy) hr')
    have hev : h' =ᶠ[𝓝 y] h := eventuallyEq_of_mem (isOpen_ball.mem_nhds hyb) heq
    rw [(laplacian_congr_nhds hev).eq_of_nhds]
    exact hΔ y (hsub (ball_subset_closedBall hyb))
  have hmain := integral_comp_mul_radial_of_contDiff hh' hΔ' hg hg0 hs0 hsr
  rw [heq (mem_ball_self (by linarith [hs0.trans hsr]))] at hmain
  rw [← hmain]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : g (‖z‖ ^ 2) = 0
  · simp [hz]
  · have hz1 : ‖z‖ ≤ 1 := by
      by_contra hcon
      exact hz (hg0 _ (by nlinarith [norm_nonneg z]))
    have hmem : x + s • z ∈ ball x r' := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]
      calc s * ‖z‖ ≤ s * 1 := by gcongr
        _ < r' := by linarith
    rw [heq hmem]

/-- **Radial mollifier identity** (item 2). Let `h` be `C²` and harmonic on an open set `U`
containing `closedBall x r`, and let `ρ` be a continuous radial function supported in the
closed unit ball with `∫ ρ = 1`. Then `h x = ∫ h (x + s • z) * ρ z dz` for all `0 ≤ s ≤ r`. -/
theorem harmonic_eq_integral_radial {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) {ρ : Space d → ℝ} (hρ : Continuous ρ)
    (hrad : ∀ y z : Space d, ‖y‖ = ‖z‖ → ρ y = ρ z)
    (hsupp : Function.support ρ ⊆ closedBall 0 1) (hint : ∫ z, ρ z = 1) {s : ℝ}
    (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    h x = ∫ z, h (x + s • z) * ρ z := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : ∀ z : Space 0, z = 0 := fun z ↦ Subsingleton.elim z 0
    have hfun : (fun z : Space 0 ↦ h (x + s • z) * ρ z) = fun z ↦ h x * ρ z := by
      funext z
      rw [hz z, smul_zero, add_zero]
    rw [hfun, integral_const_mul, hint, mul_one]
  · obtain ⟨e, he⟩ : ∃ e : Space d, ‖e‖ = 1 :=
      ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), by simp⟩
    let g : ℝ → ℝ := fun t ↦ ρ (Real.sqrt t • e)
    have hg : Continuous g := hρ.comp (Real.continuous_sqrt.smul continuous_const)
    have hρg : ∀ z, ρ z = g (‖z‖ ^ 2) := fun z ↦ hrad _ _ (by
      simp [norm_smul, he, Real.sqrt_sq (norm_nonneg z)])
    have hg0 : ∀ t, 1 < t → g t = 0 := by
      intro t ht
      apply Function.notMem_support.mp
      intro hmem
      have h1 := hsupp hmem
      have h2 : 1 < Real.sqrt t := by
        rw [Real.lt_sqrt zero_le_one]
        simpa using ht
      simp only [mem_closedBall, dist_zero_right, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg t)] at h1
      linarith
    have key := harmonic_integral_comp_mul_radial hU hh hΔ hxr hg hg0 hs0 hsr
    simp_rw [← hρg] at key
    rw [key, hint, mul_one]


/-! ### An explicit smooth radial mollifier -/

/-- The profile, in the squared radius, of the standard radial bump. -/
def harmonicProfile (t : ℝ) : ℝ := expNegInvGlue (1 - t)

theorem contDiff_harmonicProfile {n : ℕ∞} : ContDiff ℝ n harmonicProfile :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)

theorem harmonicProfile_nonneg (t : ℝ) : 0 ≤ harmonicProfile t :=
  expNegInvGlue.nonneg _

theorem harmonicProfile_eq_zero {t : ℝ} (ht : 1 ≤ t) : harmonicProfile t = 0 :=
  expNegInvGlue.zero_of_nonpos (by linarith)

theorem harmonicProfile_pos {t : ℝ} (ht : t < 1) : 0 < harmonicProfile t :=
  expNegInvGlue.pos_of_pos (by linarith)

/-- The unnormalized standard radial bump, positive exactly on the open unit ball. -/
def harmonicBump (d : ℕ) (z : Space d) : ℝ := harmonicProfile (‖z‖ ^ 2)

theorem contDiff_harmonicBump {n : ℕ∞} : ContDiff ℝ n (harmonicBump d) :=
  contDiff_harmonicProfile.comp (contDiff_norm_sq ℝ)

theorem harmonicBump_eq_zero {z : Space d} (hz : 1 ≤ ‖z‖) : harmonicBump d z = 0 :=
  harmonicProfile_eq_zero (one_le_pow₀ hz)

theorem hasCompactSupport_harmonicBump : HasCompactSupport (harmonicBump d) :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz ↦ harmonicBump_eq_zero (by
    simp only [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le)

theorem integral_harmonicBump_pos : 0 < ∫ z : Space d, harmonicBump d z := by
  have hint : Integrable (harmonicBump d) :=
    (contDiff_harmonicBump (n := 0)).continuous.integrable_of_hasCompactSupport
      hasCompactSupport_harmonicBump
  refine (integral_pos_iff_support_of_nonneg (f := harmonicBump d)
    (fun z ↦ harmonicProfile_nonneg _) hint).2 ?_
  have hsub : ball (0 : Space d) 1 ⊆ Function.support (harmonicBump d) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact (harmonicProfile_pos (by nlinarith [norm_nonneg z])).ne'
  exact (measure_ball_pos volume 0 one_pos).trans_le (measure_mono hsub)

/-- The normalized profile of the standard mollifier. -/
def harmonicKernelProfile (d : ℕ) (t : ℝ) : ℝ :=
  (∫ z : Space d, harmonicBump d z)⁻¹ * harmonicProfile t

/-- The standard smooth radial mollifier on `Space d`: it is nonnegative, vanishes outside the
open unit ball and has integral one. -/
def harmonicKernel (d : ℕ) (z : Space d) : ℝ := harmonicKernelProfile d (‖z‖ ^ 2)

theorem continuous_harmonicKernelProfile : Continuous (harmonicKernelProfile d) :=
  continuous_const.mul (contDiff_harmonicProfile (n := 0)).continuous

theorem harmonicKernelProfile_eq_zero {t : ℝ} (ht : 1 ≤ t) : harmonicKernelProfile d t = 0 := by
  simp [harmonicKernelProfile, harmonicProfile_eq_zero ht]

theorem contDiff_harmonicKernel {n : ℕ∞} : ContDiff ℝ n (harmonicKernel d) :=
  contDiff_const.mul (contDiff_harmonicProfile.comp (contDiff_norm_sq ℝ))

theorem harmonicKernel_nonneg (z : Space d) : 0 ≤ harmonicKernel d z :=
  mul_nonneg (inv_nonneg.2 integral_harmonicBump_pos.le) (harmonicProfile_nonneg _)

theorem harmonicKernel_eq_zero {z : Space d} (hz : 1 ≤ ‖z‖) : harmonicKernel d z = 0 :=
  harmonicKernelProfile_eq_zero (one_le_pow₀ hz)

theorem hasCompactSupport_harmonicKernel : HasCompactSupport (harmonicKernel d) :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz ↦ harmonicKernel_eq_zero (by
    simp only [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le)

theorem harmonicKernel_neg (z : Space d) : harmonicKernel d (-z) = harmonicKernel d z := by
  simp [harmonicKernel]

theorem integral_harmonicKernel : ∫ z : Space d, harmonicKernel d z = 1 := by
  change ∫ z : Space d, (∫ z : Space d, harmonicBump d z)⁻¹ * harmonicBump d z = 1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ integral_harmonicBump_pos.ne'

/-- The rescaled mollifier `z ↦ r⁻ᵈ ρ (r⁻¹ • z)`, which vanishes outside `ball 0 r`. -/
def scaledHarmonicKernel (d : ℕ) (r : ℝ) (z : Space d) : ℝ :=
  (r ^ d)⁻¹ * harmonicKernel d (r⁻¹ • z)

theorem contDiff_scaledHarmonicKernel {n : ℕ∞} (r : ℝ) :
    ContDiff ℝ n (scaledHarmonicKernel d r) :=
  contDiff_const.mul (contDiff_harmonicKernel.comp (contDiff_id.const_smul r⁻¹))

theorem scaledHarmonicKernel_eq_zero {r : ℝ} (hr : 0 < r) {z : Space d} (hz : r ≤ ‖z‖) :
    scaledHarmonicKernel d r z = 0 := by
  have h1 : 1 ≤ ‖r⁻¹ • z‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, le_inv_mul_iff₀ hr]
    simpa using hz
  simp [scaledHarmonicKernel, harmonicKernel_eq_zero h1]

theorem scaledHarmonicKernel_nonneg {r : ℝ} (hr : 0 < r) (z : Space d) :
    0 ≤ scaledHarmonicKernel d r z :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le d)) (harmonicKernel_nonneg _)

theorem tsupport_scaledHarmonicKernel_subset {r : ℝ} (hr : 0 < r) :
    tsupport (scaledHarmonicKernel d r) ⊆ closedBall 0 r := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  by_contra hzr
  apply hz
  apply scaledHarmonicKernel_eq_zero hr
  simp only [mem_closedBall, dist_zero_right, not_le] at hzr
  exact hzr.le

theorem hasCompactSupport_scaledHarmonicKernel {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledHarmonicKernel d r) :=
  (isCompact_closedBall 0 r).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_scaledHarmonicKernel_subset hr)

theorem scaledHarmonicKernel_neg (r : ℝ) (z : Space d) :
    scaledHarmonicKernel d r (-z) = scaledHarmonicKernel d r z := by
  simp only [scaledHarmonicKernel, smul_neg, harmonicKernel_neg]

theorem integral_scaledHarmonicKernel {r : ℝ} (hr : 0 < r) :
    ∫ z : Space d, scaledHarmonicKernel d r z = 1 := by
  simp only [scaledHarmonicKernel]
  rw [integral_const_mul, Measure.integral_comp_inv_smul, finrank_euclideanSpace_fin,
    integral_harmonicKernel, smul_eq_mul, mul_one, abs_of_pos (pow_pos hr d)]
  exact inv_mul_cancel₀ (pow_pos hr d).ne'

/-- Change of variables `y = x + r • z` against the rescaled mollifier. -/
theorem integral_mul_scaledHarmonicKernel (F : Space d → ℝ) (x : Space d) {r : ℝ}
    (hr : 0 < r) :
    ∫ y, F y * scaledHarmonicKernel d r (x - y) = ∫ z, F (x + r • z) * harmonicKernel d z := by
  have h := integral_comp_add_smul (fun y ↦ F y * scaledHarmonicKernel d r (x - y)) x hr
  have hk : ∀ z : Space d,
      scaledHarmonicKernel d r (x - (x + r • z)) = (r ^ d)⁻¹ * harmonicKernel d z := by
    intro z
    rw [sub_add_cancel_left, scaledHarmonicKernel_neg]
    simp [scaledHarmonicKernel, smul_smul, inv_mul_cancel₀ hr.ne']
  simp_rw [hk] at h
  have h2 : ∫ z, F (x + r • z) * ((r ^ d)⁻¹ * harmonicKernel d z) =
      (r ^ d)⁻¹ * ∫ z, F (x + r • z) * harmonicKernel d z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [h2] at h
  exact (mul_left_cancel₀ (inv_ne_zero (pow_pos hr d).ne') h).symm

/-- **Mollifier identity** for the rescaled standard mollifier:
`h x = ∫ h y * ρ_r (x - y) dy` for `h` harmonic near `closedBall x r`. -/
theorem harmonic_eq_integral_mul_scaledHarmonicKernel {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    h x = ∫ y, h y * scaledHarmonicKernel d r (x - y) := by
  rw [integral_mul_scaledHarmonicKernel h x hr]
  have key := harmonic_integral_comp_mul_radial hU hh hΔ hxr (g := harmonicKernelProfile d)
    continuous_harmonicKernelProfile (fun t ht ↦ harmonicKernelProfile_eq_zero ht.le) hr.le
    le_rfl
  change h x = ∫ z, h (x + r • z) * harmonicKernelProfile d (‖z‖ ^ 2)
  rw [key]
  change h x = h x * ∫ z, harmonicKernel d z
  rw [integral_harmonicKernel, mul_one]

/-! ### Calculus of convolutions with smooth compactly supported kernels -/

private theorem convolution_lsmul_eq_integral (f K : Space d → ℝ) (x : Space d) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) x = ∫ y, f y * K (x - y) := by
  rw [convolution_lsmul]
  rfl

/-- The mollifier identity written with Mathlib's convolution. -/
theorem harmonic_eq_convolution {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    h x = (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d r) x := by
  rw [convolution_lsmul_eq_integral]
  exact harmonic_eq_integral_mul_scaledHarmonicKernel hU hh hΔ hxr hr

private theorem integrable_mul_comp_sub {f k : Space d → ℝ} (hf : LocallyIntegrable f)
    (hk : Continuous k) (hkc : HasCompactSupport k) (x : Space d) :
    Integrable (fun y ↦ f y * k (x - y)) :=
  hkc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hk x

private theorem fderiv_fderiv_apply_eq {u : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (v w : Space d) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y w) x v = fderiv ℝ (fderiv ℝ u) x v w := by
  rw [fderiv_clm_apply hu (differentiableAt_const w)]
  simp

private theorem hasCompactSupport_fderiv_fderiv_apply {K : Space d → ℝ} (hKc : HasCompactSupport K)
    (v w : Space d) : HasCompactSupport (fun z ↦ fderiv ℝ (fderiv ℝ K) z v w) :=
  ((hKc.fderiv ℝ).fderiv ℝ).mono' fun z hz ↦ subset_tsupport _ fun h0 ↦ hz (by simp [h0])

theorem fderiv_convolution_lsmul_apply {f K : Space d → ℝ} (hf : LocallyIntegrable f)
    (hK : ContDiff ℝ 1 K) (hKc : HasCompactSupport K) (x v : Space d) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) x v =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z ↦ fderiv ℝ K z v) x := by
  rw [(hKc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hK x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf (hKc.fderiv ℝ)
    (hK.continuous_fderiv one_ne_zero) x v

theorem fderiv_fderiv_convolution_lsmul_apply {f K : Space d → ℝ} (hf : LocallyIntegrable f)
    (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K) (x v w : Space d) :
    fderiv ℝ (fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K)) x v w =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z ↦ fderiv ℝ (fderiv ℝ K) z v w) x := by
  have hu : ContDiff ℝ 2 (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) :=
    hKc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf (n := 2) hK
  have hdu : DifferentiableAt ℝ (fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K)) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hK1 : ContDiff ℝ 1 (fderiv ℝ K) := hK.fderiv_right (m := 1) (by norm_num)
  rw [← fderiv_fderiv_apply_eq hdu]
  have hKw : ContDiff ℝ 1 (fun z ↦ fderiv ℝ K z w) := hK1.clm_apply contDiff_const
  have hfun : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) y w) =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun z ↦ fderiv ℝ K z w) :=
    funext fun y ↦ fderiv_convolution_lsmul_apply hf (hK.of_le (by norm_num)) hKc y w
  rw [hfun, fderiv_convolution_lsmul_apply hf hKw (hKc.fderiv_apply ℝ w) x v]
  have hfun2 : (fun z ↦ fderiv ℝ (fun z' ↦ fderiv ℝ K z' w) z v) =
      fun z ↦ fderiv ℝ (fderiv ℝ K) z v w :=
    funext fun z ↦ fderiv_fderiv_apply_eq (hK1.differentiable one_ne_zero z) v w
  rw [hfun2]

private theorem laplacian_eq_sum_fderiv_fderiv (u : Space d → ℝ) (y : Space d) :
    Δ u y = ∑ i, fderiv ℝ (fderiv ℝ u) y (stdOrthonormalBasis ℝ (Space d) i)
      (stdOrthonormalBasis ℝ (Space d) i) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_two_apply]

/-- The Laplacian of a convolution falls on the smooth compactly supported kernel. -/
theorem laplacian_convolution_lsmul {f K : Space d → ℝ} (hf : LocallyIntegrable f)
    (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K) (x : Space d) :
    Δ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) x = ∫ y, f y * Δ K (x - y) := by
  have hK2 : Continuous (fderiv ℝ (fderiv ℝ K)) :=
    (hK.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  rw [laplacian_eq_sum_fderiv_fderiv]
  simp_rw [fderiv_fderiv_convolution_lsmul_apply hf hK hKc, convolution_lsmul_eq_integral,
    laplacian_eq_sum_fderiv_fderiv K, Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact integrable_mul_comp_sub hf ((hK2.clm_apply continuous_const).clm_apply continuous_const)
    (hasCompactSupport_fderiv_fderiv_apply hKc _ _) x


/-! ### Derivative bounds for the mollifier -/

/-- A uniform bound for the first derivative of the standard mollifier. -/
def harmonicKernelC1 (d : ℕ) : ℝ := ⨆ z : Space d, ‖fderiv ℝ (harmonicKernel d) z‖

/-- A uniform bound for the second derivative of the standard mollifier. -/
def harmonicKernelC2 (d : ℕ) : ℝ := ⨆ z : Space d, ‖fderiv ℝ (fderiv ℝ (harmonicKernel d)) z‖

theorem norm_fderiv_harmonicKernel_le (z : Space d) :
    ‖fderiv ℝ (harmonicKernel d) z‖ ≤ harmonicKernelC1 d := by
  obtain ⟨C, hC⟩ := ((contDiff_harmonicKernel (d := d) (n := 1)).continuous_fderiv
    (by norm_num)).bounded_above_of_compact_support (hasCompactSupport_harmonicKernel.fderiv ℝ)
  exact le_ciSup (f := fun z : Space d ↦ ‖fderiv ℝ (harmonicKernel d) z‖)
    ⟨C, by rintro _ ⟨w, rfl⟩; simpa using hC w⟩ z

theorem norm_fderiv_fderiv_harmonicKernel_le (z : Space d) :
    ‖fderiv ℝ (fderiv ℝ (harmonicKernel d)) z‖ ≤ harmonicKernelC2 d := by
  obtain ⟨C, hC⟩ := (((contDiff_harmonicKernel (d := d) (n := 2)).fderiv_right (m := 1)
    (by norm_num)).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    ((hasCompactSupport_harmonicKernel.fderiv ℝ).fderiv ℝ)
  exact le_ciSup (f := fun z : Space d ↦ ‖fderiv ℝ (fderiv ℝ (harmonicKernel d)) z‖)
    ⟨C, by rintro _ ⟨w, rfl⟩; simpa using hC w⟩ z

theorem harmonicKernelC1_nonneg : 0 ≤ harmonicKernelC1 d :=
  (norm_nonneg _).trans (norm_fderiv_harmonicKernel_le (d := d) 0)

theorem harmonicKernelC2_nonneg : 0 ≤ harmonicKernelC2 d :=
  (ContinuousLinearMap.opNorm_nonneg _).trans (norm_fderiv_fderiv_harmonicKernel_le (d := d) 0)

theorem fderiv_scaledHarmonicKernel (r : ℝ) (z : Space d) :
    fderiv ℝ (scaledHarmonicKernel d r) z =
      ((r ^ d)⁻¹ * r⁻¹) • fderiv ℝ (harmonicKernel d) (r⁻¹ • z) := by
  have hd : DifferentiableAt ℝ (fun z : Space d ↦ harmonicKernel d (r⁻¹ • z)) z :=
    ((contDiff_harmonicKernel (n := 1)).comp (contDiff_id.const_smul r⁻¹)).differentiable
      (by norm_num) z
  change fderiv ℝ (fun z ↦ (r ^ d)⁻¹ * harmonicKernel d (r⁻¹ • z)) z = _
  rw [fderiv_const_mul hd, fderiv_comp_smul, smul_smul]

theorem fderiv_fderiv_scaledHarmonicKernel (r : ℝ) (z : Space d) :
    fderiv ℝ (fderiv ℝ (scaledHarmonicKernel d r)) z =
      ((r ^ d)⁻¹ * r⁻¹ * r⁻¹) • fderiv ℝ (fderiv ℝ (harmonicKernel d)) (r⁻¹ • z) := by
  have hfun : fderiv ℝ (scaledHarmonicKernel d r) =
      fun z ↦ ((r ^ d)⁻¹ * r⁻¹) • fderiv ℝ (harmonicKernel d) (r⁻¹ • z) :=
    funext (fderiv_scaledHarmonicKernel r)
  have hd : DifferentiableAt ℝ (fun z : Space d ↦ fderiv ℝ (harmonicKernel d) (r⁻¹ • z)) z :=
    ((((contDiff_harmonicKernel (n := 2)).fderiv_right (m := 1) (by norm_num)).comp
      (contDiff_id.const_smul r⁻¹))).differentiable (by norm_num) z
  rw [hfun, fderiv_fun_const_smul hd, fderiv_comp_smul, smul_smul]

theorem norm_fderiv_scaledHarmonicKernel_le {r : ℝ} (hr : 0 < r) (z : Space d) :
    ‖fderiv ℝ (scaledHarmonicKernel d r) z‖ ≤ (r ^ d)⁻¹ * r⁻¹ * harmonicKernelC1 d := by
  rw [fderiv_scaledHarmonicKernel, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_fderiv_harmonicKernel_le _) (by positivity)

theorem abs_fderiv_fderiv_scaledHarmonicKernel_le {r : ℝ} (hr : 0 < r) (z v w : Space d) :
    |fderiv ℝ (fderiv ℝ (scaledHarmonicKernel d r)) z v w| ≤
      (r ^ d)⁻¹ * r⁻¹ * r⁻¹ * harmonicKernelC2 d * ‖v‖ * ‖w‖ := by
  rw [fderiv_fderiv_scaledHarmonicKernel]
  change |((r ^ d)⁻¹ * r⁻¹ * r⁻¹) *
    fderiv ℝ (fderiv ℝ (harmonicKernel d)) (r⁻¹ • z) v w| ≤ _
  have hc : 0 ≤ (r ^ d)⁻¹ * r⁻¹ * r⁻¹ := by positivity
  have hL : |fderiv ℝ (fderiv ℝ (harmonicKernel d)) (r⁻¹ • z) v w| ≤
      harmonicKernelC2 d * ‖v‖ * ‖w‖ := by
    rw [← Real.norm_eq_abs]
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ (harmonicKernel d)) (r⁻¹ • z)‖ * ‖v‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ harmonicKernelC2 d * ‖v‖ * ‖w‖ := by
          gcongr
          exact norm_fderiv_fderiv_harmonicKernel_le _
  rw [abs_mul, abs_of_nonneg hc]
  calc _ ≤ ((r ^ d)⁻¹ * r⁻¹ * r⁻¹) * (harmonicKernelC2 d * ‖v‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left hL hc
    _ = _ := by ring

theorem fderiv_scaledHarmonicKernel_eq_zero {r : ℝ} (hr : 0 < r) {z : Space d}
    (hz : r < ‖z‖) : fderiv ℝ (scaledHarmonicKernel d r) z = 0 := by
  apply fderiv_of_notMem_tsupport
  intro hmem
  have h1 := tsupport_scaledHarmonicKernel_subset hr hmem
  simp only [mem_closedBall, dist_zero_right] at h1
  linarith

theorem fderiv_fderiv_scaledHarmonicKernel_eq_zero {r : ℝ} (hr : 0 < r) {z : Space d}
    (hz : r < ‖z‖) : fderiv ℝ (fderiv ℝ (scaledHarmonicKernel d r)) z = 0 := by
  apply fderiv_of_notMem_tsupport
  intro hmem
  have h1 := tsupport_scaledHarmonicKernel_subset hr (tsupport_fderiv_subset ℝ hmem)
  simp only [mem_closedBall, dist_zero_right] at h1
  linarith

/-! ### Two elementary integral inequalities -/

/-- A convolution against a bounded kernel supported in `closedBall 0 s` is controlled by the
`L¹` norm on any larger ball. -/
private theorem abs_integral_mul_comp_sub_le {f k : Space d → ℝ} {x : Space d} {s r C : ℝ}
    (hsr : s < r) (hf : IntegrableOn f (ball x r)) (hk : ∀ z, |k z| ≤ C)
    (hk0 : ∀ z, s < ‖z‖ → k z = 0) :
    |∫ y, f y * k (x - y)| ≤ C * ∫ y in ball x r, |f y| := by
  calc |∫ y, f y * k (x - y)| ≤ ∫ y, |f y * k (x - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, C * (ball x r).indicator (fun y ↦ |f y|) y := by
        have hfa : IntegrableOn (fun y ↦ |f y|) (ball x r) := hf.abs
        apply integral_mono_of_nonneg (Eventually.of_forall fun y ↦ abs_nonneg _)
          ((hfa.integrable_indicator measurableSet_ball).const_mul C)
        filter_upwards with y
        by_cases hy : y ∈ ball x r
        · rw [indicator_of_mem hy, abs_mul, mul_comm C]
          exact mul_le_mul_of_nonneg_left (hk _) (abs_nonneg _)
        · have hxy : s < ‖x - y‖ := by
            rw [← dist_eq_norm, dist_comm]
            simp only [mem_ball, not_lt] at hy
            linarith
          simp [hk0 _ hxy, indicator_of_notMem hy]
    _ = C * ∫ y in ball x r, |f y| := by
        rw [integral_const_mul, integral_indicator measurableSet_ball]

/-- The Cauchy–Schwarz inequality `(∫ₛ |f|)² ≤ |s| · ∫ₛ f²`. -/
private theorem sq_setIntegral_abs_le {s : Set (Space d)} (hs : volume s ≠ ⊤)
    {f : Space d → ℝ} (hf : IntegrableOn f s) (hf2 : IntegrableOn (fun y ↦ f y ^ 2) s) :
    (∫ y in s, |f y|) ^ 2 ≤ volume.real s * ∫ y in s, f y ^ 2 := by
  set A := ∫ y in s, |f y| with hA
  set B := ∫ y in s, f y ^ 2 with hB
  set V := volume.real s with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  rcases hV0.eq_or_lt with hV' | hV'
  · have hs0 : volume s = 0 := (measureReal_eq_zero_iff hs).1 hV'.symm
    have hA' : A = 0 := setIntegral_measure_zero _ hs0
    rw [hA', ← hV']
    simp
  · have hint : 0 ≤ ∫ y in s, (|f y| - A / V) ^ 2 := integral_nonneg fun y ↦ sq_nonneg _
    have h1 : ∀ y, (|f y| - A / V) ^ 2 = (f y ^ 2 - (2 * (A / V)) * |f y|) + (A / V) ^ 2 := by
      intro y
      rw [sub_sq, sq_abs]
      ring
    simp_rw [h1] at hint
    have i2 : IntegrableOn (fun y ↦ 2 * (A / V) * |f y|) s := hf.abs.const_mul _
    have i1 : IntegrableOn (fun y ↦ f y ^ 2 - 2 * (A / V) * |f y|) s := hf2.sub i2
    have e1 : ∫ y in s, (f y ^ 2 - 2 * (A / V) * |f y| + (A / V) ^ 2) =
        (∫ y in s, (f y ^ 2 - 2 * (A / V) * |f y|)) + ∫ y in s, (A / V) ^ 2 :=
      integral_add i1 (integrableOn_const (C := (A / V) ^ 2) hs)
    have e2 : ∫ y in s, (f y ^ 2 - 2 * (A / V) * |f y|) =
        (∫ y in s, f y ^ 2) - ∫ y in s, 2 * (A / V) * |f y| := integral_sub hf2 i2
    have e3 : ∫ y in s, 2 * (A / V) * |f y| = 2 * (A / V) * A := integral_const_mul _ _
    have e4 : ∫ y in s, (A / V) ^ 2 = V * (A / V) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul]
    rw [e1, e2, e3, e4, ← hB] at hint
    have h2 : B - 2 * (A / V) * A + V * (A / V) ^ 2 = B - A ^ 2 / V := by
      field_simp
      ring
    rw [h2] at hint
    have h3 : A ^ 2 / V ≤ B := by linarith
    rw [div_le_iff₀ hV'] at h3
    linarith

/-- The Cauchy–Schwarz inequality `∫ₛ |f| ≤ √|s| · √(∫ₛ f²)`. -/
private theorem integral_abs_le_sqrt_mul_sqrt {s : Set (Space d)} (hs : volume s ≠ ⊤)
    {f : Space d → ℝ} (hf : IntegrableOn f s) (hf2 : IntegrableOn (fun y ↦ f y ^ 2) s) :
    ∫ y in s, |f y| ≤ Real.sqrt (volume.real s) * Real.sqrt (∫ y in s, f y ^ 2) := by
  have hA0 : 0 ≤ ∫ y in s, |f y| := integral_nonneg fun y ↦ abs_nonneg _
  calc ∫ y in s, |f y| = Real.sqrt ((∫ y in s, |f y|) ^ 2) := (Real.sqrt_sq hA0).symm
    _ ≤ Real.sqrt (volume.real s * ∫ y in s, f y ^ 2) :=
        Real.sqrt_le_sqrt (sq_setIntegral_abs_le hs hf hf2)
    _ = _ := Real.sqrt_mul measureReal_nonneg _

private theorem volume_real_ball (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ d * volume.real (ball (0 : Space d) 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d), measureReal_def]

private theorem inv_pow_mul_sqrt_pow_eq_rpow {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (r ^ (d + k))⁻¹ * Real.sqrt (r ^ d) = r ^ (-(k : ℝ) - d / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r d, ← Real.rpow_mul hr.le,
    ← Real.rpow_natCast r (d + k), ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
  congr 1
  push_cast
  ring

private theorem norm_iteratedFDeriv_two_eq (h : Space d → ℝ) (x : Space d) :
    ‖iteratedFDeriv ℝ 2 h x‖ = ‖fderiv ℝ (fderiv ℝ h) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-! ### Interior derivative estimates for harmonic functions -/

private theorem integrableOn_ball_of_continuousOn_of_subset {U : Set (Space d)} {h : Space d → ℝ}
    (hh : ContinuousOn h U) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U) :
    IntegrableOn h (ball x r) :=
  ((hh.mono hxr).integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall

/-- Near `x`, a harmonic function coincides with the mollification of its restriction to
`closedBall x r`. -/
theorem harmonic_eventuallyEq_convolution {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    h =ᶠ[𝓝 x] ((closedBall x r).indicator h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      scaledHarmonicKernel d (r / 2)) := by
  filter_upwards [ball_mem_nhds x (half_pos hr)] with x' hx'
  have hx'x : dist x' x < r / 2 := hx'
  have hsub : closedBall x' (r / 2) ⊆ U := fun y hy ↦ hxr (by
    rw [mem_closedBall] at hy ⊢
    linarith [dist_triangle y x' x])
  rw [convolution_lsmul_eq_integral]
  conv_lhs => rw [harmonic_eq_integral_mul_scaledHarmonicKernel hU hh hΔ hsub (half_pos hr)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ closedBall x r
  · rw [indicator_of_mem hy]
  · have hyx : r < dist y x := by simpa using hy
    have hk : scaledHarmonicKernel d (r / 2) (x' - y) = 0 := by
      apply scaledHarmonicKernel_eq_zero (half_pos hr)
      rw [← dist_eq_norm]
      linarith [dist_triangle y x' x, dist_comm x' y]
    rw [hk, mul_zero, mul_zero]

private theorem integrable_indicator_closedBall {U : Set (Space d)} {h : Space d → ℝ}
    (hh : ContinuousOn h U) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U) :
    Integrable ((closedBall x r).indicator h) :=
  ((hh.mono hxr).integrableOn_compact (isCompact_closedBall x r)).integrable_indicator
    measurableSet_closedBall

private theorem setIntegral_abs_indicator_closedBall (h : Space d → ℝ) (x : Space d) (r : ℝ) :
    ∫ y in ball x r, |(closedBall x r).indicator h y| = ∫ y in ball x r, |h y| :=
  setIntegral_congr_fun measurableSet_ball fun y hy ↦ by
    simp [indicator_of_mem (ball_subset_closedBall hy)]

/-- Interior gradient estimate in `L¹` form. -/
theorem norm_fderiv_le_integral_abs_of_harmonic {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    ‖fderiv ℝ h x‖ ≤
      2 ^ (d + 1) * harmonicKernelC1 d * (r ^ (d + 1))⁻¹ * ∫ y in ball x r, |h y| := by
  have hs0 : 0 < r / 2 := half_pos hr
  have hfi := integrable_indicator_closedBall hh.continuousOn hxr
  rw [(harmonic_eventuallyEq_convolution hU hh hΔ hxr hr).fderiv_eq]
  have hconst : ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ = 2 ^ (d + 1) * (r ^ (d + 1))⁻¹ := by
    rw [← mul_inv, ← pow_succ, div_pow, inv_div, div_eq_mul_inv]
  have hI0 : 0 ≤ ∫ y in ball x r, |h y| := integral_nonneg fun y ↦ abs_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) harmonicKernelC1_nonneg)
      (by positivity)) hI0)
  intro v
  rw [fderiv_convolution_lsmul_apply hfi.locallyIntegrable (contDiff_scaledHarmonicKernel _)
    (hasCompactSupport_scaledHarmonicKernel hs0), convolution_lsmul_eq_integral,
    Real.norm_eq_abs]
  have hb := abs_integral_mul_comp_sub_le (x := x) (s := r / 2) (r := r)
    (k := fun z ↦ fderiv ℝ (scaledHarmonicKernel d (r / 2)) z v)
    (C := ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d * ‖v‖) (by linarith)
    hfi.integrableOn ?_ ?_
  · rw [setIntegral_abs_indicator_closedBall] at hb
    calc _ ≤ _ := hb
      _ = _ := by rw [hconst]; ring
  · intro z
    calc |fderiv ℝ (scaledHarmonicKernel d (r / 2)) z v|
        ≤ ‖fderiv ℝ (scaledHarmonicKernel d (r / 2)) z‖ * ‖v‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_fderiv_scaledHarmonicKernel_le hs0 z) (norm_nonneg _)
  · intro z hz
    simp [fderiv_scaledHarmonicKernel_eq_zero hs0 hz]

/-- Interior Hessian estimate in `L¹` form. -/
theorem norm_fderiv_fderiv_le_integral_abs_of_harmonic {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    ‖fderiv ℝ (fderiv ℝ h) x‖ ≤
      2 ^ (d + 2) * harmonicKernelC2 d * (r ^ (d + 2))⁻¹ * ∫ y in ball x r, |h y| := by
  have hs0 : 0 < r / 2 := half_pos hr
  have hfi := integrable_indicator_closedBall hh.continuousOn hxr
  rw [(harmonic_eventuallyEq_convolution hU hh hΔ hxr hr).fderiv.fderiv_eq]
  have hconst : ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * (r / 2)⁻¹ = 2 ^ (d + 2) * (r ^ (d + 2))⁻¹ := by
    rw [← mul_inv, ← pow_succ, ← mul_inv, ← pow_succ, div_pow, inv_div, div_eq_mul_inv]
  have hI0 : 0 ≤ ∫ y in ball x r, |h y| := integral_nonneg fun y ↦ abs_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound₂ _
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) harmonicKernelC2_nonneg)
      (by positivity)) hI0)
  intro v w
  rw [fderiv_fderiv_convolution_lsmul_apply hfi.locallyIntegrable (contDiff_scaledHarmonicKernel _)
    (hasCompactSupport_scaledHarmonicKernel hs0), convolution_lsmul_eq_integral,
    Real.norm_eq_abs]
  have hb := abs_integral_mul_comp_sub_le (x := x) (s := r / 2) (r := r)
    (k := fun z ↦ fderiv ℝ (fderiv ℝ (scaledHarmonicKernel d (r / 2))) z v w)
    (C := ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * (r / 2)⁻¹ * harmonicKernelC2 d * ‖v‖ * ‖w‖)
    (by linarith) hfi.integrableOn ?_ ?_
  · rw [setIntegral_abs_indicator_closedBall] at hb
    calc _ ≤ _ := hb
      _ = _ := by rw [hconst]; ring
  · intro z
    exact abs_fderiv_fderiv_scaledHarmonicKernel_le hs0 z v w
  · intro z hz
    simp [fderiv_fderiv_scaledHarmonicKernel_eq_zero hs0 hz]


private theorem fderiv_comp_const_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Space d → F) (x y : Space d) :
    fderiv ℝ (fun y ↦ G (x - y)) y = -fderiv ℝ G (x - y) := by
  have h1 : (fun y ↦ G (x - y)) = fun y ↦ G (x + (-1 : ℝ) • y) := by
    funext y
    simp [sub_eq_add_neg]
  have h2 := fderiv_comp_smul (𝕜 := ℝ) (f := fun z ↦ G (x + z)) (x := y) (-1 : ℝ)
  beta_reduce at h2
  rw [h1, h2, fderiv_comp_add_left]
  simp [sub_eq_add_neg]

/-- Interior Hessian estimate in terms of the gradient, `L¹` form. -/
theorem norm_fderiv_fderiv_le_integral_norm_fderiv_of_harmonic {U : Set (Space d)}
    (hU : IsOpen U) {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0)
    {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    ‖fderiv ℝ (fderiv ℝ h) x‖ ≤
      2 ^ (d + 1) * harmonicKernelC1 d * (r ^ (d + 1))⁻¹ *
        ∫ y in ball x r, ‖fderiv ℝ h y‖ := by
  have hs0 : 0 < r / 2 := half_pos hr
  set K := scaledHarmonicKernel d (r / 2) with hKdef
  have hfi := integrable_indicator_closedBall hh.continuousOn hxr
  rw [(harmonic_eventuallyEq_convolution hU hh hΔ hxr hr).fderiv.fderiv_eq]
  have hconst : ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ = 2 ^ (d + 1) * (r ^ (d + 1))⁻¹ := by
    rw [← mul_inv, ← pow_succ, div_pow, inv_div, div_eq_mul_inv]
  have hJ0 : 0 ≤ ∫ y in ball x r, ‖fderiv ℝ h y‖ := integral_nonneg fun y ↦ norm_nonneg _
  have hK2 : ContDiff ℝ 2 K := contDiff_scaledHarmonicKernel _
  have hK1 : ContDiff ℝ 1 (fderiv ℝ K) := hK2.fderiv_right (m := 1) (by norm_num)
  have hh1 : ContDiffOn ℝ 1 h (ball x r) :=
    (hh.of_le (by norm_num)).mono (ball_subset_closedBall.trans hxr)
  have hdfc : ContinuousOn (fderiv ℝ h) U := hh.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hC0 : 0 ≤ ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d :=
    mul_nonneg (by positivity) harmonicKernelC1_nonneg
  apply ContinuousLinearMap.opNorm_le_bound₂ _
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) harmonicKernelC1_nonneg)
      (by positivity)) hJ0)
  intro v w
  rw [fderiv_fderiv_convolution_lsmul_apply hfi.locallyIntegrable hK2
    (hasCompactSupport_scaledHarmonicKernel hs0), convolution_lsmul_eq_integral,
    Real.norm_eq_abs]
  have hrepl : ∫ y, (closedBall x r).indicator h y * fderiv ℝ (fderiv ℝ K) (x - y) v w =
      ∫ y, h y * fderiv ℝ (fderiv ℝ K) (x - y) v w := by
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ closedBall x r
    · rw [indicator_of_mem hy]
    · have hyx : r < dist y x := by simpa using hy
      have h0 : fderiv ℝ (fderiv ℝ K) (x - y) = 0 :=
        fderiv_fderiv_scaledHarmonicKernel_eq_zero hs0 (by
          rw [← dist_eq_norm, dist_comm]
          linarith)
      simp [h0]
  rw [hrepl]
  let ψ : Space d → ℝ := fun y ↦ fderiv ℝ K (x - y) w
  have hψ : ContDiff ℝ 1 ψ :=
    (hK1.clm_apply contDiff_const).comp (contDiff_const.sub contDiff_id)
  have hψsupp : ∀ y, ψ y ≠ 0 → y ∈ closedBall x (r / 2) := by
    intro y hy
    by_contra hy'
    apply hy
    have hyx : r / 2 < dist y x := by simpa using hy'
    have h0 : fderiv ℝ K (x - y) = 0 :=
      fderiv_scaledHarmonicKernel_eq_zero hs0 (by
        rw [← dist_eq_norm, dist_comm]
        exact hyx)
    simp [ψ, h0]
  have hψt : tsupport ψ ⊆ closedBall x (r / 2) :=
    closure_minimal (fun y hy ↦ hψsupp y hy) isClosed_closedBall
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall x (r / 2)).of_isClosed_subset (isClosed_tsupport _) hψt
  have hψsub : tsupport ψ ⊆ ball x r := hψt.trans (closedBall_subset_ball (by linarith))
  have hderψ : ∀ y, fderiv ℝ ψ y v = -(fderiv ℝ (fderiv ℝ K) (x - y) v w) := by
    intro y
    have h1 := fderiv_comp_const_sub (fun z ↦ fderiv ℝ K z w) x y
    change fderiv ℝ (fun y ↦ fderiv ℝ K (x - y) w) y v = _
    rw [h1, neg_apply,
      fderiv_fderiv_apply_eq (hK1.differentiable one_ne_zero _)]
  have ibp := integral_mul_fderiv_eq_neg_of_hasCompactSupport (μ := volume) isOpen_ball hh1
    hψ hψc hψsub v
  simp_rw [hderψ] at ibp
  have heq : ∫ y, h y * fderiv ℝ (fderiv ℝ K) (x - y) v w = ∫ y, fderiv ℝ h y v * ψ y := by
    have hneg : ∫ y, h y * -(fderiv ℝ (fderiv ℝ K) (x - y) v w) =
        -∫ y, h y * fderiv ℝ (fderiv ℝ K) (x - y) v w := by
      rw [← integral_neg]
      congr 1
      funext y
      ring
    rw [hneg] at ibp
    exact neg_injective ibp
  rw [heq]
  have hfv : IntegrableOn (fun y ↦ fderiv ℝ h y v) (ball x r) :=
    integrableOn_ball_of_continuousOn_of_subset (hdfc.clm_apply continuousOn_const) hxr
  have hb := abs_integral_mul_comp_sub_le (x := x) (s := r / 2) (r := r)
    (f := fun y ↦ fderiv ℝ h y v) (k := fun z ↦ fderiv ℝ K z w)
    (C := ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d * ‖w‖) (by linarith) hfv ?_ ?_
  · have hmono : ∫ y in ball x r, |fderiv ℝ h y v| ≤ (∫ y in ball x r, ‖fderiv ℝ h y‖) * ‖v‖ := by
      rw [← integral_mul_const]
      apply setIntegral_mono_on hfv.abs
        ((integrableOn_ball_of_continuousOn_of_subset hdfc.norm hxr).mul_const _) measurableSet_ball
      intro y _
      rw [← Real.norm_eq_abs]
      exact ContinuousLinearMap.le_opNorm _ _
    calc |∫ y, fderiv ℝ h y v * ψ y|
        ≤ ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d * ‖w‖ *
            ∫ y in ball x r, |fderiv ℝ h y v| := hb
      _ ≤ ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d * ‖w‖ *
            ((∫ y in ball x r, ‖fderiv ℝ h y‖) * ‖v‖) :=
          mul_le_mul_of_nonneg_left hmono (mul_nonneg hC0 (norm_nonneg _))
      _ = _ := by rw [hconst]; ring
  · intro z
    calc |fderiv ℝ K z w| ≤ ‖fderiv ℝ K z‖ * ‖w‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((r / 2) ^ d)⁻¹ * (r / 2)⁻¹ * harmonicKernelC1 d * ‖w‖ :=
          mul_le_mul_of_nonneg_right (norm_fderiv_scaledHarmonicKernel_le hs0 z) (norm_nonneg _)
  · intro z hz
    simp [K, fderiv_scaledHarmonicKernel_eq_zero hs0 hz]

/-- Passage from an `L¹` bound on a ball to the scale-invariant `L²` form. -/
private theorem le_mul_rpow_of_le_integral_abs {f : Space d → ℝ} {x : Space d} {r : ℝ} (hr : 0 < r)
    (hf : IntegrableOn f (ball x r)) (hf2 : IntegrableOn (fun y ↦ f y ^ 2) (ball x r))
    {a A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (ha : a ≤ A * (r ^ (d + k))⁻¹ * ∫ y in ball x r, |f y|) :
    a ≤ A * Real.sqrt (volume.real (ball (0 : Space d) 1)) * r ^ (-(k : ℝ) - d / 2) *
      (∫ y in ball x r, f y ^ 2) ^ (1 / 2 : ℝ) := by
  have hcs := integral_abs_le_sqrt_mul_sqrt measure_ball_lt_top.ne hf hf2
  rw [volume_real_ball x hr, Real.sqrt_mul (pow_nonneg hr.le d)] at hcs
  calc a ≤ A * (r ^ (d + k))⁻¹ * ∫ y in ball x r, |f y| := ha
    _ ≤ A * (r ^ (d + k))⁻¹ * (Real.sqrt (r ^ d) *
          Real.sqrt (volume.real (ball (0 : Space d) 1)) *
          Real.sqrt (∫ y in ball x r, f y ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = A * Real.sqrt (volume.real (ball (0 : Space d) 1)) *
          ((r ^ (d + k))⁻¹ * Real.sqrt (r ^ d)) * Real.sqrt (∫ y in ball x r, f y ^ 2) := by
        ring
    _ = _ := by
        rw [inv_pow_mul_sqrt_pow_eq_rpow hr k, Real.sqrt_eq_rpow (∫ y in ball x r, f y ^ 2)]

/-- The constant in the interior gradient estimates. -/
def harmonicGradConst (d : ℕ) : ℝ :=
  2 ^ (d + 1) * harmonicKernelC1 d * Real.sqrt (volume.real (ball (0 : Space d) 1))

/-- The constant in the interior Hessian estimate. -/
def harmonicHessConst (d : ℕ) : ℝ :=
  2 ^ (d + 2) * harmonicKernelC2 d * Real.sqrt (volume.real (ball (0 : Space d) 1))

theorem harmonicGradConst_nonneg : 0 ≤ harmonicGradConst d :=
  mul_nonneg (mul_nonneg (by positivity) harmonicKernelC1_nonneg) (Real.sqrt_nonneg _)

theorem harmonicHessConst_nonneg : 0 ≤ harmonicHessConst d :=
  mul_nonneg (mul_nonneg (by positivity) harmonicKernelC2_nonneg) (Real.sqrt_nonneg _)

/-- **Interior gradient estimate** (item 5). -/
theorem norm_fderiv_le_of_harmonic {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    ‖fderiv ℝ h x‖ ≤ harmonicGradConst d * r ^ (-(1 : ℝ) - d / 2) *
      (∫ y in ball x r, h y ^ 2) ^ (1 / 2 : ℝ) := by
  have h1 := norm_fderiv_le_integral_abs_of_harmonic hU hh hΔ hxr hr
  have h2 := le_mul_rpow_of_le_integral_abs hr
    (integrableOn_ball_of_continuousOn_of_subset hh.continuousOn hxr)
    (integrableOn_ball_of_continuousOn_of_subset (hh.continuousOn.pow 2) hxr)
    (mul_nonneg (by positivity) harmonicKernelC1_nonneg) 1 h1
  simpa only [harmonicGradConst, Nat.cast_one] using h2

/-- **Interior Hessian estimate** (item 5). -/
theorem norm_iteratedFDeriv_two_le_of_harmonic {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ 2 h x‖ ≤ harmonicHessConst d * r ^ (-(2 : ℝ) - d / 2) *
      (∫ y in ball x r, h y ^ 2) ^ (1 / 2 : ℝ) := by
  rw [norm_iteratedFDeriv_two_eq]
  have h1 := norm_fderiv_fderiv_le_integral_abs_of_harmonic hU hh hΔ hxr hr
  have h2 := le_mul_rpow_of_le_integral_abs hr
    (integrableOn_ball_of_continuousOn_of_subset hh.continuousOn hxr)
    (integrableOn_ball_of_continuousOn_of_subset (hh.continuousOn.pow 2) hxr)
    (mul_nonneg (by positivity) harmonicKernelC2_nonneg) 2 h1
  simpa only [harmonicHessConst, Nat.cast_ofNat] using h2

/-- **Interior Hessian estimate in terms of the gradient** (item 5). -/
theorem norm_iteratedFDeriv_two_le_of_harmonic_grad {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ 2 h x‖ ≤ harmonicGradConst d * r ^ (-(1 : ℝ) - d / 2) *
      (∫ y in ball x r, ‖fderiv ℝ h y‖ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [norm_iteratedFDeriv_two_eq]
  have hdfc : ContinuousOn (fderiv ℝ h) U := hh.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have h1 := norm_fderiv_fderiv_le_integral_norm_fderiv_of_harmonic hU hh hΔ hxr hr
  have habs : ∫ y in ball x r, ‖fderiv ℝ h y‖ = ∫ y in ball x r, |‖fderiv ℝ h y‖| := by
    simp_rw [abs_norm]
  rw [habs] at h1
  have h2 := le_mul_rpow_of_le_integral_abs hr
    (integrableOn_ball_of_continuousOn_of_subset hdfc.norm hxr)
    (integrableOn_ball_of_continuousOn_of_subset (hdfc.norm.pow 2) hxr)
    (mul_nonneg (by positivity) harmonicKernelC1_nonneg) 1 h1
  simpa only [harmonicGradConst, Nat.cast_one] using h2


/-! ### Excess decay for harmonic functions -/

private theorem closedBall_half_subset {x z : Space d} {r : ℝ} (hz : z ∈ closedBall x (r / 2)) :
    closedBall z (r / 2) ⊆ closedBall x r := by
  intro y hy
  rw [mem_closedBall] at hy hz ⊢
  linarith [dist_triangle y z x]

private theorem ball_half_subset {x z : Space d} {r : ℝ} (hz : z ∈ closedBall x (r / 2)) :
    ball z (r / 2) ⊆ ball x r := by
  intro y hy
  rw [mem_ball] at hy ⊢
  rw [mem_closedBall] at hz
  linarith [dist_triangle y z x]

/-- Pointwise Hessian bound on the half ball in terms of the gradient energy on the ball. -/
theorem sq_norm_fderiv_fderiv_le_grad_energy {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) {z : Space d}
    (hz : z ∈ closedBall x (r / 2)) :
    ‖fderiv ℝ (fderiv ℝ h) z‖ ^ 2 ≤ (2 ^ (d + 1) * harmonicKernelC1 d) ^ 2 *
      (((r / 2) ^ (d + 1))⁻¹) ^ 2 * ((r / 2) ^ d * volume.real (ball (0 : Space d) 1)) *
        ∫ y in ball x r, ‖fderiv ℝ h y‖ ^ 2 := by
  have hs0 : 0 < r / 2 := half_pos hr
  have hzsub := closedBall_half_subset hz
  have hdfc : ContinuousOn (fderiv ℝ h) U := hh.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have h1 := norm_fderiv_fderiv_le_integral_norm_fderiv_of_harmonic hU hh hΔ
    (hzsub.trans hxr) hs0
  have hcs := sq_setIntegral_abs_le (s := ball z (r / 2)) measure_ball_lt_top.ne
    (f := fun y ↦ ‖fderiv ℝ h y‖)
    (integrableOn_ball_of_continuousOn_of_subset hdfc.norm (hzsub.trans hxr))
    (integrableOn_ball_of_continuousOn_of_subset (hdfc.norm.pow 2) (hzsub.trans hxr))
  simp only [abs_norm] at hcs
  rw [volume_real_ball z hs0] at hcs
  have hmono : ∫ y in ball z (r / 2), ‖fderiv ℝ h y‖ ^ 2 ≤
      ∫ y in ball x r, ‖fderiv ℝ h y‖ ^ 2 :=
    setIntegral_mono_set (integrableOn_ball_of_continuousOn_of_subset (hdfc.norm.pow 2) hxr)
      (Eventually.of_forall fun y ↦ by positivity) (ball_half_subset hz).eventuallyLE
  calc ‖fderiv ℝ (fderiv ℝ h) z‖ ^ 2
      ≤ (2 ^ (d + 1) * harmonicKernelC1 d * ((r / 2) ^ (d + 1))⁻¹ *
          ∫ y in ball z (r / 2), ‖fderiv ℝ h y‖) ^ 2 :=
        pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) h1 2
    _ = (2 ^ (d + 1) * harmonicKernelC1 d) ^ 2 * (((r / 2) ^ (d + 1))⁻¹) ^ 2 *
          (∫ y in ball z (r / 2), ‖fderiv ℝ h y‖) ^ 2 := by ring
    _ ≤ (2 ^ (d + 1) * harmonicKernelC1 d) ^ 2 * (((r / 2) ^ (d + 1))⁻¹) ^ 2 *
          ((r / 2) ^ d * volume.real (ball (0 : Space d) 1) *
            ∫ y in ball z (r / 2), ‖fderiv ℝ h y‖ ^ 2) := by gcongr
    _ ≤ (2 ^ (d + 1) * harmonicKernelC1 d) ^ 2 * (((r / 2) ^ (d + 1))⁻¹) ^ 2 *
          ((r / 2) ^ d * volume.real (ball (0 : Space d) 1) *
            ∫ y in ball x r, ‖fderiv ℝ h y‖ ^ 2) := by
        have hω := measureReal_nonneg (μ := volume) (s := ball (0 : Space d) 1)
        gcongr
    _ = _ := by ring

/-- Pointwise Hessian bound on the half ball in terms of the `L²` norm on the ball. -/
theorem sq_norm_fderiv_fderiv_le_energy {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d}
    {r : ℝ} (hxr : closedBall x r ⊆ U) (hr : 0 < r) {z : Space d}
    (hz : z ∈ closedBall x (r / 2)) :
    ‖fderiv ℝ (fderiv ℝ h) z‖ ^ 2 ≤ (2 ^ (d + 2) * harmonicKernelC2 d) ^ 2 *
      (((r / 2) ^ (d + 2))⁻¹) ^ 2 * ((r / 2) ^ d * volume.real (ball (0 : Space d) 1)) *
        ∫ y in ball x r, h y ^ 2 := by
  have hs0 : 0 < r / 2 := half_pos hr
  have hzsub := closedBall_half_subset hz
  have h1 := norm_fderiv_fderiv_le_integral_abs_of_harmonic hU hh hΔ (hzsub.trans hxr) hs0
  have hcs := sq_setIntegral_abs_le (s := ball z (r / 2)) measure_ball_lt_top.ne
    (integrableOn_ball_of_continuousOn_of_subset hh.continuousOn (hzsub.trans hxr))
    (integrableOn_ball_of_continuousOn_of_subset (hh.continuousOn.pow 2) (hzsub.trans hxr))
  rw [volume_real_ball z hs0] at hcs
  have hmono : ∫ y in ball z (r / 2), h y ^ 2 ≤ ∫ y in ball x r, h y ^ 2 :=
    setIntegral_mono_set (integrableOn_ball_of_continuousOn_of_subset (hh.continuousOn.pow 2) hxr)
      (Eventually.of_forall fun y ↦ by positivity) (ball_half_subset hz).eventuallyLE
  calc ‖fderiv ℝ (fderiv ℝ h) z‖ ^ 2
      ≤ (2 ^ (d + 2) * harmonicKernelC2 d * ((r / 2) ^ (d + 2))⁻¹ *
          ∫ y in ball z (r / 2), |h y|) ^ 2 :=
        pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) h1 2
    _ = (2 ^ (d + 2) * harmonicKernelC2 d) ^ 2 * (((r / 2) ^ (d + 2))⁻¹) ^ 2 *
          (∫ y in ball z (r / 2), |h y|) ^ 2 := by ring
    _ ≤ (2 ^ (d + 2) * harmonicKernelC2 d) ^ 2 * (((r / 2) ^ (d + 2))⁻¹) ^ 2 *
          ((r / 2) ^ d * volume.real (ball (0 : Space d) 1) *
            ∫ y in ball z (r / 2), h y ^ 2) := by gcongr
    _ ≤ (2 ^ (d + 2) * harmonicKernelC2 d) ^ 2 * (((r / 2) ^ (d + 2))⁻¹) ^ 2 *
          ((r / 2) ^ d * volume.real (ball (0 : Space d) 1) * ∫ y in ball x r, h y ^ 2) := by
        have hω := measureReal_nonneg (μ := volume) (s := ball (0 : Space d) 1)
        gcongr
    _ = _ := by ring

private theorem hasFDerivWithinAt_fderiv_of_harmonic {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) {s : Set (Space d)} {z : Space d}
    (hz : z ∈ U) : HasFDerivWithinAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) z) s z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ h) z :=
    ((hh.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num) z
      hz).differentiableAt (hU.mem_nhds hz)
  exact hd.hasFDerivAt.hasFDerivWithinAt

private theorem excess_algebra_one {r : ℝ} (hr : 0 < r) (A V J θ : ℝ) :
    (θ * r) ^ d * V * (A ^ 2 * (((r / 2) ^ (d + 1))⁻¹) ^ 2 * ((r / 2) ^ d * V) * J *
      (θ * r) ^ 2) = A ^ 2 * V ^ 2 * 2 ^ (d + 2) * θ ^ (d + 2) * J := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 2 * ρ := ⟨r / 2, by ring⟩
  have hρ : 0 < ρ := by linarith
  have h2 : 2 * ρ / 2 = ρ := by ring
  rw [h2]
  field_simp
  ring

private theorem excess_algebra_two {r : ℝ} (hr : 0 < r) (A V J θ : ℝ) :
    (θ * r) ^ d * V * (A ^ 2 * (((r / 2) ^ (d + 2))⁻¹) ^ 2 * ((r / 2) ^ d * V) * J *
      (θ * r) ^ 4) = A ^ 2 * V ^ 2 * 2 ^ (d + 4) * θ ^ (d + 4) * J := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 2 * ρ := ⟨r / 2, by ring⟩
  have hρ : 0 < ρ := by linarith
  have h2 : 2 * ρ / 2 = ρ := by ring
  rw [h2]
  field_simp
  ring

/-- The constant in the gradient excess decay estimate. -/
def harmonicGradExcessConst (d : ℕ) : ℝ :=
  (2 ^ (d + 1) * harmonicKernelC1 d) ^ 2 * volume.real (ball (0 : Space d) 1) ^ 2 * 2 ^ (d + 2)

/-- The constant in the first-order Taylor excess decay estimate. -/
def harmonicTaylorExcessConst (d : ℕ) : ℝ :=
  (2 ^ (d + 2) * harmonicKernelC2 d) ^ 2 * volume.real (ball (0 : Space d) 1) ^ 2 * 2 ^ (d + 4)

theorem harmonicGradExcessConst_nonneg : 0 ≤ harmonicGradExcessConst d := by
  unfold harmonicGradExcessConst
  positivity

theorem harmonicTaylorExcessConst_nonneg : 0 ≤ harmonicTaylorExcessConst d := by
  unfold harmonicTaylorExcessConst
  positivity

/-- **Gradient excess decay** (item 6a), on an arbitrary ball. -/
theorem harmonic_fderiv_excess_le {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∫ y in ball x (θ * r), ‖fderiv ℝ h y - fderiv ℝ h x‖ ^ 2 ≤
      harmonicGradExcessConst d * θ ^ (d + 2) * ∫ y in ball x r, ‖fderiv ℝ h y‖ ^ 2 := by
  set vol1 := volume.real (ball (0 : Space d) 1) with hvol1
  set J := ∫ y in ball x r, ‖fderiv ℝ h y‖ ^ 2 with hJ
  set M2 := (2 ^ (d + 1) * harmonicKernelC1 d) ^ 2 * (((r / 2) ^ (d + 1))⁻¹) ^ 2 *
    ((r / 2) ^ d * vol1) * J with hM2
  have hJ0 : 0 ≤ J := integral_nonneg fun _ ↦ by positivity
  have hvol0 : 0 ≤ vol1 := measureReal_nonneg
  have hM20 : 0 ≤ M2 := by positivity
  have hθr : 0 < θ * r := mul_pos hθ0 hr
  have hθr2 : θ * r ≤ r / 2 := by nlinarith
  have hhalf : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hxr
  have hbound : ∀ z ∈ closedBall x (r / 2), ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ Real.sqrt M2 := by
    intro z hz
    rw [← Real.sqrt_sq (norm_nonneg (fderiv ℝ (fderiv ℝ h) z))]
    exact Real.sqrt_le_sqrt (sq_norm_fderiv_fderiv_le_grad_energy hU hh hΔ hxr hr hz)
  have hpt : ∀ y ∈ ball x (θ * r), ‖fderiv ℝ h y - fderiv ℝ h x‖ ^ 2 ≤ M2 * (θ * r) ^ 2 := by
    intro y hy
    have hyc : y ∈ closedBall x (r / 2) :=
      closedBall_subset_closedBall hθr2 (ball_subset_closedBall hy)
    have hmvt := (convex_closedBall x (r / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz ↦ hasFDerivWithinAt_fderiv_of_harmonic hU hh (hhalf hz)) hbound
      (mem_closedBall_self (by linarith)) hyc
    have hyx : ‖y - x‖ ≤ θ * r := by
      rw [← dist_eq_norm]
      exact (mem_ball.1 hy).le
    calc ‖fderiv ℝ h y - fderiv ℝ h x‖ ^ 2 ≤ (Real.sqrt M2 * ‖y - x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hmvt 2
      _ ≤ (Real.sqrt M2 * (θ * r)) ^ 2 := by gcongr
      _ = M2 * (θ * r) ^ 2 := by rw [mul_pow, Real.sq_sqrt hM20]
  have hint : IntegrableOn (fun y ↦ ‖fderiv ℝ h y - fderiv ℝ h x‖ ^ 2) (ball x (θ * r)) :=
    integrableOn_ball_of_continuousOn_of_subset
      (((hh.continuousOn_fderiv_of_isOpen hU (by norm_num)).sub continuousOn_const).norm.pow 2)
      ((closedBall_subset_closedBall hθr2).trans hhalf)
  calc ∫ y in ball x (θ * r), ‖fderiv ℝ h y - fderiv ℝ h x‖ ^ 2
      ≤ ∫ y in ball x (θ * r), M2 * (θ * r) ^ 2 :=
        setIntegral_mono_on hint (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball
          hpt
    _ = (θ * r) ^ d * vol1 * (M2 * (θ * r) ^ 2) := by
        rw [setIntegral_const, smul_eq_mul, volume_real_ball x hθr]
    _ = harmonicGradExcessConst d * θ ^ (d + 2) * J := by
        rw [hM2, excess_algebra_one hr]
        rfl

/-- **First-order Taylor excess decay** (item 6b), on an arbitrary ball. -/
theorem harmonic_taylor_excess_le {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∫ y in ball x (θ * r), (h y - h x - fderiv ℝ h x (y - x)) ^ 2 ≤
      harmonicTaylorExcessConst d * θ ^ (d + 4) * ∫ y in ball x r, h y ^ 2 := by
  set vol1 := volume.real (ball (0 : Space d) 1) with hvol1
  set I := ∫ y in ball x r, h y ^ 2 with hI
  set M2 := (2 ^ (d + 2) * harmonicKernelC2 d) ^ 2 * (((r / 2) ^ (d + 2))⁻¹) ^ 2 *
    ((r / 2) ^ d * vol1) * I with hM2
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ by positivity
  have hvol0 : 0 ≤ vol1 := measureReal_nonneg
  have hM20 : 0 ≤ M2 := by positivity
  have hθr : 0 < θ * r := mul_pos hθ0 hr
  have hθr2 : θ * r ≤ r / 2 := by nlinarith
  have hhalf : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hxr
  have hsmall : closedBall x (θ * r) ⊆ U := (closedBall_subset_closedBall hθr2).trans hhalf
  have hbound : ∀ z ∈ closedBall x (r / 2), ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ Real.sqrt M2 := by
    intro z hz
    rw [← Real.sqrt_sq (norm_nonneg (fderiv ℝ (fderiv ℝ h) z))]
    exact Real.sqrt_le_sqrt (sq_norm_fderiv_fderiv_le_energy hU hh hΔ hxr hr hz)
  have hgrad : ∀ z ∈ closedBall x (θ * r),
      ‖fderiv ℝ h z - fderiv ℝ h x‖ ≤ Real.sqrt M2 * (θ * r) := by
    intro z hz
    have hzc : z ∈ closedBall x (r / 2) := closedBall_subset_closedBall hθr2 hz
    have hmvt := (convex_closedBall x (r / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw ↦ hasFDerivWithinAt_fderiv_of_harmonic hU hh (hhalf hw)) hbound
      (mem_closedBall_self (by linarith)) hzc
    have hzx : ‖z - x‖ ≤ θ * r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hz
    calc ‖fderiv ℝ h z - fderiv ℝ h x‖ ≤ Real.sqrt M2 * ‖z - x‖ := hmvt
      _ ≤ Real.sqrt M2 * (θ * r) := by gcongr
  let g : Space d → ℝ := fun y ↦ h y - h x - fderiv ℝ h x (y - x)
  have hgd : ∀ z ∈ closedBall x (θ * r),
      HasFDerivWithinAt g (fderiv ℝ h z - fderiv ℝ h x) (closedBall x (θ * r)) z := by
    intro z hz
    have hzU := hsmall hz
    have hdh : HasFDerivAt h (fderiv ℝ h z) z :=
      ((hh.differentiableOn (by norm_num) z hzU).differentiableAt
        (hU.mem_nhds hzU)).hasFDerivAt
    have hlin : HasFDerivAt (fun y ↦ fderiv ℝ h x (y - x)) (fderiv ℝ h x) z := by
      have := (fderiv ℝ h x).hasFDerivAt.comp z ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x)
      rwa [ContinuousLinearMap.comp_id] at this
    exact ((hdh.sub_const (h x)).sub hlin).hasFDerivWithinAt
  have hpt : ∀ y ∈ ball x (θ * r), (h y - h x - fderiv ℝ h x (y - x)) ^ 2 ≤
      M2 * (θ * r) ^ 4 := by
    intro y hy
    have hyc : y ∈ closedBall x (θ * r) := ball_subset_closedBall hy
    have hmvt := (convex_closedBall x (θ * r)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hgd hgrad (mem_closedBall_self hθr.le) hyc
    have hgx : g x = 0 := by simp [g]
    rw [hgx, sub_zero, Real.norm_eq_abs] at hmvt
    have hyx : ‖y - x‖ ≤ θ * r := by
      rw [← dist_eq_norm]
      exact (mem_ball.1 hy).le
    have hgy : |g y| ≤ Real.sqrt M2 * (θ * r) * (θ * r) :=
      hmvt.trans (mul_le_mul_of_nonneg_left hyx (by positivity))
    calc (h y - h x - fderiv ℝ h x (y - x)) ^ 2 = |g y| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt M2 * (θ * r) * (θ * r)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hgy 2
      _ = M2 * (θ * r) ^ 4 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hM20]
          ring
  have hint : IntegrableOn (fun y ↦ (h y - h x - fderiv ℝ h x (y - x)) ^ 2) (ball x (θ * r)) :=
    integrableOn_ball_of_continuousOn_of_subset
      (((hh.continuousOn.sub continuousOn_const).sub
        ((fderiv ℝ h x).continuous.comp (continuous_id.sub continuous_const)).continuousOn).pow 2)
      hsmall
  calc ∫ y in ball x (θ * r), (h y - h x - fderiv ℝ h x (y - x)) ^ 2
      ≤ ∫ y in ball x (θ * r), M2 * (θ * r) ^ 4 :=
        setIntegral_mono_on hint (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball
          hpt
    _ = (θ * r) ^ d * vol1 * (M2 * (θ * r) ^ 4) := by
        rw [setIntegral_const, smul_eq_mul, volume_real_ball x hθr]
    _ = harmonicTaylorExcessConst d * θ ^ (d + 4) * I := by
        rw [hM2, excess_algebra_two hr]
        rfl

/-- **Gradient excess decay** (item 6a) on the unit ball. -/
theorem harmonic_fderiv_excess_le_unit {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) (h1 : closedBall (0 : Space d) 1 ⊆ U)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∫ y in ball (0 : Space d) θ, ‖fderiv ℝ h y - fderiv ℝ h 0‖ ^ 2 ≤
      harmonicGradExcessConst d * θ ^ (d + 2) *
        ∫ y in ball (0 : Space d) 1, ‖fderiv ℝ h y‖ ^ 2 := by
  simpa using harmonic_fderiv_excess_le hU hh hΔ h1 one_pos hθ0 hθ

/-- **First-order Taylor excess decay** (item 6b) on the unit ball. -/
theorem harmonic_taylor_excess_le_unit {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) (h1 : closedBall (0 : Space d) 1 ⊆ U)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∫ y in ball (0 : Space d) θ, (h y - h 0 - fderiv ℝ h 0 y) ^ 2 ≤
      harmonicTaylorExcessConst d * θ ^ (d + 4) * ∫ y in ball (0 : Space d) 1, h y ^ 2 := by
  simpa using harmonic_taylor_excess_le hU hh hΔ h1 one_pos hθ0 hθ


/-! ### Weyl's lemma -/

/-- Very weak harmonicity on an open set: `h` is locally integrable on `U` and
`∫ h * Δ φ = 0` for every smooth (`C^∞`) compactly supported test function `φ` with
`tsupport φ ⊆ U`. -/
def IsVeryWeaklyHarmonicOn (U : Set (Space d)) (h : Space d → ℝ) : Prop :=
  LocallyIntegrableOn h U ∧
    ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, h x * Δ φ x = 0

/-- The mollification of `h` at scale `ε` by the standard radial mollifier. -/
def harmonicMollify (h : Space d → ℝ) (ε : ℝ) (x : Space d) : ℝ :=
  ∫ y, h y * scaledHarmonicKernel d ε (x - y)

private theorem laplacian_comp_const_sub (K : Space d → ℝ) (x y : Space d) :
    Δ (fun y ↦ K (x - y)) y = Δ K (x - y) := by
  rw [laplacian_eq_sum_fderiv_fderiv, laplacian_eq_sum_fderiv_fderiv]
  have h1 : fderiv ℝ (fun y ↦ K (x - y)) = fun y ↦ -fderiv ℝ K (x - y) :=
    funext fun y ↦ fderiv_comp_const_sub K x y
  have h2 : fderiv ℝ (fun y ↦ -fderiv ℝ K (x - y)) y = fderiv ℝ (fderiv ℝ K) (x - y) := by
    rw [fderiv_fun_neg, fderiv_comp_const_sub (fderiv ℝ K) x y, neg_neg]
  rw [h1, h2]

private theorem laplacian_eq_zero_of_notMem_tsupport {K : Space d → ℝ} {z : Space d}
    (hz : z ∉ tsupport K) : Δ K z = 0 := by
  have hev : K =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hz
  rw [(laplacian_congr_nhds hev).eq_of_nhds]
  simp

private theorem lsmul_flip_eq : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
    ContinuousLinearMap.lsmul ℝ ℝ := by
  ext
  simp

/-- Associativity of the convolution of an integrable function with two mollifiers. -/
theorem convolution_scaledHarmonicKernel_assoc {f : Space d → ℝ} (hf : Integrable f)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (x : Space d) :
    ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d δ) x =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (scaledHarmonicKernel d ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          scaledHarmonicKernel d δ)) x := by
  have hcε : Continuous (scaledHarmonicKernel d ε) :=
    (contDiff_scaledHarmonicKernel (n := 0) ε).continuous
  have hcδ : Continuous (scaledHarmonicKernel d δ) :=
    (contDiff_scaledHarmonicKernel (n := 0) δ).continuous
  have hsε := hasCompactSupport_scaledHarmonicKernel (d := d) hε
  have hsδ := hasCompactSupport_scaledHarmonicKernel (d := d) hδ
  apply convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
  · intro a b c
    simp [smul_eq_mul, mul_assoc]
  · exact hf.aestronglyMeasurable
  · exact hcε.aestronglyMeasurable
  · exact hcδ.aestronglyMeasurable
  · exact Eventually.of_forall fun y ↦
      hsε.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf.locallyIntegrable hcε y
  · exact Eventually.of_forall fun y ↦
      hsδ.norm.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
        hcε.norm.locallyIntegrable hcδ.norm y
  · have hcs : HasCompactSupport ((fun x ↦ ‖scaledHarmonicKernel d ε x‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x ↦ ‖scaledHarmonicKernel d δ x‖) :=
      hsε.norm.convolution (ContinuousLinearMap.mul ℝ ℝ) hsδ.norm
    have hcc : Continuous ((fun x ↦ ‖scaledHarmonicKernel d ε x‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x ↦ ‖scaledHarmonicKernel d δ x‖) :=
      hsδ.norm.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        hcε.norm.locallyIntegrable hcδ.norm
    exact hcs.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf.norm.locallyIntegrable
      hcc x

theorem scaledHarmonicKernel_convolution_comm (ε δ : ℝ) :
    (scaledHarmonicKernel d ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        scaledHarmonicKernel d δ) =
      (scaledHarmonicKernel d δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        scaledHarmonicKernel d ε) :=
  convolution_symm (ContinuousLinearMap.lsmul ℝ ℝ) lsmul_flip_eq

/-- **Lebesgue differentiation** for the standard mollifier. -/
theorem ae_tendsto_convolution_scaledHarmonicKernel {f : Space d → ℝ}
    (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun ε ↦ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      scaledHarmonicKernel d ε) x) (𝓝[>] 0) (𝓝 (f x)) := by
  obtain ⟨B, hB⟩ := (contDiff_harmonicKernel (d := d) (n := 0)).continuous
    |>.bounded_above_of_compact_support hasCompactSupport_harmonicKernel
  set V := volume.real (closedBall (0 : Space d) 1) with hV
  have hVpos : 0 < V := by
    rw [hV, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  filter_upwards [(Besicovitch.vitaliFamily
    (volume : Measure (Space d))).ae_tendsto_average_norm_sub hf] with x₀ h₀
  have h1 := h₀.comp (Besicovitch.tendsto_filterAt volume x₀)
  have key := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume) (B * V)
    (a := fun ε ↦ closedBall x₀ ε) (g := fun ε y ↦ scaledHarmonicKernel d ε (x₀ - y)) h1
    ?_ ?_ ?_ ?_
  · refine key.congr' ?_
    filter_upwards with ε
    rw [convolution_lsmul_eq_integral]
    congr 1
    funext y
    rw [smul_eq_mul, mul_comm]
  · exact Eventually.of_forall fun ε ↦ hf.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_sub_left_eq_self (fun y ↦ scaledHarmonicKernel d ε y) volume x₀,
      integral_scaledHarmonicKernel hε]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    intro y hy
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra hcon
    exact hy (scaledHarmonicKernel_eq_zero hε (le_of_lt (not_le.mp hcon)))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    intro y
    have hε' : 0 < ε := hε
    have hvol : volume.real (closedBall x₀ ε) = ε ^ d * V := by
      rw [measureReal_def, Measure.addHaar_closedBall' volume x₀ hε'.le,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (pow_nonneg hε'.le d), ← measureReal_def]
    have hεd : 0 < ε ^ d := pow_pos hε' d
    rw [hvol, show B * V / (ε ^ d * V) = (ε ^ d)⁻¹ * B by field_simp]
    simp only [scaledHarmonicKernel]
    rw [abs_mul, abs_of_pos (inv_pos.2 hεd)]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB _) (inv_nonneg.2 hεd.le)

section WeylLocal

variable {U : Set (Space d)} {h : Space d → ℝ} {x₀ : Space d} {R : ℝ}

theorem harmonicMollify_eq_convolution {ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {x : Space d}
    (hx : x ∈ ball x₀ (2 * R)) :
    harmonicMollify h ε x = ((closedBall x₀ (3 * R)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε) x := by
  rw [convolution_lsmul_eq_integral, harmonicMollify]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ closedBall x₀ (3 * R)
  · rw [indicator_of_mem hy]
  · have hyx : 3 * R < dist y x₀ := by simpa using hy
    have hxx : dist x x₀ < 2 * R := hx
    have hk : scaledHarmonicKernel d ε (x - y) = 0 := by
      apply scaledHarmonicKernel_eq_zero hε
      rw [← dist_eq_norm]
      linarith [dist_triangle y x x₀, dist_comm x y]
    rw [hk, mul_zero, mul_zero]

theorem integrable_indicator_of_isVeryWeaklyHarmonicOn (hh : IsVeryWeaklyHarmonicOn U h)
    (hsub : closedBall x₀ (3 * R) ⊆ U) : Integrable ((closedBall x₀ (3 * R)).indicator h) :=
  (hh.1.integrableOn_compact_subset hsub (isCompact_closedBall _ _)).integrable_indicator
    measurableSet_closedBall

theorem laplacian_localMollify_eq_zero (hh : IsVeryWeaklyHarmonicOn U h)
    (hsub : closedBall x₀ (3 * R) ⊆ U) {ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {x : Space d}
    (hx : x ∈ ball x₀ (2 * R)) :
    Δ ((closedBall x₀ (3 * R)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε) x = 0 := by
  have hfi := integrable_indicator_of_isVeryWeaklyHarmonicOn hh hsub
  rw [laplacian_convolution_lsmul hfi.locallyIntegrable (contDiff_scaledHarmonicKernel ε)
    (hasCompactSupport_scaledHarmonicKernel hε)]
  let φ : Space d → ℝ := fun y ↦ scaledHarmonicKernel d ε (x - y)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (contDiff_scaledHarmonicKernel ε).comp (contDiff_const.sub contDiff_id)
  have hxx : dist x x₀ < 2 * R := hx
  have hφs : ∀ y, φ y ≠ 0 → y ∈ closedBall x ε := by
    intro y hy
    by_contra hy'
    apply hy
    apply scaledHarmonicKernel_eq_zero hε
    rw [← dist_eq_norm, dist_comm]
    simp only [mem_closedBall, not_le] at hy'
    exact hy'.le
  have hφt : tsupport φ ⊆ closedBall x ε :=
    closure_minimal (fun y hy ↦ hφs y hy) isClosed_closedBall
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall x ε).of_isClosed_subset (isClosed_tsupport _) hφt
  have hφU : tsupport φ ⊆ U := hφt.trans (fun y hy ↦ hsub (by
    rw [mem_closedBall] at hy ⊢
    linarith [dist_triangle y x x₀]))
  rw [← hh.2 φ hφ hφc hφU]
  apply integral_congr_ae
  filter_upwards with y
  rw [laplacian_comp_const_sub]
  by_cases hy : y ∈ closedBall x₀ (3 * R)
  · rw [indicator_of_mem hy]
  · have hyx : 3 * R < dist y x₀ := by simpa using hy
    have hz : x - y ∉ tsupport (scaledHarmonicKernel d ε) := by
      intro hmem
      have h1 := tsupport_scaledHarmonicKernel_subset hε hmem
      rw [mem_closedBall, dist_zero_right, ← dist_eq_norm] at h1
      linarith [dist_triangle y x x₀, dist_comm x y]
    rw [laplacian_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

theorem localMollify_indep (hh : IsVeryWeaklyHarmonicOn U h)
    (hsub : closedBall x₀ (3 * R) ⊆ U) {ε δ : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hδ : 0 < δ)
    (hδR : δ ≤ R) {x : Space d} (hx : x ∈ ball x₀ R) :
    ((closedBall x₀ (3 * R)).indicator h
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε) x =
      ((closedBall x₀ (3 * R)).indicator h
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d δ) x := by
  set f := (closedBall x₀ (3 * R)).indicator h with hfdef
  have hfi : Integrable f := integrable_indicator_of_isVeryWeaklyHarmonicOn hh hsub
  have hxx : dist x x₀ < R := hx
  have hmoll : ∀ {a b : ℝ}, 0 < a → a ≤ R → 0 < b → b ≤ R →
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d a) x =
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (scaledHarmonicKernel d a
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d b)) x := by
    intro a b ha haR hb hbR
    have hw : ContDiff ℝ 2 (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        scaledHarmonicKernel d a) :=
      (hasCompactSupport_scaledHarmonicKernel ha).contDiff_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hfi.locallyIntegrable (n := 2)
        (contDiff_scaledHarmonicKernel a)
    have hxr : closedBall x b ⊆ ball x₀ (2 * R) := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [mem_ball]
      linarith [dist_triangle y x x₀]
    rw [harmonic_eq_convolution isOpen_ball hw.contDiffOn
      (fun y hy ↦ laplacian_localMollify_eq_zero hh hsub ha haR hy) hxr hb]
    exact convolution_scaledHarmonicKernel_assoc hfi ha hb x
  rw [hmoll hε hεR hδ hδR, hmoll hδ hδR hε hεR, scaledHarmonicKernel_convolution_comm]

theorem localMollify_ae_eq (hh : IsVeryWeaklyHarmonicOn U h) (hR : 0 < R)
    (hsub : closedBall x₀ (3 * R) ⊆ U) {ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∀ᵐ x ∂(volume.restrict (ball x₀ R)), ((closedBall x₀ (3 * R)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε) x = h x := by
  have hfi := integrable_indicator_of_isVeryWeaklyHarmonicOn hh hsub
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [ae_tendsto_convolution_scaledHarmonicKernel (d := d)
    hfi.locallyIntegrable] with x hx hxb
  have hconst : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((closedBall x₀ (3 * R)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d δ) x =
      ((closedBall x₀ (3 * R)).indicator h
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε) x := by
    filter_upwards [Ioo_mem_nhdsGT hR] with δ hδ
    exact localMollify_indep hh hsub hδ.1 hδ.2.le hε hεR hxb
  have h2 : Tendsto (fun δ ↦ ((closedBall x₀ (3 * R)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d δ) x) (𝓝[>] 0)
      (𝓝 (((closedBall x₀ (3 * R)).indicator h
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d ε) x)) :=
    tendsto_const_nhds.congr' (hconst.mono fun δ hδ ↦ hδ.symm)
  rw [tendsto_nhds_unique h2 hx]
  have hxc : x ∈ closedBall x₀ (3 * R) := by
    rw [mem_closedBall]
    have : dist x x₀ < R := hxb
    linarith
  rw [indicator_of_mem hxc]

end WeylLocal

/-- **Weyl's lemma** (item 4). A very weakly harmonic function on an open set agrees almost
everywhere with a smooth (`C^∞`) classically harmonic function. -/
theorem weyl_lemma {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : IsVeryWeaklyHarmonicOn U h) :
    ∃ h' : Space d → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h' U ∧ (∀ x ∈ U, Δ h' x = 0) ∧
      h =ᵐ[volume.restrict U] h' := by
  have hrad : ∀ x ∈ U, ∃ R > 0, closedBall x (3 * R) ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨ε / 6, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose! R hRpos hRsub using hrad
  let h' : Space d → ℝ := fun x ↦ harmonicMollify h (R x) x
  have hloc : ∀ x₀ ∈ U, ∀ x ∈ ball x₀ (R x₀), h' x = ((closedBall x₀ (3 * R x₀)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d (R x₀)) x := by
    intro x₀ hx₀ x hx
    have hR0 := hRpos x₀ hx₀
    have hxU : x ∈ U := hRsub x₀ hx₀ (by
      rw [mem_closedBall]
      have : dist x x₀ < R x₀ := hx
      linarith)
    have hRx := hRpos x hxU
    set δ := min (R x) (R x₀) with hδ
    have hδ0 : 0 < δ := lt_min hRx hR0
    have hxx : x ∈ ball x (R x) := mem_ball_self hRx
    have e1 : h' x = harmonicMollify h δ x := by
      change harmonicMollify h (R x) x = _
      rw [harmonicMollify_eq_convolution (R := R x) (x₀ := x) hRx le_rfl
          (mem_ball_self (by linarith)),
        localMollify_indep hh (hRsub x hxU) hRx le_rfl hδ0 (min_le_left _ _) hxx,
        ← harmonicMollify_eq_convolution hδ0 (min_le_left _ _) (mem_ball_self (by linarith))]
    have hx2 : x ∈ ball x₀ (2 * R x₀) := by
      rw [mem_ball]
      have : dist x x₀ < R x₀ := hx
      linarith
    rw [e1, localMollify_indep hh (hRsub x₀ hx₀) hR0 le_rfl hδ0 (min_le_right _ _) hx,
      harmonicMollify_eq_convolution hδ0 (min_le_right _ _) hx2]
  have hev : ∀ x₀ ∈ U, h' =ᶠ[𝓝 x₀] ((closedBall x₀ (3 * R x₀)).indicator h
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d (R x₀)) := fun x₀ hx₀ ↦
    eventuallyEq_of_mem (ball_mem_nhds x₀ (hRpos x₀ hx₀)) (hloc x₀ hx₀)
  refine ⟨h', ?_, ?_, ?_⟩
  · intro x₀ hx₀
    have hw : ContDiff ℝ (⊤ : ℕ∞) ((closedBall x₀ (3 * R x₀)).indicator h
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledHarmonicKernel d (R x₀)) :=
      (hasCompactSupport_scaledHarmonicKernel (hRpos x₀ hx₀)).contDiff_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (integrable_indicator_of_isVeryWeaklyHarmonicOn hh (hRsub x₀ hx₀)).locallyIntegrable
        (contDiff_scaledHarmonicKernel _)
    exact (hw.contDiffAt.congr_of_eventuallyEq (hev x₀ hx₀)).contDiffWithinAt
  · intro x₀ hx₀
    rw [(laplacian_congr_nhds (hev x₀ hx₀)).eq_of_nhds]
    exact laplacian_localMollify_eq_zero hh (hRsub x₀ hx₀) (hRpos x₀ hx₀) le_rfl
      (mem_ball_self (by linarith [hRpos x₀ hx₀]))
  · have hcov : ∀ x ∈ U, ball x (R x) ∈ 𝓝[U] x := fun x hx ↦
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hRpos x hx))
    obtain ⟨T, hTU, hTc, hUT⟩ := TopologicalSpace.countable_cover_nhdsWithin hcov
    have hT : ∀ᵐ y ∂volume.restrict (⋃ x ∈ T, ball x (R x)), h y = h' y := by
      rw [ae_restrict_biUnion_iff _ hTc]
      intro x₀ hx₀
      have hx₀U := hTU hx₀
      filter_upwards [localMollify_ae_eq hh (hRpos x₀ hx₀U) (hRsub x₀ hx₀U)
        (hRpos x₀ hx₀U) le_rfl, ae_restrict_mem measurableSet_ball] with y hy hyb
      rw [hloc x₀ hx₀U y hyb, hy]
    exact ae_restrict_of_ae_restrict_of_subset hUT hT


/-- A continuous very weakly harmonic function is itself smooth and harmonic. -/
theorem IsVeryWeaklyHarmonicOn.contDiffOn_of_continuousOn {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : IsVeryWeaklyHarmonicOn U h) (hc : ContinuousOn h U) :
    ContDiffOn ℝ (⊤ : ℕ∞) h U ∧ ∀ x ∈ U, Δ h x = 0 := by
  obtain ⟨h', hh', hΔ', hae⟩ := weyl_lemma hU hh
  have heq : EqOn h h' U := Measure.eqOn_open_of_ae_eq hae hU hc hh'.continuousOn
  refine ⟨hh'.congr heq, fun x hx ↦ ?_⟩
  have hev : h =ᶠ[𝓝 x] h' := eventuallyEq_of_mem (hU.mem_nhds hx) heq
  rw [(laplacian_congr_nhds hev).eq_of_nhds]
  exact hΔ' x hx

private theorem integrable_mul_of_continuousOn_of_tsupport_subset {c ψ : Space d → ℝ}
    {U : Set (Space d)} (hc : ContinuousOn c U) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ U) : Integrable (fun x ↦ c x * ψ x) :=
  (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right c ψ).trans (subset_tsupport ψ))).mp
    (((hc.mono hsub).mul hψ.continuousOn).integrableOn_compact hψc)

/-- A classical `C²` harmonic function is very weakly harmonic. -/
theorem isVeryWeaklyHarmonicOn_of_harmonic {U : Set (Space d)} (hU : IsOpen U)
    {h : Space d → ℝ} (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) :
    IsVeryWeaklyHarmonicOn U h := by
  refine ⟨hh.continuousOn.locallyIntegrableOn hU.measurableSet, fun φ hφ hφc hφU ↦ ?_⟩
  let b := stdOrthonormalBasis ℝ (Space d)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (m := 1) (by norm_num)
  have hψ : ∀ i, ContDiff ℝ 1 (fun x ↦ fderiv ℝ φ x (b i)) := fun i ↦
    hd.clm_apply contDiff_const
  have hψc : ∀ i, HasCompactSupport (fun x ↦ fderiv ℝ φ x (b i)) := fun i ↦
    hφc.fderiv_apply ℝ (b i)
  have hψU : ∀ i, tsupport (fun x ↦ fderiv ℝ φ x (b i)) ⊆ U := fun i ↦
    (tsupport_fderiv_apply_subset ℝ (b i)).trans hφU
  have hh1 : ContDiffOn ℝ 1 h U := hh.of_le (by norm_num)
  have hdh : ∀ i, ContinuousOn (fun x ↦ fderiv ℝ h x (b i)) U := fun i ↦
    (hh1.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hint : ∀ i, Integrable (fun x ↦ h x * fderiv ℝ (fun y ↦ fderiv ℝ φ y (b i)) x (b i)) :=
    fun i ↦ integrable_mul_of_continuousOn_of_tsupport_subset hh.continuousOn
      (((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hψc i).fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans (hψU i))
  have hint2 : ∀ i, Integrable (fun x ↦ fderiv ℝ h x (b i) * fderiv ℝ φ x (b i)) := fun i ↦
    integrable_mul_of_continuousOn_of_tsupport_subset (hdh i) (hψ i).continuous (hψc i) (hψU i)
  have hlap : ∀ x, Δ φ x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ φ y (b i)) x (b i) := fun x ↦
    laplacian_eq_sum_fderiv b (hd.differentiable one_ne_zero x)
  have hgreen := integral_inner_gradient_eq_neg_laplacian_mul (μ := volume) hU hh
    (hφ.of_le (by simp)) hφc hφU
  have hzero : (fun x ↦ (Δ h) x * φ x) = fun _ ↦ 0 := by
    funext x
    by_cases hx : x ∈ U
    · rw [hΔ x hx, zero_mul]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' ↦ hx (hφU hx')
      rw [hφx, mul_zero]
  rw [hzero, integral_zero, neg_zero] at hgreen
  simp_rw [inner_gradient_eq_sum_fderiv b h φ] at hgreen
  rw [integral_finsetSum _ (fun i _ ↦ hint2 i)] at hgreen
  simp_rw [hlap, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hint i)]
  simp_rw [integral_mul_fderiv_eq_neg_of_hasCompactSupport hU hh1 (hψ _) (hψc _) (hψU _)]
  rw [Finset.sum_neg_distrib, hgreen, neg_zero]

/-! ### The mean value property on balls -/

/-- Continuous profiles increasing to the indicator of `(-∞, 1)`. -/
def ballCutoffProfile (n : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * (1 - t)))

theorem continuous_ballCutoffProfile (n : ℕ) : Continuous (ballCutoffProfile n) := by
  unfold ballCutoffProfile
  fun_prop

theorem ballCutoffProfile_eq_zero (n : ℕ) {t : ℝ} (ht : 1 ≤ t) : ballCutoffProfile n t = 0 := by
  have h1 : ((n : ℝ) + 1) * (1 - t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  rw [ballCutoffProfile, max_eq_left h1, min_eq_right zero_le_one]

theorem ballCutoffProfile_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ballCutoffProfile n t :=
  le_min zero_le_one (le_max_left _ _)

theorem ballCutoffProfile_le_one (n : ℕ) (t : ℝ) : ballCutoffProfile n t ≤ 1 :=
  min_le_left _ _

theorem tendsto_ballCutoffProfile_of_lt {t : ℝ} (ht : t < 1) :
    Tendsto (fun n ↦ ballCutoffProfile n t) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / (1 - t))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have h1 : 1 ≤ ((n : ℝ) + 1) * (1 - t) := by
    have h2 : 1 / (1 - t) ≤ n := hN.trans (by exact_mod_cast hn)
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith
  rw [ballCutoffProfile, min_eq_left (le_max_of_le_right h1)]

theorem tendsto_ballCutoffProfile_norm (z : Space d) :
    Tendsto (fun n ↦ ballCutoffProfile n (‖z‖ ^ 2)) atTop
      (𝓝 ((ball (0 : Space d) 1).indicator 1 z)) := by
  by_cases hz : ‖z‖ < 1
  · have hzb : z ∈ ball (0 : Space d) 1 := by simpa using hz
    rw [indicator_of_mem hzb, Pi.one_apply]
    exact tendsto_ballCutoffProfile_of_lt (by nlinarith [norm_nonneg z])
  · have hzb : z ∉ ball (0 : Space d) 1 := by simpa using hz
    rw [indicator_of_notMem hzb]
    have h1 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ (not_lt.mp hz)
    simp only [ballCutoffProfile_eq_zero _ h1]
    exact tendsto_const_nhds

/-- **Mean value property** (item 3): a `C²` function harmonic on an open set containing
`closedBall x r` equals its average over `ball x r`. -/
theorem harmonic_eq_average_ball {U : Set (Space d)} (hU : IsOpen U) {h : Space d → ℝ}
    (hh : ContDiffOn ℝ 2 h U) (hΔ : ∀ y ∈ U, Δ h y = 0) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) (hr : 0 < r) :
    h x = ⨍ y in ball x r, h y := by
  obtain ⟨r', hr', h', hh', heq, hsub⟩ :=
    exists_contDiff_eqOn_ball_of_contDiffOn hU (n := 2) hh hr.le hxr
  have hΔ' : ∀ y ∈ ball x r', Δ h' y = 0 := fun y hy ↦ by
    rw [(laplacian_congr_nhds (eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) heq)).eq_of_nhds]
    exact hΔ y (hsub (ball_subset_closedBall hy))
  have hxr' : closedBall x r ⊆ ball x r' := closedBall_subset_ball hr'
  have hc : Continuous h' := hh'.continuous
  let ρ : ℕ → Space d → ℝ := fun n z ↦ ballCutoffProfile n (‖z‖ ^ 2)
  have hρc : ∀ n, Continuous (ρ n) := fun n ↦
    (continuous_ballCutoffProfile n).comp (continuous_norm.pow 2)
  have hρ0 : ∀ n, ∀ z : Space d, z ∉ closedBall (0 : Space d) 1 → ρ n z = 0 := by
    intro n z hz
    simp only [mem_closedBall, dist_zero_right, not_le] at hz
    exact ballCutoffProfile_eq_zero n (one_le_pow₀ hz.le)
  have hid : ∀ n, ∫ z, h' (x + r • z) * ρ n z = h' x * ∫ z, ρ n z := fun n ↦
    harmonic_integral_comp_mul_radial isOpen_ball hh'.contDiffOn hΔ' hxr'
      (continuous_ballCutoffProfile n) (fun t ht ↦ ballCutoffProfile_eq_zero n ht.le) hr.le
      le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hc.continuousOn
  have hmem : ∀ z ∈ closedBall (0 : Space d) 1, x + r • z ∈ closedBall x r := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    calc r * ‖z‖ ≤ r * 1 := by gcongr
      _ = r := mul_one r
  have hbint : ∀ C : ℝ, Integrable ((closedBall (0 : Space d) 1).indicator fun _ ↦ C) :=
    fun C ↦ (integrableOn_const (C := C) measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hcomp : Continuous fun z : Space d ↦ x + r • z := by fun_prop
  have hLmeas : ∀ n, AEStronglyMeasurable (fun z ↦ h' (x + r • z) * ρ n z) volume :=
    fun n ↦ ((hc.comp hcomp).mul (hρc n)).aestronglyMeasurable
  have hLbound : ∀ n, ∀ᵐ z ∂(volume : Measure (Space d)),
      ‖h' (x + r • z) * ρ n z‖ ≤ (closedBall (0 : Space d) 1).indicator (fun _ ↦ M) z := by
    intro n
    filter_upwards with z
    by_cases hz : z ∈ closedBall (0 : Space d) 1
    · rw [indicator_of_mem hz, norm_mul]
      have h1 : ‖h' (x + r • z)‖ ≤ M := hM _ (hmem z hz)
      have h2 : ‖ρ n z‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (ballCutoffProfile_nonneg _ _)]
        exact ballCutoffProfile_le_one _ _
      calc ‖h' (x + r • z)‖ * ‖ρ n z‖ ≤ M * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = M := mul_one M
    · rw [indicator_of_notMem hz, hρ0 n z hz, mul_zero, norm_zero]
  have hLlim : ∀ᵐ z ∂(volume : Measure (Space d)), Tendsto (fun n ↦ h' (x + r • z) * ρ n z)
      atTop (𝓝 (h' (x + r • z) * (ball (0 : Space d) 1).indicator 1 z)) :=
    Eventually.of_forall fun z ↦ (tendsto_ballCutoffProfile_norm z).const_mul (h' (x + r • z))
  have hLHS := tendsto_integral_of_dominated_convergence _ hLmeas (hbint M) hLbound hLlim
  have hRHS : Tendsto (fun n ↦ h' x * ∫ z, ρ n z) atTop
      (𝓝 (h' x * volume.real (ball (0 : Space d) 1))) := by
    apply Tendsto.const_mul
    have hlim := tendsto_integral_of_dominated_convergence (F := ρ)
      (f := (ball (0 : Space d) 1).indicator 1) _ (fun n ↦ (hρc n).aestronglyMeasurable)
      (hbint 1) (fun n ↦ Eventually.of_forall fun z ↦ by
        by_cases hz : z ∈ closedBall (0 : Space d) 1
        · rw [indicator_of_mem hz, Real.norm_of_nonneg (ballCutoffProfile_nonneg _ _)]
          exact ballCutoffProfile_le_one _ _
        · rw [indicator_of_notMem hz, hρ0 n z hz, norm_zero])
      (Eventually.of_forall tendsto_ballCutoffProfile_norm)
    rwa [integral_indicator_one measurableSet_ball] at hlim
  have hlimit := tendsto_nhds_unique hLHS (hRHS.congr fun n ↦ (hid n).symm)
  have hcv : ∫ z, h' (x + r • z) * (ball (0 : Space d) 1).indicator 1 z =
      (r ^ d)⁻¹ * ∫ y in ball x r, h' y := by
    rw [← integral_indicator measurableSet_ball, ← integral_comp_add_smul _ x hr]
    congr 1
    funext z
    have hiff : x + r • z ∈ ball x r ↔ z ∈ ball (0 : Space d) 1 := by
      rw [mem_ball, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hr.le, dist_zero_right]
      constructor
      · intro h1
        nlinarith [norm_nonneg z]
      · intro h1
        nlinarith [norm_nonneg z]
    by_cases hz : z ∈ ball (0 : Space d) 1
    · rw [indicator_of_mem hz, indicator_of_mem (hiff.2 hz), Pi.one_apply, mul_one]
    · rw [indicator_of_notMem hz, indicator_of_notMem (fun h1 ↦ hz (hiff.1 h1)), mul_zero]
  rw [hcv] at hlimit
  have hint : ∫ y in ball x r, h y = ∫ y in ball x r, h' y :=
    setIntegral_congr_fun measurableSet_ball fun y hy ↦ (heq (ball_subset_ball hr'.le hy)).symm
  have hhx : h x = h' x := (heq (mem_ball_self (by linarith))).symm
  have hvol : 0 < volume.real (ball (0 : Space d) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hrd : 0 < r ^ d := pow_pos hr d
  rw [setAverage_eq, smul_eq_mul, volume_real_ball x hr, hint, hhx]
  have hI : ∫ y in ball x r, h' y = r ^ d * (h' x * volume.real (ball (0 : Space d) 1)) := by
    rw [← hlimit]
    field_simp
  rw [hI]
  field_simp

end SerrinEpigraph
