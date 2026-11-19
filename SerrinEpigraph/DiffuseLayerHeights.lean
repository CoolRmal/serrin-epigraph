module

public import SerrinEpigraph.BVColumnGraph
public import SerrinEpigraph.DiffuseStressEstimates
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Level heights of diffuse layers: the HA2 Sobolev bound and the HA3 level comparison

This file implements the function-theoretic part of HA2 and HA3 in
`docs/rigidity-proof/harmonic-approximation.md`, for an arbitrary continuous function
`v : Space (m + 1) → ℝ` in vertical coordinates `x = point y t`. Nothing about the PDE is used;
the actual rescaled solution is treated in `SerrinEpigraph.DiffuseGoodLayers`.

* `LevelGraphFamily v D τ s₁ s₂ T c L h` is the HA2.1 input: over the horizontal set `D` and in
  the slab `|t| < τ`, each value `s ∈ [s₁, s₂]` is attained on each vertical line exactly once,
  at height `h s y`; the heights are `L`-Lipschitz on `D`; `v` is differentiable at the level
  points and `c ≤ T⁻¹ * ∂ₜ v` there (`ε = T⁻¹`). Monotonicity in `s` is *derived*.
* `LevelGraphFamily.height_le_and_mul_sub_le`, `height_sub_le`: HA3,
  `0 ≤ h_{s'} - h_s ≤ ε (s' - s) / c`.
* `mcShaneExtension`, `extendedHeight`: the common McShane extension (level truncated to
  `[s₁, s₂]`, values truncated to `[-τ, τ]`). It is `L`-Lipschitz, agrees with `h` on `D`, is
  monotone in `s`, satisfies HA3 everywhere (`extendedHeight_le_add`) and is jointly
  Lipschitz in `(s, y)` (`continuous_extendedHeight`).
* `LevelGraphFamily.lintegral_levelRegion_eq`: the change of variables to level coordinates,
  `∫_{level region} Φ = ∫_D ∫_{s₁}^{s₂} Φ(y, h_s y) / ∂ₜ v(y, h_s y) ds dy`.
* `LevelGraphFamily.horizontal_gradient_eq`: implicit differentiation,
  `∇_y v = -∂ₜ v ∇ h_s` wherever the extension is differentiable (a.e. by Rademacher).
* `LevelGraphFamily.lintegral_height_energy_eq`: the HA2 identity
  `∫_I ∫_D ε ∂ₜ v |∇ h_s|² = ∫_{level region} ε |∇_y v|²`.
* `LevelGraphFamily.lintegral_height_gradient_le`: HA2.3,
  `∫_I ∫_B |∇ h̃_s|² ≤ c⁻¹ ∫_{level region} ε |∇_y v|² + |I| L² |B \ D|`.
* `LevelGraphFamily.exists_reference_level(_normalized)`: the mean-value choice of `s₀` and the
  uniform bound `∫_B |∇ H|² ≤ (c⁻¹ + |I| L² M) / |I|` for `H = (h̃_{s₀} - a) / δ`.
* `normalizedHeight` and its scaling identities; `lintegral_sq_normalizedHeight_le_of_poincare`
  takes a Poincaré inequality as an explicit hypothesis (none is proved here);
  `LevelGraphFamily.lintegral_sq_normalizedHeight_le_slab` is the bound by the slab height.
* `LevelGraphFamily.lintegral_normalizedHeight_sub_sq_le`: HA3.1.
* `lintegral_sq_sub_le_of_lipschitzWith`, `exists_mem_ball_of_volume_lt`: HA9.2, the
  comparison of extensions built on different good sets.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

/-! ### McShane extension -/

/-- McShane's inf-convolution extension `y ↦ inf_{z ∈ D} (h z + L * dist y z)`. -/
def mcShaneExtension {X : Type*} [PseudoMetricSpace X] (D : Set X) (L : ℝ) (h : X → ℝ)
    (y : X) : ℝ :=
  ⨅ z : D, (h z + L * dist y z)

section McShane

variable {X : Type*} [PseudoMetricSpace X] {D : Set X} {L : ℝ≥0} {h : X → ℝ}

theorem mcShaneExtension_bddBelow (hD : D.Nonempty) (hh : LipschitzOnWith L h D) (y : X) :
    BddBelow (range fun z : D ↦ h z + (L : ℝ) * dist y z) := by
  obtain ⟨z₀, hz₀⟩ := hD
  refine ⟨h z₀ - L * dist y z₀, ?_⟩
  rintro w ⟨z, rfl⟩
  have h1 : h z₀ ≤ h z + L * dist z₀ z := hh.le_add_mul hz₀ z.2
  have h2 : dist z₀ z ≤ dist y z₀ + dist y z := dist_triangle_left _ _ _
  have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
  dsimp only
  linarith

theorem mcShaneExtension_le (hD : D.Nonempty) (hh : LipschitzOnWith L h D) (y : X)
    {z : X} (hz : z ∈ D) :
    mcShaneExtension D L h y ≤ h z + L * dist y z :=
  ciInf_le (mcShaneExtension_bddBelow hD hh y) ⟨z, hz⟩

theorem le_mcShaneExtension (hD : D.Nonempty) {y : X} {a : ℝ}
    (ha : ∀ z ∈ D, a ≤ h z + L * dist y z) :
    a ≤ mcShaneExtension D L h y := by
  have : Nonempty D := hD.to_subtype
  exact le_ciInf fun z ↦ ha z z.2

/-- The McShane extension agrees with the original function on its domain. -/
theorem mcShaneExtension_eq_of_mem (hh : LipschitzOnWith L h D) {y : X} (hy : y ∈ D) :
    mcShaneExtension D L h y = h y := by
  have hD : D.Nonempty := ⟨y, hy⟩
  apply le_antisymm
  · simpa using mcShaneExtension_le hD hh y hy
  · exact le_mcShaneExtension hD fun z hz ↦ hh.le_add_mul hy hz

/-- The McShane extension is globally Lipschitz with the same constant. -/
theorem mcShaneExtension_lipschitzWith (hD : D.Nonempty) (hh : LipschitzOnWith L h D) :
    LipschitzWith L (mcShaneExtension D L h) := by
  apply LipschitzWith.of_le_add_mul
  intro y₁ y₂
  have hh' : mcShaneExtension D L h y₁ - L * dist y₁ y₂ ≤ mcShaneExtension D L h y₂ := by
    apply le_mcShaneExtension hD
    intro z hz
    have h1 := mcShaneExtension_le hD hh y₁ hz
    have h2 : dist y₁ z ≤ dist y₁ y₂ + dist y₂ z := dist_triangle _ _ _
    have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
    linarith
  linarith

/-- An upper comparison on the domain, with an additive constant, survives the extension. -/
theorem mcShaneExtension_le_add_of_le_add {h₁ h₂ : X → ℝ} (hD : D.Nonempty)
    (hh₂ : LipschitzOnWith L h₂ D) {κ : ℝ}
    (hle : ∀ z ∈ D, h₂ z ≤ h₁ z + κ) (y : X) :
    mcShaneExtension D L h₂ y ≤ mcShaneExtension D L h₁ y + κ := by
  have hh' : mcShaneExtension D L h₂ y - κ ≤ mcShaneExtension D L h₁ y := by
    apply le_mcShaneExtension hD
    intro z hz
    have h1 := mcShaneExtension_le hD hh₂ y hz
    have h2 := hle z hz
    linarith
  linarith

/-- The extension preserves order. -/
theorem mcShaneExtension_mono {h₁ h₂ : X → ℝ} (hD : D.Nonempty)
    (hh₁ : LipschitzOnWith L h₁ D) (hle : ∀ z ∈ D, h₁ z ≤ h₂ z) (y : X) :
    mcShaneExtension D L h₁ y ≤ mcShaneExtension D L h₂ y := by
  simpa using mcShaneExtension_le_add_of_le_add (h₁ := h₂) hD hh₁ (κ := 0)
    (fun z hz ↦ by simpa using hle z hz) y

end McShane

/-! ### Clamping to a slab -/

/-- Truncation of a real number to the closed interval `[-τ, τ]`. -/
def slabClamp (τ x : ℝ) : ℝ := max (-τ) (min τ x)

theorem slabClamp_eq_of_mem {τ x : ℝ} (hx : x ∈ Icc (-τ) τ) : slabClamp τ x = x := by
  unfold slabClamp
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem slabClamp_mono (τ : ℝ) : Monotone (slabClamp τ) :=
  fun _ _ hxy ↦ max_le_max le_rfl (min_le_min le_rfl hxy)

theorem slabClamp_le_add {τ x y κ : ℝ} (hκ : 0 ≤ κ) (hxy : x ≤ y + κ) :
    slabClamp τ x ≤ slabClamp τ y + κ := by
  unfold slabClamp
  rcases le_total τ x with h1 | h1 <;> rcases le_total τ y with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, h1, h2] <;>
    rcases le_total (-τ) τ with h3 | h3 <;> grind

theorem abs_slabClamp_sub_le (τ x y : ℝ) : |slabClamp τ x - slabClamp τ y| ≤ |x - y| := by
  unfold slabClamp
  have h1 := abs_max_sub_max_le_abs (-τ) (min τ x) (min τ y)
  have h2 := abs_min_sub_min_le_max τ x τ y
  simp only [sub_self, abs_zero] at h2
  calc _ ≤ |min τ x - min τ y| := by
        simpa [max_comm] using abs_max_sub_max_le_max (-τ) (min τ x) (-τ) (min τ y)
    _ ≤ |x - y| := by
        simpa [min_comm] using abs_min_sub_min_le_max τ x τ y

theorem slabClamp_lipschitzWith (τ : ℝ) : LipschitzWith 1 (slabClamp τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq] using abs_slabClamp_sub_le τ x y

theorem slabClamp_mem_Icc {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) : slabClamp τ x ∈ Icc (-τ) τ := by
  unfold slabClamp
  refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-! ### Level heights on one vertical line -/

/-- Between two points whose values are attained only once on an order-connected set,
the function stays between those two values. -/
theorem mem_uIcc_of_unique_level_aux {F : ℝ → ℝ} {t₁ t₂ : ℝ}
    (hF : ContinuousOn F (Icc t₁ t₂))
    (hu₁ : ∀ τ ∈ Icc t₁ t₂, F τ = F t₁ → τ = t₁)
    (hu₂ : ∀ τ ∈ Icc t₁ t₂, F τ = F t₂ → τ = t₂)
    {τ : ℝ} (hτ : τ ∈ Icc t₁ t₂) : F τ ∈ uIcc (F t₁) (F t₂) := by
  have hl : ContinuousOn F (Icc t₁ τ) := hF.mono (Icc_subset_Icc le_rfl hτ.2)
  have hr : ContinuousOn F (Icc τ t₂) := hF.mono (Icc_subset_Icc hτ.1 le_rfl)
  refine ⟨?_, ?_⟩
  · by_contra hn
    push Not at hn
    rcases le_total (F t₁) (F t₂) with h | h
    · -- `F τ < F t₁ ≤ F t₂`: the value `F t₁` is attained again in `[τ, t₂]`.
      have hlt : F τ < F t₁ := lt_of_lt_of_le hn (le_of_eq (min_eq_left h))
      obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc hτ.2 hr ⟨hlt.le, h⟩
      have := hu₁ σ ⟨hτ.1.trans hσ.1, hσ.2⟩ hFσ
      have hτe : τ = t₁ := le_antisymm (this ▸ hσ.1) hτ.1
      rw [hτe] at hlt
      exact lt_irrefl _ hlt
    · have hlt : F τ < F t₂ := lt_of_lt_of_le hn (le_of_eq (min_eq_right h))
      obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc' hτ.1 hl ⟨hlt.le, h⟩
      have := hu₂ σ ⟨hσ.1, hσ.2.trans hτ.2⟩ hFσ
      have hτe : τ = t₂ := le_antisymm hτ.2 (this ▸ hσ.2)
      rw [hτe] at hlt
      exact lt_irrefl _ hlt
  · by_contra hn
    push Not at hn
    rcases le_total (F t₁) (F t₂) with h | h
    · have hlt : F t₂ < F τ := lt_of_le_of_lt (le_of_eq (max_eq_right h).symm) hn
      obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc hτ.1 hl ⟨h, hlt.le⟩
      have := hu₂ σ ⟨hσ.1, hσ.2.trans hτ.2⟩ hFσ
      have hτe : τ = t₂ := le_antisymm hτ.2 (this ▸ hσ.2)
      rw [hτe] at hlt
      exact lt_irrefl _ hlt
    · have hlt : F t₁ < F τ := lt_of_le_of_lt (le_of_eq (max_eq_left h).symm) hn
      obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc' hτ.2 hr ⟨h, hlt.le⟩
      have := hu₁ σ ⟨hτ.1.trans hσ.1, hσ.2⟩ hFσ
      have hτe : τ = t₁ := le_antisymm (this ▸ hσ.1) hτ.1
      rw [hτe] at hlt
      exact lt_irrefl _ hlt


/-- Along a segment, a derivative lower bound at every interior point gives the
corresponding lower bound for the increment. -/
theorem mul_sub_le_sub_of_hasDerivAt_lower {F : ℝ → ℝ} {t₁ t₂ c : ℝ} (h12 : t₁ ≤ t₂)
    (hF : ContinuousOn F (Icc t₁ t₂))
    (hd : ∀ τ ∈ Ioo t₁ t₂, ∃ F' : ℝ, HasDerivAt F F' τ ∧ c ≤ F') :
    c * (t₂ - t₁) ≤ F t₂ - F t₁ := by
  have hdiff : DifferentiableOn ℝ F (interior (Icc t₁ t₂)) := by
    rw [interior_Icc]
    intro τ hτ
    obtain ⟨F', hF', -⟩ := hd τ hτ
    exact hF'.differentiableAt.differentiableWithinAt
  have hderiv : ∀ τ ∈ interior (Icc t₁ t₂), c ≤ deriv F τ := by
    rw [interior_Icc]
    intro τ hτ
    obtain ⟨F', hF', hc⟩ := hd τ hτ
    rw [hF'.deriv]
    exact hc
  exact (convex_Icc t₁ t₂).mul_sub_le_image_sub_of_le_deriv hF hdiff hderiv t₁
    (left_mem_Icc.mpr h12) t₂ (right_mem_Icc.mpr h12) h12

/-- The one-dimensional HA3 comparison. On an order-connected set `J`, suppose that every
value `s ∈ [a, b]` is attained exactly once, at `H s`, and that `F` has derivative at least
`c > 0` at each such point. Then the heights increase with the value and their separation is
at most the value separation divided by `c`. -/
theorem height_le_and_mul_sub_le {F : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hF : ContinuousOn F J) {a b c : ℝ} (hc : 0 < c) {H : ℝ → ℝ}
    (hmem : ∀ s ∈ Icc a b, H s ∈ J) (hlevel : ∀ s ∈ Icc a b, F (H s) = s)
    (hunique : ∀ s ∈ Icc a b, ∀ t ∈ J, F t = s → t = H s)
    (hderiv : ∀ s ∈ Icc a b, ∃ F' : ℝ, HasDerivAt F F' (H s) ∧ c ≤ F')
    {s s' : ℝ} (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) (hss' : s ≤ s') :
    H s ≤ H s' ∧ c * (H s' - H s) ≤ s' - s := by
  -- The increment along any ordered pair of level heights.
  have key : ∀ σ₁ ∈ Icc a b, ∀ σ₂ ∈ Icc a b, H σ₁ ≤ H σ₂ →
      c * (H σ₂ - H σ₁) ≤ σ₂ - σ₁ := by
    intro σ₁ hσ₁ σ₂ hσ₂ hle
    have hseg : Icc (H σ₁) (H σ₂) ⊆ J := hJ.out (hmem σ₁ hσ₁) (hmem σ₂ hσ₂)
    have hFseg : ContinuousOn F (Icc (H σ₁) (H σ₂)) := hF.mono hseg
    have hval : ∀ τ ∈ Icc (H σ₁) (H σ₂), F τ ∈ uIcc σ₁ σ₂ := by
      intro τ hτ
      have hh := mem_uIcc_of_unique_level_aux hFseg
        (fun ρ hρ hFρ ↦ hunique σ₁ hσ₁ ρ (hseg hρ) (by rw [hFρ, hlevel σ₁ hσ₁]))
        (fun ρ hρ hFρ ↦ hunique σ₂ hσ₂ ρ (hseg hρ) (by rw [hFρ, hlevel σ₂ hσ₂])) hτ
      rwa [hlevel σ₁ hσ₁, hlevel σ₂ hσ₂] at hh
    have hsub : uIcc σ₁ σ₂ ⊆ Icc a b := uIcc_subset_Icc hσ₁ hσ₂
    have hh := mul_sub_le_sub_of_hasDerivAt_lower hle hFseg (fun τ hτ ↦ by
      have hτ' : τ ∈ Icc (H σ₁) (H σ₂) := Ioo_subset_Icc_self hτ
      have hFτ : F τ ∈ Icc a b := hsub (hval τ hτ')
      have hτH : τ = H (F τ) := hunique (F τ) hFτ τ (hseg hτ') rfl
      obtain ⟨F', hF', hcF'⟩ := hderiv (F τ) hFτ
      rw [← hτH] at hF'
      exact ⟨F', hF', hcF'⟩)
    rwa [hlevel σ₁ hσ₁, hlevel σ₂ hσ₂] at hh
  rcases le_total (H s) (H s') with h | h
  · exact ⟨h, key s hs s' hs' h⟩
  · have hh := key s' hs' s hs h
    have heq : H s = H s' := by
      refine (le_antisymm h ?_).symm
      by_contra hn
      push Not at hn
      have : 0 < c * (H s - H s') := mul_pos hc (by linarith)
      linarith
    refine ⟨heq.le, ?_⟩
    rw [heq, sub_self, mul_zero]
    linarith

/-- Values of the section between two level heights lie in the corresponding value interval. -/
theorem mem_Icc_of_mem_Icc_heights {F : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hF : ContinuousOn F J) {a b : ℝ} {H : ℝ → ℝ}
    (hmem : ∀ s ∈ Icc a b, H s ∈ J) (hlevel : ∀ s ∈ Icc a b, F (H s) = s)
    (hunique : ∀ s ∈ Icc a b, ∀ t ∈ J, F t = s → t = H s)
    (hab : a ≤ b) {t : ℝ} (ht : t ∈ Icc (H a) (H b)) : F t ∈ Icc a b := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hseg : Icc (H a) (H b) ⊆ J := hJ.out (hmem a ha) (hmem b hb)
  have hh := mem_uIcc_of_unique_level_aux (hF.mono hseg)
    (fun ρ hρ hFρ ↦ hunique a ha ρ (hseg hρ) (by rw [hFρ, hlevel a ha]))
    (fun ρ hρ hFρ ↦ hunique b hb ρ (hseg hρ) (by rw [hFρ, hlevel b hb])) ht
  rwa [hlevel a ha, hlevel b hb, uIcc_of_le hab] at hh

/-- The vertical section of a function differentiable at a point has the vertical
derivative as its derivative. -/
theorem hasDerivAt_vertical_section {m : ℕ} {v : Space (m + 1) → ℝ} {y : Space m} {t : ℝ}
    (hv : DifferentiableAt ℝ v (point y t)) :
    HasDerivAt (fun τ ↦ v (point y τ)) (verticalDerivative v (point y t)) t := by
  have hp : HasDerivAt (fun τ : ℝ ↦ point y 0 + τ • verticalDirection m)
      (verticalDirection m) t := by
    simpa using ((hasDerivAt_id t).smul_const (verticalDirection m)).const_add (point y 0)
  have he (τ : ℝ) : point y 0 + τ • verticalDirection m = point y τ := by
    rw [point_add_vertical, zero_add]
  have hv' : DifferentiableAt ℝ v (point y 0 + t • verticalDirection m) := by rwa [he]
  have hh := hv'.hasFDerivAt.comp_hasDerivAt t hp
  simp only [he] at hh
  exact hh


/-! ### Level graph families -/

/-- The level region: points in the slab `|t| < τ` over `D` whose value lies in `[s₁, s₂]`. -/
def levelRegion {m : ℕ} (v : Space (m + 1) → ℝ) (D : Set (Space m)) (τ s₁ s₂ : ℝ) :
    Set (Space (m + 1)) :=
  {x | horizontal x ∈ D ∧ x (Fin.last m) ∈ Ioo (-τ) τ ∧ v x ∈ Icc s₁ s₂}

theorem point_mem_levelRegion_iff {m : ℕ} {v : Space (m + 1) → ℝ} {D : Set (Space m)}
    {τ s₁ s₂ : ℝ} {y : Space m} {t : ℝ} :
    point y t ∈ levelRegion v D τ s₁ s₂ ↔
      y ∈ D ∧ t ∈ Ioo (-τ) τ ∧ v (point y t) ∈ Icc s₁ s₂ := by
  simp [levelRegion]

theorem measurableSet_levelRegion {m : ℕ} {v : Space (m + 1) → ℝ} (hv : Continuous v)
    {D : Set (Space m)} (hD : MeasurableSet D) (τ s₁ s₂ : ℝ) :
    MeasurableSet (levelRegion v D τ s₁ s₂) := by
  have h1 : MeasurableSet (horizontal ⁻¹' D : Set (Space (m + 1))) :=
    hD.preimage continuous_horizontal.measurable
  have h2 : MeasurableSet {x : Space (m + 1) | x (Fin.last m) ∈ Ioo (-τ) τ} :=
    measurableSet_Ioo.preimage continuous_last.measurable
  have h3 : MeasurableSet {x | v x ∈ Icc s₁ s₂} := measurableSet_Icc.preimage hv.measurable
  exact h1.inter (h2.inter h3)

/-- HA2.1 input: level graphs over a horizontal good set.

Over `D`, inside the slab `|t| < τ`, every value `s ∈ [s₁, s₂]` of `v` is attained on each
vertical line at exactly one height `h s y`. The heights are `L`-Lipschitz on `D`, `v` is
differentiable at the level points, and the diffuse vertical derivative `T⁻¹ * ∂ₜ v` is at
least `c` there. Monotonicity of the heights in `s` is not assumed; it is derived. -/
structure LevelGraphFamily {m : ℕ} (v : Space (m + 1) → ℝ) (D : Set (Space m))
    (τ s₁ s₂ T c : ℝ) (L : ℝ≥0) (h : ℝ → Space m → ℝ) : Prop where
  continuous : Continuous v
  mem_slab : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, h s y ∈ Ioo (-τ) τ
  level : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, v (point y (h s y)) = s
  unique : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, v (point y t) = s → t = h s y
  lipschitzOnWith : ∀ s ∈ Icc s₁ s₂, LipschitzOnWith L (h s) D
  differentiableAt : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, DifferentiableAt ℝ v (point y (h s y))
  vertical_lower : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, c ≤ T⁻¹ * verticalDerivative v (point y (h s y))

namespace LevelGraphFamily

variable {m : ℕ} {v : Space (m + 1) → ℝ} {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
  {h : ℝ → Space m → ℝ}

/-- The undiffused vertical derivative at a level point is at least `c * T`. -/
theorem mul_le_verticalDerivative (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    {s : ℝ} (hs : s ∈ Icc s₁ s₂) {y : Space m} (hy : y ∈ D) :
    c * T ≤ verticalDerivative v (point y (h s y)) := by
  have hh := hG.vertical_lower s hs y hy
  have hh' := mul_le_mul_of_nonneg_right hh hT.le
  rwa [mul_comm (T⁻¹), mul_assoc, inv_mul_cancel₀ hT.ne', mul_one] at hh'

theorem verticalDerivative_pos (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) {s : ℝ} (hs : s ∈ Icc s₁ s₂) {y : Space m} (hy : y ∈ D) :
    0 < verticalDerivative v (point y (h s y)) :=
  (mul_pos hc hT).trans_le (hG.mul_le_verticalDerivative hT hs hy)

theorem continuousOn_section (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (y : Space m) :
    ContinuousOn (fun t ↦ v (point y t)) (Ioo (-τ) τ) :=
  (hG.continuous.comp (continuous_point y)).continuousOn

/-- HA3 on one vertical line: monotone heights with separation at most `(s' - s) / (c T)`. -/
theorem height_le_and_mul_sub_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) {y : Space m} (hy : y ∈ D) {s s' : ℝ} (hs : s ∈ Icc s₁ s₂)
    (hs' : s' ∈ Icc s₁ s₂) (hss' : s ≤ s') :
    h s y ≤ h s' y ∧ c * T * (h s' y - h s y) ≤ s' - s :=
  SerrinEpigraph.height_le_and_mul_sub_le (F := fun t ↦ v (point y t)) (J := Ioo (-τ) τ)
    ordConnected_Ioo (hG.continuousOn_section y) (mul_pos hc hT) (H := fun σ ↦ h σ y)
    (fun σ hσ ↦ hG.mem_slab σ hσ y hy) (fun σ hσ ↦ hG.level σ hσ y hy)
    (fun σ hσ t ht hFt ↦ hG.unique σ hσ y hy t ht hFt)
    (fun σ hσ ↦ ⟨_, hasDerivAt_vertical_section (hG.differentiableAt σ hσ y hy),
      hG.mul_le_verticalDerivative hT hσ hy⟩) hs hs' hss'

theorem height_mono (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T) (hc : 0 < c)
    {y : Space m} (hy : y ∈ D) {s s' : ℝ} (hs : s ∈ Icc s₁ s₂) (hs' : s' ∈ Icc s₁ s₂)
    (hss' : s ≤ s') : h s y ≤ h s' y :=
  (hG.height_le_and_mul_sub_le hT hc hy hs hs' hss').1

/-- HA3: `0 ≤ h_{s'} - h_s ≤ (s' - s) / (c T)`, i.e. `ε (s' - s) / c` with `ε = T⁻¹`. -/
theorem height_sub_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T) (hc : 0 < c)
    {y : Space m} (hy : y ∈ D) {s s' : ℝ} (hs : s ∈ Icc s₁ s₂) (hs' : s' ∈ Icc s₁ s₂)
    (hss' : s ≤ s') : h s' y - h s y ≤ (s' - s) / (c * T) := by
  rw [le_div_iff₀ (mul_pos hc hT), mul_comm]
  exact (hG.height_le_and_mul_sub_le hT hc hy hs hs' hss').2

theorem Icc_heights_subset_slab (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hs : s₁ ≤ s₂) {y : Space m} (hy : y ∈ D) :
    Icc (h s₁ y) (h s₂ y) ⊆ Ioo (-τ) τ :=
  ordConnected_Ioo.out (hG.mem_slab s₁ (left_mem_Icc.mpr hs) y hy)
    (hG.mem_slab s₂ (right_mem_Icc.mpr hs) y hy)

theorem value_mem_Icc_of_mem_heights (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hs : s₁ ≤ s₂) {y : Space m} (hy : y ∈ D) {t : ℝ} (ht : t ∈ Icc (h s₁ y) (h s₂ y)) :
    v (point y t) ∈ Icc s₁ s₂ :=
  mem_Icc_of_mem_Icc_heights (F := fun t ↦ v (point y t)) (J := Ioo (-τ) τ)
    ordConnected_Ioo (hG.continuousOn_section y) (H := fun σ ↦ h σ y)
    (fun σ hσ ↦ hG.mem_slab σ hσ y hy) (fun σ hσ ↦ hG.level σ hσ y hy)
    (fun σ hσ t ht hFt ↦ hG.unique σ hσ y hy t ht hFt) hs ht

/-- Every point of a vertical segment between the extreme heights is a level point. -/
theorem eq_height_of_mem_heights (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hs : s₁ ≤ s₂) {y : Space m} (hy : y ∈ D) {t : ℝ} (ht : t ∈ Icc (h s₁ y) (h s₂ y)) :
    t = h (v (point y t)) y :=
  hG.unique _ (hG.value_mem_Icc_of_mem_heights hs hy ht) y hy t
    (hG.Icc_heights_subset_slab hs hy ht) rfl

/-- The level region is exactly the union of the vertical segments between the extreme
heights. -/
theorem point_mem_levelRegion_iff_mem_heights (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) {y : Space m} {t : ℝ} :
    point y t ∈ levelRegion v D τ s₁ s₂ ↔ y ∈ D ∧ t ∈ Icc (h s₁ y) (h s₂ y) := by
  rw [point_mem_levelRegion_iff]
  constructor
  · rintro ⟨hy, ht, hv⟩
    refine ⟨hy, ?_⟩
    have he := hG.unique _ hv y hy t ht rfl
    rw [he]
    exact ⟨hG.height_mono hT hc hy (left_mem_Icc.mpr hs) hv hv.1,
      hG.height_mono hT hc hy hv (right_mem_Icc.mpr hs) hv.2⟩
  · rintro ⟨hy, ht⟩
    exact ⟨hy, hG.Icc_heights_subset_slab hs hy ht, hG.value_mem_Icc_of_mem_heights hs hy ht⟩

theorem injOn_section (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hs : s₁ ≤ s₂)
    {y : Space m} (hy : y ∈ D) :
    InjOn (fun t ↦ v (point y t)) (Icc (h s₁ y) (h s₂ y)) := by
  intro t ht t' ht' heq
  rw [hG.eq_height_of_mem_heights hs hy ht, hG.eq_height_of_mem_heights hs hy ht']
  simp only at heq
  rw [heq]

theorem image_section (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T) (hc : 0 < c)
    (hs : s₁ ≤ s₂) {y : Space m} (hy : y ∈ D) :
    (fun t ↦ v (point y t)) '' Icc (h s₁ y) (h s₂ y) = Icc s₁ s₂ := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact hG.value_mem_Icc_of_mem_heights hs hy ht
  · intro σ hσ
    exact ⟨h σ y, ⟨hG.height_mono hT hc hy (left_mem_Icc.mpr hs) hσ hσ.1,
      hG.height_mono hT hc hy hσ (right_mem_Icc.mpr hs) hσ.2⟩, hG.level σ hσ y hy⟩

theorem hasDerivWithinAt_section (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hs : s₁ ≤ s₂)
    {y : Space m} (hy : y ∈ D) {t : ℝ} (ht : t ∈ Icc (h s₁ y) (h s₂ y)) :
    HasDerivWithinAt (fun t ↦ v (point y t)) (verticalDerivative v (point y t))
      (Icc (h s₁ y) (h s₂ y)) t := by
  have he := hG.eq_height_of_mem_heights hs hy ht
  have hd := hG.differentiableAt _ (hG.value_mem_Icc_of_mem_heights hs hy ht) y hy
  rw [← he] at hd
  exact (hasDerivAt_vertical_section hd).hasDerivWithinAt

theorem verticalDerivative_pos_of_mem_heights (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) {y : Space m} (hy : y ∈ D) {t : ℝ}
    (ht : t ∈ Icc (h s₁ y) (h s₂ y)) :
    0 < verticalDerivative v (point y t) := by
  have he := hG.eq_height_of_mem_heights hs hy ht
  have hp := hG.verticalDerivative_pos hT hc (hG.value_mem_Icc_of_mem_heights hs hy ht) hy
  rwa [← he] at hp

/-- HA2 change of variables on one vertical line: level coordinates. -/
theorem setLIntegral_section_eq (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) {y : Space m} (hy : y ∈ D) (Φ : Space (m + 1) → ℝ≥0∞) :
    ∫⁻ t in Icc (h s₁ y) (h s₂ y), Φ (point y t) =
      ∫⁻ s in Icc s₁ s₂,
        Φ (point y (h s y)) / ENNReal.ofReal (verticalDerivative v (point y (h s y))) := by
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
    (fun t ht ↦ hG.hasDerivWithinAt_section hs hy ht) (hG.injOn_section hs hy)
    (fun s ↦ Φ (point y (h s y)) / ENNReal.ofReal (verticalDerivative v (point y (h s y))))
  rw [hG.image_section hT hc hs hy] at hcov
  rw [hcov]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  have he := hG.eq_height_of_mem_heights hs hy ht
  have hp := hG.verticalDerivative_pos_of_mem_heights hT hc hs hy ht
  simp only
  rw [← he, abs_of_pos hp, ENNReal.mul_div_cancel (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top]

/-- HA2 change of variables: the level region in level coordinates `(y, s)`. -/
theorem lintegral_levelRegion_eq (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : MeasurableSet D) {Φ : Space (m + 1) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ x in levelRegion v D τ s₁ s₂, Φ x =
      ∫⁻ y in D, ∫⁻ s in Icc s₁ s₂,
        Φ (point y (h s y)) / ENNReal.ofReal (verticalDerivative v (point y (h s y))) := by
  have hGm := measurableSet_levelRegion hG.continuous hD τ s₁ s₂
  have hind : Measurable ((levelRegion v D τ s₁ s₂).indicator Φ) := hΦ.indicator hGm
  rw [← lintegral_indicator hGm, ← (measurePreserving_point m).lintegral_comp hind,
    lintegral_prod (fun p : Space m × ℝ ↦ (levelRegion v D τ s₁ s₂).indicator Φ (point p.1 p.2))
      (hind.comp (measurePreserving_point m).measurable).aemeasurable,
    ← lintegral_indicator hD]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ D
  · rw [indicator_of_mem hy, ← hG.setLIntegral_section_eq hT hc hs hy,
      ← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    simp only
    by_cases ht : t ∈ Icc (h s₁ y) (h s₂ y)
    · rw [indicator_of_mem ht, indicator_of_mem
        ((hG.point_mem_levelRegion_iff_mem_heights hT hc hs).mpr ⟨hy, ht⟩)]
    · rw [indicator_of_notMem ht, indicator_of_notMem
        (fun hm ↦ ht ((hG.point_mem_levelRegion_iff_mem_heights hT hc hs).mp hm).2)]
  · rw [indicator_of_notMem hy]
    apply lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun t ↦ ?_)
    simp only [Pi.zero_apply]
    exact indicator_of_notMem (fun hm ↦ hy (point_mem_levelRegion_iff.mp hm).1) _

end LevelGraphFamily

/-! ### The common extension of all level heights -/

/-- The level value truncated to `[s₁, s₂]`. -/
def clampLevel (s₁ s₂ s : ℝ) : ℝ := max s₁ (min s₂ s)

theorem clampLevel_mem {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) (s : ℝ) : clampLevel s₁ s₂ s ∈ Icc s₁ s₂ :=
  ⟨le_max_left _ _, max_le hs (min_le_left _ _)⟩

theorem clampLevel_eq {s₁ s₂ s : ℝ} (hs : s ∈ Icc s₁ s₂) : clampLevel s₁ s₂ s = s := by
  unfold clampLevel
  rw [min_eq_right hs.2, max_eq_right hs.1]

theorem clampLevel_mono (s₁ s₂ : ℝ) : Monotone (clampLevel s₁ s₂) :=
  fun _ _ hxy ↦ max_le_max le_rfl (min_le_min le_rfl hxy)

theorem clampLevel_sub_le (s₁ s₂ : ℝ) {s s' : ℝ} (hss' : s ≤ s') :
    clampLevel s₁ s₂ s' - clampLevel s₁ s₂ s ≤ s' - s := by
  unfold clampLevel
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- The common extension of the level heights: the level is truncated to `[s₁, s₂]`, the
height is extended from `D` by McShane's formula with constant `L`, and the result is
truncated to the slab `[-τ, τ]`. -/
def extendedHeight {m : ℕ} (D : Set (Space m)) (L : ℝ≥0) (τ s₁ s₂ : ℝ)
    (h : ℝ → Space m → ℝ) (s : ℝ) (y : Space m) : ℝ :=
  slabClamp τ (mcShaneExtension D L (h (clampLevel s₁ s₂ s)) y)

namespace LevelGraphFamily

variable {m : ℕ} {v : Space (m + 1) → ℝ} {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
  {h : ℝ → Space m → ℝ}

theorem extendedHeight_eq (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) {s : ℝ}
    (hσ : s ∈ Icc s₁ s₂) {y : Space m} (hy : y ∈ D) :
    extendedHeight D L τ s₁ s₂ h s y = h s y := by
  unfold extendedHeight
  rw [clampLevel_eq hσ, mcShaneExtension_eq_of_mem (hG.lipschitzOnWith s hσ) hy]
  exact slabClamp_eq_of_mem (Ioo_subset_Icc_self (hG.mem_slab s hσ y hy))

theorem extendedHeight_lipschitzWith (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hs : s₁ ≤ s₂) (hD : D.Nonempty) (s : ℝ) :
    LipschitzWith L (extendedHeight D L τ s₁ s₂ h s) := by
  have hh := (slabClamp_lipschitzWith τ).comp
    (mcShaneExtension_lipschitzWith hD (hG.lipschitzOnWith _ (clampLevel_mem hs s)))
  rw [one_mul] at hh
  exact hh

theorem extendedHeight_mem_Icc {τ : ℝ} (hτ : 0 ≤ τ) (D : Set (Space m)) (L : ℝ≥0)
    (s₁ s₂ : ℝ) (h : ℝ → Space m → ℝ) (s : ℝ) (y : Space m) :
    extendedHeight D L τ s₁ s₂ h s y ∈ Icc (-τ) τ :=
  slabClamp_mem_Icc hτ _

/-- The extended heights are monotone in the level. -/
theorem extendedHeight_mono (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) {s s' : ℝ} (hss' : s ≤ s') (y : Space m) :
    extendedHeight D L τ s₁ s₂ h s y ≤ extendedHeight D L τ s₁ s₂ h s' y := by
  apply slabClamp_mono
  apply mcShaneExtension_mono hD (hG.lipschitzOnWith _ (clampLevel_mem hs s))
  intro z hz
  exact hG.height_mono hT hc hz (clampLevel_mem hs s) (clampLevel_mem hs s')
    (clampLevel_mono s₁ s₂ hss')

/-- HA3 for the common extension: the thickness bound holds at every horizontal point. -/
theorem extendedHeight_le_add (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) {s s' : ℝ} (hss' : s ≤ s') (y : Space m) :
    extendedHeight D L τ s₁ s₂ h s' y ≤
      extendedHeight D L τ s₁ s₂ h s y + (s' - s) / (c * T) := by
  have hκ : 0 ≤ (s' - s) / (c * T) := div_nonneg (by linarith) (mul_pos hc hT).le
  apply slabClamp_le_add hκ
  apply mcShaneExtension_le_add_of_le_add hD (hG.lipschitzOnWith _ (clampLevel_mem hs s'))
  intro z hz
  have h1 := hG.height_sub_le hT hc hz (clampLevel_mem hs s) (clampLevel_mem hs s')
    (clampLevel_mono s₁ s₂ hss')
  have h2 : (clampLevel s₁ s₂ s' - clampLevel s₁ s₂ s) / (c * T) ≤ (s' - s) / (c * T) :=
    div_le_div_of_nonneg_right (clampLevel_sub_le s₁ s₂ hss') (mul_pos hc hT).le
  linarith

theorem abs_extendedHeight_sub_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) (s s' : ℝ) (y : Space m) :
    |extendedHeight D L τ s₁ s₂ h s y - extendedHeight D L τ s₁ s₂ h s' y| ≤
      |s - s'| / (c * T) := by
  rcases le_total s s' with hss' | hss'
  · have h1 := hG.extendedHeight_mono hT hc hs hD hss' y
    have h2 := hG.extendedHeight_le_add hT hc hs hD hss' y
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hG.extendedHeight_mono hT hc hs hD hss' y
    have h2 := hG.extendedHeight_le_add hT hc hs hD hss' y
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- The extended heights are jointly Lipschitz, hence jointly continuous. -/
theorem continuous_extendedHeight (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) :
    Continuous (fun p : ℝ × Space m ↦ extendedHeight D L τ s₁ s₂ h p.1 p.2) := by
  apply LipschitzWith.continuous (K := L + Real.toNNReal (c * T)⁻¹)
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq, Prod.dist_eq]
  have h1 := (hG.extendedHeight_lipschitzWith hs hD p.1).dist_le_mul p.2 q.2
  rw [Real.dist_eq] at h1
  have h2 := hG.abs_extendedHeight_sub_le hT hc hs hD p.1 q.1 q.2
  have h3 : |p.1 - q.1| / (c * T) = (c * T)⁻¹ * dist p.1 q.1 := by
    rw [Real.dist_eq, div_eq_inv_mul]
  have hinv : 0 ≤ (c * T)⁻¹ := inv_nonneg.mpr (mul_pos hc hT).le
  have hmax1 : dist p.1 q.1 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_left _ _
  have hmax2 : dist p.2 q.2 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_right _ _
  have htri := abs_sub_le (extendedHeight D L τ s₁ s₂ h p.1 p.2)
    (extendedHeight D L τ s₁ s₂ h p.1 q.2) (extendedHeight D L τ s₁ s₂ h q.1 q.2)
  push_cast
  rw [Real.coe_toNNReal _ hinv]
  have h4 := mul_le_mul_of_nonneg_left hmax1 hinv
  have h5 := mul_le_mul_of_nonneg_left hmax2 L.coe_nonneg
  nlinarith

/-- Implicit differentiation of the level identity: at every point of the open set `D`
where the extended height is differentiable, `∇_y v = -∂ₜ v • ∇ h_s`. -/
theorem horizontal_gradient_eq (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hDo : IsOpen D) {s : ℝ} (hσ : s ∈ Icc s₁ s₂) {y : Space m} (hy : y ∈ D)
    (hd : DifferentiableAt ℝ (extendedHeight D L τ s₁ s₂ h s) y) :
    horizontal (gradient v (point y (h s y))) =
      -(verticalDerivative v (point y (h s y))) •
        gradient (extendedHeight D L τ s₁ s₂ h s) y := by
  set φ := extendedHeight D L τ s₁ s₂ h s with hφ
  have hφy : φ y = h s y := hG.extendedHeight_eq hσ hy
  have hpt : HasFDerivAt (fun z ↦ point z (φ z))
      (pointContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ (Space m)).prod (fderiv ℝ φ y))) y :=
    pointContinuousLinearMap.hasFDerivAt.comp y ((hasFDerivAt_id y).prodMk hd.hasFDerivAt)
  have hvx : DifferentiableAt ℝ v (point y (φ y)) := by
    rw [hφy]
    exact hG.differentiableAt s hσ y hy
  have hcomp := hvx.hasFDerivAt.comp y hpt
  have hconst : HasFDerivAt (fun z ↦ v (point z (φ z))) (0 : Space m →L[ℝ] ℝ) y := by
    apply (hasFDerivAt_const s y).congr_of_eventuallyEq
    filter_upwards [hDo.mem_nhds hy] with z hz
    simp only [hφ]
    rw [hG.extendedHeight_eq hσ hz]
    exact hG.level s hσ z hz
  have huniq := hcomp.unique hconst
  rw [hφy] at huniq
  apply ext_inner_right ℝ
  intro w
  have h1 := congrArg (fun Λ : Space m →L[ℝ] ℝ ↦ Λ w) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, pointContinuousLinearMap_apply,
    zero_apply] at h1
  rw [show point w (fderiv ℝ φ y w) = point w 0 + (fderiv ℝ φ y w) • verticalDirection m by
    rw [point_add_vertical, zero_add], map_add, map_smul, smul_eq_mul] at h1
  rw [← inner_gradient_left, inner_point_zero_right, ← inner_gradient_left] at h1
  rw [real_inner_smul_left]
  change inner ℝ (horizontal (gradient v (point y (h s y)))) w =
    -(fderiv ℝ v (point y (h s y)) (verticalDirection m)) * inner ℝ (gradient φ y) w
  linarith

theorem norm_gradient_extendedHeight_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hs : s₁ ≤ s₂) (hD : D.Nonempty) (s : ℝ) (y : Space m) :
    ‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ≤ L := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ (hG.extendedHeight_lipschitzWith hs hD s)

end LevelGraphFamily

theorem ofReal_mul_div_ofReal_cancel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ENNReal.ofReal (a * b) / ENNReal.ofReal b = ENNReal.ofReal a := by
  rw [ENNReal.ofReal_mul ha, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hb).ne'
    ENNReal.ofReal_ne_top]

theorem measurable_diffuseTiltDensity_vertical {m : ℕ} (T : ℝ) (v : Space (m + 1) → ℝ) :
    Measurable (diffuseTiltDensity T v (verticalDirection m)) := by
  have he : diffuseTiltDensity T v (verticalDirection m) =
      fun x ↦ T⁻¹ * ‖horizontal (gradient v x)‖ ^ 2 :=
    funext (diffuseTiltDensity_vertical_eq T v)
  rw [he]
  exact ((continuous_horizontal.measurable.comp (measurable_gradient v)).norm.pow_const 2).const_mul
    _

namespace LevelGraphFamily

variable {m : ℕ} {v : Space (m + 1) → ℝ} {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
  {h : ℝ → Space m → ℝ}

/-- HA2 energy identity. With `ε = T⁻¹`, the weighted Dirichlet energy of the common extended
heights over `D × [s₁, s₂]` equals the tangential diffuse energy of the level region:
`∫_I ∫_D ε ∂ₜv(y, h_s y) |∇ h_s y|² = ∫_{level region} ε |∇_y v|²`. -/
theorem lintegral_height_energy_eq (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hDo : IsOpen D) :
    ∫⁻ s in Icc s₁ s₂, ∫⁻ y in D, ENNReal.ofReal
        (T⁻¹ * verticalDerivative v (point y (h s y)) *
          ‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) =
      ∫⁻ x in levelRegion v D τ s₁ s₂,
        ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x) := by
  rcases D.eq_empty_or_nonempty with hDe | hDne
  · subst hDe
    have he : levelRegion v (∅ : Set (Space m)) τ s₁ s₂ = ∅ := by
      ext x
      simp [levelRegion]
    simp [he]
  set Φ : Space (m + 1) → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x) with hΦdef
  have hΦ : Measurable Φ :=
    ENNReal.measurable_ofReal.comp (measurable_diffuseTiltDensity_vertical T v)
  rw [hG.lintegral_levelRegion_eq hT hc hs hDo.measurableSet hΦ]
  set φ := extendedHeight D L τ s₁ s₂ h with hφ
  have hstep : ∀ s ∈ Icc s₁ s₂,
      ∫⁻ y in D, ENNReal.ofReal (T⁻¹ * verticalDerivative v (point y (h s y)) *
          ‖gradient (φ s) y‖ ^ 2) =
        ∫⁻ y in D, Φ (point y (φ s y)) /
          ENNReal.ofReal (verticalDerivative v (point y (φ s y))) := by
    intro s hσ
    apply lintegral_congr_ae
    have hdiff := (hG.extendedHeight_lipschitzWith hs hDne s).ae_differentiableAt
      (μ := (volume : Measure (Space m)))
    filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem hDo.measurableSet] with y hyd hy
    have hφy : φ s y = h s y := hG.extendedHeight_eq hσ hy
    rw [hφy]
    have hgrad := hG.horizontal_gradient_eq hDo hσ hy hyd
    have hp := hG.verticalDerivative_pos hT hc hσ hy
    simp only [hΦdef, diffuseTiltDensity_vertical_eq, hgrad, norm_smul, norm_neg,
      Real.norm_eq_abs, abs_of_pos hp, mul_pow]
    rw [show T⁻¹ * (verticalDerivative v (point y (h s y)) ^ 2 * ‖gradient (φ s) y‖ ^ 2) =
        (T⁻¹ * verticalDerivative v (point y (h s y)) * ‖gradient (φ s) y‖ ^ 2) *
          verticalDerivative v (point y (h s y)) by ring]
    exact (ofReal_mul_div_ofReal_cancel (mul_nonneg (mul_nonneg (inv_nonneg.mpr hT.le) hp.le)
      (sq_nonneg _)) hp).symm
  rw [setLIntegral_congr_fun measurableSet_Icc hstep]
  have hP : Continuous (fun p : ℝ × Space m ↦ point p.2 (φ p.1 p.2)) :=
    pointContinuousLinearMap.continuous.comp
      (continuous_snd.prodMk (hG.continuous_extendedHeight hT hc hs hDne))
  have hmeas : Measurable (Function.uncurry fun (s : ℝ) (y : Space m) ↦
      Φ (point y (φ s y)) / ENNReal.ofReal (verticalDerivative v (point y (φ s y)))) := by
    have h1 : Measurable (fun p : ℝ × Space m ↦ Φ (point p.2 (φ p.1 p.2))) :=
      hΦ.comp hP.measurable
    have h2 : Measurable (fun p : ℝ × Space m ↦
        ENNReal.ofReal (verticalDerivative v (point p.2 (φ p.1 p.2)))) :=
      ENNReal.measurable_ofReal.comp ((measurable_verticalDerivative v).comp hP.measurable)
    exact h1.div h2
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  apply setLIntegral_congr_fun hDo.measurableSet
  intro y hy
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s hσ
  have hφy : φ s y = h s y := hG.extendedHeight_eq hσ hy
  simp only
  rw [hφy]

/-- HA2.3 on the good set: the Dirichlet energy of the extended heights over `D × [s₁, s₂]` is at
most the tangential energy of the level region divided by `c`. -/
theorem lintegral_height_gradient_good_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) (hDo : IsOpen D) :
    ∫⁻ s in Icc s₁ s₂, ∫⁻ y in D,
        ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ x in levelRegion v D τ s₁ s₂,
          ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x) := by
  rw [← hG.lintegral_height_energy_eq hT hc hs hDo,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro s hσ
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hDo.measurableSet
  intro y hy
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  apply ENNReal.ofReal_le_ofReal
  have hlow := hG.vertical_lower s hσ y hy
  have hsq : 0 ≤ ‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right hlow hsq
  calc
    ‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2 =
        c⁻¹ * (c * ‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) := by
      field_simp
    _ ≤ c⁻¹ * (T⁻¹ * verticalDerivative v (point y (h s y)) *
        ‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hc.le)

/-- HA2.3. The Dirichlet energy of the common extended heights over any horizontal set `B`,
integrated over the level interval, is controlled by the tangential energy of the level region
divided by `c`, plus the Lipschitz bound times the bad volume `|B \ D|`. -/
theorem lintegral_height_gradient_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) (hDo : IsOpen D) (hDne : D.Nonempty)
    (B : Set (Space m)) :
    ∫⁻ s in Icc s₁ s₂, ∫⁻ y in B,
        ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) ≤
      ENNReal.ofReal c⁻¹ * (∫⁻ x in levelRegion v D τ s₁ s₂,
          ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x)) +
        ENNReal.ofReal ((s₂ - s₁) * (L : ℝ) ^ 2) * volume (B \ D) := by
  have hpt : ∀ s ∈ Icc s₁ s₂,
      ∫⁻ y in B, ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) ≤
        (∫⁻ y in D, ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2)) +
          ENNReal.ofReal ((L : ℝ) ^ 2) * volume (B \ D) := by
    intro s _
    rw [← lintegral_inter_add_sdiff _ B hDo.measurableSet]
    refine add_le_add (lintegral_mono_set inter_subset_right) ?_
    calc
      ∫⁻ y in B \ D, ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2) ≤
          ∫⁻ _ in B \ D, ENNReal.ofReal ((L : ℝ) ^ 2) := by
        apply lintegral_mono
        intro y
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
          (hG.norm_gradient_extendedHeight_le hs hDne s y) 2)
      _ = ENNReal.ofReal ((L : ℝ) ^ 2) * volume (B \ D) := setLIntegral_const _ _
  have hadd := lintegral_add_right (μ := volume.restrict (Icc s₁ s₂))
    (fun s ↦ ∫⁻ y in D, ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2))
    (measurable_const (a := ENNReal.ofReal ((L : ℝ) ^ 2) * volume (B \ D)))
  calc
    _ ≤ ∫⁻ s in Icc s₁ s₂,
        ((∫⁻ y in D, ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2)) +
          ENNReal.ofReal ((L : ℝ) ^ 2) * volume (B \ D)) :=
      setLIntegral_mono' measurableSet_Icc hpt
    _ = (∫⁻ s in Icc s₁ s₂, ∫⁻ y in D,
          ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2)) +
        ENNReal.ofReal ((L : ℝ) ^ 2) * volume (B \ D) * volume (Icc s₁ s₂) := by
      rw [hadd, setLIntegral_const]
    _ ≤ ENNReal.ofReal c⁻¹ * (∫⁻ x in levelRegion v D τ s₁ s₂,
          ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x)) +
        ENNReal.ofReal ((L : ℝ) ^ 2) * volume (B \ D) * volume (Icc s₁ s₂) := by
      gcongr ?_ + _
      exact hG.lintegral_height_gradient_good_le hT hc hs hDo
    _ = _ := by
      rw [Real.volume_Icc, ENNReal.ofReal_mul (sub_nonneg.mpr hs)]
      ring

/-- The level-wise Dirichlet energy of the extended heights is measurable in the level. -/
theorem measurable_lintegral_gradient (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) (hDne : D.Nonempty) (B : Set (Space m)) :
    Measurable (fun s ↦ ∫⁻ y in B,
      ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s) y‖ ^ 2)) := by
  have hcont := hG.continuous_extendedHeight hT hc hs hDne
  have hmeas : Measurable (fun p : ℝ × Space m ↦
      fderiv ℝ (extendedHeight D L τ s₁ s₂ h p.1) p.2) :=
    measurable_fderiv_with_param ℝ (f := extendedHeight D L τ s₁ s₂ h) hcont
  have hmeas' : Measurable (fun p : ℝ × Space m ↦
      ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h p.1) p.2‖ ^ 2)) := by
    simp_rw [norm_gradient_eq_norm_fderiv]
    exact ENNReal.measurable_ofReal.comp (hmeas.norm.pow_const 2)
  exact hmeas'.lintegral_prod_right'

/-- HA2 mean-value choice of the reference level: some level in `[s₁, s₂]` has extended
height energy at most the average of the HA2.3 bound. -/
theorem exists_reference_level (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ < s₂) (hDo : IsOpen D) (hDne : D.Nonempty) (B : Set (Space m)) :
    ∃ s₀ ∈ Icc s₁ s₂, ∫⁻ y in B,
        ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s₀) y‖ ^ 2) ≤
      (ENNReal.ofReal c⁻¹ * (∫⁻ x in levelRegion v D τ s₁ s₂,
          ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x)) +
        ENNReal.ofReal ((s₂ - s₁) * (L : ℝ) ^ 2) * volume (B \ D)) /
          ENNReal.ofReal (s₂ - s₁) := by
  have hμ : volume (Icc s₁ s₂) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hs)).ne'
  have hμ' : volume (Icc s₁ s₂) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨s₀, hs₀, hle⟩ := exists_le_setLAverage hμ hμ'
    (hG.measurable_lintegral_gradient hT hc hs.le hDne B).aemeasurable
  refine ⟨s₀, hs₀, hle.trans ?_⟩
  rw [setLAverage_eq, Real.volume_Icc]
  gcongr
  exact hG.lintegral_height_gradient_le hT hc hs.le hDo hDne B

end LevelGraphFamily

/-! ### Normalized heights -/

/-- The normalized height `(φ - a) / δ`. -/
def normalizedHeight {m : ℕ} (φ : Space m → ℝ) (a δ : ℝ) (y : Space m) : ℝ := (φ y - a) / δ

theorem gradient_normalizedHeight {m : ℕ} (φ : Space m → ℝ) (a δ : ℝ) (y : Space m) :
    gradient (normalizedHeight φ a δ) y = δ⁻¹ • gradient φ y := by
  have hfun : normalizedHeight φ a δ = δ⁻¹ • (fun z ↦ φ z - a) := by
    funext z
    simp [normalizedHeight, div_eq_inv_mul]
  simp only [gradient, hfun, fderiv_const_smul_field, Pi.smul_apply, fderiv_sub_const, map_smul]

theorem lintegral_gradient_normalizedHeight {m : ℕ} (φ : Space m → ℝ) (a δ : ℝ)
    (B : Set (Space m)) :
    ∫⁻ y in B, ENNReal.ofReal (‖gradient (normalizedHeight φ a δ) y‖ ^ 2) =
      ENNReal.ofReal (δ⁻¹ ^ 2) * ∫⁻ y in B, ENNReal.ofReal (‖gradient φ y‖ ^ 2) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  rw [gradient_normalizedHeight, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ENNReal.ofReal_mul (sq_nonneg _)]

theorem lintegral_sq_normalizedHeight {m : ℕ} (φ : Space m → ℝ) (a δ : ℝ)
    (B : Set (Space m)) :
    ∫⁻ y in B, ENNReal.ofReal (normalizedHeight φ a δ y ^ 2) =
      ENNReal.ofReal (δ⁻¹ ^ 2) * ∫⁻ y in B, ENNReal.ofReal ((φ y - a) ^ 2) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  rw [normalizedHeight, div_eq_inv_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]

/-- A Poincaré inequality for a height transfers verbatim to its normalization. The
Poincaré inequality itself is an explicit hypothesis here. -/
theorem lintegral_sq_normalizedHeight_le_of_poincare {m : ℕ} {φ : Space m → ℝ} {a δ CP : ℝ}
    {B : Set (Space m)}
    (hP : ∫⁻ y in B, ENNReal.ofReal ((φ y - a) ^ 2) ≤
      ENNReal.ofReal CP * ∫⁻ y in B, ENNReal.ofReal (‖gradient φ y‖ ^ 2)) :
    ∫⁻ y in B, ENNReal.ofReal (normalizedHeight φ a δ y ^ 2) ≤
      ENNReal.ofReal CP *
        ∫⁻ y in B, ENNReal.ofReal (‖gradient (normalizedHeight φ a δ) y‖ ^ 2) := by
  rw [lintegral_sq_normalizedHeight, lintegral_gradient_normalizedHeight]
  calc
    ENNReal.ofReal (δ⁻¹ ^ 2) * ∫⁻ y in B, ENNReal.ofReal ((φ y - a) ^ 2) ≤
        ENNReal.ofReal (δ⁻¹ ^ 2) * (ENNReal.ofReal CP *
          ∫⁻ y in B, ENNReal.ofReal (‖gradient φ y‖ ^ 2)) := by gcongr
    _ = _ := by ring

/-- With the set average as center, the normalized height has mean zero. -/
theorem setIntegral_normalizedHeight_average_eq_zero {m : ℕ} {φ : Space m → ℝ}
    {B : Set (Space m)} (hφ : IntegrableOn φ B) (hB : volume B ≠ ⊤) (δ : ℝ) :
    ∫ y in B, normalizedHeight φ (⨍ z in B, φ z) δ y = 0 := by
  unfold normalizedHeight
  rw [integral_div, integral_sub hφ (integrableOn_const hB), setIntegral_const, setAverage_eq,
    smul_eq_mul, smul_eq_mul]
  by_cases h0 : volume.real B = 0
  · rw [h0]
    have hnull : volume B = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h0
      exact h0.resolve_right hB
    rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure]
    simp
  · field_simp
    ring

namespace LevelGraphFamily

variable {m : ℕ} {v : Space (m + 1) → ℝ} {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
  {h : ℝ → Space m → ℝ}

/-- HA3 for normalized extended heights: changing the level moves the normalized height by at
most `|s - s'| / (c T δ)` at every point. -/
theorem abs_normalizedHeight_sub_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h) (hT : 0 < T)
    (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) {δ : ℝ} (hδ : 0 < δ) (a s s' : ℝ)
    (y : Space m) :
    |normalizedHeight (extendedHeight D L τ s₁ s₂ h s) a δ y -
        normalizedHeight (extendedHeight D L τ s₁ s₂ h s') a δ y| ≤
      |s - s'| / (c * T * δ) := by
  unfold normalizedHeight
  rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ,
    div_le_div_iff₀ hδ (mul_pos (mul_pos hc hT) hδ)]
  have hh := hG.abs_extendedHeight_sub_le hT hc hs hD s s' y
  rw [le_div_iff₀ (mul_pos hc hT)] at hh
  nlinarith

/-- HA3.1: all fixed levels share the normalized-height limit when `T⁻¹ / δ → 0`. -/
theorem lintegral_normalizedHeight_sub_sq_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (a : ℝ) {s s' : ℝ} (hσ : s ∈ Icc s₁ s₂) (hσ' : s' ∈ Icc s₁ s₂) (B : Set (Space m)) :
    ∫⁻ y in B, ENNReal.ofReal ((normalizedHeight (extendedHeight D L τ s₁ s₂ h s) a δ y -
        normalizedHeight (extendedHeight D L τ s₁ s₂ h s') a δ y) ^ 2) ≤
      ENNReal.ofReal (((s₂ - s₁) / (c * T * δ)) ^ 2) * volume B := by
  rw [← setLIntegral_const]
  apply lintegral_mono
  intro y
  apply ENNReal.ofReal_le_ofReal
  have hh := hG.abs_normalizedHeight_sub_le hT hc hs hD hδ a s s' y
  have hss : |s - s'| ≤ s₂ - s₁ := abs_sub_le_of_le_of_le hσ.1 hσ.2 hσ'.1 hσ'.2
  have hk : |s - s'| / (c * T * δ) ≤ (s₂ - s₁) / (c * T * δ) :=
    div_le_div_of_nonneg_right hss (mul_pos (mul_pos hc hT) hδ).le
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hh.trans hk) 2

/-- The bounded-slab bound for normalized heights: if the center lies in `[-τ, τ]`, then the
normalized extended heights are bounded by `2 τ / δ`. -/
theorem abs_normalizedHeight_le (hτ : 0 ≤ τ) {a δ : ℝ} (ha : |a| ≤ τ) (hδ : 0 < δ) (s : ℝ)
    (y : Space m) :
    |normalizedHeight (extendedHeight D L τ s₁ s₂ h s) a δ y| ≤ 2 * τ / δ := by
  unfold normalizedHeight
  rw [abs_div, abs_of_pos hδ]
  apply div_le_div_of_nonneg_right _ hδ.le
  have hm := extendedHeight_mem_Icc hτ D L s₁ s₂ h s y
  rw [abs_le] at ha ⊢
  constructor <;> linarith [hm.1, hm.2]

theorem lintegral_sq_normalizedHeight_le_slab (hτ : 0 ≤ τ) {a δ : ℝ} (ha : |a| ≤ τ)
    (hδ : 0 < δ) (s : ℝ) (B : Set (Space m)) :
    ∫⁻ y in B, ENNReal.ofReal (normalizedHeight (extendedHeight D L τ s₁ s₂ h s) a δ y ^ 2) ≤
      ENNReal.ofReal ((2 * τ / δ) ^ 2) * volume B := by
  rw [← setLIntegral_const]
  apply lintegral_mono
  intro y
  apply ENNReal.ofReal_le_ofReal
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_normalizedHeight_le (D := D) (L := L) (s₁ := s₁) (s₂ := s₂) (h := h) hτ ha hδ s y) 2

theorem abs_setAverage_extendedHeight_le (hτ : 0 ≤ τ) (s : ℝ) {B : Set (Space m)}
    (hB : volume B ≠ ⊤) :
    |⨍ y in B, extendedHeight D L τ s₁ s₂ h s y| ≤ τ := by
  have hbound : ∀ y, |extendedHeight D L τ s₁ s₂ h s y| ≤ τ := fun y ↦
    abs_le.mpr (extendedHeight_mem_Icc hτ D L s₁ s₂ h s y)
  rw [setAverage_eq, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
  by_cases h0 : volume.real B = 0
  · rw [h0, inv_zero, zero_mul]
    exact hτ
  · have hpos : 0 < volume.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
    rw [inv_mul_le_iff₀ hpos]
    have hfin : volume B < ⊤ := lt_top_iff_ne_top.mpr hB
    have hh := norm_setIntegral_le_of_norm_le_const hfin
      (f := extendedHeight D L τ s₁ s₂ h s) (fun y _ ↦ by
        rw [Real.norm_eq_abs]; exact hbound y)
    rw [Real.norm_eq_abs] at hh
    linarith

/-- HA2 under the quantitative HA2.1–HA2.2 smallness: with tangential level energy at most
`δ²` and bad volume at most `M δ²`, some reference level has normalized extended height with
Dirichlet energy at most `(c⁻¹ + (s₂ - s₁) L² M) / (s₂ - s₁)` on `B`, for every center `a`. -/
theorem exists_reference_level_normalized (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ < s₂) (hDo : IsOpen D) (hDne : D.Nonempty)
    (B : Set (Space m)) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (htilt : ∫⁻ x in levelRegion v D τ s₁ s₂,
      ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x) ≤ ENNReal.ofReal (δ ^ 2))
    (hbad : volume (B \ D) ≤ ENNReal.ofReal (M * δ ^ 2)) :
    ∃ s₀ ∈ Icc s₁ s₂, ∀ a : ℝ, ∫⁻ y in B, ENNReal.ofReal
        (‖gradient (normalizedHeight (extendedHeight D L τ s₁ s₂ h s₀) a δ) y‖ ^ 2) ≤
      ENNReal.ofReal ((c⁻¹ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁)) := by
  obtain ⟨s₀, hs₀, hle⟩ := hG.exists_reference_level hT hc hs hDo hDne B
  refine ⟨s₀, hs₀, fun a ↦ ?_⟩
  have hI : 0 < s₂ - s₁ := sub_pos.mpr hs
  have hnum : ENNReal.ofReal c⁻¹ * (∫⁻ x in levelRegion v D τ s₁ s₂,
        ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x)) +
      ENNReal.ofReal ((s₂ - s₁) * (L : ℝ) ^ 2) * volume (B \ D) ≤
      ENNReal.ofReal (c⁻¹ * δ ^ 2 + (s₂ - s₁) * (L : ℝ) ^ 2 * (M * δ ^ 2)) := by
    have e1 : ENNReal.ofReal (c⁻¹ * δ ^ 2 + (s₂ - s₁) * (L : ℝ) ^ 2 * (M * δ ^ 2)) =
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (δ ^ 2) +
          ENNReal.ofReal ((s₂ - s₁) * (L : ℝ) ^ 2) * ENNReal.ofReal (M * δ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
        ENNReal.ofReal_mul (show 0 ≤ (s₂ - s₁) * (L : ℝ) ^ 2 by positivity)]
    rw [e1]
    gcongr
  rw [lintegral_gradient_normalizedHeight]
  calc
    ENNReal.ofReal (δ⁻¹ ^ 2) * ∫⁻ y in B,
        ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s₀) y‖ ^ 2) ≤
        ENNReal.ofReal (δ⁻¹ ^ 2) *
          (ENNReal.ofReal (c⁻¹ * δ ^ 2 + (s₂ - s₁) * (L : ℝ) ^ 2 * (M * δ ^ 2)) /
            ENNReal.ofReal (s₂ - s₁)) := by
      gcongr
      exact hle.trans (by gcongr)
    _ = ENNReal.ofReal ((c⁻¹ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁)) := by
      rw [← ENNReal.ofReal_div_of_pos hI, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-- The Bochner form of the normalized HA2 bound. -/
theorem integral_gradient_normalizedHeight_le {φ : Space m → ℝ} {a δ C : ℝ} (hC : 0 ≤ C)
    {B : Set (Space m)}
    (hle : ∫⁻ y in B, ENNReal.ofReal (‖gradient (normalizedHeight φ a δ) y‖ ^ 2) ≤
      ENNReal.ofReal C) :
    ∫ y in B, ‖gradient (normalizedHeight φ a δ) y‖ ^ 2 ≤ C := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ sq_nonneg _)
    ((measurable_gradient _).norm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC hle

end LevelGraphFamily

/-! ### Different good sets give the same normalized limit (HA9.2) -/

/-- Two `L`-Lipschitz functions that differ by at most `κ` on `D` differ by at most
`κ + 2 L r` at every point within distance `r` of `D`. -/
theorem abs_sub_le_of_lipschitzWith_of_near {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith L g)
    {D : Set X} {κ r : ℝ} (hfg : ∀ z ∈ D, |f z - g z| ≤ κ) {y z : X} (hz : z ∈ D)
    (hyz : dist y z ≤ r) :
    |f y - g y| ≤ κ + 2 * L * r := by
  have h1 := hf.dist_le_mul y z
  have h2 := hg.dist_le_mul y z
  rw [Real.dist_eq] at h1 h2
  have h3 := hfg z hz
  have hL := mul_le_mul_of_nonneg_left hyz L.coe_nonneg
  have htri : |f y - g y| ≤ |f y - f z| + |f z - g z| + |g z - g y| := by
    have := abs_sub_le (f y) (f z) (g y)
    have := abs_sub_le (f z) (g z) (g y)
    linarith
  rw [abs_sub_comm (g z)] at htri
  linarith

/-- A set whose complement in `B` has volume smaller than a ball inside `B` meets that ball. -/
theorem exists_mem_ball_of_volume_lt {m : ℕ} {D B : Set (Space m)} {y : Space m} {r : ℝ}
    (hball : ball y r ⊆ B) (hvol : volume (B \ D) < volume (ball y r)) :
    ∃ z ∈ D, dist y z < r := by
  by_contra hn
  push Not at hn
  have hsub : ball y r ⊆ B \ D := by
    intro z hz
    refine ⟨hball hz, fun hzD ↦ ?_⟩
    have := hn z hzD
    rw [mem_ball, dist_comm] at hz
    linarith
  exact (not_lt_of_ge (measure_mono hsub)) hvol

/-- HA9.2. Two `L`-Lipschitz heights which differ by at most `κ` on a good set `D` are
`L²`-close on any set `B'` all of whose points lie within distance `r` of `D`; the error on
the bad part is weighted by its volume only. -/
theorem lintegral_sq_sub_le_of_lipschitzWith {m : ℕ} {f g : Space m → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith L g) {D B' : Set (Space m)}
    (hD : MeasurableSet D) {κ r : ℝ} (hfg : ∀ z ∈ D, |f z - g z| ≤ κ)
    (hnear : ∀ y ∈ B', ∃ z ∈ D, dist y z ≤ r) :
    ∫⁻ y in B', ENNReal.ofReal ((f y - g y) ^ 2) ≤
      ENNReal.ofReal (κ ^ 2) * volume B' +
        ENNReal.ofReal ((κ + 2 * L * r) ^ 2) * volume (B' \ D) := by
  rw [← lintegral_inter_add_sdiff _ B' hD]
  refine add_le_add ?_ ?_
  · calc
      ∫⁻ y in B' ∩ D, ENNReal.ofReal ((f y - g y) ^ 2) ≤
          ∫⁻ _ in B' ∩ D, ENNReal.ofReal (κ ^ 2) := by
        apply setLIntegral_mono measurable_const
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfg y hy.2) 2
      _ = ENNReal.ofReal (κ ^ 2) * volume (B' ∩ D) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (κ ^ 2) * volume B' := by gcongr; exact inter_subset_left
  · calc
      ∫⁻ y in B' \ D, ENNReal.ofReal ((f y - g y) ^ 2) ≤
          ∫⁻ _ in B' \ D, ENNReal.ofReal ((κ + 2 * L * r) ^ 2) := by
        apply setLIntegral_mono measurable_const
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        obtain ⟨z, hz, hyz⟩ := hnear y hy.1
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_sub_le_of_lipschitzWith_of_near hf hg hfg hz hyz) 2
      _ = ENNReal.ofReal ((κ + 2 * L * r) ^ 2) * volume (B' \ D) := setLIntegral_const _ _

end SerrinEpigraph
