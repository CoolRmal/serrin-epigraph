module

public import SerrinEpigraph.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Local Hölder classes `C^{k,γ}` on open subsets of `Space d`

* `LocHolderOn γ f U`: every point of `U` has a ball in `U` on which `f` is `γ`-Hölder.
* `HolderC γ U k f`: `C^{k,γ}` regularity on `U`, defined recursively: `HolderC γ U 0 f` is
  `LocHolderOn γ f U`, and `HolderC γ U (k + 1) f` means that `f` is differentiable on `U` and
  `fderiv ℝ f` is `HolderC γ U k`.
* Closure properties on open sets (for `0 < γ ≤ 1`): sums, continuous linear maps, continuous
  bilinear maps, composition with smooth maps, partial derivatives, assembly from partial
  derivatives, `HolderC (k + 1) → HolderC k`, `ContDiffOn (k + 1) → HolderC k`, and
  `HolderC k → ContDiffOn k`.
* `IsHolderC U k f`: `HolderC γ U k f` for some `0 < γ ≤ 1`.
-/

@[expose] public section

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace SerrinEpigraph

variable {d : ℕ}

/-! ### Local Hölder continuity -/

section LocHolder

variable {F G H : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]

/-- Local `γ`-Hölder continuity on `U`. -/
def LocHolderOn (γ : ℝ) (f : Space d → F) (U : Set (Space d)) : Prop :=
  ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ M, ∀ y ∈ ball x r, ∀ z ∈ ball x r,
    ‖f y - f z‖ ≤ M * dist y z ^ γ

theorem LocHolderOn.continuousOn {γ : ℝ} (hγ : 0 < γ) {f : Space d → F} {U : Set (Space d)}
    (h : LocHolderOn γ f U) : ContinuousOn f U := by
  intro x hx
  obtain ⟨r, hr, -, M, hM⟩ := h x hx
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hd0 : Tendsto (fun y ↦ dist y x) (𝓝 x) (𝓝 0) := by
    have := (continuous_id.dist (continuous_const : Continuous fun _ : Space d ↦ x)).tendsto x
    simpa using this
  have hpow : Tendsto (fun y ↦ M * dist y x ^ γ) (𝓝 x) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto).comp hd0
    simpa [Real.zero_rpow hγ.ne'] using this.const_mul M
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hpow
  filter_upwards [ball_mem_nhds x hr] with y hy
  exact hM y hy x (mem_ball_self hr)

theorem LocHolderOn.mono_exp {γ γ' : ℝ} (hγ' : 0 < γ') (hγγ' : γ' ≤ γ) {f : Space d → F}
    {U : Set (Space d)} (h : LocHolderOn γ f U) : LocHolderOn γ' f U := by
  intro x hx
  obtain ⟨r, hr, hrU, M, hM⟩ := h x hx
  refine ⟨min r (1 / 2), lt_min hr (by norm_num), (ball_subset_ball (min_le_left _ _)).trans hrU,
    max M 0, fun y hy z hz ↦ ?_⟩
  have hy' := ball_subset_ball (min_le_left _ _) hy
  have hz' := ball_subset_ball (min_le_left _ _) hz
  have hdist : dist y z ≤ 1 := by
    have h1 := mem_ball.1 hy
    have h2 := mem_ball.1 hz
    have h3 := min_le_right r (1 / 2)
    linarith [dist_triangle_right y z x]
  have h1 : dist y z ^ γ ≤ dist y z ^ γ' :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hdist hγ'.le hγγ'
  calc ‖f y - f z‖ ≤ M * dist y z ^ γ := hM y hy' z hz'
    _ ≤ max M 0 * dist y z ^ γ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    _ ≤ max M 0 * dist y z ^ γ' := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

theorem LocHolderOn.congr {γ : ℝ} {f g : Space d → F} {U : Set (Space d)}
    (h : LocHolderOn γ f U) (hfg : ∀ y ∈ U, f y = g y) : LocHolderOn γ g U := by
  intro x hx
  obtain ⟨r, hr, hrU, M, hM⟩ := h x hx
  refine ⟨r, hr, hrU, M, fun y hy z hz ↦ ?_⟩
  rw [← hfg y (hrU hy), ← hfg z (hrU hz)]
  exact hM y hy z hz

theorem locHolderOn_const {γ : ℝ} (c : F) (U : Set (Space d)) (hU : IsOpen U) :
    LocHolderOn γ (fun _ ↦ c) U := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  exact ⟨r, hr, hrU, 0, fun y _ z _ ↦ by simp⟩

theorem LocHolderOn.add {γ : ℝ} {f g : Space d → F} {U : Set (Space d)}
    (hf : LocHolderOn γ f U) (hg : LocHolderOn γ g U) : LocHolderOn γ (fun y ↦ f y + g y) U := by
  intro x hx
  obtain ⟨r₁, hr₁, hU₁, M₁, hM₁⟩ := hf x hx
  obtain ⟨r₂, hr₂, -, M₂, hM₂⟩ := hg x hx
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hU₁, M₁ + M₂,
    fun y hy z hz ↦ ?_⟩
  have hy₁ := ball_subset_ball (min_le_left _ _) hy
  have hz₁ := ball_subset_ball (min_le_left _ _) hz
  have hy₂ := ball_subset_ball (min_le_right _ _) hy
  have hz₂ := ball_subset_ball (min_le_right _ _) hz
  calc ‖f y + g y - (f z + g z)‖ = ‖(f y - f z) + (g y - g z)‖ := by congr 1; abel
    _ ≤ ‖f y - f z‖ + ‖g y - g z‖ := norm_add_le _ _
    _ ≤ M₁ * dist y z ^ γ + M₂ * dist y z ^ γ := add_le_add (hM₁ y hy₁ z hz₁) (hM₂ y hy₂ z hz₂)
    _ = (M₁ + M₂) * dist y z ^ γ := by ring

theorem LocHolderOn.neg {γ : ℝ} {f : Space d → F} {U : Set (Space d)}
    (hf : LocHolderOn γ f U) : LocHolderOn γ (fun y ↦ -f y) U := by
  intro x hx
  obtain ⟨r, hr, hrU, M, hM⟩ := hf x hx
  refine ⟨r, hr, hrU, M, fun y hy z hz ↦ ?_⟩
  rw [show -f y - -f z = -(f y - f z) by abel, norm_neg]
  exact hM y hy z hz

theorem LocHolderOn.mono_set {γ : ℝ} {f : Space d → F} {U V : Set (Space d)}
    (h : LocHolderOn γ f U) (hVU : V ⊆ U) (hV : IsOpen V) : LocHolderOn γ f V := by
  intro x hx
  obtain ⟨r, hr, -, M, hM⟩ := h x (hVU hx)
  obtain ⟨r', hr', hr'V⟩ := Metric.isOpen_iff.1 hV x hx
  refine ⟨min r r', lt_min hr hr', (ball_subset_ball (min_le_right _ _)).trans hr'V, M,
    fun y hy z hz ↦ hM y (ball_subset_ball (min_le_left _ _) hy) z
      (ball_subset_ball (min_le_left _ _) hz)⟩

variable [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]

theorem LocHolderOn.clm_comp {γ : ℝ} {f : Space d → F} {U : Set (Space d)}
    (hf : LocHolderOn γ f U) (L : F →L[ℝ] G) : LocHolderOn γ (fun y ↦ L (f y)) U := by
  intro x hx
  obtain ⟨r, hr, hrU, M, hM⟩ := hf x hx
  refine ⟨r, hr, hrU, ‖L‖ * M, fun y hy z hz ↦ ?_⟩
  calc ‖L (f y) - L (f z)‖ = ‖L (f y - f z)‖ := by rw [map_sub]
    _ ≤ ‖L‖ * ‖f y - f z‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (M * dist y z ^ γ) := mul_le_mul_of_nonneg_left (hM y hy z hz) (norm_nonneg _)
    _ = ‖L‖ * M * dist y z ^ γ := by ring

theorem LocHolderOn.bilinear {γ : ℝ} (hγ : 0 < γ) {f : Space d → F} {g : Space d → G}
    {U : Set (Space d)} (hf : LocHolderOn γ f U) (hg : LocHolderOn γ g U)
    (B : F →L[ℝ] G →L[ℝ] H) : LocHolderOn γ (fun y ↦ B (f y) (g y)) U := by
  intro x hx
  obtain ⟨r₁, hr₁, hU₁, M₁, hM₁⟩ := hf x hx
  obtain ⟨r₂, hr₂, -, M₂, hM₂⟩ := hg x hx
  set r := min r₁ r₂ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hsub₁ : closedBall x r ⊆ ball x r₁ :=
    closedBall_subset_ball (by have := min_le_left r₁ r₂; linarith)
  have hsub₂ : closedBall x r ⊆ ball x r₂ :=
    closedBall_subset_ball (by have := min_le_right r₁ r₂; linarith)
  have hfc : ContinuousOn f (closedBall x r) :=
    (hf.continuousOn hγ).mono (hsub₁.trans hU₁)
  have hgc : ContinuousOn g (closedBall x r) :=
    (hg.continuousOn hγ).mono (hsub₁.trans hU₁)
  obtain ⟨Cf, hCf⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hfc
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hgc
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf x (mem_closedBall_self hr.le))
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg x (mem_closedBall_self hr.le))
  refine ⟨r, hr, (ball_subset_closedBall.trans hsub₁).trans hU₁,
    ‖B‖ * (max M₁ 0 * Cg + Cf * max M₂ 0), fun y hy z hz ↦ ?_⟩
  have hy₁ := hsub₁ (ball_subset_closedBall hy)
  have hz₁ := hsub₁ (ball_subset_closedBall hz)
  have hy₂ := hsub₂ (ball_subset_closedBall hy)
  have hz₂ := hsub₂ (ball_subset_closedBall hz)
  have hdγ : 0 ≤ dist y z ^ γ := Real.rpow_nonneg dist_nonneg _
  have h1 : ‖f y - f z‖ ≤ max M₁ 0 * dist y z ^ γ :=
    (hM₁ y hy₁ z hz₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hdγ)
  have h2 : ‖g y - g z‖ ≤ max M₂ 0 * dist y z ^ γ :=
    (hM₂ y hy₂ z hz₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hdγ)
  have hgy := hCg y (ball_subset_closedBall hy)
  have hfz := hCf z (ball_subset_closedBall hz)
  calc ‖B (f y) (g y) - B (f z) (g z)‖ = ‖B (f y - f z) (g y) + B (f z) (g y - g z)‖ := by
        rw [map_sub, sub_apply, map_sub]
        congr 1
        abel
    _ ≤ ‖B (f y - f z) (g y)‖ + ‖B (f z) (g y - g z)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖f y - f z‖ * ‖g y‖ + ‖B‖ * ‖f z‖ * ‖g y - g z‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * (max M₁ 0 * dist y z ^ γ) * Cg + ‖B‖ * Cf * (max M₂ 0 * dist y z ^ γ) := by
        gcongr
    _ = ‖B‖ * (max M₁ 0 * Cg + Cf * max M₂ 0) * dist y z ^ γ := by ring

theorem LocHolderOn.comp_contDiff {γ : ℝ} (hγ : 0 < γ) {f : Space d → F} {U : Set (Space d)}
    (hf : LocHolderOn γ f U) {Φ : F → G} (hΦ : ContDiff ℝ 1 Φ) :
    LocHolderOn γ (fun y ↦ Φ (f y)) U := by
  intro x hx
  obtain ⟨r, hr, hrU, M, hM⟩ := hf x hx
  obtain ⟨K, t, ht, hK⟩ := (hΦ.contDiffAt (x := f x)).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.1 ht
  have hfc : ContinuousAt f x :=
    ((hf.continuousOn hγ) x hx).continuousAt (Metric.isOpen_ball.mem_nhds (mem_ball_self hr)
      |> fun h ↦ Filter.mem_of_superset h hrU)
  obtain ⟨r', hr', hr'f⟩ := Metric.continuousAt_iff.1 hfc δ hδ
  refine ⟨min r r', lt_min hr hr', (ball_subset_ball (min_le_left _ _)).trans hrU, K * max M 0,
    fun y hy z hz ↦ ?_⟩
  have hy₁ := ball_subset_ball (min_le_left _ _) hy
  have hz₁ := ball_subset_ball (min_le_left _ _) hz
  have hyt : f y ∈ t := hδt (hr'f (ball_subset_ball (min_le_right _ _) hy))
  have hzt : f z ∈ t := hδt (hr'f (ball_subset_ball (min_le_right _ _) hz))
  have h1 := hK.dist_le_mul (f y) hyt (f z) hzt
  rw [dist_eq_norm, dist_eq_norm] at h1
  have hdγ : 0 ≤ dist y z ^ γ := Real.rpow_nonneg dist_nonneg _
  calc ‖Φ (f y) - Φ (f z)‖ ≤ K * ‖f y - f z‖ := h1
    _ ≤ K * (max M 0 * dist y z ^ γ) := mul_le_mul_of_nonneg_left
        ((hM y hy₁ z hz₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hdγ)) K.2
    _ = K * max M 0 * dist y z ^ γ := by ring

theorem locHolderOn_of_contDiffOn {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {f : Space d → F}
    {U : Set (Space d)} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : LocHolderOn γ f U := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  set ρ := min (r / 2) (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by norm_num)
  have hsub : closedBall x ρ ⊆ U :=
    (closedBall_subset_ball (by have := min_le_left (r / 2) (1 / 2); linarith)).trans hrU
  obtain ⟨K, hK⟩ := (hf.mono hsub).exists_lipschitzOnWith one_ne_zero (convex_closedBall x ρ)
    (isCompact_closedBall x ρ)
  refine ⟨ρ, hρ0, ball_subset_closedBall.trans hsub, K, fun y hy z hz ↦ ?_⟩
  have h1 := hK.dist_le_mul y (ball_subset_closedBall hy) z (ball_subset_closedBall hz)
  rw [dist_eq_norm] at h1
  have hdist : dist y z ≤ 1 := by
    have h1 := mem_ball.1 hy
    have h2 := mem_ball.1 hz
    have h3 := min_le_right (r / 2) (1 / 2)
    linarith [dist_triangle_right y z x]
  have h2 : dist y z ≤ dist y z ^ γ := by
    calc dist y z = dist y z ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ dist y z ^ γ := Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hdist hγ0.le hγ1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 K.2)

end LocHolder

/-! ### The classes `C^{k,γ}` -/

/-- `C^{k,γ}` regularity on `U`: `HolderC γ U 0 f` is local `γ`-Hölder continuity, and
`HolderC γ U (k + 1) f` means that `f` is differentiable on `U` with `fderiv ℝ f` in
`HolderC γ U k`. -/
def HolderC (γ : ℝ) (U : Set (Space d)) :
    ℕ → ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F], (Space d → F) → Prop
  | 0 => fun f ↦ LocHolderOn γ f U
  | k + 1 => fun f ↦ DifferentiableOn ℝ f U ∧ HolderC γ U k (fderiv ℝ f)

section HolderC

variable {F G H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem holderC_zero_iff {γ : ℝ} {U : Set (Space d)} {f : Space d → F} :
    HolderC γ U 0 f ↔ LocHolderOn γ f U := Iff.rfl

theorem holderC_succ_iff {γ : ℝ} {U : Set (Space d)} {k : ℕ} {f : Space d → F} :
    HolderC γ U (k + 1) f ↔ DifferentiableOn ℝ f U ∧ HolderC γ U k (fderiv ℝ f) := Iff.rfl

theorem HolderC.continuousOn {γ : ℝ} (hγ : 0 < γ) {U : Set (Space d)} {k : ℕ}
    {f : Space d → F} (h : HolderC γ U k f) : ContinuousOn f U := by
  cases k with
  | zero => exact LocHolderOn.continuousOn hγ h
  | succ k => exact h.1.continuousOn

theorem HolderC.congr {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Space d → F},
      HolderC γ U k f → (∀ y ∈ U, f y = g y) → HolderC γ U k g := by
  induction k with
  | zero => intro F _ _ f g hf hfg; exact LocHolderOn.congr hf hfg
  | succ k ih =>
    intro F _ _ f g hf hfg
    refine ⟨hf.1.congr (fun y hy ↦ (hfg y hy).symm), ih hf.2 (fun y hy ↦ ?_)⟩
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg z hz
    exact hev.fderiv_eq

theorem HolderC.mono_exp {γ γ' : ℝ} (hγ' : 0 < γ') (hγγ' : γ' ≤ γ) {U : Set (Space d)} {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F},
      HolderC γ U k f → HolderC γ' U k f := by
  induction k with
  | zero => intro F _ _ f hf; exact LocHolderOn.mono_exp hγ' hγγ' hf
  | succ k ih => intro F _ _ f hf; exact ⟨hf.1, ih hf.2⟩

/-- `C^{k+1,γ} ⊆ C^{k,γ}` on open sets, for `γ ≤ 1`. -/
theorem HolderC.of_succ {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {U : Set (Space d)} (hU : IsOpen U)
    {k : ℕ} : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F},
      HolderC γ U (k + 1) f → HolderC γ U k f := by
  induction k with
  | zero =>
    intro F _ _ f hf
    obtain ⟨hdiff, hD⟩ := hf
    have hDc : ContinuousOn (fderiv ℝ f) U := LocHolderOn.continuousOn hγ0 hD
    intro x hx
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    set ρ := min (r / 2) (1 / 2) with hρ
    have hρ0 : 0 < ρ := lt_min (by linarith) (by norm_num)
    have hsub : closedBall x ρ ⊆ U :=
      (closedBall_subset_ball (by have := min_le_left (r / 2) (1 / 2); linarith)).trans hrU
    obtain ⟨C, hC⟩ := (isCompact_closedBall x ρ).exists_bound_of_continuousOn (hDc.mono hsub)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x (mem_closedBall_self hρ0.le))
    refine ⟨ρ, hρ0, ball_subset_closedBall.trans hsub, C, fun y hy z hz ↦ ?_⟩
    have h1 := (convex_ball x ρ).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw ↦ (hdiff w (hsub (ball_subset_closedBall hw))).differentiableAt
        (hU.mem_nhds (hsub (ball_subset_closedBall hw))))
      (fun w hw ↦ hC w (ball_subset_closedBall hw)) hz hy
    rw [← dist_eq_norm y z] at h1
    have hdist : dist y z ≤ 1 := by
      have h1 := mem_ball.1 hy
      have h2 := mem_ball.1 hz
      have h3 := min_le_right (r / 2) (1 / 2)
      linarith [dist_triangle_right y z x]
    have h2 : dist y z ≤ dist y z ^ γ := by
      calc dist y z = dist y z ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ dist y z ^ γ := Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hdist hγ0.le hγ1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
  | succ k ih => intro F _ _ f hf; exact ⟨hf.1, ih hf.2⟩

theorem HolderC.of_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {U : Set (Space d)} (hU : IsOpen U)
    {k l : ℕ} (hkl : k ≤ l) {f : Space d → F} (h : HolderC γ U l f) : HolderC γ U k f := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih (HolderC.of_succ hγ0 hγ1 hU ‹_›)

theorem holderC_const {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F),
      HolderC γ U k (fun _ : Space d ↦ c) := by
  induction k with
  | zero => intro F _ _ c; exact locHolderOn_const c U hU
  | succ k ih =>
    intro F _ _ c
    refine ⟨differentiableOn_const c, ?_⟩
    have h : (fderiv ℝ (fun _ : Space d ↦ c)) = fun _ ↦ 0 := by
      funext y
      exact fderiv_const_apply c
    rw [h]
    exact ih 0

theorem HolderC.add {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Space d → F},
      HolderC γ U k f → HolderC γ U k g → HolderC γ U k (fun y ↦ f y + g y) := by
  induction k with
  | zero => intro F _ _ f g hf hg; exact LocHolderOn.add hf hg
  | succ k ih =>
    intro F _ _ f g hf hg
    refine ⟨hf.1.add hg.1, HolderC.congr hU (ih hf.2 hg.2) (fun y hy ↦ ?_)⟩
    exact (fderiv_add ((hf.1 y hy).differentiableAt (hU.mem_nhds hy))
      ((hg.1 y hy).differentiableAt (hU.mem_nhds hy))).symm

theorem HolderC.neg {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F},
      HolderC γ U k f → HolderC γ U k (fun y ↦ -f y) := by
  induction k with
  | zero => intro F _ _ f hf; exact LocHolderOn.neg hf
  | succ k ih =>
    intro F _ _ f hf
    refine ⟨hf.1.neg, HolderC.congr hU (ih hf.2) (fun y hy ↦ ?_)⟩
    exact (fderiv_neg (f := f)).symm

theorem HolderC.sub {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} {f g : Space d → F}
    (hf : HolderC γ U k f) (hg : HolderC γ U k g) : HolderC γ U k (fun y ↦ f y - g y) := by
  have h := HolderC.add hU hf (HolderC.neg hU hg)
  exact HolderC.congr hU h (fun y _ ↦ by simp [sub_eq_add_neg])

/-- Composition with a fixed continuous linear map. -/
theorem HolderC.clm_comp {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} :
    ∀ {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
      [NormedSpace ℝ G] {f : Space d → F} (L : F →L[ℝ] G),
      HolderC γ U k f → HolderC γ U k (fun y ↦ L (f y)) := by
  induction k with
  | zero => intro F G _ _ _ _ f L hf; exact LocHolderOn.clm_comp hf L
  | succ k ih =>
    intro F G _ _ _ _ f L hf
    refine ⟨L.differentiable.comp_differentiableOn hf.1, ?_⟩
    have h := ih (ContinuousLinearMap.compL ℝ (Space d) F G L) hf.2
    refine HolderC.congr hU h (fun y hy ↦ ?_)
    have hd := (hf.1 y hy).differentiableAt (hU.mem_nhds hy)
    rw [fderiv_fun_comp y L.differentiableAt hd, L.fderiv]
    rfl

/-- Composition with a continuous bilinear map. -/
theorem HolderC.bilinear {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {U : Set (Space d)} (hU : IsOpen U)
    {k : ℕ} : ∀ {F G H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
      [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] {f : Space d → F}
      {g : Space d → G} (B : F →L[ℝ] G →L[ℝ] H),
      HolderC γ U k f → HolderC γ U k g → HolderC γ U k (fun y ↦ B (f y) (g y)) := by
  induction k with
  | zero => intro F G H _ _ _ _ _ _ f g B hf hg; exact LocHolderOn.bilinear hγ0 hf hg B
  | succ k ih =>
    intro F G H _ _ _ _ _ _ f g B hf hg
    have hdf : ∀ y ∈ U, HasFDerivAt f (fderiv ℝ f y) y := fun y hy ↦
      ((hf.1 y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
    have hdg : ∀ y ∈ U, HasFDerivAt g (fderiv ℝ g y) y := fun y hy ↦
      ((hg.1 y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
    refine ⟨fun y hy ↦ (B.hasFDerivAt_of_bilinear (hdf y hy) (hdg y hy)).differentiableAt
      |>.differentiableWithinAt, ?_⟩
    have h1 := ih (B.precompR (Space d)) (HolderC.of_succ hγ0 hγ1 hU hf) hg.2
    have h2 := ih (B.precompL (Space d)) hf.2 (HolderC.of_succ hγ0 hγ1 hU hg)
    refine HolderC.congr hU (HolderC.add hU h1 h2) (fun y hy ↦ ?_)
    exact ((B.hasFDerivAt_of_bilinear (hdf y hy) (hdg y hy)).fderiv).symm

/-- Composition with a smooth map. -/
theorem HolderC.comp_contDiff {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {U : Set (Space d)}
    (hU : IsOpen U) {k : ℕ} : ∀ {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space d → F} {Φ : F → G},
      ContDiff ℝ ∞ Φ → HolderC γ U k f → HolderC γ U k (fun y ↦ Φ (f y)) := by
  induction k with
  | zero =>
    intro F G _ _ _ _ f Φ hΦ hf
    exact LocHolderOn.comp_contDiff hγ0 hf (hΦ.of_le (by simp))
  | succ k ih =>
    intro F G _ _ _ _ f Φ hΦ hf
    have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
    refine ⟨hΦd.comp_differentiableOn hf.1, ?_⟩
    have hΦ' : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
    have h1 : HolderC γ U k (fun y ↦ fderiv ℝ Φ (f y)) :=
      ih hΦ' (HolderC.of_succ hγ0 hγ1 hU hf)
    have h2 := HolderC.bilinear hγ0 hγ1 hU (ContinuousLinearMap.compL ℝ (Space d) F G) h1 hf.2
    refine HolderC.congr hU h2 (fun y hy ↦ ?_)
    have hd := (hf.1 y hy).differentiableAt (hU.mem_nhds hy)
    rw [fderiv_fun_comp y (hΦd (f y)) hd]
    rfl

/-- `ContDiffOn (k + 1)` functions are `C^{k,γ}` for `γ ≤ 1`. -/
theorem holderC_of_contDiffOn {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {U : Set (Space d)}
    (hU : IsOpen U) {k : ℕ} : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : Space d → F}, ContDiffOn ℝ (k + 1) f U → HolderC γ U k f := by
  induction k with
  | zero =>
    intro F _ _ f hf
    exact locHolderOn_of_contDiffOn hγ0 hγ1 hU (by simpa using hf)
  | succ k ih =>
    intro F _ _ f hf
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen hU (n := (k + 1 : ℕ))).1
      (by exact_mod_cast hf)
    exact ⟨h.1, ih (by exact_mod_cast h.2.2)⟩

/-- `C^{k,γ}` functions are `C^k`. -/
theorem HolderC.contDiffOn {γ : ℝ} (hγ0 : 0 < γ) {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F},
      HolderC γ U k f → ContDiffOn ℝ k f U := by
  induction k with
  | zero =>
    intro F _ _ f hf
    exact contDiffOn_zero.2 (LocHolderOn.continuousOn hγ0 hf)
  | succ k ih =>
    intro F _ _ f hf
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen hU (n := (k : ℕ))).2
      ⟨hf.1, by simp, ih hf.2⟩
    exact_mod_cast h

/-- Directional derivatives of `C^{k+1,γ}` functions are `C^{k,γ}`. -/
theorem HolderC.fderiv_apply {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ}
    {f : Space d → F} (h : HolderC γ U (k + 1) f) (v : Space d) :
    HolderC γ U k (fun y ↦ fderiv ℝ f y v) :=
  HolderC.clm_comp hU (ContinuousLinearMap.apply ℝ F v) h.2

theorem HolderC.finset_sum {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ} {ι : Type*}
    (s : Finset ι) {f : ι → Space d → F} (hf : ∀ i ∈ s, HolderC γ U k (f i)) :
    HolderC γ U k (fun y ↦ ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holderC_const hU (k := k) (0 : F)
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    refine HolderC.congr hU (HolderC.add hU h1 h2) (fun y _ ↦ ?_)
    rw [Finset.sum_insert ha]

/-- Assembly from partial derivatives: a real function differentiable on `U` whose partial
derivatives along the standard basis are `C^{k,γ}` is `C^{k+1,γ}`. -/
theorem holderC_succ_of_partials {γ : ℝ} {U : Set (Space d)} (hU : IsOpen U) {k : ℕ}
    {f : Space d → ℝ} (hdiff : DifferentiableOn ℝ f U)
    (hpart : ∀ i, HolderC γ U k (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))) :
    HolderC γ U (k + 1) f := by
  refine ⟨hdiff, ?_⟩
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), HolderC γ U k (fun y ↦
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.proj i :
        Space d →L[ℝ] ℝ)) (fderiv ℝ f y (EuclideanSpace.single i 1))) :=
    fun i _ ↦ HolderC.clm_comp hU _ (hpart i)
  refine HolderC.congr hU (HolderC.finset_sum hU Finset.univ hterm) (fun y _ ↦ ?_)
  ext v
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
    simpa using this.symm
  have lhs : fderiv ℝ f y v = ∑ i, v i * fderiv ℝ f y (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  rw [lhs, sum_apply]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  simp [mul_comm]

theorem HolderC.mono_set {γ : ℝ} {U V : Set (Space d)} (hVU : V ⊆ U) (hV : IsOpen V) {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F},
      HolderC γ U k f → HolderC γ V k f := by
  induction k with
  | zero => intro F _ _ f hf; exact LocHolderOn.mono_set hf hVU hV
  | succ k ih => intro F _ _ f hf; exact ⟨hf.1.mono hVU, ih hf.2⟩

/-- `C^{k,γ}` regularity is a local property. -/
theorem holderC_of_forall_ball {γ : ℝ} {U : Set (Space d)} {k : ℕ} :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F},
      (∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ HolderC γ (ball x r) k f) → HolderC γ U k f := by
  induction k with
  | zero =>
    intro F _ _ f h x hx
    obtain ⟨r, hr, hrU, hf⟩ := h x hx
    obtain ⟨r', hr', hr'B, M, hM⟩ := hf x (mem_ball_self hr)
    exact ⟨r', hr', hr'B.trans hrU, M, hM⟩
  | succ k ih =>
    intro F _ _ f h
    refine ⟨fun y hy ↦ ?_, ih (fun x hx ↦ ?_)⟩
    · obtain ⟨r, hr, -, hf⟩ := h y hy
      exact ((hf.1 y (mem_ball_self hr)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))).differentiableWithinAt
    · obtain ⟨r, hr, hrU, hf⟩ := h x hx
      exact ⟨r, hr, hrU, hf.2⟩

end HolderC

/-- `C^{k,γ}` for some exponent `0 < γ ≤ 1`. -/
def IsHolderC (U : Set (Space d)) (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space d → F) : Prop :=
  ∃ γ, 0 < γ ∧ γ ≤ 1 ∧ HolderC γ U k f

/-- Smoothness from all `C^{k,γ}` classes. -/
theorem contDiffOn_infty_of_isHolderC {U : Set (Space d)} (hU : IsOpen U) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space d → F} (h : ∀ k, IsHolderC U k f) :
    ContDiffOn ℝ ∞ f U := by
  rw [contDiffOn_infty]
  intro k
  obtain ⟨γ, hγ0, -, hk⟩ := h k
  exact HolderC.contDiffOn hγ0 hU hk

end SerrinEpigraph
