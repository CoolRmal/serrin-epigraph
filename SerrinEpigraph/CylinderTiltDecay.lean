module

public import SerrinEpigraph.CoarseConeAssembly

/-!
# Cylinder tilt decay (HA0) and the bridge to ball tilt improvement (HA12)

This module states the cylinder decay interface of `docs/rigidity-proof/harmonic-approximation.md`
(section "记号、衰减接口及适用范围", HA0) for the rescaled translates of the zero extension, and
proves the bridge HA12 from cylinder decay to the backward ball tilt recursion
`HasBallTiltImprovement` consumed by the coarse-cone assembly.

* `tiltCylinder e r` is the scale-invariant open cylinder
  `Q_r^e = {y : |y - (y·e) e| < r, |y·e| < r}`, and `cylinderTilt R v r e` is the HA0 tilt
  `𝓔_ε(r, e) = r ^ (-d) ∫_{Q_r^e} ε (|∇v|² - (e·∇v)²)` with `ε = 1 / R`, written through
  `diffuseTiltDensity R v e = ε (|∇v|² - (e·∇v)²)`. For the solution,
  `rescaledCylinderTilt g u x R r e` is this tilt of `y ↦ zeroExtension g u (x + R • y)`.
* `HasCylinderTiltDecay g u` is HA0 at all free-boundary centers, with exactly the HA0
  quantifiers: there are `ε₀, δ₀, K, C > 0` and `θ ∈ (0, 1/4)` such that whenever
  `1 / R ≤ ε₀` and `K / R ≤ δ := 𝓔_{1/R}(2, e) ^ (1/2) ≤ δ₀`, some unit `e*` satisfies
  `‖e* - e‖ ≤ C δ` and `𝓔_{1/R}(θ, e*) ≤ (θ / 2) δ²`.
* **HA12** (`Hypotheses.hasBallTiltImprovement_of_cylinderTiltDecay`): cylinder decay gives the
  stopped ball tilt recursion. In physical variables the cylinder tilt at radius `t` decays by
  `λ = θ / 2` from radius `t` to `λ t`, or the stopping branch `δ < K ε` bounds it by `4 K² / t²`.
  Iterating `m + 1` cylinder steps inside one ball step and comparing
  `B_t ⊆ Q_t^e ⊆ B_{√2 t}` gives `optimalBallTilt v x (ρ R) ≤ q optimalBallTilt v x R + C / (ρ R)²`
  with `ρ = λ ^ (m + 1) / √2` and `q = λ ^ (m + 1) √2 ^ m ≤ λ < 1`. Iterating the cylinder decay
  inside one ball step absorbs the dimensional factor `√2 ^ m` of the ball–cylinder comparison,
  so no smallness of `θ` beyond `θ < 1/4` is needed (the one-step comparison of the blueprint
  would require `2 ^ (d/2 - 1) θ < 1/2`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Pointwise

namespace SerrinEpigraph

/-! ## HA0. Scale-invariant cylinders and cylinder tilt -/

/-- The scale-invariant open cylinder `Q_r^e = {y : |y - (y·e) e| < r, |y·e| < r}` of HA0 with
axis `e`, cross-sectional radius `r`, and half-height `r`. -/
def tiltCylinder {d : ℕ} (e : Space d) (r : ℝ) : Set (Space d) :=
  {y | ‖y - inner ℝ y e • e‖ < r ∧ |inner ℝ y e| < r}

/-- The HA0 cylinder tilt `𝓔_ε(r, e) = r ^ (-d) ∫_{Q_r^e} ε (|∇v|² - (e·∇v)²)` with `ε = 1 / R`;
here `diffuseTiltDensity R v e y = (|∇v y|² - (∇v y·e)²) / R`. -/
def cylinderTilt {m : ℕ} (R : ℝ) (v : Space (m + 1) → ℝ) (r : ℝ) (e : Space (m + 1)) : ℝ :=
  r ^ (-(m : ℤ)) * ∫ y in tiltCylinder e r, diffuseTiltDensity R v e y

/-- The HA0 cylinder tilt `𝓔_{1/R}(r, e)` of the rescaled translate
`v y = zeroExtension g u (x + R • y)` centered at `x`, with `ε = 1 / R`. -/
def rescaledCylinderTilt {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (x : Space (m + 1)) (R r : ℝ) (e : Space (m + 1)) : ℝ :=
  cylinderTilt R (fun y ↦ zeroExtension g u (x + R • y)) r e

/-- **HA0 cylinder tilt decay** at every free-boundary center, with exactly the quantifiers of
HA0: there are `ε₀, δ₀, K, C > 0` and `θ ∈ (0, 1/4)` such that for every free-boundary center `x`,
every scale `R` with `ε = 1 / R ≤ ε₀`, and every unit `e` with
`K ε ≤ δ := 𝓔_ε(2, e) ^ (1/2) ≤ δ₀`, there is a unit `e*` with `‖e* - e‖ ≤ C δ` and
`𝓔_ε(θ, e*) ≤ (θ / 2) δ²`, where `𝓔_ε` is the cylinder tilt of
`y ↦ zeroExtension g u (x + R • y)`. The structural hypotheses of HA0 (minimality, stationarity,
the Modica bound, and the sharp energy bound HA0.1) are hypotheses of the theorems proving this
property, not part of it. -/
def HasCylinderTiltDecay {m : ℕ} (g : Space m → ℝ) (u : Space (m + 1) → ℝ) : Prop :=
  ∃ ε₀ δ₀ K C θ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < K ∧ 0 < C ∧ 0 < θ ∧ θ < 1 / 4 ∧
    ∀ x ∈ frontier (epigraph g), ∀ R : ℝ, 0 < R → 1 / R ≤ ε₀ →
      ∀ e : Space (m + 1), ‖e‖ = 1 →
        ∀ δ : ℝ, δ = Real.sqrt (rescaledCylinderTilt g u x R 2 e) →
          K * (1 / R) ≤ δ → δ ≤ δ₀ →
            ∃ e' : Space (m + 1), ‖e'‖ = 1 ∧ ‖e' - e‖ ≤ C * δ ∧
              rescaledCylinderTilt g u x R θ e' ≤ θ / 2 * δ ^ 2

/-! ## Elementary cylinder geometry -/

/-- The component of `w` orthogonal to a unit vector `e` has squared norm `‖w‖² - (w·e)²`. -/
theorem norm_sub_inner_smul_sq {d : ℕ} {e : Space d} (he : ‖e‖ = 1) (w : Space d) :
    ‖w - inner ℝ w e • e‖ ^ 2 = ‖w‖ ^ 2 - inner ℝ w e ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- The open ball of radius `r` lies in the cylinder `Q_r^e`. -/
theorem mem_tiltCylinder_of_norm_lt {d : ℕ} {e : Space d} (he : ‖e‖ = 1) {w : Space d} {r : ℝ}
    (hw : ‖w‖ < r) : w ∈ tiltCylinder e r := by
  refine ⟨?_, ?_⟩
  · have hsq := norm_sub_inner_smul_sq he w
    have h1 : ‖w - inner ℝ w e • e‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg (inner ℝ w e)]
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1).trans_lt hw
  · have hcs := abs_real_inner_le_norm w e
    rw [he, mul_one] at hcs
    exact hcs.trans_lt hw

/-- The cylinder `Q_r^e` lies in the open ball of radius `√2 r`. -/
theorem norm_lt_of_mem_tiltCylinder {d : ℕ} {e : Space d} (he : ‖e‖ = 1) {w : Space d} {r : ℝ}
    (hw : w ∈ tiltCylinder e r) : ‖w‖ < Real.sqrt 2 * r := by
  obtain ⟨h1, h2⟩ := hw
  have hr : 0 < r := (abs_nonneg _).trans_lt h2
  have hsq := norm_sub_inner_smul_sq he w
  have ha : ‖w - inner ℝ w e • e‖ ^ 2 < r ^ 2 := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr h1
  have hb : |inner ℝ w e| ^ 2 < r ^ 2 := (sq_lt_sq₀ (abs_nonneg _) hr.le).mpr h2
  rw [sq_abs] at hb
  have hw2 : ‖w‖ ^ 2 < (Real.sqrt 2 * r) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hw2

/-- Cylinders with a common axis increase with the radius. -/
theorem tiltCylinder_mono {d : ℕ} (e : Space d) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    tiltCylinder e r₁ ⊆ tiltCylinder e r₂ :=
  fun _ hw ↦ ⟨hw.1.trans_le h, hw.2.trans_le h⟩

/-- The cylinder `Q_r^e` is open. -/
theorem isOpen_tiltCylinder {d : ℕ} (e : Space d) (r : ℝ) : IsOpen (tiltCylinder e r) := by
  have hc1 : Continuous (fun w : Space d ↦ ‖w - inner ℝ w e • e‖) := by fun_prop
  have hc2 : Continuous (fun w : Space d ↦ |inner ℝ w e|) := by fun_prop
  exact (isOpen_lt hc1 continuous_const).inter (isOpen_lt hc2 continuous_const)

/-- Dilating the cylinder `Q_r^e` by `R > 0` gives `Q_{R r}^e`. -/
theorem smul_tiltCylinder {d : ℕ} (e : Space d) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    R • tiltCylinder e r = tiltCylinder e (R * r) := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  have hin : inner ℝ (R⁻¹ • z) e = R⁻¹ * inner ℝ z e := real_inner_smul_left z e R⁻¹
  have hperp : R⁻¹ • z - inner ℝ (R⁻¹ • z) e • e = R⁻¹ • (z - inner ℝ z e • e) := by
    rw [hin, smul_sub, smul_smul]
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  change (‖R⁻¹ • z - inner ℝ (R⁻¹ • z) e • e‖ < r ∧ |inner ℝ (R⁻¹ • z) e| < r) ↔
    (‖z - inner ℝ z e • e‖ < R * r ∧ |inner ℝ z e| < R * r)
  rw [hperp, hin, norm_smul, Real.norm_of_nonneg hRi.le, abs_mul, abs_of_pos hRi,
    inv_mul_lt_iff₀ hR, inv_mul_lt_iff₀ hR]

/-- Translation of a set integral: `∫_S F (x + z) dz = ∫_{x + S} F`. -/
theorem setIntegral_comp_add_left_eq_preimage {d : ℕ} (F : Space d → ℝ) (x : Space d)
    {S : Set (Space d)} (hS : MeasurableSet S) :
    (∫ z in S, F (x + z)) = ∫ z in (fun z ↦ z - x) ⁻¹' S, F z := by
  have hS' : MeasurableSet ((fun z : Space d ↦ z - x) ⁻¹' S) := hS.preimage (measurable_sub_const x)
  have hp : (fun z : Space d ↦ x + z) ⁻¹' ((fun z ↦ z - x) ⁻¹' S) = S := by
    ext z
    simp only [mem_preimage, add_sub_cancel_left]
  have ht := ((measurePreserving_add_left volume x).restrict_preimage hS').integral_comp
    (Homeomorph.addLeft x).measurableEmbedding F
  simpa only [hp] using ht

/-! ## Physical cylinder tilt and comparison with balls -/

/-- Non-normalized physical tilt `∫_{x + Q_t^e} (|∇v|² - (e·∇v)²)` on the cylinder centered
at `x`. -/
def cylinderTiltIntegral {d : ℕ} (v : Space d → ℝ) (x e : Space d) (t : ℝ) : ℝ :=
  ∫ z in (fun z ↦ z - x) ⁻¹' tiltCylinder e t, ‖gradient v z‖ ^ 2 - inner ℝ (gradient v z) e ^ 2

/-- Scale-normalized physical cylinder tilt `t ^ (-m) ∫_{x + Q_t^e} (|∇v|² - (e·∇v)²)`. -/
def normalizedCylinderTilt {m : ℕ} (v : Space (m + 1) → ℝ) (x e : Space (m + 1)) (t : ℝ) : ℝ :=
  t ^ (-(m : ℤ)) * cylinderTiltIntegral v x e t

/-- The translated cylinder `x + Q_t^e` lies in the closed ball of radius `√2 t` around `x`. -/
theorem preimage_tiltCylinder_subset_closedBall {d : ℕ} {e : Space d} (he : ‖e‖ = 1)
    (x : Space d) (t : ℝ) :
    (fun z ↦ z - x) ⁻¹' tiltCylinder e t ⊆ closedBall x (Real.sqrt 2 * t) := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_lt_of_mem_tiltCylinder he hz).le

/-- The cylinder tilt integrand is integrable on every translated cylinder. -/
theorem integrableOn_cylinderTiltIntegrand {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {e : Space d} (he : ‖e‖ = 1) (x : Space d) (t : ℝ) :
    IntegrableOn (fun y ↦ ‖gradient v y‖ ^ 2 - inner ℝ (gradient v y) e ^ 2)
      ((fun z ↦ z - x) ⁻¹' tiltCylinder e t) :=
  (integrableOn_ballTiltIntegrand hv (isCompact_closedBall x (Real.sqrt 2 * t)) e).mono_set
    (preimage_tiltCylinder_subset_closedBall he x t)

theorem cylinderTiltIntegral_nonneg {d : ℕ} (v : Space d → ℝ) (x : Space d) {e : Space d}
    (he : ‖e‖ = 1) (t : ℝ) : 0 ≤ cylinderTiltIntegral v x e t :=
  integral_nonneg fun y ↦ sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit (gradient v y) he)

/-- The closed ball of radius `t` lies in the cylinder `x + Q_t^e` up to its null boundary sphere,
so the ball tilt is at most the cylinder tilt. -/
theorem ballTiltIntegral_le_cylinderTiltIntegral {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) {e : Space (m + 1)} (he : ‖e‖ = 1) (x : Space (m + 1)) (t : ℝ) :
    ballTiltIntegral v x e t ≤ cylinderTiltIntegral v x e t := by
  unfold ballTiltIntegral cylinderTiltIntegral
  refine setIntegral_mono_set (integrableOn_cylinderTiltIntegrand hv he x t)
    (Eventually.of_forall fun _ ↦ sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit _ he)) ?_
  rw [ae_le_set]
  refine measure_mono_null ?_ (Measure.addHaar_sphere volume x t)
  rintro y ⟨hy, hyC⟩
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [mem_sphere, dist_eq_norm]
  by_contra hne
  exact hyC (mem_tiltCylinder_of_norm_lt he (lt_of_le_of_ne hy hne))

/-- The cylinder tilt is at most the ball tilt on the ball of radius `√2 t`. -/
theorem cylinderTiltIntegral_le_ballTiltIntegral {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {e : Space d} (he : ‖e‖ = 1) (x : Space d) (t : ℝ) :
    cylinderTiltIntegral v x e t ≤ ballTiltIntegral v x e (Real.sqrt 2 * t) :=
  setIntegral_mono_set (integrableOn_ballTiltIntegrand hv (isCompact_closedBall _ _) e)
    (Eventually.of_forall fun _ ↦ sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit _ he))
    (Eventually.of_forall (preimage_tiltCylinder_subset_closedBall he x t))

/-- The cylinder tilt increases with the radius. -/
theorem cylinderTiltIntegral_mono {d : ℕ} {v : Space d → ℝ} (hv : LocallyLipschitz v)
    {e : Space d} (he : ‖e‖ = 1) (x : Space d) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    cylinderTiltIntegral v x e t₁ ≤ cylinderTiltIntegral v x e t₂ :=
  setIntegral_mono_set (integrableOn_cylinderTiltIntegrand hv he x t₂)
    (Eventually.of_forall fun _ ↦ sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit _ he))
    (Eventually.of_forall fun _ hz ↦ tiltCylinder_mono e h hz)

/-- Change of variables: the HA0 cylinder tilt of a translated dilation is the physical
normalized cylinder tilt at radius `R r`. -/
theorem cylinderTilt_translate_dilation {m : ℕ} (v : Space (m + 1) → ℝ)
    (x e : Space (m + 1)) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    cylinderTilt R (fun y ↦ v (x + R • y)) r e = normalizedCylinderTilt v x e (R * r) := by
  unfold cylinderTilt normalizedCylinderTilt cylinderTiltIntegral
  simp_rw [diffuseTiltDensity_translate_dilation v x e hR]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume
      (fun z ↦ ‖gradient v (x + z)‖ ^ 2 - inner ℝ (gradient v (x + z)) e ^ 2) _ hR,
    smul_tiltCylinder e hR r,
    setIntegral_comp_add_left_eq_preimage
      (fun z ↦ ‖gradient v z‖ ^ 2 - inner ℝ (gradient v z) e ^ 2) x
      (isOpen_tiltCylinder e (R * r)).measurableSet]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  have hRR : R * (R ^ (m + 1))⁻¹ = (R ^ m)⁻¹ := by
    rw [pow_succ]
    field_simp
  rw [mul_zpow, zpow_neg R, zpow_natCast R]
  set I := ∫ z in (fun z ↦ z - x) ⁻¹' tiltCylinder e (R * r),
    ‖gradient v z‖ ^ 2 - inner ℝ (gradient v z) e ^ 2
  calc r ^ (-(m : ℤ)) * (R * ((R ^ (m + 1))⁻¹ * I))
      = r ^ (-(m : ℤ)) * ((R * (R ^ (m + 1))⁻¹) * I) := by ring
    _ = (R ^ m)⁻¹ * r ^ (-(m : ℤ)) * I := by rw [hRR]; ring

/-- The optimal ball tilt is at most the normalized cylinder tilt in any unit direction. -/
theorem optimalBallTilt_le_normalizedCylinderTilt {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1)) {e : Space (m + 1)} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    optimalBallTilt v x t ≤ normalizedCylinderTilt v x e t :=
  (optimalBallTilt_le hv x ht he).trans
    (mul_le_mul_of_nonneg_left (ballTiltIntegral_le_cylinderTiltIntegral hv he x t)
      (zpow_nonneg ht.le _))

/-- The normalized cylinder tilt at radius `R / √2` is at most `√2 ^ m` times the normalized
ball tilt at radius `R` in the same direction. -/
theorem normalizedCylinderTilt_le_ball {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) {e : Space (m + 1)} (he : ‖e‖ = 1) (x : Space (m + 1))
    {R : ℝ} (hR : 0 < R) :
    normalizedCylinderTilt v x e (R / Real.sqrt 2) ≤
      Real.sqrt 2 ^ m * (R ^ (-(m : ℤ)) * ballTiltIntegral v x e R) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hcomp := cylinderTiltIntegral_le_ballTiltIntegral hv he x (R / Real.sqrt 2)
  rw [mul_div_cancel₀ R hs2.ne'] at hcomp
  have hz : (R / Real.sqrt 2) ^ (-(m : ℤ)) = Real.sqrt 2 ^ m * R ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, div_pow, inv_div, div_eq_mul_inv]
  unfold normalizedCylinderTilt
  rw [hz, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcomp (zpow_nonneg hR.le _))
    (pow_nonneg hs2.le m)

/-- Coarse inclusion bound: shrinking the radius by `λ ∈ (0, 1]` costs at most `λ ^ (-m)`. -/
theorem normalizedCylinderTilt_mul_le {m : ℕ} {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (x : Space (m + 1)) {lam t : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (ht : 0 < t) :
    normalizedCylinderTilt v x e (lam * t) ≤ (lam ^ m)⁻¹ * normalizedCylinderTilt v x e t := by
  unfold normalizedCylinderTilt
  have hmono := cylinderTiltIntegral_mono hv he x (mul_le_of_le_one_left ht.le hlam1)
  rw [mul_zpow, zpow_neg lam, zpow_natCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (zpow_nonneg ht.le _))
    (inv_nonneg.mpr (pow_nonneg hlam0.le m))

/-! ## HA12. Iterating cylinder decay with a stopping threshold -/

/-- Iteration of a one-step decay with a stopping threshold (HA12). Assume that for `T₀ ≤ t`,
`P t e ≤ D₀`, and `A ≤ P t e * t²`, some admissible `e'` has `P (λ t) e' ≤ λ P t e`, and that
shrinking the radius by `λ` costs at most the factor `M`. Then after `k` steps from radius `t` with
`T₀ ≤ λ ^ k t`, either all steps decayed, or the stopping error `A` has been transported:
`P (λ ^ k t) e' (λ ^ k t)² ≤ A Λ ^ k` with `Λ = max 1 (M λ²)`. -/
theorem iterate_decay_with_stopping {ι : Type*} (P : ℝ → ι → ℝ) (U : ι → Prop)
    {lam M T₀ D₀ A : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hT₀ : 0 < T₀) (hA : 0 ≤ A)
    (hnonneg : ∀ t e, U e → 0 < t → 0 ≤ P t e)
    (hcoarse : ∀ t e, U e → 0 < t → P (lam * t) e ≤ M * P t e)
    (hstep : ∀ t e, U e → T₀ ≤ t → P t e ≤ D₀ → A ≤ P t e * t ^ 2 →
      ∃ e', U e' ∧ P (lam * t) e' ≤ lam * P t e) (k : ℕ) :
    ∀ t e, U e → T₀ ≤ lam ^ k * t → P t e ≤ D₀ →
      ∃ e', U e' ∧ (P (lam ^ k * t) e' ≤ lam ^ k * P t e ∨
        P (lam ^ k * t) e' * (lam ^ k * t) ^ 2 ≤ A * max 1 (M * lam ^ 2) ^ k) := by
  induction k with
  | zero =>
    intro t e he _ _
    exact ⟨e, he, Or.inl (by simp)⟩
  | succ k ih =>
    intro t e he hT hD
    have hΛ1 : 1 ≤ max 1 (M * lam ^ 2) := le_max_left _ _
    have hMΛ : M * lam ^ 2 ≤ max 1 (M * lam ^ 2) := le_max_right _ _
    have hsucc : lam ^ (k + 1) * t = lam * (lam ^ k * t) := by rw [pow_succ]; ring
    have hpos_succ : 0 < lam ^ (k + 1) * t := hT₀.trans_le hT
    have hpos_k : 0 < lam ^ k * t := by
      rw [hsucc] at hpos_succ
      exact pos_of_mul_pos_right hpos_succ hlam0.le
    have ht : 0 < t := pos_of_mul_pos_right hpos_k (pow_nonneg hlam0.le k)
    have hT_k : T₀ ≤ lam ^ k * t := by
      rw [hsucc] at hT
      exact hT.trans (mul_le_of_le_one_left hpos_k.le hlam1.le)
    obtain ⟨e₁, he₁, halt⟩ := ih t e he hT_k hD
    rw [hsucc]
    have hP₁ : 0 ≤ P (lam ^ k * t) e₁ := hnonneg _ e₁ he₁ hpos_k
    have hcoarse₁ := hcoarse _ e₁ he₁ hpos_k
    have htransport : P (lam * (lam ^ k * t)) e₁ * (lam * (lam ^ k * t)) ^ 2 ≤
        max 1 (M * lam ^ 2) * (P (lam ^ k * t) e₁ * (lam ^ k * t) ^ 2) := by
      calc P (lam * (lam ^ k * t)) e₁ * (lam * (lam ^ k * t)) ^ 2
          ≤ (M * P (lam ^ k * t) e₁) * (lam * (lam ^ k * t)) ^ 2 :=
            mul_le_mul_of_nonneg_right hcoarse₁ (sq_nonneg _)
        _ = (M * lam ^ 2) * (P (lam ^ k * t) e₁ * (lam ^ k * t) ^ 2) := by ring
        _ ≤ max 1 (M * lam ^ 2) * (P (lam ^ k * t) e₁ * (lam ^ k * t) ^ 2) :=
            mul_le_mul_of_nonneg_right hMΛ (mul_nonneg hP₁ (sq_nonneg _))
    rcases halt with hdec | herr
    · by_cases hstop : A ≤ P (lam ^ k * t) e₁ * (lam ^ k * t) ^ 2
      · have hPt : 0 ≤ P t e := hnonneg t e he ht
        have hD₁ : P (lam ^ k * t) e₁ ≤ D₀ := by
          have hlk : lam ^ k ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
          calc P (lam ^ k * t) e₁ ≤ lam ^ k * P t e := hdec
            _ ≤ 1 * P t e := mul_le_mul_of_nonneg_right hlk hPt
            _ = P t e := one_mul _
            _ ≤ D₀ := hD
        obtain ⟨e₂, he₂, hstep₂⟩ := hstep _ e₁ he₁ hT_k hD₁ hstop
        refine ⟨e₂, he₂, Or.inl ?_⟩
        calc P (lam * (lam ^ k * t)) e₂ ≤ lam * P (lam ^ k * t) e₁ := hstep₂
          _ ≤ lam * (lam ^ k * P t e) := mul_le_mul_of_nonneg_left hdec hlam0.le
          _ = lam ^ (k + 1) * P t e := by rw [pow_succ]; ring
      · push Not at hstop
        refine ⟨e₁, he₁, Or.inr ?_⟩
        have hΛk : max 1 (M * lam ^ 2) ≤ max 1 (M * lam ^ 2) ^ (k + 1) :=
          le_self_pow₀ hΛ1 (Nat.succ_ne_zero k)
        calc P (lam * (lam ^ k * t)) e₁ * (lam * (lam ^ k * t)) ^ 2
            ≤ max 1 (M * lam ^ 2) * (P (lam ^ k * t) e₁ * (lam ^ k * t) ^ 2) := htransport
          _ ≤ max 1 (M * lam ^ 2) * A :=
              mul_le_mul_of_nonneg_left hstop.le (zero_le_one.trans hΛ1)
          _ ≤ max 1 (M * lam ^ 2) ^ (k + 1) * A := mul_le_mul_of_nonneg_right hΛk hA
          _ = A * max 1 (M * lam ^ 2) ^ (k + 1) := mul_comm _ _
    · refine ⟨e₁, he₁, Or.inr ?_⟩
      calc P (lam * (lam ^ k * t)) e₁ * (lam * (lam ^ k * t)) ^ 2
          ≤ max 1 (M * lam ^ 2) * (P (lam ^ k * t) e₁ * (lam ^ k * t) ^ 2) := htransport
        _ ≤ max 1 (M * lam ^ 2) * (A * max 1 (M * lam ^ 2) ^ k) :=
            mul_le_mul_of_nonneg_left herr (zero_le_one.trans hΛ1)
        _ = A * max 1 (M * lam ^ 2) ^ (k + 1) := by rw [pow_succ]; ring

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **HA12.** Cylinder tilt decay at free-boundary centers yields the stopped backward ball tilt
recursion `optimalBallTilt v x (ρ R) ≤ q optimalBallTilt v x R + C / (ρ R)²` for the zero
extension, with `ρ = λ ^ (m + 1) / √2`, `q = λ ^ (m + 1) √2 ^ m < 1`, `λ = θ / 2`, starting radius
`2 / ε₀`, and ball-tilt threshold `δ₀² / √2 ^ m`. -/
theorem Hypotheses.hasBallTiltImprovement_of_cylinderTiltDecay (h : Hypotheses g u f κ)
    (hdecay : HasCylinderTiltDecay g u) :
    HasBallTiltImprovement (zeroExtension g u) (frontier (epigraph g)) := by
  obtain ⟨ε₀, δ₀, K, C, θ, hε₀, hδ₀, hK, -, hθ0, hθ1, hdec⟩ := hdecay
  have hv : LocallyLipschitz (zeroExtension g u) := h.zeroExtension_locallyLipschitz
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2_1 : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hs2_2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = θ / 2 := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; exact half_pos hθ0
  have hlam1 : lam < 1 := by rw [hlam]; linarith
  have hlam_s2 : lam * Real.sqrt 2 ≤ 1 := by
    rw [hlam]
    nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = lam ^ (m + 1) / Real.sqrt 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = lam ^ (m + 1) * Real.sqrt 2 ^ m := ⟨_, rfl⟩
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ,
      Cst = 4 * K ^ 2 * max 1 ((lam ^ m)⁻¹ * lam ^ 2) ^ (m + 1) := ⟨_, rfl⟩
  obtain ⟨δb, hδb⟩ : ∃ δb : ℝ, δb = δ₀ ^ 2 / Real.sqrt 2 ^ m := ⟨_, rfl⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, T₀ = 2 / ε₀ := ⟨_, rfl⟩
  have hlk1 : lam ^ (m + 1) < 1 := pow_lt_one₀ hlam0.le hlam1 (Nat.succ_ne_zero m)
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos (pow_pos hlam0 _) hs2
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one hs2]
    linarith
  have hq0 : 0 ≤ q := by rw [hq]; exact mul_nonneg (pow_nonneg hlam0.le _) (pow_nonneg hs2.le _)
  have hq1 : q < 1 := by
    have hpow : (lam * Real.sqrt 2) ^ m ≤ 1 :=
      pow_le_one₀ (mul_nonneg hlam0.le hs2.le) hlam_s2
    have hqe : q = lam * (lam * Real.sqrt 2) ^ m := by rw [hq, mul_pow, pow_succ]; ring
    rw [hqe]
    calc lam * (lam * Real.sqrt 2) ^ m ≤ lam * 1 := mul_le_mul_of_nonneg_left hpow hlam0.le
      _ < 1 := by linarith
  have hCst0 : 0 ≤ Cst := by
    rw [hCst]
    exact mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hδb0 : 0 < δb := by rw [hδb]; positivity
  have hT₀0 : 0 < T₀ := by rw [hT₀]; positivity
  refine ⟨ρ, q, Cst, δb, T₀, hρ0, hρ1, hq0, hq1, hCst0, hδb0, hT₀0, ?_⟩
  intro x hx R hRρ hIR
  have hRpos : 0 < R := pos_of_mul_pos_right (hT₀0.trans_le hRρ) hρ0.le
  let P : ℝ → Space (m + 1) → ℝ := fun t e ↦ normalizedCylinderTilt (zeroExtension g u) x e t
  have hnonneg : ∀ t e, ‖e‖ = 1 → 0 < t → 0 ≤ P t e := fun t e he ht ↦
    mul_nonneg (zpow_nonneg ht.le _) (cylinderTiltIntegral_nonneg _ x he t)
  have hcoarse : ∀ t e, ‖e‖ = 1 → 0 < t → P (lam * t) e ≤ (lam ^ m)⁻¹ * P t e :=
    fun t e he ht ↦ normalizedCylinderTilt_mul_le hv he x hlam0 hlam1.le ht
  have hstep : ∀ t e, ‖e‖ = 1 → T₀ ≤ t → P t e ≤ δ₀ ^ 2 → 4 * K ^ 2 ≤ P t e * t ^ 2 →
      ∃ e', ‖e'‖ = 1 ∧ P (lam * t) e' ≤ lam * P t e := by
    intro t e he hT hPδ hPK
    have ht : 0 < t := hT₀0.trans_le hT
    have hR' : 0 < t / 2 := half_pos ht
    have h1R : 1 / (t / 2) ≤ ε₀ := by
      rw [one_div_div, div_le_iff₀ ht]
      rw [hT₀, div_le_iff₀ hε₀] at hT
      linarith
    have hcyl2 : rescaledCylinderTilt g u x (t / 2) 2 e = P t e := by
      change cylinderTilt (t / 2) (fun y ↦ zeroExtension g u (x + (t / 2) • y)) 2 e = P t e
      rw [cylinderTilt_translate_dilation _ x e hR', show t / 2 * 2 = t by ring]
    have hPt := hnonneg t e he ht
    have hKδ : K * (1 / (t / 2)) ≤ Real.sqrt (rescaledCylinderTilt g u x (t / 2) 2 e) := by
      rw [hcyl2]
      have hKt : 0 ≤ K * (1 / (t / 2)) := by positivity
      rw [Real.le_sqrt hKt hPt]
      have hsq : (K * (1 / (t / 2))) ^ 2 = 4 * K ^ 2 / t ^ 2 := by
        field_simp
        ring
      rw [hsq, div_le_iff₀ (pow_pos ht 2)]
      exact hPK
    have hδδ₀ : Real.sqrt (rescaledCylinderTilt g u x (t / 2) 2 e) ≤ δ₀ := by
      rw [hcyl2, Real.sqrt_le_left hδ₀.le]
      exact hPδ
    obtain ⟨e', he', -, hdec'⟩ := hdec x hx (t / 2) hR' h1R e he _ rfl hKδ hδδ₀
    refine ⟨e', he', ?_⟩
    have hcylθ : rescaledCylinderTilt g u x (t / 2) θ e' = P (lam * t) e' := by
      change cylinderTilt (t / 2) (fun y ↦ zeroExtension g u (x + (t / 2) • y)) θ e' =
        P (lam * t) e'
      rw [cylinderTilt_translate_dilation _ x e' hR', show t / 2 * θ = lam * t by rw [hlam]; ring]
    rw [hcylθ, hcyl2, Real.sq_sqrt hPt, ← hlam] at hdec'
    exact hdec'
  obtain ⟨e, he, hopt, -, -⟩ := exists_optimalBallTilt_direction hv x hRpos
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = R / Real.sqrt 2 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; exact div_pos hRpos hs2
  have hPt_le : P t e ≤ Real.sqrt 2 ^ m * optimalBallTilt (zeroExtension g u) x R := by
    rw [hopt, ht_def]
    exact normalizedCylinderTilt_le_ball hv he x hRpos
  have hPδ : P t e ≤ δ₀ ^ 2 := by
    calc P t e ≤ Real.sqrt 2 ^ m * optimalBallTilt (zeroExtension g u) x R := hPt_le
      _ ≤ Real.sqrt 2 ^ m * δb := mul_le_mul_of_nonneg_left hIR (pow_nonneg hs2.le m)
      _ = δ₀ ^ 2 := by
        rw [hδb]
        field_simp
  have hρR : ρ * R = lam ^ (m + 1) * t := by
    rw [hρ, ht_def]
    ring
  have hTk : T₀ ≤ lam ^ (m + 1) * t := hρR ▸ hRρ
  obtain ⟨e', he', halt⟩ := iterate_decay_with_stopping P (fun e ↦ ‖e‖ = 1) hlam0 hlam1 hT₀0
    (by positivity : (0 : ℝ) ≤ 4 * K ^ 2) hnonneg hcoarse hstep (m + 1) t e he hTk hPδ
  have hpos : 0 < lam ^ (m + 1) * t := mul_pos (pow_pos hlam0 _) ht
  have hball : optimalBallTilt (zeroExtension g u) x (lam ^ (m + 1) * t) ≤
      P (lam ^ (m + 1) * t) e' :=
    optimalBallTilt_le_normalizedCylinderTilt hv x he' hpos
  have hI0 : 0 ≤ optimalBallTilt (zeroExtension g u) x R := optimalBallTilt_nonneg hv x hRpos
  rw [hρR]
  rcases halt with h1 | h2
  · calc optimalBallTilt (zeroExtension g u) x (lam ^ (m + 1) * t)
        ≤ P (lam ^ (m + 1) * t) e' := hball
      _ ≤ lam ^ (m + 1) * P t e := h1
      _ ≤ lam ^ (m + 1) * (Real.sqrt 2 ^ m * optimalBallTilt (zeroExtension g u) x R) :=
          mul_le_mul_of_nonneg_left hPt_le (pow_nonneg hlam0.le _)
      _ = q * optimalBallTilt (zeroExtension g u) x R := by rw [hq]; ring
      _ ≤ q * optimalBallTilt (zeroExtension g u) x R + Cst / (lam ^ (m + 1) * t) ^ 2 :=
          le_add_of_nonneg_right (div_nonneg hCst0 (sq_nonneg _))
  · have h2' : P (lam ^ (m + 1) * t) e' ≤ Cst / (lam ^ (m + 1) * t) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hpos 2), hCst]
      exact h2
    calc optimalBallTilt (zeroExtension g u) x (lam ^ (m + 1) * t)
        ≤ P (lam ^ (m + 1) * t) e' := hball
      _ ≤ Cst / (lam ^ (m + 1) * t) ^ 2 := h2'
      _ ≤ q * optimalBallTilt (zeroExtension g u) x R + Cst / (lam ^ (m + 1) * t) ^ 2 :=
          le_add_of_nonneg_left (mul_nonneg hq0 hI0)

end SerrinEpigraph
