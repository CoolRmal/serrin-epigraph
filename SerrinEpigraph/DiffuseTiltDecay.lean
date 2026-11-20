module

public import SerrinEpigraph.CylinderTiltDecay
public import SerrinEpigraph.HarmonicWeyl
public import SerrinEpigraph.DiffuseStressEstimates

/-!
# HA7 and HA11: cylinder tilt decay from harmonic approximation

This module carries out the last two steps of `docs/rigidity-proof/harmonic-approximation.md`:

* **HA7** (`eventually_cylinderTilt_tiltedNormal_le`, `cylinderTilt_tiltedNormal_le_of_approx`):
  in a frame where the tilt direction is vertical, if the normalized horizontal gradients converge
  strongly to the harmonic tilt, `ε |∇_y v / δ + ∂ₜ v ∇H(y)|² → 0` on the cylinder `Q_{1/4}`, and
  the normal kinetic measure `ε (∂ₜ v)² dx` has at most the planar density `σ dy` on vertical
  cylinders, then for the rotated unit normal `ẽ = (-δ ∇H(0), 1) / |(-δ ∇H(0), 1)|` (`tiltedNormal`)
  the cylinder tilt satisfies
  `𝓔(θ, ẽ) ≤ (2 σ θ^{-m} ∫_{B_{2θ}} |∇H - ∇H(0)|² + η) δ²` eventually. The interior gradient
  excess estimate for harmonic functions then gives the HA0 factor `θ / 2` for a fixed small `θ`.
* **HA11** (`Hypotheses.hasCylinderTiltDecay_of_harmonicApproximation`): the decay constants of
  HA0 exist. The proof is the contradiction argument of HA11: counterexamples with `ε, δ ≤ 1/j`
  and `K = j` form a sequence with `ε_j → 0`, `δ_j → 0` and `ε_j / δ_j → 0`; rotating each tilt
  direction to the vertical, the harmonic approximation `HasHarmonicApproximation` (the output of
  HA2–HA6 along such sequences) and HA7 contradict the choice of the counterexamples.

`HasHarmonicApproximation g u σ M` is the precise interface to HA2–HA6: for every contradiction
sequence, along a subsequence, there is a `C²` function `H`, harmonic on a neighborhood of
`closedBall 0 (1/2)`,
with `∫_{B_{1/2}} H² ≤ M` and `∫_{B_{1/2}} |∇H|² ≤ M` (a fixed bound, as provided by HA2.3), the
strong convergence of HA6 on `Q_{1/4}`, and the upper planar density bound for `ε (∂ₜ v)²`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

variable {m : ℕ}

/-! ## Point coordinates and the tilted normal -/

theorem norm_point_sq_eq (y : Space m) (t : ℝ) : ‖point y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
  ring

theorem point_sub_point_eq (y z : Space m) (s t : ℝ) :
    point y s - point z t = point (y - z) (s - t) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]

theorem point_zero_one_eq_vertical : point (0 : Space m) 1 = verticalDirection m := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point, verticalDirection]

theorem smul_point_eq (c : ℝ) (y : Space m) (t : ℝ) : c • point y t = point (c • y) (c * t) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]

/-- The unit upward normal `(-a, 1) / |(-a, 1)|` of the graph of `y ↦ ⟪a, y⟫`. -/
def tiltedNormal (a : Space m) : Space (m + 1) :=
  ‖point (-a) 1‖⁻¹ • point (-a) 1

theorem one_le_norm_point_neg_one (a : Space m) : 1 ≤ ‖point (-a) 1‖ := by
  have h := norm_point_sq_eq (-a) 1
  have h0 := norm_nonneg (point (-a) 1)
  nlinarith [sq_nonneg ‖-a‖]

theorem norm_tiltedNormal (a : Space m) : ‖tiltedNormal a‖ = 1 := by
  have hpos : 0 < ‖point (-a) 1‖ := one_pos.trans_le (one_le_norm_point_neg_one a)
  rw [tiltedNormal, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']

/-- The tilted normal is within `2 |a|` of the vertical direction. -/
theorem norm_tiltedNormal_sub_le (a : Space m) :
    ‖tiltedNormal a - verticalDirection m‖ ≤ 2 * ‖a‖ := by
  set N := ‖point (-a) 1‖ with hNdef
  have hN1 : 1 ≤ N := one_le_norm_point_neg_one a
  have hN0 : 0 < N := one_pos.trans_le hN1
  have hNa : N ≤ ‖a‖ + 1 := by
    have h := norm_point_sq_eq (-a) 1
    rw [norm_neg] at h
    have hsq : N ^ 2 ≤ (‖a‖ + 1) ^ 2 := by
      rw [← hNdef] at h
      nlinarith [norm_nonneg a]
    exact (sq_le_sq₀ hN0.le (by positivity)).mp hsq
  have hev : verticalDirection m = point (0 : Space m) 1 := by
    rw [← point_zero_one_eq_vertical]
  have hdiff : point (-a) 1 - verticalDirection m = point (-a) 0 := by
    rw [hev, point_sub_point_eq, sub_zero, sub_self]
  have hinv1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hN0.le
  have hsplit : tiltedNormal a - verticalDirection m =
      N⁻¹ • (point (-a) 1 - verticalDirection m) + (N⁻¹ - 1) • verticalDirection m := by
    rw [tiltedNormal, smul_sub, sub_smul, one_smul]
    abel
  have h1 : ‖N⁻¹ • (point (-a) 1 - verticalDirection m)‖ ≤ ‖a‖ := by
    rw [hdiff, norm_smul, norm_inv, norm_norm, norm_point_zero, norm_neg]
    calc N⁻¹ * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hinv1 (norm_nonneg _)
      _ = ‖a‖ := one_mul _
  have h2 : ‖(N⁻¹ - 1) • verticalDirection m‖ ≤ ‖a‖ := by
    rw [norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    have hNN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN0.ne'
    nlinarith [mul_le_mul_of_nonneg_left hNa hinv0]
  calc ‖tiltedNormal a - verticalDirection m‖
      ≤ ‖N⁻¹ • (point (-a) 1 - verticalDirection m)‖ + ‖(N⁻¹ - 1) • verticalDirection m‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ 2 * ‖a‖ := by linarith

/-- For a unit vector `e` and any `c`, `|q|² - (q·e)² ≤ |q - c e|²`. -/
theorem norm_sq_sub_inner_sq_le_norm_sub_smul_sq {d : ℕ} {e : Space d} (he : ‖e‖ = 1)
    (q : Space d) (c : ℝ) :
    ‖q‖ ^ 2 - inner ℝ q e ^ 2 ≤ ‖q - c • e‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (c - inner ℝ q e)]

/-- **HA7 pointwise inequality.** `|q|² - (q·ẽ)² ≤ |q_y + q_t a|²` for `ẽ = tiltedNormal a`. -/
theorem norm_sq_sub_inner_tiltedNormal_sq_le (a : Space m) (q : Space (m + 1)) :
    ‖q‖ ^ 2 - inner ℝ q (tiltedNormal a) ^ 2 ≤ ‖horizontal q + q (Fin.last m) • a‖ ^ 2 := by
  have hN : 0 < ‖point (-a) 1‖ := one_pos.trans_le (one_le_norm_point_neg_one a)
  have h := norm_sq_sub_inner_sq_le_norm_sub_smul_sq (norm_tiltedNormal a) q
    (q (Fin.last m) * ‖point (-a) 1‖)
  have hq : q - (q (Fin.last m) * ‖point (-a) 1‖) • tiltedNormal a =
      point (horizontal q + q (Fin.last m) • a) 0 := by
    rw [tiltedNormal, smul_smul, mul_assoc, mul_inv_cancel₀ hN.ne', mul_one]
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [point]
    · simp [point, horizontal]
  rw [hq, norm_point_zero] at h
  exact h

/-! ## Vertical cylinders -/

theorem sub_inner_verticalDirection_smul (z : Space (m + 1)) :
    z - inner ℝ z (verticalDirection m) • verticalDirection m = point (horizontal z) 0 := by
  rw [inner_verticalDirection_right]
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [point, verticalDirection]
  · simp [point, horizontal, verticalDirection]

theorem mem_tiltCylinder_vertical_iff {z : Space (m + 1)} {r : ℝ} :
    z ∈ tiltCylinder (verticalDirection m) r ↔ ‖horizontal z‖ < r ∧ |z (Fin.last m)| < r := by
  change (‖z - inner ℝ z (verticalDirection m) • verticalDirection m‖ < r ∧
    |inner ℝ z (verticalDirection m)| < r) ↔ _
  rw [sub_inner_verticalDirection_smul, norm_point_zero, inner_verticalDirection_right]

/-- A cylinder with axis close to the vertical lies in the vertical cylinder of twice the
radius. -/
theorem tiltCylinder_subset_vertical {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hnear : ‖e - verticalDirection m‖ ≤ 1 / 4) (θ : ℝ) :
    tiltCylinder e θ ⊆ tiltCylinder (verticalDirection m) (2 * θ) := by
  intro x hx
  have hx2 := norm_lt_of_mem_tiltCylinder he hx
  obtain ⟨h1, h2⟩ := hx
  have hθ : 0 < θ := (abs_nonneg _).trans_lt h2
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hxn : ‖x‖ < 3 / 2 * θ := hx2.trans (by nlinarith)
  set w := e - verticalDirection m with hw
  have hxw : |inner ℝ x w| ≤ 3 / 8 * θ := by
    calc |inner ℝ x w| ≤ ‖x‖ * ‖w‖ := abs_real_inner_le_norm x w
      _ ≤ 3 / 2 * θ * (1 / 4) := mul_le_mul hxn.le hnear (norm_nonneg _) (by positivity)
      _ = 3 / 8 * θ := by ring
  have hev : inner ℝ x (verticalDirection m) = inner ℝ x e - inner ℝ x w := by
    rw [hw, inner_sub_right]
    ring
  refine ⟨?_, ?_⟩
  · have hdecomp : x - inner ℝ x (verticalDirection m) • verticalDirection m =
        (x - inner ℝ x e • e) + (inner ℝ x e • w + inner ℝ x w • verticalDirection m) := by
      rw [hev, hw]
      module
    have hb : ‖inner ℝ x e • w‖ ≤ θ / 4 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |inner ℝ x e| * ‖w‖ ≤ θ * (1 / 4) :=
            mul_le_mul h2.le hnear (norm_nonneg _) hθ.le
        _ = θ / 4 := by ring
    have hc : ‖inner ℝ x w • verticalDirection m‖ ≤ 3 / 8 * θ := by
      rw [norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs]
      exact hxw
    rw [hdecomp]
    calc ‖(x - inner ℝ x e • e) + (inner ℝ x e • w + inner ℝ x w • verticalDirection m)‖
        ≤ ‖x - inner ℝ x e • e‖ + (‖inner ℝ x e • w‖ + ‖inner ℝ x w • verticalDirection m‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ < 2 * θ := by linarith
  · rw [hev]
    calc |inner ℝ x e - inner ℝ x w| ≤ |inner ℝ x e| + |inner ℝ x w| := abs_sub _ _
      _ < 2 * θ := by linarith

/-- The cylinder tilt is nonnegative for a unit direction and positive scale. -/
theorem cylinderTilt_nonneg {T : ℝ} (hT : 0 ≤ T) (v : Space (m + 1) → ℝ) {r : ℝ} (hr : 0 ≤ r)
    {e : Space (m + 1)} (he : ‖e‖ = 1) : 0 ≤ cylinderTilt T v r e :=
  mul_nonneg (zpow_nonneg hr _) (integral_nonneg fun y ↦ div_nonneg
    (sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit (gradient v y) he)) hT)

/-! ## Rotation invariance -/

/-- Rotating the function rotates the cylinder tilt direction. -/
theorem cylinderTilt_comp_linearIsometryEquiv (T : ℝ) (V : Space (m + 1) → ℝ)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (r : ℝ) (e : Space (m + 1)) :
    cylinderTilt T (fun y ↦ V (Q y)) r e = cylinderTilt T V r (Q e) := by
  have hpre : Q ⁻¹' tiltCylinder (Q e) r = tiltCylinder e r := by
    ext y
    have hin : inner ℝ (Q y) (Q e) = inner ℝ y e := LinearIsometryEquiv.inner_map_map Q y e
    have hnorm : ‖Q y - inner ℝ y e • Q e‖ = ‖y - inner ℝ y e • e‖ := by
      rw [← LinearIsometryEquiv.norm_map Q (y - inner ℝ y e • e), map_sub, map_smul]
    change (‖Q y - inner ℝ (Q y) (Q e) • Q e‖ < r ∧ |inner ℝ (Q y) (Q e)| < r) ↔
      (‖y - inner ℝ y e • e‖ < r ∧ |inner ℝ y e| < r)
    rw [hin, hnorm]
  have hpt (y : Space (m + 1)) :
      diffuseTiltDensity T (fun y ↦ V (Q y)) e y = diffuseTiltDensity T V (Q e) (Q y) := by
    unfold diffuseTiltDensity
    rw [gradient_comp_linearIsometryEquiv, LinearIsometryEquiv.norm_map]
    have hin : inner ℝ (Q.symm (gradient V (Q y))) e = inner ℝ (gradient V (Q y)) (Q e) := by
      rw [← Q.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    rw [hin]
  unfold cylinderTilt
  congr 1
  simp_rw [hpt]
  rw [← hpre]
  exact (Q.measurePreserving.restrict_preimage
    (isOpen_tiltCylinder (Q e) r).measurableSet).integral_comp
      Q.toHomeomorph.measurableEmbedding _

/-- The HA0 cylinder tilt of the solution in direction `Q e` is the cylinder tilt of the rotated
rescaling in direction `e`. -/
theorem rescaledCylinderTilt_eq_rotated {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    (x : Space (m + 1)) (R r : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (e : Space (m + 1)) :
    rescaledCylinderTilt g u x R r (Q e) =
      cylinderTilt R (fun z ↦ zeroExtension g u (x + R • Q z)) r e :=
  (cylinderTilt_comp_linearIsometryEquiv R (fun y ↦ zeroExtension g u (x + R • y)) Q r e).symm

/-! ## HA7 -/

/-- A measurable function bounded by a multiple of `|∇v|²` on a bounded measurable set is
integrable there. -/
theorem integrableOn_of_abs_le_mul_gradient_sq {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {F : Space d → ℝ} (hF : Measurable F) {S : Set (Space d)}
    (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) {C : ℝ}
    (hbound : ∀ x ∈ S, |F x| ≤ C * ‖gradient v x‖ ^ 2) : IntegrableOn F S := by
  obtain ⟨r, hr⟩ := hSb.subset_closedBall (0 : Space d)
  have hg0 : IntegrableOn (fun x ↦ C * ‖gradient v x‖ ^ 2) (closedBall 0 r) :=
    (integrableOn_gradient_sq_of_locallyLipschitz hv (isCompact_closedBall 0 r)).const_mul C
  have hg : IntegrableOn (fun x ↦ C * ‖gradient v x‖ ^ 2) S := hg0.mono_set hr
  refine hg.mono' hF.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  rw [Real.norm_eq_abs]
  exact hbound x hx

theorem horizontal_norm_sq_le_gradient (v : Space (m + 1) → ℝ) (z : Space (m + 1)) :
    ‖horizontal (gradient v z)‖ ^ 2 ≤ ‖gradient v z‖ ^ 2 := by
  rw [norm_sq_eq_horizontal_add_last_sq (gradient v z)]
  nlinarith [sq_nonneg (gradient v z (Fin.last m))]

theorem verticalDerivative_sq_le_gradient (v : Space (m + 1) → ℝ) (z : Space (m + 1)) :
    verticalDerivative v z ^ 2 ≤ ‖gradient v z‖ ^ 2 := by
  rw [norm_sq_eq_horizontal_add_last_sq (gradient v z), gradient_last_eq_verticalDerivative]
  nlinarith [sq_nonneg ‖horizontal (gradient v z)‖]

theorem isBounded_tiltCylinder {d : ℕ} {e : Space d} (he : ‖e‖ = 1) (r : ℝ) :
    Bornology.IsBounded (tiltCylinder e r) := by
  refine Metric.isBounded_closedBall (x := (0 : Space d)) (r := Real.sqrt 2 * r) |>.subset ?_
  intro y hy
  rw [mem_closedBall, dist_zero_right]
  exact (norm_lt_of_mem_tiltCylinder he hy).le

theorem norm_add_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

/-- **HA7 at one index.** In the vertical frame, the cylinder tilt along the tilted normal
`tiltedNormal (δ ∇H(0))` on `Q_θ` is bounded by the strong approximation error on `Q_{1/4}` and
the normal kinetic mass weighted by `|∇H - ∇H(0)|²` on `Q_{2θ}`. -/
theorem cylinderTilt_tiltedNormal_le_of_approx {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) {H : Space m → ℝ}
    (hHc : ContinuousOn (gradient H) (closedBall (0 : Space m) (1 / 4)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 8)
    (hnear : ‖tiltedNormal (δ • gradient H 0) - verticalDirection m‖ ≤ 1 / 4) {a b : ℝ}
    (hA : (∫ z in tiltCylinder (verticalDirection m) (1 / 4),
      ‖δ⁻¹ • horizontal (gradient v z) + verticalDerivative v z • gradient H (horizontal z)‖ ^ 2 /
        T) ≤ a)
    (hB : (∫ z in tiltCylinder (verticalDirection m) (2 * θ),
      verticalDerivative v z ^ 2 / T * ‖gradient H (horizontal z) - gradient H 0‖ ^ 2) ≤ b) :
    cylinderTilt T v θ (tiltedNormal (δ • gradient H 0)) ≤
      (θ ^ m)⁻¹ * (2 * a + 2 * b) * δ ^ 2 := by
  set p := gradient H 0 with hp
  set et := tiltedNormal (δ • p) with het
  set ev := verticalDirection m with hev
  set S := tiltCylinder ev (2 * θ) with hS
  set S' := tiltCylinder ev (1 / 4) with hS'
  have hSS' : S ⊆ S' := tiltCylinder_mono ev (by linarith)
  have hSm : MeasurableSet S := (isOpen_tiltCylinder _ _).measurableSet
  have hS'm : MeasurableSet S' := (isOpen_tiltCylinder _ _).measurableSet
  have hS'b : Bornology.IsBounded S' := isBounded_tiltCylinder (norm_verticalDirection m) _
  have hSb : Bornology.IsBounded S := isBounded_tiltCylinder (norm_verticalDirection m) _
  have hEm : MeasurableSet (tiltCylinder et θ) := (isOpen_tiltCylinder _ _).measurableSet
  have hEb : Bornology.IsBounded (tiltCylinder et θ) :=
    isBounded_tiltCylinder (norm_tiltedNormal _) _
  have hES : tiltCylinder et θ ⊆ S := tiltCylinder_subset_vertical (norm_tiltedNormal _) hnear θ
  obtain ⟨CH, hCH⟩ :=
    (isCompact_closedBall (0 : Space m) (1 / 4)).exists_bound_of_continuousOn hHc
  have hp_le : ‖p‖ ≤ CH := hCH 0 (mem_closedBall_self (by norm_num))
  have hCH0 : 0 ≤ CH := (norm_nonneg _).trans hp_le
  have hp2 : ‖p‖ ^ 2 ≤ CH ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp_le 2
  have hhor : ∀ z ∈ S', horizontal z ∈ closedBall (0 : Space m) (1 / 4) := by
    intro z hz
    rw [hS', mem_tiltCylinder_vertical_iff] at hz
    rw [mem_closedBall, dist_zero_right]
    exact hz.1.le
  set A : Space (m + 1) → Space m := fun z ↦
    δ⁻¹ • horizontal (gradient v z) + verticalDerivative v z • gradient H (horizontal z) with hAdef
  set W : Space (m + 1) → ℝ := fun z ↦
    verticalDerivative v z ^ 2 / T * ‖gradient H (horizontal z) - p‖ ^ 2 with hWdef
  set G : Space (m + 1) → ℝ := fun z ↦
    ‖horizontal (gradient v z) + verticalDerivative v z • (δ • p)‖ ^ 2 / T with hGdef
  have hmeas_hor : Measurable (fun z ↦ horizontal (gradient v z)) :=
    continuous_horizontal.measurable.comp (measurable_gradient v)
  have hmeas_vd : Measurable (verticalDerivative v) := measurable_verticalDerivative v
  have hmeas_H : Measurable (fun z : Space (m + 1) ↦ gradient H (horizontal z)) :=
    (measurable_gradient H).comp continuous_horizontal.measurable
  have hA_meas : Measurable (fun z ↦ ‖A z‖ ^ 2 / T) :=
    (((hmeas_hor.const_smul δ⁻¹).add (hmeas_vd.smul hmeas_H)).norm.pow_const 2).div_const T
  have hW_meas : Measurable W :=
    ((hmeas_vd.pow_const 2).div_const T).mul ((hmeas_H.sub_const p).norm.pow_const 2)
  have hG_meas : Measurable G :=
    ((hmeas_hor.add (hmeas_vd.smul_const (δ • p))).norm.pow_const 2).div_const T
  have hD_meas : Measurable (diffuseTiltDensity T v et) := by
    unfold diffuseTiltDensity
    exact (((measurable_gradient v).norm.pow_const 2).sub
      (((measurable_gradient v).inner measurable_const).pow_const 2)).div_const T
  have hhv (z : Space (m + 1)) := horizontal_norm_sq_le_gradient v z
  have hvd (z : Space (m + 1)) := verticalDerivative_sq_le_gradient v z
  -- integrability
  have hA_int : IntegrableOn (fun z ↦ ‖A z‖ ^ 2 / T) S' := by
    refine integrableOn_of_abs_le_mul_gradient_sq hv hA_meas hS'm hS'b
      (C := (2 * (δ⁻¹) ^ 2 + 2 * CH ^ 2) / T) fun z hz ↦ ?_
    rw [abs_of_nonneg (by positivity)]
    have hHz := hCH _ (hhor z hz)
    have h1 := norm_add_sq_le_two_mul (δ⁻¹ • horizontal (gradient v z))
      (verticalDerivative v z • gradient H (horizontal z))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      sq_abs] at h1
    have h2 : ‖gradient H (horizontal z)‖ ^ 2 ≤ CH ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hHz 2
    have h3 : verticalDerivative v z ^ 2 * ‖gradient H (horizontal z)‖ ^ 2 ≤
        ‖gradient v z‖ ^ 2 * CH ^ 2 :=
      mul_le_mul (hvd z) h2 (sq_nonneg _) (sq_nonneg _)
    have h4 : (δ⁻¹) ^ 2 * ‖horizontal (gradient v z)‖ ^ 2 ≤ (δ⁻¹) ^ 2 * ‖gradient v z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hhv z) (sq_nonneg _)
    have h5 : ‖A z‖ ^ 2 ≤ (2 * (δ⁻¹) ^ 2 + 2 * CH ^ 2) * ‖gradient v z‖ ^ 2 := by
      have h1' : ‖A z‖ ^ 2 ≤ 2 * ((δ⁻¹) ^ 2 * ‖horizontal (gradient v z)‖ ^ 2) +
          2 * (verticalDerivative v z ^ 2 * ‖gradient H (horizontal z)‖ ^ 2) := h1
      nlinarith
    calc ‖A z‖ ^ 2 / T ≤ (2 * (δ⁻¹) ^ 2 + 2 * CH ^ 2) * ‖gradient v z‖ ^ 2 / T :=
          div_le_div_of_nonneg_right h5 hT.le
      _ = (2 * (δ⁻¹) ^ 2 + 2 * CH ^ 2) / T * ‖gradient v z‖ ^ 2 := by ring
  have hW_int : IntegrableOn W S' := by
    refine integrableOn_of_abs_le_mul_gradient_sq hv hW_meas hS'm hS'b
      (C := 4 * CH ^ 2 / T) fun z hz ↦ ?_
    rw [abs_of_nonneg (by simp only [hWdef]; positivity)]
    have hHz := hCH _ (hhor z hz)
    have hdiff : ‖gradient H (horizontal z) - p‖ ≤ 2 * CH := by
      calc ‖gradient H (horizontal z) - p‖ ≤ ‖gradient H (horizontal z)‖ + ‖p‖ :=
            norm_sub_le _ _
        _ ≤ 2 * CH := by linarith
    have hdiff2 : ‖gradient H (horizontal z) - p‖ ^ 2 ≤ 4 * CH ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hdiff 2
      nlinarith
    calc W z = verticalDerivative v z ^ 2 / T * ‖gradient H (horizontal z) - p‖ ^ 2 := rfl
      _ ≤ ‖gradient v z‖ ^ 2 / T * (4 * CH ^ 2) :=
          mul_le_mul (div_le_div_of_nonneg_right (hvd z) hT.le) hdiff2 (sq_nonneg _)
            (by positivity)
      _ = 4 * CH ^ 2 / T * ‖gradient v z‖ ^ 2 := by ring
  have hG_int : IntegrableOn G S := by
    refine integrableOn_of_abs_le_mul_gradient_sq hv hG_meas hSm hSb
      (C := (2 + 2 * (δ ^ 2 * CH ^ 2)) / T) fun z _ ↦ ?_
    rw [abs_of_nonneg (by simp only [hGdef]; positivity)]
    have h1 := norm_add_sq_le_two_mul (horizontal (gradient v z))
      (verticalDerivative v z • (δ • p))
    have hn : ‖verticalDerivative v z • (δ • p)‖ ^ 2 =
        verticalDerivative v z ^ 2 * (δ ^ 2 * ‖p‖ ^ 2) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
        sq_abs]
    rw [hn] at h1
    have h3 : verticalDerivative v z ^ 2 * (δ ^ 2 * ‖p‖ ^ 2) ≤
        ‖gradient v z‖ ^ 2 * (δ ^ 2 * CH ^ 2) :=
      mul_le_mul (hvd z) (mul_le_mul_of_nonneg_left hp2 (sq_nonneg δ)) (by positivity)
        (sq_nonneg _)
    have h4 := hhv z
    calc G z ≤ (2 * ‖gradient v z‖ ^ 2 + 2 * (‖gradient v z‖ ^ 2 * (δ ^ 2 * CH ^ 2))) / T := by
          apply div_le_div_of_nonneg_right _ hT.le
          linarith
      _ = (2 + 2 * (δ ^ 2 * CH ^ 2)) / T * ‖gradient v z‖ ^ 2 := by ring
  have hD_int : IntegrableOn (diffuseTiltDensity T v et) (tiltCylinder et θ) := by
    refine integrableOn_of_abs_le_mul_gradient_sq hv hD_meas hEm hEb (C := 1 / T) fun z _ ↦ ?_
    unfold diffuseTiltDensity
    have h0 := inner_sq_le_norm_sq_of_unit (gradient v z) (norm_tiltedNormal (δ • p))
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr h0) hT.le)]
    calc (‖gradient v z‖ ^ 2 - inner ℝ (gradient v z) et ^ 2) / T ≤ ‖gradient v z‖ ^ 2 / T :=
          div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) hT.le
      _ = 1 / T * ‖gradient v z‖ ^ 2 := by ring
  -- pointwise inequalities
  have hpt1 : ∀ z, diffuseTiltDensity T v et z ≤ G z := by
    intro z
    unfold diffuseTiltDensity
    simp only [hGdef]
    apply div_le_div_of_nonneg_right _ hT.le
    have h := norm_sq_sub_inner_tiltedNormal_sq_le (δ • p) (gradient v z)
    rwa [gradient_last_eq_verticalDerivative] at h
  have hid : ∀ z, horizontal (gradient v z) + verticalDerivative v z • (δ • p) =
      δ • (A z + verticalDerivative v z • (p - gradient H (horizontal z))) := by
    intro z
    have h1 : A z + verticalDerivative v z • (p - gradient H (horizontal z)) =
        δ⁻¹ • horizontal (gradient v z) + verticalDerivative v z • p := by
      simp only [hAdef]
      module
    rw [h1, smul_add, smul_smul δ δ⁻¹, mul_inv_cancel₀ hδ.ne', one_smul,
      smul_comm δ (verticalDerivative v z) p]
  have hpt2 : ∀ z, G z ≤ δ ^ 2 * (2 * (‖A z‖ ^ 2 / T) + 2 * W z) := by
    intro z
    simp only [hGdef, hWdef]
    rw [hid z, norm_smul, Real.norm_of_nonneg hδ.le, mul_pow]
    have h1 := norm_add_sq_le_two_mul (A z)
      (verticalDerivative v z • (p - gradient H (horizontal z)))
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev] at h1
    have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    calc δ ^ 2 * ‖A z + verticalDerivative v z • (p - gradient H (horizontal z))‖ ^ 2 / T
        ≤ δ ^ 2 * (2 * ‖A z‖ ^ 2 + 2 * (verticalDerivative v z ^ 2 *
            ‖gradient H (horizontal z) - p‖ ^ 2)) / T :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hδ2) hT.le
      _ = δ ^ 2 * (2 * (‖A z‖ ^ 2 / T) + 2 * (verticalDerivative v z ^ 2 / T *
            ‖gradient H (horizontal z) - p‖ ^ 2)) := by
          field_simp
  -- the chain of integral inequalities
  have hI1 : (∫ z in tiltCylinder et θ, diffuseTiltDensity T v et z) ≤
      ∫ z in tiltCylinder et θ, G z :=
    setIntegral_mono_on hD_int (hG_int.mono_set hES) hEm (fun z _ ↦ hpt1 z)
  have hI2 : (∫ z in tiltCylinder et θ, G z) ≤ ∫ z in S, G z :=
    setIntegral_mono_set hG_int (Eventually.of_forall fun z ↦ by
      simp only [hGdef, Pi.zero_apply]; positivity) (Eventually.of_forall hES)
  have hAS : IntegrableOn (fun z ↦ ‖A z‖ ^ 2 / T) S := hA_int.mono_set hSS'
  have hWS : IntegrableOn W S := hW_int.mono_set hSS'
  have hI3 : (∫ z in S, G z) ≤ ∫ z in S, δ ^ 2 * (2 * (‖A z‖ ^ 2 / T) + 2 * W z) :=
    setIntegral_mono_on hG_int (((hAS.const_mul 2).add (hWS.const_mul 2)).const_mul (δ ^ 2)) hSm
      (fun z _ ↦ hpt2 z)
  have hI4 : (∫ z in S, δ ^ 2 * (2 * (‖A z‖ ^ 2 / T) + 2 * W z)) =
      δ ^ 2 * (2 * (∫ z in S, ‖A z‖ ^ 2 / T) + 2 * ∫ z in S, W z) := by
    rw [integral_const_mul, integral_add (hAS.const_mul 2) (hWS.const_mul 2), integral_const_mul,
      integral_const_mul]
  have hI5 : (∫ z in S, ‖A z‖ ^ 2 / T) ≤ ∫ z in S', ‖A z‖ ^ 2 / T :=
    setIntegral_mono_set hA_int (Eventually.of_forall fun z ↦ by
      simp only [Pi.zero_apply]; positivity) (Eventually.of_forall hSS')
  have hfinal : (∫ z in tiltCylinder et θ, diffuseTiltDensity T v et z) ≤
      δ ^ 2 * (2 * a + 2 * b) := by
    have hB' : (∫ z in S, W z) ≤ b := hB
    have hA' : (∫ z in S', ‖A z‖ ^ 2 / T) ≤ a := hA
    calc (∫ z in tiltCylinder et θ, diffuseTiltDensity T v et z)
        ≤ δ ^ 2 * (2 * (∫ z in S, ‖A z‖ ^ 2 / T) + 2 * ∫ z in S, W z) := by
          rw [← hI4]; exact hI1.trans (hI2.trans hI3)
      _ ≤ δ ^ 2 * (2 * a + 2 * b) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg δ)
          linarith
  unfold cylinderTilt
  rw [zpow_neg, zpow_natCast]
  calc (θ ^ m)⁻¹ * (∫ z in tiltCylinder et θ, diffuseTiltDensity T v et z)
      ≤ (θ ^ m)⁻¹ * (δ ^ 2 * (2 * a + 2 * b)) :=
        mul_le_mul_of_nonneg_left hfinal (inv_nonneg.mpr (pow_nonneg hθ0.le m))
    _ = (θ ^ m)⁻¹ * (2 * a + 2 * b) * δ ^ 2 := by ring

/-- **HA7 along a sequence.** Under the strong approximation `(S1)` on `Q_{1/4}` and the upper
planar density bound `(S2)` for `ε (∂ₜ v)²`, the cylinder tilt along the tilted normal satisfies,
for every `η > 0`, eventually
`𝓔(θ, ẽ_j) ≤ (2 σ θ^{-m} ∫_{B_{2θ}} |∇H - ∇H(0)|² + η) δ_j²`. -/
theorem eventually_cylinderTilt_tiltedNormal_le {v : ℕ → Space (m + 1) → ℝ}
    (hv : ∀ j, LocallyLipschitz (v j)) {T δ : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hδ : ∀ j, 0 < δ j)
    (hδ0 : Tendsto δ atTop (𝓝 0)) {H : Space m → ℝ}
    (hHc : Continuous (gradient H)) {σ : ℝ}
    (hS1 : Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 4),
      ‖(δ j)⁻¹ • horizontal (gradient (v j) z) +
        verticalDerivative (v j) z • gradient H (horizontal z)‖ ^ 2 / T j) atTop (𝓝 0))
    (hS2 : ∀ s ∈ Ioc (0 : ℝ) (1 / 4), ∀ w : Space m → ℝ, Continuous w →
      (∀ y, 0 ≤ w y) → ∀ η > 0, ∀ᶠ j in atTop,
        (∫ z in tiltCylinder (verticalDirection m) s,
          verticalDerivative (v j) z ^ 2 / T j * w (horizontal z)) ≤
            σ * (∫ y in ball (0 : Space m) s, w y) + η)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 8) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, cylinderTilt (T j) (v j) θ (tiltedNormal (δ j • gradient H 0)) ≤
      (2 * σ * (θ ^ m)⁻¹ * (∫ y in ball (0 : Space m) (2 * θ),
        ‖gradient H y - gradient H 0‖ ^ 2) + η) * δ j ^ 2 := by
  have hθm : 0 < θ ^ m := pow_pos hθ0 m
  set ε' : ℝ := η * θ ^ m / 4 with hε'
  have hε'0 : 0 < ε' := by positivity
  have h1 := hS1.eventually (ge_mem_nhds hε'0)
  have hw_cont : Continuous (fun y ↦ ‖gradient H y - gradient H 0‖ ^ 2) :=
    (hHc.sub continuous_const).norm.pow 2
  have h2 := hS2 (2 * θ) ⟨by positivity, by linarith⟩ _ hw_cont (fun y ↦ sq_nonneg _) ε' hε'0
  have h3 : ∀ᶠ j in atTop, ‖tiltedNormal (δ j • gradient H 0) - verticalDirection m‖ ≤ 1 / 4 := by
    have hlim : Tendsto (fun j ↦ 2 * ‖δ j • gradient H 0‖) atTop (𝓝 0) := by
      have := ((hδ0.smul_const (gradient H 0)).norm).const_mul 2
      simpa using this
    filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with j hj
    exact (norm_tiltedNormal_sub_le _).trans hj
  filter_upwards [h1, h2, h3] with j hj1 hj2 hj3
  have hmain := cylinderTilt_tiltedNormal_le_of_approx (hv j) (hT j) (hδ j) hHc.continuousOn hθ0 hθ
    hj3 hj1 hj2
  refine hmain.trans_eq ?_
  rw [hε']
  field_simp
  ring

/-- Harmonic gradient excess on `B_{2θ}` in terms of the Dirichlet energy on `B_{1/2}`. -/
theorem integral_ball_gradient_excess_le_of_harmonic {H : Space m → ℝ} {U : Set (Space m)}
    (hU : IsOpen U) (hHU : closedBall (0 : Space m) (1 / 2) ⊆ U) (hH : ContDiffOn ℝ 2 H U)
    (hΔ : ∀ y ∈ U, Δ H y = 0) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 8) :
    (∫ y in ball (0 : Space m) (2 * θ), ‖gradient H y - gradient H 0‖ ^ 2) ≤
      harmonicGradExcessConst m * (4 * θ) ^ (m + 2) *
        ∫ y in ball (0 : Space m) (1 / 2), ‖gradient H y‖ ^ 2 := by
  have h := harmonic_fderiv_excess_le hU hH hΔ hHU (by norm_num : (0 : ℝ) < 1 / 2)
    (θ := 4 * θ) (by positivity) (by linarith)
  have h2θ : 4 * θ * (1 / 2) = 2 * θ := by ring
  rw [h2θ] at h
  have hg (y : Space m) : ‖gradient H y - gradient H 0‖ = ‖fderiv ℝ H y - fderiv ℝ H 0‖ := by
    simp only [gradient, ← map_sub, LinearIsometryEquiv.norm_map]
  have hg' (y : Space m) : ‖gradient H y‖ = ‖fderiv ℝ H y‖ := by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  simp_rw [hg, hg']
  exact h

/-! ## HA11 -/

/-- **Harmonic approximation along HA11 contradiction sequences** (the output of HA2–HA6).
For free-boundary centers `x j`, scales `R j → ∞`, rotations `Q j` and `δ j → 0` with
`R j δ j → ∞`, such that the vertical cylinder tilt of `v j z = zeroExtension g u (x j + R j • Q j z)`
on `Q_2` is `δ j ²`, there are a subsequence and a `C²` function `H`, harmonic near
`closedBall 0 (1/2)`, with `∫_{B_{1/2}} H² ≤ M` and `∫_{B_{1/2}} |∇H|² ≤ M` such that
* (HA6) `∫_{Q_{1/4}} ε |∇_y v / δ + ∂ₜ v ∇H(y)|² → 0`, and
* (normal kinetic mass) `∫_{Q_s} ε (∂ₜ v)² w(y) ≤ σ ∫_{B_s} w + η` eventually, for every
  `s ∈ (0, 1/4]`, every continuous `w ≥ 0` and every `η > 0`. -/
def HasHarmonicApproximation (g : Space m → ℝ) (u : Space (m + 1) → ℝ) (σ M : ℝ) : Prop :=
  ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (δ : ℕ → ℝ),
    (∀ j, x j ∈ frontier (epigraph g)) → (∀ j, 0 < R j) → Tendsto R atTop atTop →
    (∀ j, 0 < δ j) → Tendsto δ atTop (𝓝 0) → Tendsto (fun j ↦ R j * δ j) atTop atTop →
    (∀ j, cylinderTilt (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z)) 2
      (verticalDirection m) = δ j ^ 2) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (H : Space m → ℝ) (U : Set (Space m)),
      IsOpen U ∧ closedBall (0 : Space m) (1 / 2) ⊆ U ∧ ContDiff ℝ 2 H ∧
      (∀ y ∈ U, Δ H y = 0) ∧
      (∫ y in ball (0 : Space m) (1 / 2), H y ^ 2) ≤ M ∧
      (∫ y in ball (0 : Space m) (1 / 2), ‖gradient H y‖ ^ 2) ≤ M ∧
      Tendsto (fun j ↦ ∫ z in tiltCylinder (verticalDirection m) (1 / 4),
        ‖(δ (φ j))⁻¹ • horizontal (gradient
            (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z) +
          verticalDerivative (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z •
            gradient H (horizontal z)‖ ^ 2 / R (φ j)) atTop (𝓝 0) ∧
      ∀ s ∈ Ioc (0 : ℝ) (1 / 4), ∀ w : Space m → ℝ, Continuous w →
        (∀ y, 0 ≤ w y) → ∀ η > 0, ∀ᶠ j in atTop,
          (∫ z in tiltCylinder (verticalDirection m) s,
            verticalDerivative (fun z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z)) z ^ 2 /
              R (φ j) * w (horizontal z)) ≤ σ * (∫ y in ball (0 : Space m) s, w y) + η

/-- **HA11.** Harmonic approximation along contradiction sequences gives the HA0 cylinder tilt
decay with fixed constants: `θ` is chosen from the harmonic gradient excess constant, `σ` and
`M`, and `C` from the interior gradient bound, before the contradiction argument; then the
counterexamples for `ε₀ = δ₀ = 1/(n+1)`, `K = n + 1` contradict HA7. -/
theorem Hypotheses.hasCylinderTiltDecay_of_harmonicApproximation {f : ℝ → ℝ} {κ : ℝ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} (h : Hypotheses g u f κ) {σ M : ℝ}
    (hσ : 0 ≤ σ) (hM : 0 ≤ M) (happ : HasHarmonicApproximation g u σ M) :
    HasCylinderTiltDecay g u := by
  set A : ℝ := 2 * σ * harmonicGradExcessConst m * 4 ^ (m + 2) * M with hA
  have hA0 : 0 ≤ A := by
    have := harmonicGradExcessConst_nonneg (d := m)
    positivity
  set θ : ℝ := min (1 / 8) (1 / (4 * A + 4)) with hθdef
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ8 : θ ≤ 1 / 8 := min_le_left _ _
  have hθA : A * θ ≤ 1 / 4 := by
    have h1 : θ ≤ 1 / (4 * A + 4) := min_le_right _ _
    have h2 : A * θ ≤ A * (1 / (4 * A + 4)) := mul_le_mul_of_nonneg_left h1 hA0
    have h3 : A * (1 / (4 * A + 4)) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  set G₀ : ℝ := harmonicGradConst m * (1 / 2 : ℝ) ^ (-(1 : ℝ) - m / 2) * M ^ (1 / 2 : ℝ)
    with hG₀
  have hG₀0 : 0 ≤ G₀ := by
    have := harmonicGradConst_nonneg (d := m)
    have : 0 ≤ (1 / 2 : ℝ) ^ (-(1 : ℝ) - m / 2) := Real.rpow_nonneg (by norm_num) _
    have : 0 ≤ M ^ (1 / 2 : ℝ) := Real.rpow_nonneg hM _
    positivity
  set C : ℝ := 2 * G₀ + 1 with hC
  have hC0 : 0 < C := by positivity
  by_contra hcon
  have hfail : ∀ n : ℕ, ∃ x ∈ frontier (epigraph g), ∃ R : ℝ, 0 < R ∧
      1 / R ≤ 1 / ((n : ℝ) + 1) ∧ ∃ e : Space (m + 1), ‖e‖ = 1 ∧
        ∃ δ : ℝ, δ = Real.sqrt (rescaledCylinderTilt g u x R 2 e) ∧
          ((n : ℝ) + 1) * (1 / R) ≤ δ ∧ δ ≤ 1 / ((n : ℝ) + 1) ∧
          ∀ e' : Space (m + 1), ‖e'‖ = 1 → ‖e' - e‖ ≤ C * δ →
            θ / 2 * δ ^ 2 < rescaledCylinderTilt g u x R θ e' := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨1 / ((n : ℝ) + 1), 1 / ((n : ℝ) + 1), (n : ℝ) + 1, C, θ, by positivity,
      by positivity, by positivity, hC0, hθ0, by linarith, ?_⟩
    intro x hx R hR hR1 e he δ hδ hKδ hδδ₀
    by_contra hne
    push Not at hne
    exact hn ⟨x, hx, R, hR, hR1, e, he, δ, hδ, hKδ, hδδ₀, hne⟩
  choose x hx R hR hR1 e he δ hδdef hKδ hδδ₀ hbad using hfail
  have hRn : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n := by
    intro n
    have h1 := hR1 n
    rwa [one_div_le_one_div (hR n) (by positivity)] at h1
  have hδpos : ∀ n, 0 < δ n := fun n ↦
    lt_of_lt_of_le (by have := hR n; positivity) (hKδ n)
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRn (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hδ0 : Tendsto δ atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hδpos n).le) hδδ₀ tendsto_one_div_add_atTop_nhds_zero_nat
  have hRδ : Tendsto (fun n ↦ R n * δ n) atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h1 := hKδ n
    rw [mul_one_div, div_le_iff₀ (hR n)] at h1
    linarith [mul_comm (δ n) (R n)]
  have hQex : ∀ n, ∃ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1), Q (verticalDirection m) = e n :=
    fun n ↦ exists_linearIsometryEquiv_vertical (he n)
  choose Q hQ using hQex
  have hnorm : ∀ n, cylinderTilt (R n) (fun z ↦ zeroExtension g u (x n + R n • Q n z)) 2
      (verticalDirection m) = δ n ^ 2 := by
    intro n
    rw [← rescaledCylinderTilt_eq_rotated, hQ n, hδdef n, Real.sq_sqrt]
    exact cylinderTilt_nonneg (hR n).le _ (by norm_num) (he n)
  obtain ⟨φ, hφ, H, U, hU, hHU, hH, hΔ, hH2, hgrad2, hS1, hS2⟩ :=
    happ x R Q δ hx hR hRt hδpos hδ0 hRδ hnorm
  have hHc : Continuous (gradient H) :=
    (toDual ℝ (Space m)).symm.continuous.comp (hH.continuous_fderiv (by norm_num))
  have hev := eventually_cylinderTilt_tiltedNormal_le
    (v := fun j z ↦ zeroExtension g u (x (φ j) + R (φ j) • Q (φ j) z))
    (T := fun j ↦ R (φ j)) (δ := fun j ↦ δ (φ j))
    (fun j ↦ locallyLipschitz_comp_translate_dilation_isometry h.zeroExtension_locallyLipschitz
      (x (φ j)) (R (φ j)) (Q (φ j)))
    (fun j ↦ hR (φ j)) (fun j ↦ hδpos (φ j)) (hδ0.comp hφ.tendsto_atTop) hHc hS1 hS2
    hθ0 hθ8 (η := θ / 4) (by positivity)
  obtain ⟨j, hj⟩ := hev.exists
  have hexc := integral_ball_gradient_excess_le_of_harmonic hU hHU hH.contDiffOn hΔ hθ0 hθ8
  have hθm : 0 < θ ^ m := pow_pos hθ0 m
  have hbound : 2 * σ * (θ ^ m)⁻¹ * (∫ y in ball (0 : Space m) (2 * θ),
      ‖gradient H y - gradient H 0‖ ^ 2) ≤ θ / 4 := by
    have hCE := harmonicGradExcessConst_nonneg (d := m)
    have h1 : 2 * σ * (θ ^ m)⁻¹ * (∫ y in ball (0 : Space m) (2 * θ),
        ‖gradient H y - gradient H 0‖ ^ 2) ≤
        2 * σ * (θ ^ m)⁻¹ * (harmonicGradExcessConst m * (4 * θ) ^ (m + 2) * M) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hexc.trans (mul_le_mul_of_nonneg_left hgrad2 (by positivity))
    have h2 : 2 * σ * (θ ^ m)⁻¹ * (harmonicGradExcessConst m * (4 * θ) ^ (m + 2) * M) =
        A * θ * θ := by
      rw [hA, mul_pow, pow_add, pow_add]
      field_simp
    have h3 : A * θ * θ ≤ 1 / 4 * θ := mul_le_mul_of_nonneg_right hθA hθ0.le
    linarith
  set n := φ j with hn
  set et := tiltedNormal (δ n • gradient H 0) with het
  have hdecay : cylinderTilt (R n) (fun z ↦ zeroExtension g u (x n + R n • Q n z)) θ et ≤
      θ / 2 * δ n ^ 2 := by
    have hj' : cylinderTilt (R n) (fun z ↦ zeroExtension g u (x n + R n • Q n z)) θ et ≤
        (2 * σ * (θ ^ m)⁻¹ * (∫ y in ball (0 : Space m) (2 * θ),
          ‖gradient H y - gradient H 0‖ ^ 2) + θ / 4) * δ n ^ 2 := hj
    calc _ ≤ _ := hj'
      _ ≤ (θ / 4 + θ / 4) * δ n ^ 2 := by gcongr
      _ = θ / 2 * δ n ^ 2 := by ring
  have hgrad0 : ‖gradient H 0‖ ≤ G₀ := by
    have hb := norm_fderiv_le_of_harmonic hU hH.contDiffOn hΔ hHU (by norm_num : (0 : ℝ) < 1 / 2)
    have hn0 : ‖gradient H 0‖ = ‖fderiv ℝ H 0‖ := by
      simp only [gradient, LinearIsometryEquiv.norm_map]
    rw [hn0]
    refine hb.trans ?_
    have hc : 0 ≤ harmonicGradConst m * (1 / 2 : ℝ) ^ (-(1 : ℝ) - m / 2) :=
      mul_nonneg harmonicGradConst_nonneg (Real.rpow_nonneg (by norm_num) _)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun _ ↦ sq_nonneg _) hH2 (by norm_num)) hc
  have hdir : ‖Q n et - e n‖ ≤ C * δ n := by
    rw [← hQ n, ← map_sub, LinearIsometryEquiv.norm_map]
    calc ‖et - verticalDirection m‖ ≤ 2 * ‖δ n • gradient H 0‖ := norm_tiltedNormal_sub_le _
      _ = 2 * (δ n * ‖gradient H 0‖) := by
          rw [norm_smul, Real.norm_of_nonneg (hδpos n).le]
      _ ≤ 2 * (δ n * G₀) := by
          have := (hδpos n).le
          gcongr
      _ ≤ C * δ n := by
          rw [hC]
          nlinarith [hδpos n]
  have hlt := hbad n (Q n et) (by rw [LinearIsometryEquiv.norm_map]; exact norm_tiltedNormal _)
    hdir
  rw [rescaledCylinderTilt_eq_rotated] at hlt
  linarith

end SerrinEpigraph
