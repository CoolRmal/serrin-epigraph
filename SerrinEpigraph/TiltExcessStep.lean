module

public import SerrinEpigraph.PerimeterDilation
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# One step of tilt-excess decay from a height bound (`GR12`, deterministic part)

* `tiltNormal p s = (-s p, 1)/√(1 + s²‖p‖²)`, the unit normal of the graph of `s ⟪p, ·⟫`, and the
  Householder frame `tiltFrame p s = reflection (ℝ ∙ (e_n - tiltNormal p s))ᗮ`, a linear isometry
  sending `e_n` to `tiltNormal p s`, with `‖e_n - tiltNormal p s‖ ≤ s ‖p‖`.
* `ae_comp_similarity`: a.e. statements pull back under similarities.
* `IsLocalPerimeterMinimizer.tilt_step` (**`GR12`, one step**): for a normalized configuration
  (`B_2 × (-1, 1)`, trapped in `|t| ≤ 1/2`) whose boundary over `B_{1/2}` lies in a band of width
  `δ ≤ θ/16` around a level `|c| ≤ δ`, and a small tilt `s ‖p‖ ≤ 1/40`, the configuration
  rescaled by `θ` in the tilted frame is again normalized, and its excess is bounded by
  `θ^{-m} (flatteningConstant / θ²) ∫ η (x_n - c - s (a + ⟪p, π x⟫))² dμ`
  for any cutoff `η ≥ 0` equal to `1` on `B_{4θ}` (tilted `GR8.2`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

/-! ### The tilted frame -/

/-- The unit normal `(-s p, 1)/√(1 + s²‖p‖²)` of the graph of `y ↦ s ⟪p, y⟫`. -/
def tiltNormal {m : ℕ} (p : Space m) (s : ℝ) : Space (m + 1) :=
  (Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2))⁻¹ • point (-(s • p)) 1

theorem tiltNormal_sigma_pos {m : ℕ} (p : Space m) (s : ℝ) :
    1 ≤ Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2) := by
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg s, sq_nonneg ‖p‖, mul_nonneg (sq_nonneg s) (sq_nonneg ‖p‖)]

theorem inner_tiltNormal {m : ℕ} (p : Space m) (s : ℝ) (x : Space (m + 1)) :
    inner ℝ x (tiltNormal p s) = (Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2))⁻¹ *
      (x (Fin.last m) - s * inner ℝ p (horizontal x)) := by
  rw [tiltNormal, real_inner_smul_right, inner_eq_inner_horizontal_add_mul_last, horizontal_point,
    last_point, inner_neg_right, real_inner_smul_right, real_inner_comm]
  ring

theorem norm_tiltNormal {m : ℕ} (p : Space m) (s : ℝ) : ‖tiltNormal p s‖ = 1 := by
  set σ := Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2) with hσ
  have hσ1 := tiltNormal_sigma_pos p s
  have hpt : ‖point (-(s • p)) (1 : ℝ)‖ = σ := by
    have h := norm_sq_eq_norm_horizontal_sq_add (point (-(s • p)) (1 : ℝ))
    rw [horizontal_point, last_point, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      one_pow] at h
    rw [hσ, show 1 + s ^ 2 * ‖p‖ ^ 2 = ‖point (-(s • p)) (1 : ℝ)‖ ^ 2 by rw [h]; ring,
      Real.sqrt_sq (norm_nonneg _)]
  rw [tiltNormal, norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith),
    inv_mul_cancel₀ (by linarith)]

theorem inner_verticalDirection_tiltNormal {m : ℕ} (p : Space m) (s : ℝ) :
    inner ℝ (verticalDirection m) (tiltNormal p s) = (Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2))⁻¹ := by
  rw [inner_tiltNormal, horizontal_verticalDirection, last_verticalDirection, inner_zero_right]
  ring

theorem norm_verticalDirection_sub_tiltNormal_le {m : ℕ} (p : Space m) {s : ℝ} (hs : 0 ≤ s) :
    ‖verticalDirection m - tiltNormal p s‖ ≤ s * ‖p‖ := by
  set σ := Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2) with hσ
  have hσ1 := tiltNormal_sigma_pos p s
  have hσsq : σ ^ 2 = 1 + s ^ 2 * ‖p‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : ‖verticalDirection m - tiltNormal p s‖ ^ 2 = 2 - 2 * σ⁻¹ := by
    rw [norm_sub_sq_real, norm_verticalDirection, norm_tiltNormal,
      inner_verticalDirection_tiltNormal]
    ring
  have hle : 2 - 2 * σ⁻¹ ≤ (s * ‖p‖) ^ 2 := by
    have hσ0 : 0 < σ := by linarith
    have hinv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0.ne'
    have hinv0 : 0 < σ⁻¹ := inv_pos.mpr hσ0
    nlinarith [mul_pos hinv0 hσ0]
  have h2 : ‖verticalDirection m - tiltNormal p s‖ ^ 2 ≤ (s * ‖p‖) ^ 2 := hsq ▸ hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- The Householder frame sending `e_n` to `tiltNormal p s`. -/
def tiltFrame {m : ℕ} (p : Space m) (s : ℝ) : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1) :=
  Submodule.reflection (ℝ ∙ (verticalDirection m - tiltNormal p s))ᗮ

theorem tiltFrame_verticalDirection {m : ℕ} (p : Space m) (s : ℝ) :
    tiltFrame p s (verticalDirection m) = tiltNormal p s :=
  Submodule.reflection_sub (by rw [norm_verticalDirection, norm_tiltNormal])

theorem inner_tiltFrame_tiltNormal {m : ℕ} (p : Space m) (s : ℝ) (x : Space (m + 1)) :
    inner ℝ (tiltFrame p s x) (tiltNormal p s) = x (Fin.last m) := by
  rw [← tiltFrame_verticalDirection p s, LinearIsometryEquiv.inner_map_map,
    inner_verticalDirection_right]

theorem tiltFrame_symm_apply_last {m : ℕ} (p : Space m) (s : ℝ) (y : Space (m + 1)) :
    (tiltFrame p s).symm y (Fin.last m) = inner ℝ y (tiltNormal p s) := by
  rw [← inner_verticalDirection_right, ← tiltFrame_verticalDirection p s,
    ← LinearIsometryEquiv.inner_map_map (tiltFrame p s), LinearIsometryEquiv.apply_symm_apply]

/-! ### Elementary geometry of cylinders -/

theorem norm_le_norm_horizontal_add_abs_last {m : ℕ} (x : Space (m + 1)) :
    ‖x‖ ≤ ‖horizontal x‖ + |x (Fin.last m)| := by
  have h := norm_sq_eq_norm_horizontal_sq_add x
  have h2 : ‖x‖ ^ 2 ≤ (‖horizontal x‖ + |x (Fin.last m)|) ^ 2 := by
    rw [h]
    nlinarith [norm_nonneg (horizontal x), abs_nonneg (x (Fin.last m)),
      sq_abs (x (Fin.last m)), mul_nonneg (norm_nonneg (horizontal x)) (abs_nonneg (x (Fin.last m)))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem norm_lt_of_mem_cylinderSet {m : ℕ} {r h : ℝ} {x : Space (m + 1)}
    (hx : x ∈ cylinderSet (ball (0 : Space m) r) h) : ‖x‖ < r + h := by
  have h1 : ‖horizontal x‖ < r := mem_ball_zero_iff.mp hx.1
  have h2 : |x (Fin.last m)| < h := abs_lt.mpr ⟨hx.2.1, hx.2.2⟩
  linarith [norm_le_norm_horizontal_add_abs_last x]

theorem mem_cylinderSet_of_norm_lt {m : ℕ} {r h : ℝ} {x : Space (m + 1)} (hr : ‖x‖ < r)
    (hh : ‖x‖ < h) : x ∈ cylinderSet (ball (0 : Space m) r) h := by
  refine ⟨mem_ball_zero_iff.mpr ((norm_horizontal_le_norm_of_space x).trans_lt hr), ?_⟩
  have := (abs_apply_last_le_norm x).trans_lt hh
  exact ⟨by linarith [neg_abs_le (x (Fin.last m))], by linarith [le_abs_self (x (Fin.last m))]⟩

/-- A.e. statements pull back under similarities. -/
theorem ae_comp_similarity {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ}
    (hθ : θ ≠ 0) {P : Space d → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂volume, P (similarity Q c θ x) := by
  have h1 : ∀ᵐ z ∂volume, P (affineIsometryHomeomorph Q c z) :=
    (measurePreserving_affineIsometryHomeomorph Q c).quasiMeasurePreserving.ae h
  rw [ae_iff] at h1 ⊢
  have hset : {x | ¬P (similarity Q c θ x)} =
      (fun x ↦ θ • x) ⁻¹' {z | ¬P (affineIsometryHomeomorph Q c z)} := by
    ext x
    simp [similarity_eq_affineIsometry]
  rw [hset, Measure.addHaar_preimage_smul volume hθ, h1, mul_zero]

theorem norm_similarity_zero {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) {θ : ℝ} (hθ : 0 ≤ θ)
    (x : Space d) : ‖similarity Q 0 θ x‖ = θ * ‖x‖ := by
  rw [similarity, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ,
    LinearIsometryEquiv.norm_map]

theorem continuous_similarity {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) (θ : ℝ) :
    Continuous (similarity Q c θ) :=
  continuous_const.add (Q.continuous.const_smul θ)

/-! ### One step of tilt-excess decay -/

namespace IsLocalPerimeterMinimizer

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}

/-- **`GR12`, one step.** Let `E` be a normalized configuration (slab-trapped representation over
`B_2 × (-1, 1) ⊆ Ω`, trapped in `|t| ≤ 1/2`) whose phase is the correct half-space outside the
band `|t - c| ≤ δ` over `B_{1/2}`, with `|c| ≤ δ ≤ θ/16`, `θ ≤ 1/10`. For a small tilt
`s ‖p‖ ≤ 1/40`, the similarity `S x = θ Q x` with the Householder frame `Q = tiltFrame p s`
yields again a normalized configuration `S⁻¹ E`, whose excess is at most
`θ^{-m} (flatteningConstant / θ²) ∫ η (x_n - c - s (a + ⟪p, π x⟫))² dμ` for every `C¹` cutoff
`η ≥ 0` with compact support, equal to `1` on `B_{4θ}`. -/
theorem tilt_step (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E (ball (0 : Space m) 2) (1 / 2) 1 μ ν)
    (hcyl : cylinderSet (ball (0 : Space m) 2) 1 ⊆ Ω)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 10) {c δ : ℝ} (hcδ : |c| ≤ δ) (hδθ : δ ≤ θ / 16)
    (hphase : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < 1 → δ < |x (Fin.last m) - c| → (x ∈ E ↔ c < x (Fin.last m)))
    {p : Space m} {a s : ℝ} (hs : 0 ≤ s) (hsp : s * ‖p‖ ≤ 1 / 40)
    {η : Space m → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hη0 : ∀ y, 0 ≤ η y)
    (hη1 : ∀ y ∈ ball (0 : Space m) (4 * θ), η y = 1) :
    IsLocalPerimeterMinimizer b (similarity (tiltFrame p s) 0 θ ⁻¹' E)
        (similarity (tiltFrame p s) 0 θ ⁻¹' Ω) ∧
      SlabTrappedRepresentation b (similarity (tiltFrame p s) 0 θ ⁻¹' E) (ball (0 : Space m) 2)
        (1 / 2) 1 ((similarityMeasure μ (tiltFrame p s) 0 θ).restrict
          (cylinderSet (ball (0 : Space m) 2) 1))
        (fun x ↦ (tiltFrame p s).symm (ν (similarity (tiltFrame p s) 0 θ x))) ∧
      cylinderSet (ball (0 : Space m) 2) 1 ⊆ similarity (tiltFrame p s) 0 θ ⁻¹' Ω ∧
      (projectedExcessMeasure ((similarityMeasure μ (tiltFrame p s) 0 θ).restrict
          (cylinderSet (ball (0 : Space m) 2) 1))
          (fun x ↦ (tiltFrame p s).symm (ν (similarity (tiltFrame p s) 0 θ x)))).real
          (ball 0 2) ≤
        (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
          ∫ x, η (horizontal x) *
            (x (Fin.last m) - (c + s * (a + inner ℝ p (horizontal x)))) ^ 2 ∂μ := by
  set Q := tiltFrame p s with hQ_def
  set ν₁ := tiltNormal p s with hν₁_def
  set S := similarity Q 0 θ with hSim_def
  set T := affineIsometryHomeomorph Q 0 with hT_def
  set W := cylinderSet (ball (0 : Space m) 2) (1 : ℝ) with hW_def
  have hd : 1 ≤ m + 1 := by omega
  have := hS.isFiniteMeasure
  have hτ : ‖verticalDirection m - ν₁‖ ≤ 1 / 40 :=
    (norm_verticalDirection_sub_tiltNormal_le p hs).trans hsp
  have hδ0 : 0 ≤ δ := (abs_nonneg c).trans hcδ
  -- the trapping principle in the original coordinates
  have hG : ∀ᵐ y ∂volume, ‖y‖ < 5 * θ →
      (θ / 2 < inner ℝ y ν₁ → y ∈ E) ∧ (inner ℝ y ν₁ < -(θ / 2) → y ∉ E) := by
    filter_upwards [hphase] with y hy hyn
    have hy3 : ‖y‖ < 1 / 2 := by linarith
    have hπ : horizontal y ∈ ball (0 : Space m) (1 / 2) :=
      mem_ball_zero_iff.mpr ((norm_horizontal_le_norm_of_space y).trans_lt hy3)
    have hlast : |y (Fin.last m)| < 1 :=
      ((abs_apply_last_le_norm y).trans_lt hy3).trans (by norm_num)
    have hdiff : |y (Fin.last m) - inner ℝ y ν₁| ≤ ‖y‖ * (1 / 40) := by
      have h1 : y (Fin.last m) - inner ℝ y ν₁ = inner ℝ y (verticalDirection m - ν₁) := by
        rw [inner_sub_right, inner_verticalDirection_right]
      rw [h1]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hτ (norm_nonneg _))
    have hcd := abs_le.mp hcδ
    have hdd := abs_le.mp hdiff
    constructor
    · intro hpos
      have hgap : δ < |y (Fin.last m) - c| := by
        rw [abs_of_pos (by linarith)]
        linarith
      exact (hy hπ hlast hgap).mpr (by linarith)
    · intro hneg hyE
      have hgap : δ < |y (Fin.last m) - c| := by
        rw [abs_of_neg (by linarith)]
        linarith
      have := (hy hπ hlast hgap).mp hyE
      linarith
  -- tilted trapping in the rotated frame
  have hGx := (LinearIsometryEquiv.measurePreserving Q).quasiMeasurePreserving.ae hG
  have hnormT : ∀ x, ‖T x‖ = ‖x‖ := fun x ↦ by
    rw [hT_def, affineIsometryHomeomorph_apply, add_zero, LinearIsometryEquiv.norm_map]
  have hbotT : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (4 * θ) →
      x (Fin.last m) ∈ Ioo (-θ) (-(θ / 2)) → Q x + 0 ∉ E := by
    filter_upwards [hGx] with x hx hxπ hxn
    have hxc : x ∈ cylinderSet (ball (0 : Space m) (4 * θ)) θ :=
      ⟨hxπ, hxn.1, by linarith [hxn.2]⟩
    have hnorm : ‖Q x‖ < 5 * θ := by
      rw [LinearIsometryEquiv.norm_map]
      linarith [norm_lt_of_mem_cylinderSet hxc]
    rw [add_zero]
    exact (hx hnorm).2 (by rw [hQ_def, hν₁_def, inner_tiltFrame_tiltNormal]; linarith [hxn.2])
  have htopT : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) (4 * θ) →
      x (Fin.last m) ∈ Ioo (θ / 2) θ → Q x + 0 ∈ E := by
    filter_upwards [hGx] with x hx hxπ hxn
    have hxc : x ∈ cylinderSet (ball (0 : Space m) (4 * θ)) θ :=
      ⟨hxπ, by linarith [hxn.1], hxn.2⟩
    have hnorm : ‖Q x‖ < 5 * θ := by
      rw [LinearIsometryEquiv.norm_map]
      linarith [norm_lt_of_mem_cylinderSet hxc]
    rw [add_zero]
    exact (hx hnorm).1 (by rw [hQ_def, hν₁_def, inner_tiltFrame_tiltNormal]; linarith [hxn.1])
  have hcylT : T '' cylinderSet (ball (0 : Space m) (4 * θ)) θ ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    have hnorm : ‖T x‖ < 5 * θ := by
      rw [hnormT]
      linarith [norm_lt_of_mem_cylinderSet hx]
    exact mem_cylinderSet_of_norm_lt (by linarith) (by linarith)
  -- tilted `GR8.2`
  set σ := Real.sqrt (1 + s ^ 2 * ‖p‖ ^ 2) with hσ_def
  have hσ1 : 1 ≤ σ := tiltNormal_sigma_pos p s
  set lam := (c + s * a) / σ with hlam
  have hGR8 := hmin.flattening_excess_closedBall_le_tilted Q 0 isOpen_ball (H := θ / 2)
    (H' := θ) (by positivity) (by linarith) (hcylT.trans hcyl) hS.rep hcylT hbotT htopT 0
    (r := 2 * θ) (R := 3 * θ) (by positivity) (by linarith)
    (closedBall_subset_ball (by linarith)) lam
  rw [← hT_def, tiltFrame_verticalDirection] at hGR8
  rw [show (3 * θ - 2 * θ) ^ 2 = θ ^ 2 by ring] at hGR8
  -- the right-hand side of `GR8.2` and the height integral
  set L : Space m → ℝ := fun w ↦ c + s * (a + inner ℝ p w) with hL_def
  have hL : ContDiff ℝ 1 L :=
    contDiff_const.add (contDiff_const.mul (contDiff_const.add (innerSL ℝ p).contDiff))
  have hint := hS.integrable_height_sq hη hηc hL
  have hpt : ∀ y, (T.symm y (Fin.last m) - lam) ^ 2 ≤ (y (Fin.last m) - L (horizontal y)) ^ 2 := by
    intro y
    have h1 : T.symm y (Fin.last m) = inner ℝ y ν₁ := by
      rw [hT_def, affineIsometryHomeomorph_symm_apply, sub_zero, hQ_def,
        tiltFrame_symm_apply_last]
    rw [h1, hν₁_def, inner_tiltNormal]
    have hσ0 : 0 < σ := by linarith
    have h2 : σ⁻¹ * (y (Fin.last m) - s * inner ℝ p (horizontal y)) - lam =
        σ⁻¹ * (y (Fin.last m) - L (horizontal y)) := by
      simp only [hlam, hL_def]
      field_simp
      ring
    rw [h2, mul_pow]
    have h3 : (σ⁻¹) ^ 2 ≤ 1 := by
      rw [inv_pow]
      exact inv_le_one_of_one_le₀ (by nlinarith)
    exact mul_le_of_le_one_left (sq_nonneg _) h3
  set R₀ := T.symm ⁻¹' (horizontal ⁻¹' ball (0 : Space m) (3 * θ)) ∩
    T '' cylinderSet (ball (0 : Space m) (4 * θ)) θ with hR₀_def
  have hcylTo : IsOpen (cylinderSet (ball (0 : Space m) (4 * θ)) θ) :=
    isOpen_cylinderSet isOpen_ball θ
  have hR₀m : MeasurableSet R₀ :=
    ((isOpen_ball.preimage continuous_horizontal).preimage T.symm.continuous).measurableSet.inter
      (T.isOpenMap _ hcylTo).measurableSet
  have hR₀η : ∀ y ∈ R₀, η (horizontal y) = 1 := by
    rintro y ⟨hy1, ⟨x, hx, rfl⟩⟩
    have hx' : T.symm (T x) = x := T.symm_apply_apply x
    simp only [mem_preimage, hx'] at hy1
    have hxn : ‖x‖ < 4 * θ := by
      have := norm_le_norm_horizontal_add_abs_last x
      have h1 : ‖horizontal x‖ < 3 * θ := mem_ball_zero_iff.mp hy1
      have h2 : |x (Fin.last m)| < θ := abs_lt.mpr ⟨hx.2.1, hx.2.2⟩
      linarith
    apply hη1
    rw [mem_ball_zero_iff]
    calc ‖horizontal (T x)‖ ≤ ‖T x‖ := norm_horizontal_le_norm_of_space _
      _ = ‖x‖ := hnormT x
      _ < 4 * θ := hxn
  have hRHS : ∫ y in R₀, (T.symm y (Fin.last m) - lam) ^ 2 ∂μ ≤
      ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 ∂μ := by
    calc ∫ y in R₀, (T.symm y (Fin.last m) - lam) ^ 2 ∂μ
        ≤ ∫ y in R₀, η (horizontal y) * (y (Fin.last m) - L (horizontal y)) ^ 2 ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
            hint.integrableOn (ae_restrict_of_forall_mem hR₀m fun y hy ↦ ?_)
          dsimp only
          rw [hR₀η y hy, one_mul]
          exact hpt y
      _ ≤ ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 ∂μ :=
          setIntegral_le_integral hint
            (Eventually.of_forall fun y ↦ mul_nonneg (hη0 _) (sq_nonneg _))
  -- the new representation
  have hWsub : W ⊆ S ⁻¹' W := by
    intro x hx
    have hnorm : ‖S x‖ < 3 * θ := by
      rw [hSim_def, norm_similarity_zero Q hθ0.le]
      have h3 : ‖x‖ < 2 + 1 := norm_lt_of_mem_cylinderSet hx
      have := mul_lt_mul_of_pos_left h3 hθ0
      linarith
    exact mem_cylinderSet_of_norm_lt (by linarith) (by linarith)
  have hWo : IsOpen W := isOpen_cylinderSet isOpen_ball 1
  have hrep'' := (hS.rep.preimage_similarity hd Q 0 hθ0).restrict hWo hWsub
  -- trapping of the new configuration
  have hGS := ae_comp_similarity Q 0 hθ0.ne' hG
  have hinnerS : ∀ x, inner ℝ (S x) ν₁ = θ * x (Fin.last m) := fun x ↦ by
    rw [hSim_def, similarity, zero_add, real_inner_smul_left, hQ_def, hν₁_def,
      inner_tiltFrame_tiltNormal]
  have hnormS : ∀ x ∈ W, ‖S x‖ < 5 * θ := fun x hx ↦ by
    rw [hSim_def, norm_similarity_zero Q hθ0.le]
    have h3 : ‖x‖ < 2 + 1 := norm_lt_of_mem_cylinderSet hx
    have := mul_lt_mul_of_pos_left h3 hθ0
    linarith
  have hbot' : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) 2 →
      x (Fin.last m) ∈ Ioo (-1) (-(1 / 2)) → x ∉ S ⁻¹' E := by
    filter_upwards [hGS] with x hx hxπ hxn
    have hxc : x ∈ W := ⟨hxπ, hxn.1, by linarith [hxn.2]⟩
    exact (hx (hnormS x hxc)).2 (by rw [hinnerS]; nlinarith [hxn.2])
  have htop' : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) 2 →
      x (Fin.last m) ∈ Ioo (1 / 2) 1 → x ∈ S ⁻¹' E := by
    filter_upwards [hGS] with x hx hxπ hxn
    have hxc : x ∈ W := ⟨hxπ, by linarith [hxn.1], hxn.2⟩
    exact (hx (hnormS x hxc)).1 (by rw [hinnerS]; nlinarith [hxn.1])
  refine ⟨hmin.preimage_similarity hd Q 0 hθ0,
    ⟨hS.measurableSet.preimage (continuous_similarity Q 0 θ).measurable, isOpen_ball,
      by norm_num, by norm_num, hrep'', hbot', htop'⟩,
    hWsub.trans (preimage_mono hcyl), ?_⟩
  -- the excess of the new configuration
  have := hrep''.isFiniteMeasure
  have hπB : MeasurableSet (horizontal ⁻¹' ball (0 : Space m) 2 : Set (Space (m + 1))) :=
    measurableSet_ball.preimage continuous_horizontal.measurable
  have hWπ : horizontal ⁻¹' ball (0 : Space m) 2 ∩ W = W :=
    inter_eq_right.mpr fun x hx ↦ hx.1
  set ν' : Space (m + 1) → Space (m + 1) := fun x ↦ Q.symm (ν (S x)) with hν'_def
  have hν'n : ∀ y, ν' (θ⁻¹ • T.symm y) (Fin.last m) = inner ℝ (ν y) ν₁ := by
    intro y
    have hSy : S (θ⁻¹ • T.symm y) = y := similarity_inv_apply Q 0 hθ0.ne' y
    simp only [hν'_def, hSy, hQ_def, tiltFrame_symm_apply_last, hν₁_def]
  have hexc : (projectedExcessMeasure ((similarityMeasure μ Q 0 θ).restrict W) ν').real
      (ball 0 2) = (θ ^ m)⁻¹ * ∫ y, W.indicator (fun x ↦ 1 - ν' x (Fin.last m))
        (θ⁻¹ • T.symm y) ∂μ := by
    rw [projectedExcessMeasure_real_eq_setIntegral hrep''.integrable hrep''.norm_eq_one
      measurableSet_ball, Measure.restrict_restrict hπB, hWπ, ← integral_indicator hWo.measurableSet,
      integral_similarityMeasure μ Q 0 hθ0, Nat.add_sub_cancel]
  rw [hexc]
  -- comparison with the left-hand side of `GR8.2`
  set L₀ := T.symm ⁻¹' (horizontal ⁻¹' closedBall (0 : Space m) (2 * θ)) ∩
    T '' cylinderSet (ball (0 : Space m) (4 * θ)) θ with hL₀_def
  have hL₀m : MeasurableSet L₀ :=
    ((isClosed_closedBall.preimage continuous_horizontal).preimage
      T.symm.continuous).measurableSet.inter (T.isOpenMap _ hcylTo).measurableSet
  have hg_int : Integrable (fun y ↦ 1 - inner ℝ (ν y) ν₁) μ :=
    (integrable_const 1).sub (hS.rep.integrable.inner_const _)
  have hg_nonneg : ∀ᵐ y ∂μ, 0 ≤ 1 - inner ℝ (ν y) ν₁ := by
    filter_upwards [hS.rep.norm_eq_one] with y hy
    have hcs := real_inner_le_norm (ν y) ν₁
    rw [hy, hν₁_def, norm_tiltNormal, mul_one] at hcs
    linarith
  have hcmp : ∫ y, W.indicator (fun x ↦ 1 - ν' x (Fin.last m)) (θ⁻¹ • T.symm y) ∂μ ≤
      ∫ y in L₀, (1 - inner ℝ (ν y) ν₁) ∂μ := by
    rw [← integral_indicator hL₀m]
    refine integral_mono_of_nonneg ?_ (hg_int.indicator hL₀m) ?_
    · filter_upwards [hg_nonneg] with y hy
      by_cases hx : θ⁻¹ • T.symm y ∈ W
      · rw [indicator_of_mem hx, hν'n]
        exact hy
      · rw [indicator_of_notMem hx]
        exact le_rfl
    · filter_upwards [hg_nonneg] with y hy
      by_cases hx : θ⁻¹ • T.symm y ∈ W
      · set v := θ⁻¹ • T.symm y with hv
        have hTy : T.symm y = θ • v := by
          rw [hv, smul_smul, mul_inv_cancel₀ hθ0.ne', one_smul]
        have hπv : ‖horizontal v‖ < 2 := mem_ball_zero_iff.mp hx.1
        have hvn : |v (Fin.last m)| < 1 := abs_lt.mpr ⟨hx.2.1, hx.2.2⟩
        have hπTy : ‖horizontal (T.symm y)‖ = θ * ‖horizontal v‖ := by
          rw [hTy, show horizontal (θ • v) = θ • horizontal v from
            map_smul horizontalContinuousLinearMap θ v, norm_smul, Real.norm_eq_abs,
            abs_of_pos hθ0]
        have hTyn : |(T.symm y) (Fin.last m)| = θ * |v (Fin.last m)| := by
          rw [hTy, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hθ0]
        have h1 := mul_lt_mul_of_pos_left hπv hθ0
        have h2 := mul_lt_mul_of_pos_left hvn hθ0
        have hyL : y ∈ L₀ := by
          refine ⟨?_, ?_⟩
          · show horizontal (T.symm y) ∈ closedBall 0 (2 * θ)
            rw [mem_closedBall_zero_iff, hπTy]
            linarith
          · rw [Homeomorph.image_eq_preimage_symm, mem_preimage]
            have h3 : |(T.symm y) (Fin.last m)| < θ := by rw [hTyn]; linarith
            refine ⟨?_, (abs_lt.mp h3).1, (abs_lt.mp h3).2⟩
            rw [mem_ball_zero_iff, hπTy]
            linarith
        rw [indicator_of_mem hx, indicator_of_mem hyL, hν'n]
      · rw [indicator_of_notMem hx]
        by_cases hyL : y ∈ L₀
        · rw [indicator_of_mem hyL]
          exact hy
        · rw [indicator_of_notMem hyL]
  have hθm : 0 < (θ ^ m)⁻¹ := inv_pos.mpr (pow_pos hθ0 m)
  calc (θ ^ m)⁻¹ * ∫ y, W.indicator (fun x ↦ 1 - ν' x (Fin.last m)) (θ⁻¹ • T.symm y) ∂μ
      ≤ (θ ^ m)⁻¹ * ∫ y in L₀, (1 - inner ℝ (ν y) ν₁) ∂μ :=
        mul_le_mul_of_nonneg_left hcmp hθm.le
    _ ≤ (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2 * ∫ y in R₀, (T.symm y (Fin.last m) - lam) ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hGR8 hθm.le
    _ ≤ (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2 *
          ∫ x, η (horizontal x) * (x (Fin.last m) - L (horizontal x)) ^ 2 ∂μ) := by
        have hF : 0 ≤ flatteningConstant / θ ^ 2 := by
          unfold flatteningConstant
          positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRHS hF) hθm.le
    _ = (θ ^ m)⁻¹ * (flatteningConstant / θ ^ 2) *
          ∫ x, η (horizontal x) * (x (Fin.last m) - (c + s * (a + inner ℝ p (horizontal x)))) ^ 2 ∂μ := by
        ring

end IsLocalPerimeterMinimizer

end SerrinEpigraph
