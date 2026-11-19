module

public import SerrinEpigraph.ConeSplitting
public import SerrinEpigraph.HalfspaceTangents

/-!
# Regular (`C¹`) boundary points and singular sets

This module fixes the notion of regular boundary point used by the regularity interface of
`docs/rigidity-proof/gmt-regularity.md` (GR14–GR17).

`IsC1BoundaryPoint E x` means: on some ball around `x`, the set `E` agrees almost everywhere with
the positivity set `{F > 0}` of a function `F` which is `C¹` on the ball, vanishes at `x` and has
nonzero differential at `x` (a `C¹` defining function). A rotated `C¹` graph chart
`E ∩ B =ᵐ {z | φ (horizontal z') < z'_last}`, `z' = Q⁻¹ (z - x)`, gives the defining function
`F z = (Q⁻¹ (z - x))_last - φ (horizontal (Q⁻¹ (z - x)))`
(`isC1BoundaryPoint_of_graph`); conversely the implicit function theorem turns a defining
function back into a graph chart. The positivity-set form is dimension independent and is
transported without effort by translations, dilations, linear isometries, null modifications and
cylinders.

`singularSet E` is the set of measure-theoretic boundary points which are not `C¹` boundary
points.

Main results:
- invariance of `IsC1BoundaryPoint` and `singularSet` under null modifications, translations and
  dilations (`isC1BoundaryPoint_preimage_add_smul_iff`, `mem_singularSet_preimage_add_smul_iff`)
  and linear isometries;
- `C¹` boundary points lie in the measure-theoretic boundary;
- at a `C¹` boundary point the blow-ups converge in `L¹_loc` to the half-space whose inner normal
  is the gradient of the defining function (`isBlowupLimit_positiveHalfspace_gradient`), so every
  tangent cone is that half-space (`IsC1BoundaryPoint.exists_forall_isTangentCone`);
- the regular boundary points form a relatively open subset of the boundary, so the singular set
  is closed (`isClosed_singularSet`);
- sets a.e. equal to a half-space have empty singular set;
- regular points lift to cylinders, so `singularSet (horizontal ⁻¹' A) ⊆ horizontal ⁻¹'
  singularSet A`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-! ### 1. Definitions -/

/-- `x` is a `C¹` boundary point of `E`: near `x`, `E` coincides almost everywhere with the
positivity set of a function which is `C¹` on a ball around `x`, vanishes at `x`, and has
nonzero differential at `x`. -/
def IsC1BoundaryPoint {d : ℕ} (E : Set (Space d)) (x : Space d) : Prop :=
  ∃ (F : Space d → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ 1 F (ball x r) ∧ F x = 0 ∧
    fderiv ℝ F x ≠ 0 ∧ ∀ᵐ y ∂volume, y ∈ ball x r → (y ∈ E ↔ 0 < F y)

/-- The singular set: measure-theoretic boundary points which are not `C¹` boundary points. -/
def singularSet {d : ℕ} (E : Set (Space d)) : Set (Space d) :=
  {x | x ∈ measureTheoreticBoundary E ∧ ¬ IsC1BoundaryPoint E x}

theorem mem_singularSet {d : ℕ} {E : Set (Space d)} {x : Space d} :
    x ∈ singularSet E ↔ x ∈ measureTheoreticBoundary E ∧ ¬ IsC1BoundaryPoint E x :=
  Iff.rfl

theorem singularSet_subset_measureTheoreticBoundary {d : ℕ} (E : Set (Space d)) :
    singularSet E ⊆ measureTheoreticBoundary E :=
  fun _ hx ↦ hx.1

/-! ### 2. Elementary helpers -/

private theorem ae_comp_add_smul_aux {d : ℕ} {P : Space d → Prop} (h : ∀ᵐ z ∂volume, P z)
    (x₀ : Space d) {c : ℝ} (hc : c ≠ 0) : ∀ᵐ y ∂volume, P (x₀ + c • y) := by
  have h1 : ∀ᵐ w ∂volume, P (x₀ + w) :=
    (measurePreserving_add_left volume x₀).quasiMeasurePreserving.ae h
  exact (Measure.quasiMeasurePreserving_smul volume hc).ae h1

private theorem norm_horizontal_le_norm_aux {k : ℕ} (x : Space (k + 1)) :
    ‖horizontal x‖ ≤ ‖x‖ := by
  have h : ‖x‖ ^ 2 = ‖horizontal x‖ ^ 2 + x (Fin.last k) ^ 2 := by
    conv_lhs => rw [← point_horizontal_last x]
    rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
    ring
  have h2 : ‖horizontal x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (x (Fin.last k))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

private theorem horizontal_zero_aux {k : ℕ} : horizontal (0 : Space (k + 1)) = 0 := by
  ext i
  simp [horizontal]

private theorem horizontal_sub_aux {k : ℕ} (x y : Space (k + 1)) :
    horizontal (x - y) = horizontal x - horizontal y := by
  ext i
  simp [horizontal]

private theorem hasFDerivAt_of_contDiffOn_ball {d : ℕ} {F : Space d → ℝ} {x y : Space d}
    {r : ℝ} (hF : ContDiffOn ℝ 1 F (ball x r)) (hy : y ∈ ball x r) :
    HasFDerivAt F (fderiv ℝ F y) y :=
  ((hF.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt

/-- A ball which lies a.e. inside `E` and inside `B` forces `E ∩ B` to have positive measure. -/
private theorem volume_inter_ne_zero_of_ae_ball {d : ℕ} {E B : Set (Space d)} {q : Space d}
    {δ : ℝ} (hδ : 0 < δ) (hsub : ball q δ ⊆ B) (hae : ∀ᵐ z ∂volume, z ∈ ball q δ → z ∈ E) :
    volume (E ∩ B) ≠ 0 := by
  intro h0
  have hcov : ball q δ ⊆ (E ∩ B) ∪ {z | ¬(z ∈ ball q δ → z ∈ E)} := by
    intro z hz
    by_cases hzE : z ∈ E
    · exact Or.inl ⟨hzE, hsub hz⟩
    · exact Or.inr fun h ↦ hzE (h hz)
  exact (measure_ball_pos volume q hδ).ne'
    (measure_mono_null hcov (measure_union_null h0 (ae_iff.mp hae)))

/-- A function continuous on an open ball and positive at a point of the ball stays positive on a
smaller ball around that point. -/
private theorem exists_ball_pos_of_continuousOn {d : ℕ} {F : Space d → ℝ} {x q : Space d}
    {r : ℝ} (hF : ContinuousOn F (ball x r)) (hq : q ∈ ball x r) (hFq : 0 < F q) :
    ∃ δ > 0, ball q δ ⊆ ball x r ∧ ∀ z ∈ ball q δ, 0 < F z := by
  have h1 : ∀ᶠ z in 𝓝 q, z ∈ ball x r := isOpen_ball.mem_nhds hq
  have h2 : ∀ᶠ z in 𝓝 q, 0 < F z :=
    (hF.continuousAt (isOpen_ball.mem_nhds hq)).eventually (lt_mem_nhds hFq)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  exact ⟨δ, hδ, fun z hz ↦ (hδsub z hz).1, fun z hz ↦ (hδsub z hz).2⟩

private theorem exists_ball_neg_of_continuousOn {d : ℕ} {F : Space d → ℝ} {x q : Space d}
    {r : ℝ} (hF : ContinuousOn F (ball x r)) (hq : q ∈ ball x r) (hFq : F q < 0) :
    ∃ δ > 0, ball q δ ⊆ ball x r ∧ ∀ z ∈ ball q δ, F z < 0 := by
  obtain ⟨δ, hδ, hsub, hpos⟩ :=
    exists_ball_pos_of_continuousOn (F := fun z ↦ -F z) hF.neg hq (by linarith)
  exact ⟨δ, hδ, hsub, fun z hz ↦ by have := hpos z hz; linarith⟩

/-! ### 3. Invariance -/

theorem IsC1BoundaryPoint.congr_ae {d : ℕ} {E E' : Set (Space d)} {x : Space d}
    (h : IsC1BoundaryPoint E x) (hEE' : E =ᵐ[volume] E') : IsC1BoundaryPoint E' x := by
  obtain ⟨F, r, hr, hF, hFx, hdF, hae⟩ := h
  refine ⟨F, r, hr, hF, hFx, hdF, ?_⟩
  filter_upwards [hae, hEE'] with y hy hyE hyB
  exact (Iff.of_eq hyE).symm.trans (hy hyB)

theorem isC1BoundaryPoint_congr_ae {d : ℕ} {E E' : Set (Space d)} (hEE' : E =ᵐ[volume] E')
    (x : Space d) : IsC1BoundaryPoint E x ↔ IsC1BoundaryPoint E' x :=
  ⟨fun h ↦ h.congr_ae hEE', fun h ↦ h.congr_ae hEE'.symm⟩

theorem singularSet_congr_ae {d : ℕ} {E E' : Set (Space d)} (hEE' : E =ᵐ[volume] E') :
    singularSet E = singularSet E' := by
  ext x
  rw [mem_singularSet, mem_singularSet, measureTheoreticBoundary_congr_ae hEE',
    isC1BoundaryPoint_congr_ae hEE' x]

/-- `C¹` boundary points are transported by the affine maps `z ↦ x₀ + c • z`, `c > 0`. -/
theorem IsC1BoundaryPoint.preimage_add_smul {d : ℕ} {E : Set (Space d)} {x₀ y : Space d}
    {c : ℝ} (hc : 0 < c) (h : IsC1BoundaryPoint E (x₀ + c • y)) :
    IsC1BoundaryPoint ((fun z ↦ x₀ + c • z) ⁻¹' E) y := by
  obtain ⟨F, r, hr, hF, hFx, hdF, hae⟩ := h
  set A : Space d → Space d := fun z ↦ x₀ + c • z with hA
  have hAc : ContDiff ℝ 1 A := contDiff_const.add (contDiff_id.const_smul c)
  have hmaps : MapsTo A (ball y (r / c)) (ball (x₀ + c • y) r) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have hAz : A z - (x₀ + c • y) = c • (z - y) := by
      simp only [hA, smul_sub]
      abel
    rw [hAz, norm_smul, Real.norm_of_nonneg hc.le]
    rwa [lt_div_iff₀ hc, mul_comm] at hz
  have hAd : HasFDerivAt A (c • ContinuousLinearMap.id ℝ (Space d)) y :=
    ((hasFDerivAt_id y).const_smul c).const_add x₀
  have hFd : HasFDerivAt F (fderiv ℝ F (x₀ + c • y)) (x₀ + c • y) :=
    hasFDerivAt_of_contDiffOn_ball hF (mem_ball_self hr)
  refine ⟨F ∘ A, r / c, div_pos hr hc, hF.comp hAc.contDiffOn hmaps, hFx, ?_, ?_⟩
  · rw [(hFd.comp y hAd).fderiv]
    intro h0
    apply hdF
    ext v
    have h1 := congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (c⁻¹ • v)) h0
    simpa [smul_smul, mul_inv_cancel₀ hc.ne', hc.ne'] using h1
  · filter_upwards [ae_comp_add_smul_aux hae x₀ hc.ne'] with z hz hzB
    exact hz (hmaps hzB)

theorem isC1BoundaryPoint_preimage_add_smul_iff {d : ℕ} {E : Set (Space d)} {x₀ y : Space d}
    {c : ℝ} (hc : 0 < c) :
    IsC1BoundaryPoint ((fun z ↦ x₀ + c • z) ⁻¹' E) y ↔ IsC1BoundaryPoint E (x₀ + c • y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.preimage_add_smul hc⟩
  have hpt : -(c⁻¹ • x₀) + c⁻¹ • (x₀ + c • y) = y := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    abel
  have h1 : IsC1BoundaryPoint ((fun z ↦ x₀ + c • z) ⁻¹' E)
      (-(c⁻¹ • x₀) + c⁻¹ • (x₀ + c • y)) := by
    rwa [hpt]
  have h2 := h1.preimage_add_smul (inv_pos.mpr hc)
  have hset : (fun z ↦ -(c⁻¹ • x₀) + c⁻¹ • z) ⁻¹' ((fun z ↦ x₀ + c • z) ⁻¹' E) = E := by
    ext w
    simp only [mem_preimage]
    rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, one_smul]
    simp
  rwa [hset] at h2

/-- `C¹` boundary points are transported by linear isometries. -/
theorem IsC1BoundaryPoint.preimage_linearIsometryEquiv {d : ℕ} {E : Set (Space d)}
    {y : Space d} (Q : Space d ≃ₗᵢ[ℝ] Space d) (h : IsC1BoundaryPoint E (Q y)) :
    IsC1BoundaryPoint (Q ⁻¹' E) y := by
  obtain ⟨F, r, hr, hF, hFx, hdF, hae⟩ := h
  have hmaps : MapsTo Q (ball y r) (ball (Q y) r) := fun z hz ↦ by
    rw [mem_ball, Q.dist_map]
    exact hz
  have hQd : HasFDerivAt (Q : Space d → Space d)
      (Q.toContinuousLinearEquiv : Space d →L[ℝ] Space d) y :=
    Q.toContinuousLinearEquiv.hasFDerivAt
  have hFd : HasFDerivAt F (fderiv ℝ F (Q y)) (Q y) :=
    hasFDerivAt_of_contDiffOn_ball hF (mem_ball_self hr)
  refine ⟨F ∘ Q, r, hr, hF.comp Q.toContinuousLinearEquiv.contDiff.contDiffOn hmaps, hFx, ?_, ?_⟩
  · rw [(hFd.comp y hQd).fderiv]
    intro h0
    apply hdF
    ext v
    have h1 := congrArg (fun L : Space d →L[ℝ] ℝ ↦ L (Q.symm v)) h0
    simpa using h1
  · have h1 := Q.measurePreserving.quasiMeasurePreserving.ae hae
    filter_upwards [h1] with z hz hzB
    exact hz (hmaps hzB)

theorem isC1BoundaryPoint_preimage_linearIsometryEquiv_iff {d : ℕ} {E : Set (Space d)}
    {y : Space d} (Q : Space d ≃ₗᵢ[ℝ] Space d) :
    IsC1BoundaryPoint (Q ⁻¹' E) y ↔ IsC1BoundaryPoint E (Q y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.preimage_linearIsometryEquiv Q⟩
  have h1 : IsC1BoundaryPoint (Q ⁻¹' E) (Q.symm (Q y)) := by
    rwa [Q.symm_apply_apply]
  have h2 := h1.preimage_linearIsometryEquiv Q.symm
  have hset : Q.symm ⁻¹' (Q ⁻¹' E) = E := by
    ext w
    simp
  rwa [hset] at h2

theorem mem_measureTheoreticBoundary_preimage_linearIsometryEquiv_iff {d : ℕ}
    (E : Set (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d) (y : Space d) :
    y ∈ measureTheoreticBoundary (Q ⁻¹' E) ↔ Q y ∈ measureTheoreticBoundary E := by
  have hball : ∀ ρ, Q ⁻¹' ball (Q y) ρ = ball y ρ := fun ρ ↦ by
    ext z
    simp
  have hemb : MeasurableEmbedding (Q : Space d → Space d) :=
    Q.toHomeomorph.measurableEmbedding
  have hmp := Q.measurePreserving
  refine forall₂_congr fun ρ _ ↦ ?_
  rw [← hball ρ, ← preimage_inter, ← preimage_sdiff, hmp.measure_preimage_emb hemb,
    hmp.measure_preimage_emb hemb]

theorem mem_singularSet_preimage_add_smul_iff {d : ℕ} {E : Set (Space d)} {x₀ y : Space d}
    {c : ℝ} (hc : 0 < c) :
    y ∈ singularSet ((fun z ↦ x₀ + c • z) ⁻¹' E) ↔ x₀ + c • y ∈ singularSet E := by
  rw [mem_singularSet, mem_singularSet, mem_measureTheoreticBoundary_preimage_add_smul E x₀ y hc,
    isC1BoundaryPoint_preimage_add_smul_iff hc]

theorem mem_singularSet_preimage_linearIsometryEquiv_iff {d : ℕ} {E : Set (Space d)}
    {y : Space d} (Q : Space d ≃ₗᵢ[ℝ] Space d) :
    y ∈ singularSet (Q ⁻¹' E) ↔ Q y ∈ singularSet E := by
  rw [mem_singularSet, mem_singularSet,
    mem_measureTheoreticBoundary_preimage_linearIsometryEquiv_iff E Q y,
    isC1BoundaryPoint_preimage_linearIsometryEquiv_iff Q]

/-! ### 4. Regular points are boundary points; tangent cones at regular points -/

/-- `C¹` boundary points lie in the measure-theoretic boundary. -/
theorem IsC1BoundaryPoint.mem_measureTheoreticBoundary {d : ℕ} {E : Set (Space d)}
    {x : Space d} (h : IsC1BoundaryPoint E x) : x ∈ measureTheoreticBoundary E := by
  obtain ⟨F, r, hr, hF, hFx, hdF, hae⟩ := h
  have hFd : HasFDerivAt F (fderiv ℝ F x) x := hasFDerivAt_of_contDiffOn_ball hF (mem_ball_self hr)
  obtain ⟨w, hw⟩ : ∃ w, 0 < fderiv ℝ F x w := by
    by_contra hcon
    push Not at hcon
    apply hdF
    ext v
    have h1 := hcon v
    have h2 := hcon (-v)
    rw [map_neg] at h2
    have h3 : fderiv ℝ F x v = 0 := by linarith
    simpa using h3
  -- along `t = (n + 1)⁻¹`, the difference quotients converge to `± F' w`
  have hc : Tendsto (fun n : ℕ ↦ ‖((n : ℝ) + 1)‖) atTop atTop := by
    refine (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
  have hlimP := hFd.lim w hc
  have hlimN := hFd.lim (-w) hc
  rw [map_neg] at hlimN
  simp only [hFx, sub_zero] at hlimP hlimN
  have hsmall : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ (one_div _)
  have hcont : ContinuousOn F (ball x r) := hF.continuousOn
  intro ρ hρ
  set ρ' := min ρ r with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ hr
  have hpt : ∀ v : Space d, ∀ᶠ n : ℕ in atTop, x + ((n : ℝ) + 1)⁻¹ • v ∈ ball x ρ' := by
    intro v
    have h1 : Tendsto (fun n : ℕ ↦ x + ((n : ℝ) + 1)⁻¹ • v) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hsmall.smul_const v)
    exact h1.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ'pos))
  have hpos_ev := hlimP.eventually (lt_mem_nhds hw)
  have hneg_ev := hlimN.eventually (gt_mem_nhds (by linarith : -(fderiv ℝ F x w) < 0))
  obtain ⟨n, hn₁, hn₂, hn₃, hn₄⟩ := ((hpt w).and (hpos_ev.and ((hpt (-w)).and hneg_ev))).exists
  have hρ'ρ : ball x ρ' ⊆ ball x ρ := ball_subset_ball (min_le_left _ _)
  have hρ'r : ball x ρ' ⊆ ball x r := ball_subset_ball (min_le_right _ _)
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · -- a small ball where `F > 0` lies a.e. in `E`
    have hFq : 0 < F (x + ((n : ℝ) + 1)⁻¹ • w) := by
      rw [smul_eq_mul] at hn₂
      exact pos_of_mul_pos_right hn₂ hn0.le
    obtain ⟨δ, hδ, hδsub, hδpos⟩ := exists_ball_pos_of_continuousOn hcont (hρ'r hn₁) hFq
    obtain ⟨δ', hδ', hδ'sub⟩ : ∃ δ' > 0, ball (x + ((n : ℝ) + 1)⁻¹ • w) δ' ⊆
        ball (x + ((n : ℝ) + 1)⁻¹ • w) δ ∩ ball x ρ' := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.inter isOpen_ball)
        _ ⟨mem_ball_self hδ, hn₁⟩
      exact ⟨ε, hε, hεsub⟩
    refine volume_inter_ne_zero_of_ae_ball hδ' (fun z hz ↦ hρ'ρ (hδ'sub hz).2) ?_
    filter_upwards [hae] with z hz hzB
    exact (hz (hδsub (hδ'sub hzB).1)).mpr (hδpos z (hδ'sub hzB).1)
  · have hFq : F (x + ((n : ℝ) + 1)⁻¹ • -w) < 0 := by
      rw [smul_eq_mul] at hn₄
      by_contra hge
      push Not at hge
      have := mul_nonneg hn0.le hge
      linarith
    obtain ⟨δ, hδ, hδsub, hδneg⟩ := exists_ball_neg_of_continuousOn hcont (hρ'r hn₃) hFq
    obtain ⟨δ', hδ', hδ'sub⟩ : ∃ δ' > 0, ball (x + ((n : ℝ) + 1)⁻¹ • -w) δ' ⊆
        ball (x + ((n : ℝ) + 1)⁻¹ • -w) δ ∩ ball x ρ' := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.inter isOpen_ball)
        _ ⟨mem_ball_self hδ, hn₃⟩
      exact ⟨ε, hε, hεsub⟩
    have h := volume_inter_ne_zero_of_ae_ball (E := Eᶜ) (B := ball x ρ) hδ'
      (fun z hz ↦ hρ'ρ (hδ'sub hz).2) ?_
    · rwa [inter_comm, ← sdiff_eq] at h
    filter_upwards [hae] with z hz hzB hzE
    have := (hz (hδsub (hδ'sub hzB).1)).mp hzE
    have := hδneg z (hδ'sub hzB).1
    linarith

theorem positiveHalfspace_smul_of_pos {d : ℕ} {c : ℝ} (hc : 0 < c) (e : Space d) :
    positiveHalfspace (c • e) = positiveHalfspace e := by
  ext y
  show 0 < inner ℝ (c • e) y ↔ 0 < inner ℝ e y
  rw [real_inner_smul_left]
  exact ⟨fun h ↦ pos_of_mul_pos_right h hc.le, fun h ↦ mul_pos hc h⟩

private theorem gradient_ne_zero_aux {d : ℕ} {F : Space d → ℝ} {x : Space d}
    (hdF : fderiv ℝ F x ≠ 0) : gradient F x ≠ 0 := by
  intro h0
  apply hdF
  have h1 : InnerProductSpace.toDual ℝ (Space d) (gradient F x) = fderiv ℝ F x := by
    simp [gradient]
  rw [← h1, h0, map_zero]

/-- **Blow-ups at a `C¹` boundary point, with the chart normal.** If near `x` the set `E` is a.e.
the positivity set of a `C¹` defining function `F` with `F x = 0` and `F' x ≠ 0`, then along
every scale sequence the blow-ups of `E` at `x` converge in `L¹_loc` to the half-space with inner
normal `∇F x`. -/
theorem isBlowupLimit_positiveHalfspace_gradient {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) {x : Space d} {F : Space d → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ContDiffOn ℝ 1 F (ball x ρ)) (hFx : F x = 0) (hdF : fderiv ℝ F x ≠ 0)
    (hae : ∀ᵐ y ∂volume, y ∈ ball x ρ → (y ∈ E ↔ 0 < F y)) {r : ℕ → ℝ}
    (hr_pos : ∀ j, 0 < r j) (hr : Tendsto r atTop (𝓝 0)) :
    IsBlowupLimit E x r (positiveHalfspace (gradient F x)) := by
  set L := fderiv ℝ F x with hLdef
  have hFd : HasFDerivAt F L x := hasFDerivAt_of_contDiffOn_ball hF (mem_ball_self hρ)
  set g : Space d := gradient F x with hgdef
  have hg : ∀ y, inner ℝ g y = L y := fun y ↦ by
    simp [hgdef, hLdef, gradient]
  have hg0 : g ≠ 0 := gradient_ne_zero_aux hdF
  have hHe : ∀ y, y ∈ positiveHalfspace g ↔ 0 < L y := fun y ↦ by
    show 0 < inner ℝ g y ↔ _
    rw [hg]
  refine ⟨hr_pos, hr, fun K hK ↦ ?_⟩
  set H := positiveHalfspace g with hHdef
  have hHmeas : MeasurableSet H := (isOpen_positiveHalfspace g).measurableSet
  have hEj : ∀ j, MeasurableSet ((fun z ↦ x + r j • z) ⁻¹' E) := fun j ↦
    hE.preimage (by fun_prop)
  have hae_all : ∀ᵐ y ∂volume, ∀ j : ℕ,
      x + r j • y ∈ ball x ρ → (x + r j • y ∈ E ↔ 0 < F (x + r j • y)) := by
    rw [ae_all_iff]
    intro j
    exact ae_comp_add_smul_aux hae x (hr_pos j).ne'
  have hhyp : ∀ᵐ y ∂volume, L y ≠ 0 := by
    have h0 := volume_orthogonal_hyperplane_eq_zero hg0
    have hset : {y : Space d | ¬ L y ≠ 0} = {y : Space d | inner ℝ g y = 0} := by
      ext y
      simp only [mem_ofPred_eq, not_not, hg]
    rw [ae_iff, hset]
    exact h0
  have hrinv : Tendsto (fun j ↦ ‖(r j)⁻¹‖) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hr, Eventually.of_forall hr_pos⟩
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun j ↦ ?_
    simp [Real.norm_of_nonneg (inv_nonneg.mpr (hr_pos j).le)]
  have hpt : ∀ᵐ y ∂volume, Tendsto (fun j ↦
      ‖((fun z ↦ x + r j • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
        H.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0) := by
    filter_upwards [hae_all, hhyp] with y hy hLy
    have hball : ∀ᶠ j in atTop, x + r j • y ∈ ball x ρ := by
      have h1 : Tendsto (fun j ↦ x + r j • y) atTop (𝓝 x) := by
        simpa using tendsto_const_nhds.add (hr.smul_const y)
      exact h1.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))
    have hsign : Tendsto (fun j ↦ (r j)⁻¹ * F (x + r j • y)) atTop (𝓝 (L y)) := by
      refine (hFd.lim y hrinv).congr fun j ↦ ?_
      simp [hFx, smul_eq_mul]
    refine tendsto_const_nhds.congr' ?_
    rcases lt_or_gt_of_ne hLy with hneg | hpos
    · filter_upwards [hball, hsign.eventually (gt_mem_nhds hneg)] with j hj1 hj2
      have hFneg : F (x + r j • y) < 0 := by
        have := mul_neg_of_pos_of_neg (hr_pos j) hj2
        rwa [← mul_assoc, mul_inv_cancel₀ (hr_pos j).ne', one_mul] at this
      have h1 : y ∉ (fun z ↦ x + r j • z) ⁻¹' E := fun hmem ↦ by
        have := (hy j hj1).mp hmem
        linarith
      have h2 : y ∉ H := fun hmem ↦ by
        have := (hHe y).mp hmem
        linarith
      simp [h1, h2]
    · filter_upwards [hball, hsign.eventually (lt_mem_nhds hpos)] with j hj1 hj2
      have hFpos : 0 < F (x + r j • y) := by
        have := mul_pos (hr_pos j) hj2
        rwa [← mul_assoc, mul_inv_cancel₀ (hr_pos j).ne', one_mul] at this
      have h1 : y ∈ (fun z ↦ x + r j • z) ⁻¹' E := (hy j hj1).mpr hFpos
      have h2 : y ∈ H := (hHe y).mpr hpos
      simp [h1, h2]
  set Φ : ℕ → Space d → ℝ := fun j y ↦
    ‖((fun z ↦ x + r j • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
      H.indicator (fun _ ↦ (1 : ℝ)) y‖ with hΦ
  have hΦmeas : ∀ j, AEStronglyMeasurable (Φ j) (volume.restrict K) := fun j ↦
    (((measurable_const.indicator (hEj j)).sub
      (measurable_const.indicator hHmeas)).norm).aestronglyMeasurable
  have hΦbound : ∀ j, ∀ᵐ y ∂(volume.restrict K), ‖Φ j y‖ ≤ 1 := by
    intro j
    refine Eventually.of_forall fun y ↦ ?_
    simp only [hΦ, norm_norm]
    by_cases h1 : y ∈ (fun z ↦ x + r j • z) ⁻¹' E <;> by_cases h2 : y ∈ H <;>
      simp [h1, h2]
  have hdom : Tendsto (fun j ↦ ∫ y in K, Φ j y) atTop (𝓝 (∫ _ in K, (0 : ℝ))) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) hΦmeas
      (integrableOn_const hK.measure_lt_top.ne) hΦbound (ae_restrict_of_ae hpt)
  rwa [integral_zero] at hdom

/-- **Tangent cones at `C¹` boundary points.** At a `C¹` boundary point of a measurable set, the
blow-ups converge in `L¹_loc` to one fixed half-space along every scale sequence. -/
theorem IsC1BoundaryPoint.exists_isBlowupLimit_positiveHalfspace {d : ℕ} {E : Set (Space d)}
    {x : Space d} (h : IsC1BoundaryPoint E x) (hE : MeasurableSet E) :
    ∃ e : Space d, ‖e‖ = 1 ∧ ∀ r : ℕ → ℝ, (∀ j, 0 < r j) → Tendsto r atTop (𝓝 0) →
      IsBlowupLimit E x r (positiveHalfspace e) := by
  obtain ⟨F, ρ, hρ, hF, hFx, hdF, hae⟩ := h
  have hg0 := gradient_ne_zero_aux hdF
  have hgn : 0 < ‖gradient F x‖ := norm_pos_iff.mpr hg0
  refine ⟨‖gradient F x‖⁻¹ • gradient F x, ?_, fun r hr_pos hr ↦ ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgn.ne']
  · rw [positiveHalfspace_smul_of_pos (inv_pos.mpr hgn)]
    exact isBlowupLimit_positiveHalfspace_gradient hE hρ hF hFx hdF hae hr_pos hr

/-- **Every tangent cone at a `C¹` boundary point is the same half-space.** -/
theorem IsC1BoundaryPoint.exists_forall_isTangentCone {d : ℕ} {E : Set (Space d)}
    {x : Space d} (h : IsC1BoundaryPoint E x) (hE : MeasurableSet E) :
    ∃ e : Space d, ‖e‖ = 1 ∧
      ∀ T : Set (Space d), IsTangentCone E x T → T =ᵐ[volume] positiveHalfspace e := by
  obtain ⟨e, he, hlim⟩ := h.exists_isBlowupLimit_positiveHalfspace hE
  refine ⟨e, he, fun T hT ↦ ?_⟩
  obtain ⟨hTm, r, hr⟩ := hT
  exact hr.ae_eq (hlim r hr.1 hr.2.1) hE hTm (isOpen_positiveHalfspace e).measurableSet

/-! ### 5. The regular set is relatively open; the singular set is closed -/

/-- Boundary points near a `C¹` boundary point are `C¹` boundary points. -/
theorem IsC1BoundaryPoint.eventually {d : ℕ} {E : Set (Space d)} {x : Space d}
    (h : IsC1BoundaryPoint E x) :
    ∀ᶠ y in 𝓝 x, y ∈ measureTheoreticBoundary E → IsC1BoundaryPoint E y := by
  obtain ⟨F, r, hr, hF, hFx, hdF, hae⟩ := h
  have hcont : ContinuousOn F (ball x r) := hF.continuousOn
  have hdcont : ContinuousOn (fderiv ℝ F) (ball x r) :=
    hF.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hev1 : ∀ᶠ y in 𝓝 x, y ∈ ball x r := isOpen_ball.mem_nhds (mem_ball_self hr)
  have hev2 : ∀ᶠ y in 𝓝 x, fderiv ℝ F y ≠ 0 :=
    (hdcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).eventually
      (isOpen_ne.mem_nhds hdF)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ ball x r ∧ fderiv ℝ F y ≠ 0 := hev1.and hev2
  filter_upwards [hev] with y ⟨hyB, hdy⟩ hyBd
  have hFy : F y = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · obtain ⟨δ, hδ, hδsub, hδneg⟩ := exists_ball_neg_of_continuousOn hcont hyB hneg
      apply (hyBd δ hδ).1
      refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp hae)
      intro hz'
      have := (hz' (hδsub hz.2)).mp hz.1
      have := hδneg z hz.2
      linarith
    · obtain ⟨δ, hδ, hδsub, hδpos⟩ := exists_ball_pos_of_continuousOn hcont hyB hpos
      apply (hyBd δ hδ).2
      refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp hae)
      intro hz'
      exact hz.2 ((hz' (hδsub hz.1)).mpr (hδpos z hz.1))
  have hr' : 0 < r - dist y x := sub_pos.mpr (mem_ball.mp hyB)
  have hsub : ball y (r - dist y x) ⊆ ball x r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    linarith [dist_triangle z y x]
  refine ⟨F, r - dist y x, hr', hF.mono hsub, hFy, hdy, ?_⟩
  filter_upwards [hae] with z hz hzB
  exact hz (hsub hzB)

/-- The singular set is closed. -/
theorem isClosed_singularSet {d : ℕ} (E : Set (Space d)) : IsClosed (singularSet E) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxBd : x ∈ measureTheoreticBoundary E
  · have hreg : IsC1BoundaryPoint E x := by
      by_contra hn
      exact hx ⟨hxBd, hn⟩
    filter_upwards [hreg.eventually] with y hy hyS
    exact hyS.2 (hy hyS.1)
  · have hopen : IsOpen (measureTheoreticBoundary E)ᶜ :=
      (isClosed_measureTheoreticBoundary E).isOpen_compl
    filter_upwards [hopen.mem_nhds hxBd] with y hy hyS
    exact hy hyS.1

/-! ### 6. Half-spaces -/

theorem measureTheoreticBoundary_positiveHalfspace_subset {d : ℕ} (e : Space d) :
    measureTheoreticBoundary (positiveHalfspace e) ⊆ {x | inner ℝ e x = 0} := by
  intro x hx
  by_contra hne
  rcases lt_or_gt_of_ne (show inner ℝ e x ≠ 0 from hne) with hneg | hpos
  · have hopen : IsOpen {y : Space d | inner ℝ e y < 0} :=
      isOpen_lt (continuous_const.inner continuous_id) continuous_const
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hopen x hneg
    apply (hx δ hδ).1
    refine measure_mono_null (fun y hy ↦ ?_) measure_empty
    have h1 : 0 < inner ℝ e y := hy.1
    have h2 : inner ℝ e y < 0 := hδsub hy.2
    linarith
  · obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (isOpen_positiveHalfspace e) x hpos
    apply (hx δ hδ).2
    refine measure_mono_null (fun y hy ↦ ?_) measure_empty
    exact hy.2 (hδsub hy.1)

/-- Points of the boundary hyperplane are `C¹` boundary points of any set a.e. equal to the
half-space. -/
theorem isC1BoundaryPoint_of_ae_eq_positiveHalfspace {d : ℕ} {E : Set (Space d)}
    {e : Space d} (he : e ≠ 0) (hE : E =ᵐ[volume] positiveHalfspace e) {x : Space d}
    (hx : inner ℝ e x = 0) : IsC1BoundaryPoint E x := by
  have hd : HasFDerivAt (fun y : Space d ↦ inner ℝ e y) (innerSL ℝ e) x :=
    (innerSL ℝ e).hasFDerivAt
  refine ⟨fun y ↦ inner ℝ e y, 1, one_pos, (innerSL ℝ e).contDiff.contDiffOn, hx, ?_, ?_⟩
  · rw [hd.fderiv]
    intro h0
    have h1 := congrArg (fun L : Space d →L[ℝ] ℝ ↦ L e) h0
    have h2 : inner ℝ e e = 0 := by simpa using h1
    exact he (inner_self_eq_zero.mp h2)
  · filter_upwards [hE] with y hy _
    exact Iff.of_eq hy

/-- Sets which are a.e. half-spaces have empty singular set. -/
theorem singularSet_eq_empty_of_ae_eq_positiveHalfspace {d : ℕ} {E : Set (Space d)}
    {e : Space d} (he : e ≠ 0) (hE : E =ᵐ[volume] positiveHalfspace e) :
    singularSet E = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ hx.2 ?_
  have hxBd' : x ∈ measureTheoreticBoundary (positiveHalfspace e) := by
    rw [← measureTheoreticBoundary_congr_ae hE]
    exact hx.1
  exact isC1BoundaryPoint_of_ae_eq_positiveHalfspace he hE
    (measureTheoreticBoundary_positiveHalfspace_subset e hxBd')

/-! ### 7. Graph charts -/

/-- A rotated `C¹` graph chart around `x` gives a `C¹` boundary point. -/
theorem isC1BoundaryPoint_of_graph {k : ℕ} {E : Set (Space (k + 1))} {x : Space (k + 1)}
    (Q : Space (k + 1) ≃ₗᵢ[ℝ] Space (k + 1)) {φ : Space k → ℝ} {r : ℝ} (hr : 0 < r)
    (hφ : ContDiffOn ℝ 1 φ (ball 0 r)) (hφ0 : φ 0 = 0)
    (hchart : ∀ᵐ y ∂volume, y ∈ ball x r →
      (y ∈ E ↔ φ (horizontal (Q.symm (y - x))) < Q.symm (y - x) (Fin.last k))) :
    IsC1BoundaryPoint E x := by
  set G : Space (k + 1) → Space (k + 1) := fun y ↦ Q.symm (y - x) with hGdef
  set F : Space (k + 1) → ℝ := fun y ↦ G y (Fin.last k) - φ (horizontal (G y)) with hFdef
  have hGc : ContDiff ℝ 1 G :=
    Q.symm.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const)
  have hmaps : MapsTo (fun y ↦ horizontal (G y)) (ball x r) (ball 0 r) := by
    intro y hy
    rw [mem_ball, dist_zero_right]
    refine (norm_horizontal_le_norm_aux _).trans_lt ?_
    rw [hGdef, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
    exact hy
  have hFc : ContDiffOn ℝ 1 F (ball x r) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last k)).contDiff.comp hGc).contDiffOn.sub
      (hφ.comp (horizontalContinuousLinearMap.contDiff.comp hGc).contDiffOn hmaps)
  have hGx : G x = 0 := by simp [hGdef]
  refine ⟨F, r, hr, hFc, by simp [hFdef, hGx, hφ0, horizontal_zero_aux], ?_, ?_⟩
  · -- the derivative in the direction `Q (verticalDirection k)` is one
    have hGd : HasFDerivAt G ((Q.symm.toContinuousLinearEquiv : Space (k + 1) →L[ℝ] _).comp
        (ContinuousLinearMap.id ℝ (Space (k + 1)))) x :=
      Q.symm.toContinuousLinearEquiv.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    have hφd : HasFDerivAt φ (fderiv ℝ φ 0) 0 :=
      hasFDerivAt_of_contDiffOn_ball hφ (mem_ball_self hr)
    have hφd' : HasFDerivAt φ (fderiv ℝ φ (horizontal (G x))) (horizontal (G x)) := by
      rw [hGx, horizontal_zero_aux]
      exact hφd
    have hFd := ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last k)).hasFDerivAt.comp x hGd).sub
      (hφd'.comp x (horizontalContinuousLinearMap.hasFDerivAt.comp x hGd))
    have hFd' : HasFDerivAt F
        ((EuclideanSpace.proj (Fin.last k)).comp ((Q.symm.toContinuousLinearEquiv :
            Space (k + 1) →L[ℝ] Space (k + 1)).comp (ContinuousLinearMap.id ℝ (Space (k + 1)))) -
          (fderiv ℝ φ (horizontal (G x))).comp (horizontalContinuousLinearMap.comp
            ((Q.symm.toContinuousLinearEquiv : Space (k + 1) →L[ℝ] Space (k + 1)).comp
              (ContinuousLinearMap.id ℝ (Space (k + 1)))))) x := hFd
    rw [hFd'.fderiv]
    intro h0
    have h1 := congrArg (fun L : Space (k + 1) →L[ℝ] ℝ ↦ L (Q (verticalDirection k))) h0
    have hh : horizontalContinuousLinearMap (verticalDirection k) = 0 :=
      horizontal_verticalDirection k
    simp [hh] at h1
  · filter_upwards [hchart] with y hy hyB
    rw [hy hyB]
    simp only [hFdef, hGdef, sub_pos]

/-! ### 8. Cylinders -/

/-- `C¹` boundary points of a horizontal set lift to its cylinder. -/
theorem IsC1BoundaryPoint.preimage_horizontal {k : ℕ} {A : Set (Space k)} {y : Space k}
    (h : IsC1BoundaryPoint A y) (t : ℝ) :
    IsC1BoundaryPoint (horizontal ⁻¹' A : Set (Space (k + 1))) (point y t) := by
  obtain ⟨F, r, hr, hF, hFy, hdF, hae⟩ := h
  have hmaps : MapsTo (horizontal : Space (k + 1) → Space k) (ball (point y t) r) (ball y r) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have h1 : horizontal z - y = horizontal (z - point y t) := by
      rw [horizontal_sub_aux, horizontal_point]
    rw [h1]
    exact (norm_horizontal_le_norm_aux _).trans_lt hz
  have hFd : HasFDerivAt F (fderiv ℝ F y) (horizontal (point y t)) := by
    rw [horizontal_point]
    exact hasFDerivAt_of_contDiffOn_ball hF (mem_ball_self hr)
  have hd := hFd.comp (point y t) (horizontalContinuousLinearMap (m := k)).hasFDerivAt
  refine ⟨F ∘ horizontal, r, hr, hF.comp horizontalContinuousLinearMap.contDiff.contDiffOn hmaps,
    by simp [hFy], ?_, ?_⟩
  · rw [hd.fderiv]
    intro h0
    apply hdF
    ext v
    have h1 := congrArg (fun L : Space (k + 1) →L[ℝ] ℝ ↦ L (point v 0)) h0
    simpa [horizontalContinuousLinearMap] using h1
  · filter_upwards [ae_comp_horizontal (k := k) hae] with z hz hzB
    exact hz (hmaps hzB)

/-- The measure-theoretic boundary of a cylinder lies over the boundary of its base. -/
theorem measureTheoreticBoundary_preimage_horizontal_subset {k : ℕ} (A : Set (Space k)) :
    measureTheoreticBoundary (horizontal ⁻¹' A : Set (Space (k + 1))) ⊆
      horizontal ⁻¹' measureTheoreticBoundary A := by
  intro x hx ρ hρ
  have hball : ∀ z : Space (k + 1), z ∈ ball x ρ → horizontal z ∈ ball (horizontal x) ρ := by
    intro z hz
    rw [mem_ball, dist_eq_norm, ← horizontal_sub_aux]
    exact (norm_horizontal_le_norm_aux _).trans_lt (by rwa [mem_ball, dist_eq_norm] at hz)
  constructor
  · intro h0
    apply (hx ρ hρ).1
    refine measure_mono_null (fun z hz ↦ ?_) (volume_preimage_horizontal_eq_zero (k := k) h0)
    exact ⟨hz.1, hball z hz.2⟩
  · intro h0
    apply (hx ρ hρ).2
    refine measure_mono_null (fun z hz ↦ ?_) (volume_preimage_horizontal_eq_zero (k := k) h0)
    exact ⟨hball z hz.1, hz.2⟩

/-- The singular set of a cylinder lies over the singular set of its base. -/
theorem singularSet_preimage_horizontal_subset {k : ℕ} (A : Set (Space k)) :
    singularSet (horizontal ⁻¹' A : Set (Space (k + 1))) ⊆ horizontal ⁻¹' singularSet A := by
  intro x hx
  refine ⟨measureTheoreticBoundary_preimage_horizontal_subset A hx.1, fun hreg ↦ hx.2 ?_⟩
  have h := hreg.preimage_horizontal (x (Fin.last k))
  rwa [point_horizontal_last] at h

end SerrinEpigraph
