module

public import SerrinEpigraph.PerimeterLocality
public import SerrinEpigraph.PlaneTiltPerimeter
public import SerrinEpigraph.VectorIntegrationByParts
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Local perimeter minimizers, invariance, and local Radon representations

This module defines `IsLocalPerimeterMinimizer` on arbitrary open subsets of `Space d` and proves:
- invariance of `variationalPerimeter` under complementation and affine translations/dilations
  (orthogonal invariance `variationalPerimeter_preimage_isometry` is re-exported from
  `PlaneTiltPerimeter`);
- stability of `IsLocalPerimeterMinimizer` under basis change, open restriction, complementation,
  null-set modification, affine rescaling, and orthogonal transformations;
- constructor from global `univ` compact-perturbation minimality and integer-ball finiteness;
- existence of a finite Radon perimeter measure and unit polar vector field on an open neighborhood
  of every closed ball contained in the domain.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported ENNReal Pointwise

namespace SerrinEpigraph

/-- A measurable set `E` locally minimizes variational perimeter in an open domain `Ω` if its
perimeter is finite on every ball compactly contained in `Ω` and does not exceed the perimeter
of any measurable competitor agreeing with `E` a.e. outside a compact subset of an open
comparison region `U ⊆ Ω`. -/
structure IsLocalPerimeterMinimizer {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E Ω : Set (Space d)) : Prop where
  measurableSet : MeasurableSet E
  isOpen_domain : IsOpen Ω
  perimeter_ball_ne_top : ∀ x₀ r, 0 < r → closedBall x₀ r ⊆ Ω →
    variationalPerimeter b E (ball x₀ r) ≠ ⊤
  minimizes : ∀ U D K, IsOpen U → U ⊆ Ω → MeasurableSet D →
    IsCompact K → K ⊆ U → (∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
    variationalPerimeter b E U ≤ variationalPerimeter b D U

/-- Enlarging a closed ball inside an open set while staying inside the open set. -/
theorem exists_pos_closedBall_add_subset_open {d : ℕ} {x₀ : Space d} {r : ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hsub : closedBall x₀ r ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ closedBall x₀ (r + δ) ⊆ Ω := by
  let K' := closedBall x₀ (r + 1) \ Ω
  have hK' : IsCompact K' := (isCompact_closedBall x₀ (r + 1)).diff hΩ
  rcases K'.eq_empty_or_nonempty with hK'e | hK'ne
  · refine ⟨1, zero_lt_one, fun y hy ↦ ?_⟩
    by_contra hyΩ
    have hyK' : y ∈ K' := ⟨hy, hyΩ⟩
    rw [hK'e] at hyK'
    exact hyK'
  · obtain ⟨y₀, hy₀, hmin⟩ :=
      hK'.exists_isMinOn hK'ne (continuous_id.dist continuous_const).continuousOn
    have hy₀_not : y₀ ∉ closedBall x₀ r := fun h ↦ hy₀.2 (hsub h)
    have hr_lt : r < dist y₀ x₀ := lt_of_not_ge (by simpa [mem_closedBall] using hy₀_not)
    have hy₀_le : dist y₀ x₀ ≤ r + 1 := mem_closedBall.mp hy₀.1
    refine ⟨(dist y₀ x₀ - r) / 2, by linarith, fun y hy ↦ ?_⟩
    have hydist : dist y x₀ ≤ r + (dist y₀ x₀ - r) / 2 := mem_closedBall.mp hy
    have hy1 : y ∈ closedBall x₀ (r + 1) := mem_closedBall.mpr (by linarith)
    by_contra hyΩ
    have hle : dist y₀ x₀ ≤ dist y x₀ := hmin ⟨hy1, hyΩ⟩
    linarith

/-! ### Complement and affine-rescaling invariance of variational perimeter -/

/-- A `C¹` compactly supported vector field has zero total divergence over `Space d`. -/
theorem integral_fieldDivergence_eq_zero {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {F : Space d → Space d}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    (∫ x, fieldDivergence b F x) = 0 := by
  obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hc
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let φ : ContDiffBump (0 : Space d) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := by linarith }
  have hφ_grad_zero : (∫ x, inner ℝ (F x) (gradient φ x)) = 0 := by
    apply integral_eq_zero_of_ae
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ ball (0 : Space d) R
    · have hev : (φ : Space d → ℝ) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
        filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact φ.one_of_mem_closedBall (ball_subset_closedBall hy)
      simp [gradient, hev.fderiv_eq]
    · have hxnot : x ∉ tsupport F := fun hts ↦ hx (hn hts)
      simp [image_eq_zero_of_notMem_tsupport hxnot]
  have hibp := integral_inner_field_gradient (μ := volume) isOpen_univ hF.contDiffOn
    (φ.contDiff (n := 1)) φ.hasCompactSupport (subset_univ _) b
  rw [hφ_grad_zero] at hibp
  have hsum_zero : (∫ x, (∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i)) * φ x) = 0 := by
    linarith
  have heq : (fun x ↦ fieldDivergence b F x) =
      fun x ↦ (∑ i, inner ℝ (fderiv ℝ F x (b i)) (b i)) * φ x := by
    funext x
    by_cases hx : x ∈ tsupport F
    · have hφ1 : φ x = 1 := φ.one_of_mem_closedBall (ball_subset_closedBall (hn hx))
      rw [hφ1, mul_one]
      unfold fieldDivergence
      exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm (fderiv ℝ F x (b i)) (b i)
    · have hz : fderiv ℝ F x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [fieldDivergence, hz]
  rw [heq, hsum_zero]

/-- Variational perimeter is invariant under taking the set-theoretic complement. -/
theorem variationalPerimeter_compl {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (Ω : Set (Space d)) :
    variationalPerimeter b Eᶜ Ω = variationalPerimeter b E Ω := by
  unfold variationalPerimeter
  refine iSup_congr fun F ↦ iSup_congr fun hF ↦ iSup_congr fun hc ↦
    iSup_congr fun _ ↦ iSup_congr fun _ ↦ ?_
  have hcont := fieldDivergence_continuous b hF
  have hsupp : tsupport (fieldDivergence b F) ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b F hn)
  have hdiv_c : HasCompactSupport (fieldDivergence b F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hdiv_int : Integrable (fieldDivergence b F) volume :=
    hcont.integrable_of_hasCompactSupport hdiv_c
  have hE_int : Integrable (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x)
      volume := by
    have heq : (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        E.indicator (fieldDivergence b F) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [heq]
    exact hdiv_int.indicator hE
  have hpoint : (fun x ↦ Eᶜ.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      fun x ↦ fieldDivergence b F x -
        E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [hpoint, integral_sub hdiv_int hE_int, integral_fieldDivergence_eq_zero b hF hc,
    zero_sub, norm_neg]

@[simp]
theorem variationalPerimeter_univ {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Ω : Set (Space d)) :
    variationalPerimeter b univ Ω = 0 := by
  rw [← compl_empty, variationalPerimeter_compl b MeasurableSet.empty Ω]
  unfold variationalPerimeter
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Scaling law of variational perimeter under affine map `y ↦ x₀ + r • y` (`r > 0`, `1 ≤ d`). -/
theorem variationalPerimeter_image_add_smul {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E U : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b E ((fun y ↦ x₀ + r • y) '' U) =
      ENNReal.ofReal (r ^ (d - 1)) *
        variationalPerimeter b ((fun y ↦ x₀ + r • y) ⁻¹' E) U := by
  let T : Space d → Space d := fun y ↦ x₀ + r • y
  let S : Space d → Space d := fun x ↦ r⁻¹ • (x - x₀)
  have hT_contDiff : ContDiff ℝ 1 T := by fun_prop
  have hS_contDiff : ContDiff ℝ 1 S := by fun_prop
  have hST (y : Space d) : S (T y) = y := by
    simp [T, S, hr.ne']
  have hTS (x : Space d) : T (S x) = x := by
    simp [T, S, smul_smul, mul_inv_cancel₀ hr.ne']
  have himg_eq : T '' U = S ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hST] using hy
    · intro hx
      exact ⟨S x, hx, hTS x⟩
  have hpow : r ^ d * r⁻¹ = r ^ (d - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
    simp [pow_succ, hr.ne']
  have hident (G : Space d → Space d) (hG : ContDiff ℝ 1 G) :
      (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b (fun z ↦ G (S z)) x) =
        r ^ (d - 1) *
          ∫ y, (T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y := by
    have hdiv_comp (y : Space d) :
        fieldDivergence b (fun z ↦ G (S z)) (T y) = r⁻¹ * fieldDivergence b G y := by
      have hS_fderiv : HasFDerivAt S (r⁻¹ • ContinuousLinearMap.id ℝ (Space d)) (T y) :=
        ((hasFDerivAt_id (T y)).sub_const x₀).const_smul r⁻¹
      have hG_fderiv : HasFDerivAt G (fderiv ℝ G y) (S (T y)) := by
        rw [hST]
        exact (hG.differentiable_one y).hasFDerivAt
      have hcomp := (hG_fderiv.comp (T y) hS_fderiv).fderiv
      change ∑ i, inner ℝ (b i) (fderiv ℝ (G ∘ S) (T y) (b i)) = _
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply, ContinuousLinearMap.comp_id,
        smul_apply, real_inner_smul_right, ← Finset.mul_sum]
      rfl
    have htrans := integral_add_left_eq_self (μ := volume)
      (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence b (fun z ↦ G (S z)) x) x₀
    have hdil := Measure.integral_comp_smul (μ := volume)
      (f := fun u : Space d ↦ E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + u) *
        fieldDivergence b (fun z ↦ G (S z)) (x₀ + u)) r
    simp only [Space, finrank_euclideanSpace_fin, abs_inv, abs_pow,
      abs_of_pos hr, smul_eq_mul] at hdil
    have hdil' : (∫ u : Space d, E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + u) *
        fieldDivergence b (fun z ↦ G (S z)) (x₀ + u)) =
        r ^ d * ∫ y : Space d, E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + r • y) *
          fieldDivergence b (fun z ↦ G (S z)) (x₀ + r • y) := by
      have hrd : r ^ d ≠ 0 := (pow_pos hr d).ne'
      calc
        _ = r ^ d * ((r ^ d)⁻¹ * ∫ u : Space d, E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + u) *
            fieldDivergence b (fun z ↦ G (S z)) (x₀ + u)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hrd, one_mul]
        _ = _ := by rw [← hdil]
    rw [← htrans, hdil']
    have hintegrand : (fun y : Space d ↦
        E.indicator (fun _ ↦ (1 : ℝ)) (x₀ + r • y) *
          fieldDivergence b (fun z ↦ G (S z)) (x₀ + r • y)) =
        fun y ↦ r⁻¹ *
          ((T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y) := by
      funext y
      change E.indicator (fun _ ↦ (1 : ℝ)) (T y) *
        fieldDivergence b (fun z ↦ G (S z)) (T y) = _
      rw [hdiv_comp y]
      by_cases hy : y ∈ T ⁻¹' E
      · have hTy : T y ∈ E := hy
        simp [hy, hTy]
      · have hTy : T y ∉ E := hy
        simp [hy, hTy]
    rw [hintegrand, integral_const_mul, ← mul_assoc, hpow]
  apply le_antisymm
  · unfold variationalPerimeter
    refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦
      iSup_le fun hs ↦ iSup_le fun hunit ↦ ?_
    let G : Space d → Space d := F ∘ T
    have hG : ContDiff ℝ 1 G := hF.comp hT_contDiff
    have hFG : F = fun z ↦ G (S z) := by
      funext z
      simp [G, hTS]
    have htsG_sub : tsupport G ⊆ T ⁻¹' tsupport F :=
      tsupport_comp_subset_preimage F hT_contDiff.continuous
    have htsG : tsupport G ⊆ U := by
      intro y hy
      have hmem := hs (htsG_sub hy)
      rw [himg_eq] at hmem
      simpa [hST] using hmem
    have hcG : HasCompactSupport G := by
      have himgK : T ⁻¹' tsupport F = S '' tsupport F := by
        ext y
        constructor
        · intro hy
          exact ⟨T y, hy, hST y⟩
        · rintro ⟨x, hx, rfl⟩
          simpa [hTS] using hx
      refine (hc.image hS_contDiff.continuous).of_isClosed_subset (isClosed_tsupport G) ?_
      rwa [← himgK]
    have hunitG (y : Space d) : ‖G y‖ ≤ 1 := hunit (T y)
    have hint := hident G hG
    rw [← hFG] at hint
    rw [hint, norm_mul, Real.norm_of_nonneg (pow_nonneg hr.le _),
      ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    have hle_sup : ENNReal.ofReal ‖∫ y, (T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y *
        fieldDivergence b G y‖ ≤
        ⨆ (G' : Space d → Space d) (_ : ContDiff ℝ 1 G') (_ : HasCompactSupport G')
          (_ : tsupport G' ⊆ U) (_ : ∀ y, ‖G' y‖ ≤ 1),
          ENNReal.ofReal ‖∫ y, (T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y *
            fieldDivergence b G' y‖ :=
      le_iSup_of_le G (le_iSup_of_le hG (le_iSup_of_le hcG
        (le_iSup_of_le htsG (le_iSup_of_le hunitG le_rfl))))
    exact mul_le_mul_of_nonneg_left hle_sup zero_le
  · unfold variationalPerimeter
    simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun G ↦ iSup_le fun hG ↦ iSup_le fun hcG ↦
      iSup_le fun hsG ↦ iSup_le fun hunitG ↦ ?_
    let F : Space d → Space d := G ∘ S
    have hF : ContDiff ℝ 1 F := hG.comp hS_contDiff
    have htsF_sub : tsupport F ⊆ S ⁻¹' tsupport G :=
      tsupport_comp_subset_preimage G hS_contDiff.continuous
    have hsF : tsupport F ⊆ T '' U := by
      rw [himg_eq]
      exact htsF_sub.trans (preimage_mono hsG)
    have hcF : HasCompactSupport F := by
      have himgK : S ⁻¹' tsupport G = T '' tsupport G := by
        ext x
        constructor
        · intro hx
          exact ⟨S x, hx, hTS x⟩
        · rintro ⟨y, hy, rfl⟩
          simpa [hST] using hy
      refine (hcG.image hT_contDiff.continuous).of_isClosed_subset (isClosed_tsupport F) ?_
      rwa [← himgK]
    have hunitF (x : Space d) : ‖F x‖ ≤ 1 := hunitG (S x)
    have hint := hident G hG
    change (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) = _ at hint
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le _),
      ← Real.norm_of_nonneg (pow_nonneg hr.le (d - 1)), ← norm_mul, ← hint]
    exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hcF
      (le_iSup_of_le hsF (le_iSup_of_le hunitF le_rfl))))

/-- Equivalent preimage form of `variationalPerimeter_image_add_smul`. -/
theorem variationalPerimeter_preimage_add_smul {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E Ω : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b ((fun y ↦ x₀ + r • y) ⁻¹' E) ((fun y ↦ x₀ + r • y) ⁻¹' Ω) =
      ENNReal.ofReal ((r ^ (d - 1))⁻¹) * variationalPerimeter b E Ω := by
  have himg : (fun y : Space d ↦ x₀ + r • y) '' ((fun y ↦ x₀ + r • y) ⁻¹' Ω) = Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨r⁻¹ • (x - x₀), ?_, by simp [smul_smul, mul_inv_cancel₀ hr.ne']⟩
      simpa [smul_smul, mul_inv_cancel₀ hr.ne'] using hx
  have hscale := variationalPerimeter_image_add_smul hd b E
    ((fun y ↦ x₀ + r • y) ⁻¹' Ω) x₀ hr
  rw [himg] at hscale
  rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le _)),
    inv_mul_cancel₀ (pow_pos hr _).ne', ENNReal.ofReal_one, one_mul]

/-- Variational perimeter on balls under `y ↦ x₀ + r • y`. -/
theorem variationalPerimeter_preimage_add_smul_ball {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E : Set (Space d))
    (x₀ y₀ : Space d) {r ρ : ℝ} (hr : 0 < r) :
    variationalPerimeter b ((fun y ↦ x₀ + r • y) ⁻¹' E) (ball y₀ ρ) =
      ENNReal.ofReal ((r ^ (d - 1))⁻¹) *
        variationalPerimeter b E (ball (x₀ + r • y₀) (r * ρ)) := by
  have hball : (fun y : Space d ↦ x₀ + r • y) ⁻¹' ball (x₀ + r • y₀) (r * ρ) = ball y₀ ρ := by
    ext y
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  rw [← hball]
  exact variationalPerimeter_preimage_add_smul hd b E (ball (x₀ + r • y₀) (r * ρ)) x₀ hr

/-! ### Stability and Radon representation of `IsLocalPerimeterMinimizer` -/

theorem IsLocalPerimeterMinimizer.of_basis {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} (c : OrthonormalBasis (Fin d) ℝ (Space d))
    {E Ω : Set (Space d)} (h : IsLocalPerimeterMinimizer b E Ω) :
    IsLocalPerimeterMinimizer c E Ω where
  measurableSet := h.measurableSet
  isOpen_domain := h.isOpen_domain
  perimeter_ball_ne_top x₀ r hr hsub := by
    rw [variationalPerimeter_basis_independent c b]
    exact h.perimeter_ball_ne_top x₀ r hr hsub
  minimizes U D K hU hUΩ hD hK hKU hED := by
    rw [variationalPerimeter_basis_independent c b E U,
      variationalPerimeter_basis_independent c b D U]
    exact h.minimizes U D K hU hUΩ hD hK hKU hED

theorem IsLocalPerimeterMinimizer.mono {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω Ω' : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    IsLocalPerimeterMinimizer b E Ω' where
  measurableSet := h.measurableSet
  isOpen_domain := hΩ'
  perimeter_ball_ne_top x₀ r hr hcb := h.perimeter_ball_ne_top x₀ r hr (hcb.trans hsub)
  minimizes U D K hU hUΩ' hD hK hKU hED :=
    h.minimizes U D K hU (hUΩ'.trans hsub) hD hK hKU hED

theorem IsLocalPerimeterMinimizer.compl {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) :
    IsLocalPerimeterMinimizer b Eᶜ Ω where
  measurableSet := h.measurableSet.compl
  isOpen_domain := h.isOpen_domain
  perimeter_ball_ne_top x₀ r hr hcb := by
    rw [variationalPerimeter_compl b h.measurableSet]
    exact h.perimeter_ball_ne_top x₀ r hr hcb
  minimizes U D K hU hUΩ hD hK hKU hED := by
    rw [variationalPerimeter_compl b h.measurableSet U,
      ← variationalPerimeter_compl b hD U]
    refine h.minimizes U Dᶜ K hU hUΩ hD.compl hK hKU ?_
    filter_upwards [hED] with x hx hxK
    have hc := hx hxK
    constructor
    · intro hxE hxD
      exact (hc.mpr hxD) hxE
    · intro hxDc
      by_contra hxEc
      exact hxDc (hc.mp hxEc)

theorem IsLocalPerimeterMinimizer.congr_ae {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E E' Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) (hE' : MeasurableSet E')
    (hae : ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ E ↔ x ∈ E')) :
    IsLocalPerimeterMinimizer b E' Ω where
  measurableSet := hE'
  isOpen_domain := h.isOpen_domain
  perimeter_ball_ne_top x₀ r hr hcb := by
    have heq : variationalPerimeter b E' (ball x₀ r) = variationalPerimeter b E (ball x₀ r) := by
      apply variationalPerimeter_congr_ae_on b
      filter_upwards [hae] with x hx hxb
      exact (hx (hcb (ball_subset_closedBall hxb))).symm
    rw [heq]
    exact h.perimeter_ball_ne_top x₀ r hr hcb
  minimizes U D K hU hUΩ hD hK hKU hED := by
    have heq : variationalPerimeter b E' U = variationalPerimeter b E U := by
      apply variationalPerimeter_congr_ae_on b
      filter_upwards [hae] with x hx hxU
      exact (hx (hUΩ hxU)).symm
    rw [heq]
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    let D' : Set (Space d) := (D ∩ W) ∪ (E \ W)
    have hD' : MeasurableSet D' := (hD.inter hWo.measurableSet).union
      (h.measurableSet.diff hWo.measurableSet)
    have hED' : ∀ᵐ x ∂volume, x ∉ closure W → (x ∈ E ↔ x ∈ D') :=
      Eventually.of_forall fun x hx ↦ by
        have hxW : x ∉ W := fun hh ↦ hx (subset_closure hh)
        simp [D', hxW]
    have hD'_U : variationalPerimeter b D' U = variationalPerimeter b D U := by
      apply variationalPerimeter_congr_ae_on b
      filter_upwards [hae, hED] with x hxAE hxK hxU
      by_cases hxW : x ∈ W
      · simp [D', hxW]
      · have hxnotK : x ∉ K := fun hh ↦ hxW (hKW hh)
        have h1 := hxAE (hUΩ hxU)
        have h2 := hxK hxnotK
        simp [D', hxW, h1.trans h2]
    rw [← hD'_U]
    exact h.minimizes U D' (closure W) hU hUΩ hD' hWc hWU hED'

set_option backward.isDefEq.respectTransparency false in
theorem IsLocalPerimeterMinimizer.preimage_add_smul {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    IsLocalPerimeterMinimizer b ((fun y ↦ x₀ + r • y) ⁻¹' E)
      ((fun y ↦ x₀ + r • y) ⁻¹' Ω) where
  measurableSet := h.measurableSet.preimage (by fun_prop)
  isOpen_domain := h.isOpen_domain.preimage (by fun_prop)
  perimeter_ball_ne_top y₀ ρ hρ hcb := by
    rw [variationalPerimeter_preimage_add_smul_ball hd b E x₀ y₀ hr]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply h.perimeter_ball_ne_top (x₀ + r • y₀) (r * ρ) (mul_pos hr hρ)
    intro x hx
    have hy : r⁻¹ • (x - x₀) ∈ closedBall y₀ ρ := by
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      have hdiff : r⁻¹ • (x - x₀) - y₀ = r⁻¹ • (x - (x₀ + r • y₀)) := by
        have hy₀ : y₀ = r⁻¹ • (r • y₀) := by simp [smul_smul, inv_mul_cancel₀ hr.ne']
        nth_rw 1 [hy₀]
        rw [← smul_sub, sub_sub]
      rw [hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      exact (inv_mul_le_iff₀ hr).mpr hx
    simpa [smul_smul, mul_inv_cancel₀ hr.ne'] using hcb hy
  minimizes U D K hU hUΩ hD hK hKU hED := by
    let T : Space d → Space d := fun y ↦ x₀ + r • y
    let S : Space d → Space d := fun x ↦ r⁻¹ • (x - x₀)
    have hT_cont : Continuous T := by fun_prop
    have hS_cont : Continuous S := by fun_prop
    have hST (y : Space d) : S (T y) = y := by simp [T, S, hr.ne']
    have hTS (x : Space d) : T (S x) = x := by simp [T, S, smul_smul, mul_inv_cancel₀ hr.ne']
    have himgU : T '' U = S ⁻¹' U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [hST] using hy
      · intro hx
        exact ⟨S x, hx, hTS x⟩
    have hTU_open : IsOpen (T '' U) := by
      rw [himgU]
      exact hU.preimage hS_cont
    have hTU_sub : T '' U ⊆ Ω := by
      rintro _ ⟨y, hy, rfl⟩
      exact hUΩ hy
    have hSD_meas : MeasurableSet (S ⁻¹' D) := hD.preimage hS_cont.measurable
    have hTK_comp : IsCompact (T '' K) := hK.image hT_cont
    have hTK_sub : T '' K ⊆ T '' U := image_mono hKU
    have hpreD : T ⁻¹' (S ⁻¹' D) = D := by
      ext y
      simp [hST]
    have hae_img : ∀ᵐ x ∂volume, x ∉ T '' K → (x ∈ E ↔ x ∈ S ⁻¹' D) := by
      let Bset : Set (Space d) := {y | ¬(y ∉ K → (y ∈ T ⁻¹' E ↔ y ∈ D))}
      have hnull : volume Bset = 0 := by
        dsimp [Bset]
        rwa [← ae_iff]
      have hset : {x | ¬(x ∉ T '' K → (x ∈ E ↔ x ∈ S ⁻¹' D))} ⊆ T '' Bset := by
        intro x hx
        refine ⟨S x, ?_, hTS x⟩
        intro hh
        apply hx
        intro hxTK
        have hSK : S x ∉ K := fun hmem ↦ hxTK ⟨S x, hmem, hTS x⟩
        simpa [hTS] using hh hSK
      rw [ae_iff]
      apply measure_mono_null hset
      have hpre_smul : T '' Bset = (fun z ↦ -x₀ + z) ⁻¹' (r • Bset) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by dsimp [T]; abel⟩
        · rintro ⟨y, hy, hyz⟩
          refine ⟨y, hy, ?_⟩
          change r • y = -x₀ + z at hyz
          dsimp [T]
          rw [hyz]
          abel
      rw [hpre_smul, measure_preimage_add, Measure.addHaar_smul volume r, hnull, mul_zero]
    have hcomp := h.minimizes (T '' U) (S ⁻¹' D) (T '' K) hTU_open hTU_sub hSD_meas
      hTK_comp hTK_sub hae_img
    rw [variationalPerimeter_image_add_smul hd b E U x₀ hr,
      variationalPerimeter_image_add_smul hd b (S ⁻¹' D) U x₀ hr, hpreD] at hcomp
    have hpos : ENNReal.ofReal (r ^ (d - 1)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
    exact (ENNReal.mul_le_mul_iff_right hpos ENNReal.ofReal_ne_top).mp hcomp

theorem IsLocalPerimeterMinimizer.preimage_isometry {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) (Q : Space d ≃ₗᵢ[ℝ] Space d) :
    IsLocalPerimeterMinimizer b (Q ⁻¹' E) (Q ⁻¹' Ω) where
  measurableSet := h.measurableSet.preimage Q.continuous.measurable
  isOpen_domain := h.isOpen_domain.preimage Q.continuous
  perimeter_ball_ne_top y₀ r hr hcb := by
    have hball : ball y₀ r = Q ⁻¹' ball (Q y₀) r := by
      simp [Q.preimage_ball]
    rw [hball, variationalPerimeter_preimage_isometry b Q E (ball (Q y₀) r)]
    apply h.perimeter_ball_ne_top (Q y₀) r hr
    intro x hx
    have hy : Q.symm x ∈ closedBall y₀ r := by
      rw [mem_closedBall, dist_eq_norm, ← Q.norm_map, map_sub, Q.apply_symm_apply]
      simpa [mem_closedBall, dist_eq_norm] using hx
    simpa using hcb hy
  minimizes U D K hU hUΩ hD hK hKU hED := by
    have hU' : IsOpen (Q.symm ⁻¹' U) := hU.preimage Q.symm.continuous
    have hUΩ' : Q.symm ⁻¹' U ⊆ Ω := fun x hx ↦ by
      simpa using hUΩ hx
    have hD' : MeasurableSet (Q.symm ⁻¹' D) := hD.preimage Q.symm.continuous.measurable
    have hK' : IsCompact (Q.symm ⁻¹' K) := by
      have himg : Q.symm ⁻¹' K = Q '' K := by
        ext x
        constructor
        · intro hx
          exact ⟨Q.symm x, hx, Q.apply_symm_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
      rw [himg]
      exact hK.image Q.continuous
    have hKU' : Q.symm ⁻¹' K ⊆ Q.symm ⁻¹' U := fun x hx ↦ hKU hx
    have hae' : ∀ᵐ x ∂volume, x ∉ Q.symm ⁻¹' K → (x ∈ E ↔ x ∈ Q.symm ⁻¹' D) := by
      have hmp := Q.symm.measurePreserving.quasiMeasurePreserving.ae hED
      filter_upwards [hmp] with x hx hxK
      simpa using hx hxK
    have hcomp := h.minimizes (Q.symm ⁻¹' U) (Q.symm ⁻¹' D) (Q.symm ⁻¹' K)
      hU' hUΩ' hD' hK' hKU' hae'
    have hpreU : Q ⁻¹' (Q.symm ⁻¹' U) = U := by ext y; simp
    have hpreD : Q ⁻¹' (Q.symm ⁻¹' D) = D := by ext y; simp
    rw [← variationalPerimeter_preimage_isometry b Q E (Q.symm ⁻¹' U),
      ← variationalPerimeter_preimage_isometry b Q (Q.symm ⁻¹' D) (Q.symm ⁻¹' U),
      hpreU, hpreD] at hcomp
    exact hcomp

/-- Global `univ` local perimeter minimizer from integer-ball finiteness and open-set
compact-perturbation minimality. -/
theorem isLocalPerimeterMinimizer_univ {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E : Set (Space d)} (hE : MeasurableSet E)
    (hPE : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤)
    (hmin : ∀ U D K, IsOpen U → MeasurableSet D → IsCompact K → K ⊆ U →
      (∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E U ≤ variationalPerimeter b D U) :
    IsLocalPerimeterMinimizer b E univ where
  measurableSet := hE
  isOpen_domain := isOpen_univ
  perimeter_ball_ne_top x₀ r _ _ := by
    obtain ⟨n, hn⟩ := compact_subset_perimeter_ball (isCompact_closedBall x₀ r)
    exact ne_top_of_le_ne_top (hPE n)
      (variationalPerimeter_mono b E (ball_subset_closedBall.trans hn))
  minimizes U D K hU _ hD hK hKU hED := hmin U D K hU hD hK hKU hED

/-- On any closed ball `closedBall x₀ r ⊆ Ω`, a local perimeter minimizer admits an enlarged ball
`ball x₀ (r + δ) ⊆ Ω` carrying a finite Radon perimeter measure `μ` and unit polar vector `ν`
representing `D 1_E` on `ball x₀ (r + δ)`. -/
theorem IsLocalPerimeterMinimizer.exists_ball_radon_measure {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space d} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x₀ r ⊆ Ω) :
    ∃ (δ : ℝ) (μ : Measure (Space d)) (ν : Space d → Space d),
      0 < δ ∧ closedBall x₀ (r + δ) ⊆ Ω ∧
      IsFiniteMeasure μ ∧ μ (ball x₀ (r + δ))ᶜ = 0 ∧
      (∀ U, IsOpen U → U ⊆ ball x₀ (r + δ) → μ U = variationalPerimeter b E U) ∧
      Integrable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
        tsupport F ⊆ ball x₀ (r + δ) →
        -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
          ∫ x, inner ℝ (F x) (ν x) ∂μ := by
  obtain ⟨δ₀, hδ₀, hsub₀⟩ := exists_pos_closedBall_add_subset_open h.isOpen_domain hsub
  let δ : ℝ := δ₀ / 2
  have hδ : 0 < δ := half_pos hδ₀
  have hcb : closedBall x₀ (r + δ) ⊆ Ω :=
    (closedBall_subset_closedBall (by dsimp [δ]; linarith)).trans hsub₀
  have hP : variationalPerimeter b E (ball x₀ (r + δ)) ≠ ⊤ :=
    h.perimeter_ball_ne_top x₀ (r + δ) (by linarith) hcb
  obtain ⟨σ, hmass, -, hzero, hdist⟩ :=
    exists_perimeter_vector_measure_concentrated b h.measurableSet isOpen_ball.measurableSet hP
  let : IsFiniteMeasure σ.variation := ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hP⟩
  have hi := integrable_vectorPolarDensity b σ
  have hn := norm_vectorPolarDensity_ae b σ
  refine ⟨δ, σ.variation, vectorPolarDensity b σ, hδ, hcb, inferInstance, hzero,
    fun U hU hs ↦ variation_eq_variationalPerimeter_of_representation b σ hdist hU hs,
    hi, hn, fun F hF hs ↦ ?_⟩
  refine (hdist F hF hs).trans ?_
  nth_rw 1 [← withDensity_vectorPolarDensity b σ]
  exact integral_withDensity_inner_of_ae_bounded hi (hn.mono fun _ hh ↦ hh.le)
    F.continuous.measurable (norm_nonneg F.toBoundedContinuousFunction)
    F.toBoundedContinuousFunction.norm_coe_le_norm

end SerrinEpigraph
