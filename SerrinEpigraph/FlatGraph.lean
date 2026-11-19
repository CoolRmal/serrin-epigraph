module

public import SerrinEpigraph.FlatIteration
public import SerrinEpigraph.ExcessEpsilonRegularity

/-!
# The boundary of a flat configuration is a `C¹` graph (`GR13`)

The abstract input is a phase `E` whose measure-theoretic boundary over `B_{3/4}` lies in a thin
band `|t - a| ≤ δ`, with interior points above the band and exterior points below it, and which
admits at every boundary point `p` of the half cylinder a unit normal `n(p)` close to `e_n`
together with the scale-wise flatness `|⟪q - p, n(p)⟫| ≤ σ_k θ^k / 8` for boundary points
`‖q - p‖ ≤ θ^k / 32`, where `σ_k → 0`.

* `exists_boundary_on_vertical_line`, `eq_of_boundary_on_vertical_line`: every vertical line over
  `B_{3/4}` meets the boundary in the band, and over `B_{1/2}` in exactly one point.
* `volume_graph_eq_zero`: graphs of measurable functions are Lebesgue null.
* `isC1BoundaryPoint_of_flat_normals` (**`GR13`**): every boundary point of the half cylinder is
  a `C¹` boundary point: the boundary is the graph of a `C¹` function, obtained from the uniform
  first-order expansions given by the normals.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

theorem point_sub_point {m : ℕ} (y y' : Space m) (t t' : ℝ) :
    point y t - point y' t' = point (y - y') (t - t') := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]

theorem exists_pow_scale {θ s : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs : 0 < s) {K : ℕ}
    (hsK : s ≤ θ ^ K) : ∃ k, K ≤ k ∧ θ ^ (k + 1) < s ∧ s ≤ θ ^ k := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one hs
    (hsK.trans (pow_le_one₀ hθ0.le hθ1.le)) hθ0 hθ1
  refine ⟨n, ?_, h1, h2⟩
  by_contra hlt
  push Not at hlt
  have : θ ^ K ≤ θ ^ (n + 1) := pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
  linarith

/-- Graphs of measurable functions are Lebesgue null. -/
theorem volume_graph_eq_zero {m : ℕ} {f : Space m → ℝ} (hf : Measurable f) :
    volume {x : Space (m + 1) | x (Fin.last m) = f (horizontal x)} = 0 := by
  have hmp := measurePreserving_horizontal_last m
  set Γ := {p : Space m × ℝ | p.2 = f p.1} with hΓ_def
  have hΓ : MeasurableSet Γ := measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  have hset : {x : Space (m + 1) | x (Fin.last m) = f (horizontal x)} =
      (fun x : Space (m + 1) ↦ (horizontal x, x (Fin.last m))) ⁻¹' Γ := by
    ext x
    simp [hΓ_def]
  rw [hset, hmp.measure_preimage hΓ.nullMeasurableSet, Measure.prod_apply hΓ]
  have hsec : ∀ y : Space m, Prod.mk y ⁻¹' Γ = {f y} := by
    intro y
    ext t
    simp [hΓ_def]
  simp [hsec]

theorem inner_verticalDirection_ge {m : ℕ} {n : Space (m + 1)}
    (hn : ‖n - verticalDirection m‖ ≤ 1 / 4) : 3 / 4 ≤ n (Fin.last m) := by
  have h1 : n (Fin.last m) = 1 + inner ℝ (n - verticalDirection m) (verticalDirection m) := by
    rw [inner_sub_left, inner_verticalDirection_right, real_inner_self_eq_norm_sq,
      norm_verticalDirection]
    ring
  have h2 := real_inner_le_norm (n - verticalDirection m) (verticalDirection m)
  have h3 : |inner ℝ (n - verticalDirection m) (verticalDirection m)| ≤ 1 / 4 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_verticalDirection, mul_one]
    exact hn
  linarith [(abs_le.mp h3).1]

theorem norm_horizontal_le_of_near_vertical {m : ℕ} {n : Space (m + 1)}
    (hn : ‖n - verticalDirection m‖ ≤ 1 / 4) : ‖horizontal n‖ ≤ 1 / 4 := by
  have h : horizontal n = horizontal (n - verticalDirection m) := by
    rw [horizontal_sub_eq, horizontal_verticalDirection, sub_zero]
  rw [h]
  exact (norm_horizontal_le_norm_of_space _).trans hn

/-! ### The abstract flat-boundary setting -/

section FlatSetting

variable {m : ℕ} {E : Set (Space (m + 1))} {a δ : ℝ}

/-- Every vertical line over `B_{3/4}` meets the boundary inside the band. -/
theorem exists_boundary_on_vertical_line (hδ : δ ≤ 1 / 128) (haδ : |a| ≤ δ)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (3 / 4) →
      |x (Fin.last m)| < 1 → |x (Fin.last m) - a| ≤ δ)
    (hint : ∀ x, horizontal x ∈ ball (0 : Space m) (3 / 4) → a + δ < x (Fin.last m) →
      x (Fin.last m) < 1 → x ∈ measureTheoreticInterior E)
    (hext : ∀ x, horizontal x ∈ ball (0 : Space m) (3 / 4) → -1 < x (Fin.last m) →
      x (Fin.last m) < a - δ → x ∈ measureTheoreticExterior E)
    {y : Space m} (hy : y ∈ ball (0 : Space m) (3 / 4)) :
    ∃ t, |t - a| ≤ δ ∧ point y t ∈ measureTheoreticBoundary E := by
  have haδ' := abs_le.mp haδ
  set L := (fun t ↦ point y t) '' Ioo (-1 : ℝ) 1 with hL_def
  have hLc : IsPreconnected L := isPreconnected_Ioo.image _ (continuous_point y).continuousOn
  by_contra hcon
  push Not at hcon
  have hLb : ∀ x ∈ L, x ∉ measureTheoreticBoundary E := by
    rintro _ ⟨t, ht, rfl⟩ hb
    have h1 := hband _ hb (by rwa [horizontal_point])
      (by rw [last_point]; exact abs_lt.mpr ⟨ht.1, ht.2⟩)
    rw [last_point] at h1
    exact (hcon t h1) hb
  set tp := (a + δ + 1) / 2 with htp
  set tm := (a - δ - 1) / 2 with htm
  have hpL : point y tp ∈ L := ⟨tp, ⟨by linarith, by linarith⟩, rfl⟩
  have hmL : point y tm ∈ L := ⟨tm, ⟨by linarith, by linarith⟩, rfl⟩
  have hpI : point y tp ∈ measureTheoreticInterior E :=
    hint _ (by rwa [horizontal_point]) (by rw [last_point]; linarith)
      (by rw [last_point]; linarith)
  have hmX : point y tm ∈ measureTheoreticExterior E :=
    hext _ (by rwa [horizontal_point]) (by rw [last_point]; linarith)
      (by rw [last_point]; linarith)
  rcases subset_measureTheoreticInterior_or_exterior hLc hLb with hI | hX
  · exact Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) (hI hmL) hmX
  · exact Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hpI (hX hpL)

end FlatSetting

theorem norm_point_zero_left {m : ℕ} (t : ℝ) : ‖point (0 : Space m) t‖ = |t| := by
  have h := norm_sq_eq_norm_horizontal_sq_add (point (0 : Space m) t)
  rw [horizontal_point, last_point, norm_zero] at h
  have h2 : ‖point (0 : Space m) t‖ ^ 2 = |t| ^ 2 := by rw [h, sq_abs]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp h2

/-- **Relative flatness from scale-wise flatness.** -/
theorem abs_inner_le_of_scale_flat {m : ℕ} {θ : ℝ} {σ : ℕ → ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hσ0 : ∀ k, 0 ≤ σ k) {p n : Space (m + 1)} {B : Set (Space (m + 1))}
    (hflat : ∀ k : ℕ, ∀ q ∈ B, ‖q - p‖ ≤ θ ^ k / 32 → |inner ℝ (q - p) n| ≤ σ k * θ ^ k / 8)
    {K : ℕ} {ε : ℝ} (hK : ∀ k, K ≤ k → 4 * σ k / θ ≤ ε) {q : Space (m + 1)} (hq : q ∈ B)
    (hqp : ‖q - p‖ ≤ θ ^ K / 32) :
    |inner ℝ (q - p) n| ≤ ε * ‖q - p‖ := by
  rcases (norm_nonneg (q - p)).eq_or_lt with h0 | hpos
  · have hqp0 : q - p = 0 := norm_eq_zero.mp h0.symm
    rw [hqp0, inner_zero_left, abs_zero, norm_zero, mul_zero]
  obtain ⟨k, hKk, hk1, hk2⟩ := exists_pow_scale hθ0 hθ1 (by positivity : 0 < 32 * ‖q - p‖)
    (K := K) (by linarith)
  have h1 := hflat k q hq (by linarith)
  have hθk : θ ^ k < 32 * ‖q - p‖ / θ := by
    rw [lt_div_iff₀ hθ0, ← pow_succ]
    exact hk1
  have hσk := hσ0 k
  have hK' := hK k hKk
  calc |inner ℝ (q - p) n| ≤ σ k * θ ^ k / 8 := h1
    _ ≤ σ k * (32 * ‖q - p‖ / θ) / 8 := by gcongr
    _ = (4 * σ k / θ) * ‖q - p‖ := by field_simp; ring
    _ ≤ ε * ‖q - p‖ := mul_le_mul_of_nonneg_right hK' (norm_nonneg _)

/-- **`GR13`: the boundary of a flat phase is a `C¹` graph.** -/
theorem isC1BoundaryPoint_of_flat_normals {m : ℕ} {E : Set (Space (m + 1))} {a δ θ : ℝ}
    {σ : ℕ → ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ0 : ∀ k, 0 ≤ σ k)
    (hσθ : ∀ k, σ k ≤ θ / 128) (hσ : Tendsto σ atTop (𝓝 0)) (haδ : |a| ≤ δ)
    (hδ : δ ≤ 1 / 128)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (3 / 4) →
      |x (Fin.last m)| < 1 → |x (Fin.last m) - a| ≤ δ)
    (hint : ∀ x, horizontal x ∈ ball (0 : Space m) (3 / 4) → a + δ < x (Fin.last m) →
      x (Fin.last m) < 1 → x ∈ measureTheoreticInterior E)
    (hext : ∀ x, horizontal x ∈ ball (0 : Space m) (3 / 4) → -1 < x (Fin.last m) →
      x (Fin.last m) < a - δ → x ∈ measureTheoreticExterior E)
    (hnormal : ∀ p ∈ measureTheoreticBoundary E, horizontal p ∈ ball (0 : Space m) (1 / 2) →
      |p (Fin.last m)| < 1 / 2 → ∃ n : Space (m + 1), ‖n - verticalDirection m‖ ≤ 1 / 4 ∧
        ∀ k : ℕ, ∀ q ∈ measureTheoreticBoundary E, ‖q - p‖ ≤ θ ^ k / 32 →
          |inner ℝ (q - p) n| ≤ σ k * θ ^ k / 8)
    {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ measureTheoreticBoundary E)
    (hx₀π : horizontal x₀ ∈ ball (0 : Space m) (1 / 2)) (hx₀n : |x₀ (Fin.last m)| < 1 / 2) :
    IsC1BoundaryPoint E x₀ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg a).trans haδ
  have haδ' := abs_le.mp haδ
  -- the normal field
  set R := {p : Space (m + 1) | p ∈ measureTheoreticBoundary E ∧
    horizontal p ∈ ball (0 : Space m) (1 / 2) ∧ |p (Fin.last m)| < 1 / 2} with hR_def
  have hnormal' : ∀ p, ∃ n : Space (m + 1), p ∈ R → ‖n - verticalDirection m‖ ≤ 1 / 4 ∧
      ∀ k : ℕ, ∀ q ∈ measureTheoreticBoundary E, ‖q - p‖ ≤ θ ^ k / 32 →
        |inner ℝ (q - p) n| ≤ σ k * θ ^ k / 8 := by
    intro p
    by_cases hp : p ∈ R
    · obtain ⟨n, hn⟩ := hnormal p hp.1 hp.2.1 hp.2.2
      exact ⟨n, fun _ ↦ hn⟩
    · exact ⟨0, fun h ↦ absurd h hp⟩
  choose nf hnf using hnormal'
  -- relative flatness
  have hrel : ∀ ε > 0, ∃ r > 0, ∀ p ∈ R, ∀ q ∈ measureTheoreticBoundary E, ‖q - p‖ ≤ r →
      |inner ℝ (q - p) (nf p)| ≤ ε * ‖q - p‖ := by
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.mp
      (hσ.eventually (gt_mem_nhds (show (0 : ℝ) < ε * θ / 4 by positivity)))
    refine ⟨θ ^ K / 32, by positivity, fun p hp q hq hqp ↦ ?_⟩
    refine abs_inner_le_of_scale_flat hθ0 hθ1 hσ0 (hnf p hp).2 (K := K) (fun k hk ↦ ?_) hq hqp
    have := hK k hk
    rw [div_le_iff₀ hθ0]
    linarith
  have hrel1 : ∀ p ∈ R, ∀ q ∈ measureTheoreticBoundary E, ‖q - p‖ ≤ 1 / 32 →
      |inner ℝ (q - p) (nf p)| ≤ 1 / 32 * ‖q - p‖ := by
    intro p hp q hq hqp
    refine abs_inner_le_of_scale_flat hθ0 hθ1 hσ0 (hnf p hp).2 (K := 0) (fun k _ ↦ ?_) hq
      (by simpa using hqp)
    have := hσθ k
    rw [div_le_iff₀ hθ0]
    linarith
  -- existence and uniqueness on vertical lines
  have hex : ∀ y, ∃ t, y ∈ ball (0 : Space m) (3 / 4) →
      |t - a| ≤ δ ∧ point y t ∈ measureTheoreticBoundary E := by
    intro y
    by_cases hy : y ∈ ball (0 : Space m) (3 / 4)
    · obtain ⟨t, ht⟩ := exists_boundary_on_vertical_line hδ haδ hband hint hext hy
      exact ⟨t, fun _ ↦ ht⟩
    · exact ⟨0, fun h ↦ absurd h hy⟩
  choose ψ hψ using hex
  have hψB : ∀ y ∈ ball (0 : Space m) (1 / 2),
      |ψ y - a| ≤ δ ∧ point y (ψ y) ∈ measureTheoreticBoundary E :=
    fun y hy ↦ hψ y (ball_subset_ball (by norm_num) hy)
  have hψR : ∀ y ∈ ball (0 : Space m) (1 / 2), point y (ψ y) ∈ R := by
    intro y hy
    refine ⟨(hψB y hy).2, by rwa [horizontal_point], ?_⟩
    rw [last_point, abs_lt]
    have := abs_le.mp (hψB y hy).1
    constructor <;> linarith
  have huniq : ∀ y ∈ ball (0 : Space m) (1 / 2), ∀ t, |t - a| ≤ δ →
      point y t ∈ measureTheoreticBoundary E → t = ψ y := by
    intro y hy t ht hbt
    have hpR := hψR y hy
    have hdiff : point y t - point y (ψ y) = point 0 (t - ψ y) := by
      rw [point_sub_point, sub_self]
    have hnorm : ‖point y t - point y (ψ y)‖ = |t - ψ y| := by
      rw [hdiff, norm_point_zero_left]
    have hle : ‖point y t - point y (ψ y)‖ ≤ 1 / 32 := by
      rw [hnorm, abs_le]
      have := abs_le.mp ht
      have := abs_le.mp (hψB y hy).1
      constructor <;> linarith
    have hflat := hrel1 _ hpR _ hbt hle
    have hinner : inner ℝ (point y t - point y (ψ y)) (nf (point y (ψ y))) =
        (t - ψ y) * nf (point y (ψ y)) (Fin.last m) := by
      rw [hdiff, inner_eq_inner_horizontal_add_mul_last, horizontal_point, last_point,
        inner_zero_left, zero_add]
    have hnn := inner_verticalDirection_ge (hnf _ hpR).1
    rw [hinner, hnorm, abs_mul] at hflat
    have hn' : 3 / 4 ≤ |nf (point y (ψ y)) (Fin.last m)| := hnn.trans (le_abs_self _)
    have h0 : |t - ψ y| = 0 := by
      have h1 := mul_le_mul_of_nonneg_left hn' (abs_nonneg (t - ψ y))
      have h2 := abs_nonneg (t - ψ y)
      nlinarith
    linarith [abs_eq_zero.mp h0]
  -- the phase above and below the graph
  have habove : ∀ x, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      ψ (horizontal x) < x (Fin.last m) → x (Fin.last m) < 1 →
        x ∈ measureTheoreticInterior E := by
    intro x hxπ hgt hlt1
    set y := horizontal x with hy_def
    have hψa := abs_le.mp (hψB y hxπ).1
    set L := (fun t ↦ point y t) '' Ioo (ψ y) 1 with hL_def
    have hLc : IsPreconnected L := isPreconnected_Ioo.image _ (continuous_point y).continuousOn
    have hLb : ∀ z ∈ L, z ∉ measureTheoreticBoundary E := by
      rintro _ ⟨t, ht, rfl⟩ hb
      have h1 := hband _ hb (by rw [horizontal_point]; exact ball_subset_ball (by norm_num) hxπ)
        (by rw [last_point, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [last_point] at h1
      have := huniq y hxπ t h1 hb
      linarith [ht.1]
    set tp := (a + δ + 1) / 2 with htp
    have hpL : point y tp ∈ L := ⟨tp, ⟨by linarith, by linarith⟩, rfl⟩
    have hpI : point y tp ∈ measureTheoreticInterior E :=
      hint _ (by rw [horizontal_point]; exact ball_subset_ball (by norm_num) hxπ)
        (by rw [last_point]; linarith) (by rw [last_point]; linarith)
    have hxL : x ∈ L := ⟨x (Fin.last m), ⟨hgt, hlt1⟩, point_horizontal_last x⟩
    rcases subset_measureTheoreticInterior_or_exterior hLc hLb with hI | hX
    · exact hI hxL
    · exact absurd (hX hpL)
        (Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hpI)
  have hbelow : ∀ x, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      x (Fin.last m) < ψ (horizontal x) → -1 < x (Fin.last m) →
        x ∈ measureTheoreticExterior E := by
    intro x hxπ hlt hgt1
    set y := horizontal x with hy_def
    have hψa := abs_le.mp (hψB y hxπ).1
    set L := (fun t ↦ point y t) '' Ioo (-1) (ψ y) with hL_def
    have hLc : IsPreconnected L := isPreconnected_Ioo.image _ (continuous_point y).continuousOn
    have hLb : ∀ z ∈ L, z ∉ measureTheoreticBoundary E := by
      rintro _ ⟨t, ht, rfl⟩ hb
      have h1 := hband _ hb (by rw [horizontal_point]; exact ball_subset_ball (by norm_num) hxπ)
        (by rw [last_point, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [last_point] at h1
      have := huniq y hxπ t h1 hb
      linarith [ht.2]
    set tm := (a - δ - 1) / 2 with htm
    have hmL : point y tm ∈ L := ⟨tm, ⟨by linarith, by linarith⟩, rfl⟩
    have hmX : point y tm ∈ measureTheoreticExterior E :=
      hext _ (by rw [horizontal_point]; exact ball_subset_ball (by norm_num) hxπ)
        (by rw [last_point]; linarith) (by rw [last_point]; linarith)
    have hxL : x ∈ L := ⟨x (Fin.last m), ⟨hgt1, hlt⟩, point_horizontal_last x⟩
    rcases subset_measureTheoreticInterior_or_exterior hLc hLb with hI | hX
    · exact absurd (hI hmL)
        (Set.disjoint_right.mp (disjoint_measureTheoreticInterior_exterior E) hmX)
    · exact hX hxL
  -- the normal along the graph and the slope
  have hnn : ∀ y ∈ ball (0 : Space m) (1 / 2), 3 / 4 ≤ nf (point y (ψ y)) (Fin.last m) :=
    fun y hy ↦ inner_verticalDirection_ge (hnf _ (hψR y hy)).1
  have hπn : ∀ y ∈ ball (0 : Space m) (1 / 2), ‖horizontal (nf (point y (ψ y)))‖ ≤ 1 / 4 :=
    fun y hy ↦ norm_horizontal_le_of_near_vertical (hnf _ (hψR y hy)).1
  set D : Space m → Space m := fun y ↦
    -(nf (point y (ψ y)) (Fin.last m))⁻¹ • horizontal (nf (point y (ψ y))) with hD_def
  have hinnerq : ∀ y₀ y, inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀))) =
      inner ℝ (y - y₀) (horizontal (nf (point y₀ (ψ y₀)))) +
        (ψ y - ψ y₀) * nf (point y₀ (ψ y₀)) (Fin.last m) := by
    intro y₀ y
    rw [point_sub_point, inner_eq_inner_horizontal_add_mul_last, horizontal_point, last_point]
  have hexpand : ∀ y₀ ∈ ball (0 : Space m) (1 / 2), ∀ y,
      ψ y - ψ y₀ - inner ℝ (D y₀) (y - y₀) =
        inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀))) /
          nf (point y₀ (ψ y₀)) (Fin.last m) := by
    intro y₀ hy₀ y
    have hne : nf (point y₀ (ψ y₀)) (Fin.last m) ≠ 0 := by linarith [hnn y₀ hy₀]
    rw [hinnerq, hD_def]
    simp only [real_inner_smul_left]
    rw [real_inner_comm (y - y₀)]
    field_simp
    ring
  have hnormq : ∀ y₀ y, ‖point y (ψ y) - point y₀ (ψ y₀)‖ ≤ ‖y - y₀‖ + |ψ y - ψ y₀| := by
    intro y₀ y
    rw [point_sub_point]
    have := norm_le_norm_horizontal_add_abs_last (point (y - y₀) (ψ y - ψ y₀))
    rwa [horizontal_point, last_point] at this
  -- local Lipschitz bound
  have hlip : ∀ y₀ ∈ ball (0 : Space m) (1 / 2), ∀ y ∈ ball (0 : Space m) (1 / 2),
      ‖y - y₀‖ ≤ 1 / 64 → |ψ y - ψ y₀| ≤ ‖y - y₀‖ := by
    intro y₀ hy₀ y hy hyy
    have hpR := hψR y₀ hy₀
    have hq := (hψB y hy).2
    have hΔ : |ψ y - ψ y₀| ≤ 2 * δ := by
      have h1 := abs_le.mp (hψB y hy).1
      have h2 := abs_le.mp (hψB y₀ hy₀).1
      rw [abs_le]
      constructor <;> linarith
    have hnq := hnormq y₀ y
    have hflat : |inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀)))| ≤
        1 / 32 * ‖point y (ψ y) - point y₀ (ψ y₀)‖ := hrel1 _ hpR _ hq (by linarith)
    have hw : |inner ℝ (y - y₀) (horizontal (nf (point y₀ (ψ y₀))))| ≤ ‖y - y₀‖ * (1 / 4) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hπn y₀ hy₀) (norm_nonneg _))
    have hn0 := hnn y₀ hy₀
    have heq : (ψ y - ψ y₀) * nf (point y₀ (ψ y₀)) (Fin.last m) =
        inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀))) -
          inner ℝ (y - y₀) (horizontal (nf (point y₀ (ψ y₀)))) := by
      rw [hinnerq]
      ring
    have key : |ψ y - ψ y₀| * nf (point y₀ (ψ y₀)) (Fin.last m) ≤
        1 / 32 * (‖y - y₀‖ + |ψ y - ψ y₀|) + ‖y - y₀‖ * (1 / 4) := by
      calc |ψ y - ψ y₀| * nf (point y₀ (ψ y₀)) (Fin.last m)
          = |(ψ y - ψ y₀) * nf (point y₀ (ψ y₀)) (Fin.last m)| := by
            rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < nf (point y₀ (ψ y₀)) (Fin.last m))]
        _ = |inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀))) -
            inner ℝ (y - y₀) (horizontal (nf (point y₀ (ψ y₀))))| := by rw [heq]
        _ ≤ |inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀)))| +
            |inner ℝ (y - y₀) (horizontal (nf (point y₀ (ψ y₀))))| := abs_sub _ _
        _ ≤ 1 / 32 * ‖point y (ψ y) - point y₀ (ψ y₀)‖ + ‖y - y₀‖ * (1 / 4) :=
            add_le_add hflat hw
        _ ≤ 1 / 32 * (‖y - y₀‖ + |ψ y - ψ y₀|) + ‖y - y₀‖ * (1 / 4) := by gcongr
    have h1 : |ψ y - ψ y₀| * (3 / 4) ≤ |ψ y - ψ y₀| * nf (point y₀ (ψ y₀)) (Fin.last m) :=
      mul_le_mul_of_nonneg_left hn0 (abs_nonneg _)
    nlinarith [abs_nonneg (ψ y - ψ y₀), norm_nonneg (y - y₀)]
  -- the uniform first-order expansion
  have hrem : ∀ ε > 0, ∃ r > 0, ∀ y₀ ∈ ball (0 : Space m) (1 / 2),
      ∀ y ∈ ball (0 : Space m) (1 / 2), ‖y - y₀‖ ≤ r →
        |ψ y - ψ y₀ - inner ℝ (D y₀) (y - y₀)| ≤ ε * ‖y - y₀‖ := by
    intro ε hε
    obtain ⟨r', hr', hr'f⟩ := hrel (3 * ε / 8) (by positivity)
    refine ⟨min (r' / 2) (1 / 64), by positivity, fun y₀ hy₀ y hy hyy ↦ ?_⟩
    have hyy1 : ‖y - y₀‖ ≤ 1 / 64 := hyy.trans (min_le_right _ _)
    have hyy2 : ‖y - y₀‖ ≤ r' / 2 := hyy.trans (min_le_left _ _)
    have hL := hlip y₀ hy₀ y hy hyy1
    have hnq : ‖point y (ψ y) - point y₀ (ψ y₀)‖ ≤ 2 * ‖y - y₀‖ := by
      linarith [hnormq y₀ y]
    have hflat : |inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀)))| ≤
        3 * ε / 8 * ‖point y (ψ y) - point y₀ (ψ y₀)‖ :=
      hr'f _ (hψR y₀ hy₀) _ (hψB y hy).2 (by linarith)
    have hn0 := hnn y₀ hy₀
    rw [hexpand y₀ hy₀ y, abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < nf (point y₀ (ψ y₀)) (Fin.last m)),
      div_le_iff₀ (by linarith)]
    have hεw : 0 ≤ ε * ‖y - y₀‖ := by positivity
    calc |inner ℝ (point y (ψ y) - point y₀ (ψ y₀)) (nf (point y₀ (ψ y₀)))|
        ≤ 3 * ε / 8 * ‖point y (ψ y) - point y₀ (ψ y₀)‖ := hflat
      _ ≤ 3 * ε / 8 * (2 * ‖y - y₀‖) := by gcongr
      _ = 3 / 4 * (ε * ‖y - y₀‖) := by ring
      _ ≤ nf (point y₀ (ψ y₀)) (Fin.last m) * (ε * ‖y - y₀‖) :=
          mul_le_mul_of_nonneg_right hn0 hεw
      _ = ε * ‖y - y₀‖ * nf (point y₀ (ψ y₀)) (Fin.last m) := by ring
  -- differentiability
  have hderiv : ∀ y₀ ∈ ball (0 : Space m) (1 / 2), HasFDerivAt ψ (innerSL ℝ (D y₀)) y₀ := by
    intro y₀ hy₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨r, hr, hrf⟩ := hrem c hc
    have h1 : ∀ᶠ h in 𝓝 (0 : Space m), y₀ + h ∈ ball (0 : Space m) (1 / 2) := by
      have hca : ContinuousAt (fun h : Space m ↦ y₀ + h) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have h2 : ball (0 : Space m) (1 / 2) ∈ 𝓝 (y₀ + 0) := by
        rw [add_zero]
        exact isOpen_ball.mem_nhds hy₀
      exact hca.preimage_mem_nhds h2
    have h2 : ∀ᶠ h in 𝓝 (0 : Space m), ‖h‖ ≤ r := by
      filter_upwards [closedBall_mem_nhds (0 : Space m) hr] with h hh
      simpa using hh
    filter_upwards [h1, h2] with h hh1 hh2
    have := hrf y₀ hy₀ (y₀ + h) hh1 (by rwa [add_sub_cancel_left])
    rw [add_sub_cancel_left] at this
    rw [Real.norm_eq_abs, innerSL_apply_apply]
    exact this
  -- continuity of the slope
  have hDcont : ∀ y₀ ∈ ball (0 : Space m) (1 / 2), ∀ ε > 0, ∃ ρ > 0, ∀ y₁,
      ‖y₁ - y₀‖ < ρ → ‖D y₁ - D y₀‖ ≤ ε := by
    intro y₀ hy₀ ε hε
    obtain ⟨r, hr, hrf⟩ := hrem (ε / 4) (by positivity)
    have hy₀' : ‖y₀‖ < 1 / 2 := mem_ball_zero_iff.mp hy₀
    set ρ := min ((1 / 2 - ‖y₀‖) / 3) (r / 2) with hρ_def
    have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
    refine ⟨ρ, hρ, fun y₁ hy₁ ↦ ?_⟩
    have hρ1 : ρ ≤ (1 / 2 - ‖y₀‖) / 3 := min_le_left _ _
    have hρ2 : ρ ≤ r / 2 := min_le_right _ _
    have hy₁B : y₁ ∈ ball (0 : Space m) (1 / 2) := by
      rw [mem_ball_zero_iff]
      have := norm_sub_norm_le y₁ y₀
      linarith
    by_cases hD : D y₁ = D y₀
    · rw [hD, sub_self, norm_zero]
      exact hε.le
    set s := ‖y₁ - y₀‖ with hs_def
    have hs0 : 0 < s := by
      rcases (norm_nonneg (y₁ - y₀)).eq_or_lt with h | h
      · exfalso
        have : y₁ = y₀ := sub_eq_zero.mp (norm_eq_zero.mp h.symm)
        exact hD (by rw [this])
      · exact h
    set w := D y₁ - D y₀ with hw_def
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hD)
    set v := ‖w‖⁻¹ • w with hv_def
    have hvnorm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
    set y₂ := y₁ + s • v with hy₂_def
    have hy₂₁ : ‖y₂ - y₁‖ = s := by
      rw [hy₂_def, add_sub_cancel_left, norm_smul, hvnorm, mul_one, Real.norm_of_nonneg hs0.le]
    have hy₂₀ : ‖y₂ - y₀‖ ≤ 2 * s := by
      calc ‖y₂ - y₀‖ = ‖(y₂ - y₁) + (y₁ - y₀)‖ := by congr 1; abel
        _ ≤ ‖y₂ - y₁‖ + ‖y₁ - y₀‖ := norm_add_le _ _
        _ = 2 * s := by rw [hy₂₁]; ring
    have hy₂B : y₂ ∈ ball (0 : Space m) (1 / 2) := by
      rw [mem_ball_zero_iff]
      have := norm_sub_norm_le y₂ y₀
      linarith
    have e1 := hrf y₁ hy₁B y₂ hy₂B (by rw [hy₂₁]; linarith)
    have e2 := hrf y₀ hy₀ y₂ hy₂B (by linarith)
    have e3 := hrf y₀ hy₀ y₁ hy₁B (by linarith)
    rw [hy₂₁] at e1
    have e2' : |ψ y₂ - ψ y₀ - inner ℝ (D y₀) (y₂ - y₀)| ≤ ε / 4 * (2 * s) :=
      e2.trans (mul_le_mul_of_nonneg_left hy₂₀ (by positivity))
    have hcomb : inner ℝ w (y₂ - y₁) =
        (ψ y₂ - ψ y₀ - inner ℝ (D y₀) (y₂ - y₀)) -
          (ψ y₁ - ψ y₀ - inner ℝ (D y₀) (y₁ - y₀)) -
            (ψ y₂ - ψ y₁ - inner ℝ (D y₁) (y₂ - y₁)) := by
      rw [hw_def, inner_sub_left]
      have h' : y₂ - y₀ = (y₂ - y₁) + (y₁ - y₀) := by abel
      rw [h', inner_add_right]
      ring
    have hwv : inner ℝ w (y₂ - y₁) = s * ‖w‖ := by
      rw [hy₂_def, add_sub_cancel_left, hv_def, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      field_simp
    have hbound : s * ‖w‖ ≤ s * ε := by
      rw [← hwv, hcomb]
      have h1 := abs_le.mp e1
      have h2 := abs_le.mp e2'
      have h3 := abs_le.mp e3
      linarith
    exact le_of_mul_le_mul_left hbound hs0
  -- `C¹` on a ball around the horizontal projection of `x₀`
  set y₀ := horizontal x₀ with hy₀_def
  have hy₀' : ‖y₀‖ < 1 / 2 := mem_ball_zero_iff.mp hx₀π
  set ρ₀ := (1 / 2 - ‖y₀‖) / 2 with hρ₀_def
  have hρ₀ : 0 < ρ₀ := by linarith
  have hball : ball y₀ ρ₀ ⊆ ball (0 : Space m) (1 / 2) := by
    intro y hy
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hy
    have := norm_sub_norm_le y y₀
    linarith
  have hC1 : ContDiffOn ℝ 1 ψ (ball y₀ ρ₀) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun y hy ↦ (hderiv y (hball hy)).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_zero]
    have heq : Set.EqOn (fun y ↦ innerSL ℝ (D y)) (fderiv ℝ ψ) (ball y₀ ρ₀) :=
      fun y hy ↦ (hderiv y (hball hy)).fderiv.symm
    refine ContinuousOn.congr ?_ heq.symm
    have hDc : ContinuousOn D (ball y₀ ρ₀) := by
      intro y hy
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨ρ, hρ, hρf⟩ := hDcont y (hball hy) (ε / 2) (by positivity)
      refine ⟨ρ, hρ, fun y' _ hy' ↦ ?_⟩
      rw [dist_eq_norm] at hy' ⊢
      exact (hρf y' hy').trans_lt (by linarith)
    exact (innerSL ℝ).continuous.comp_continuousOn hDc
  -- `x₀` lies on the graph
  have hx₀n1 : |x₀ (Fin.last m)| < 1 := by
    have := abs_lt.mp hx₀n
    rw [abs_lt]
    constructor <;> linarith
  have hx₀band : |x₀ (Fin.last m) - a| ≤ δ :=
    hband x₀ hx₀ (ball_subset_ball (by norm_num) hx₀π) hx₀n1
  have hx₀g : x₀ (Fin.last m) = ψ y₀ :=
    huniq y₀ hx₀π _ hx₀band (by rw [hy₀_def, point_horizontal_last]; exact hx₀)
  -- the chart
  set ρ' := min ρ₀ (1 / 4) with hρ'_def
  have hρ' : 0 < ρ' := lt_min hρ₀ (by norm_num)
  set φ : Space m → ℝ := fun w ↦ ψ (y₀ + w) - x₀ (Fin.last m) with hφ_def
  have hφC1 : ContDiffOn ℝ 1 φ (ball 0 ρ') := by
    have hmaps : MapsTo (fun w : Space m ↦ y₀ + w) (ball 0 ρ') (ball y₀ ρ₀) := by
      intro w hw
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_zero_iff.mp hw).trans_le (min_le_left _ _)
    exact (hC1.comp (contDiff_const.add contDiff_id).contDiffOn hmaps).sub contDiffOn_const
  have hφ0 : φ 0 = 0 := by
    simp only [hφ_def, add_zero, ← hx₀g, sub_self]
  -- the null sets
  classical
  set ψt : Space m → ℝ := (ball y₀ ρ₀).piecewise ψ (fun _ ↦ 0) with hψt_def
  have hψtm : Measurable ψt :=
    ContinuousOn.measurable_piecewise hC1.continuousOn continuousOn_const
      isOpen_ball.measurableSet
  have hnull1 := volume_measureTheoreticInterior_sdiff E
  have hnull2 := volume_inter_measureTheoreticExterior E
  have hnull3 := volume_graph_eq_zero hψtm
  refine isC1BoundaryPoint_of_graph (LinearIsometryEquiv.refl ℝ (Space (m + 1))) hρ' hφC1 hφ0 ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull1,
    measure_eq_zero_iff_ae_notMem.mp hnull2, measure_eq_zero_iff_ae_notMem.mp hnull3]
    with y hy1 hy2 hy3 hyB
  have hsimp : φ (horizontal ((LinearIsometryEquiv.refl ℝ (Space (m + 1))).symm (y - x₀))) =
      ψ (horizontal y) - x₀ (Fin.last m) := by
    show ψ (y₀ + horizontal (y - x₀)) - x₀ (Fin.last m) = _
    rw [horizontal_sub_eq, hy₀_def, add_sub_cancel]
  have hsimp2 : (LinearIsometryEquiv.refl ℝ (Space (m + 1))).symm (y - x₀) (Fin.last m) =
      y (Fin.last m) - x₀ (Fin.last m) := by
    show (y - x₀) (Fin.last m) = _
    simp
  rw [hsimp, hsimp2]
  have hyB' : ‖y - x₀‖ < ρ' := by rw [← dist_eq_norm]; exact hyB
  have hyπ : horizontal y ∈ ball y₀ ρ₀ := by
    rw [mem_ball, dist_eq_norm, hy₀_def, ← horizontal_sub_eq]
    exact (norm_horizontal_le_norm_of_space _).trans_lt (hyB'.trans_le (min_le_left _ _))
  have hyπ' : horizontal y ∈ ball (0 : Space m) (1 / 2) := hball hyπ
  have hyn' : -1 < y (Fin.last m) ∧ y (Fin.last m) < 1 := by
    have h1 := (abs_apply_last_le_norm (y - x₀)).trans_lt (hyB'.trans_le (min_le_right _ _))
    have h2 : |y (Fin.last m) - x₀ (Fin.last m)| < 1 / 4 := by simpa using h1
    have h3 := abs_lt.mp hx₀n
    have h4 := abs_lt.mp h2
    constructor <;> linarith
  have hψt : ψt (horizontal y) = ψ (horizontal y) := by
    rw [hψt_def, Set.piecewise_eq_of_mem _ _ _ hyπ]
  constructor
  · intro hyE
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hyX := hbelow y hyπ' (by linarith) hyn'.1
      exact hy2 ⟨hyE, hyX⟩
    · apply hy3
      show y (Fin.last m) = ψt (horizontal y)
      rw [hψt]
      linarith
  · intro hlt
    have hyI := habove y hyπ' (by linarith) hyn'.2
    by_contra hyE
    exact hy1 ⟨hyI, hyE⟩

end SerrinEpigraph
