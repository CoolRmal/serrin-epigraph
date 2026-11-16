module

public import SerrinEpigraph.ZeroExtension
public import SerrinEpigraph.BoundaryGradient

/-!
# From directional translation order to affine one-dimensionality

This is the terminal implication F3--F4. Its translation-order premise is the
conclusion required of the global sliding argument, not an additional hypothesis
of either rigidity target.
-/

public section

noncomputable section

open Set Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Continuity extends translation order from an open half-space of directions
to its closure. -/
theorem translation_le_of_inner_nonneg {d : ℕ} {U : Space d → ℝ} (hU : Continuous U)
    {e : Space d} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z → U x ≤ U (x + z))
    (x z : Space d) (hz : 0 ≤ inner ℝ e z) : U x ≤ U (x + z) := by
  have ht : Tendsto (fun t : ℝ ↦ U (x + (z + t • e))) (𝓝[>] 0) (𝓝 (U (x + z))) := by
    have hc : Continuous (fun t : ℝ ↦ U (x + (z + t • e))) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply horder
  rw [inner_add_right, real_inner_smul_right]
  exact add_pos_of_nonneg_of_pos hz (mul_pos ht (real_inner_self_pos.mpr he))

/-- Translation order in every positive normal direction forces invariance in
all tangent directions. -/
theorem translation_eq_of_inner_zero {d : ℕ} {U : Space d → ℝ} (hU : Continuous U)
    {e : Space d} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z → U x ≤ U (x + z))
    (x z : Space d) (hz : inner ℝ e z = 0) : U (x + z) = U x := by
  apply le_antisymm
  · have hn : 0 ≤ inner ℝ e (-z) := by simp [hz]
    simpa using translation_le_of_inner_nonneg hU he horder (x + z) (-z) hn
  · exact translation_le_of_inner_nonneg hU he horder x z hz.ge

/-- Points with the same normal coordinate have equal values. -/
theorem value_eq_of_inner_eq {d : ℕ} {U : Space d → ℝ} (hU : Continuous U)
    {e : Space d} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z → U x ≤ U (x + z))
    {x y : Space d} (hxy : inner ℝ e x = inner ℝ e y) : U x = U y := by
  have hz : inner ℝ e (x - y) = 0 := by rw [inner_sub_right, hxy, sub_self]
  simpa using translation_eq_of_inner_zero hU he horder y (x - y) hz

/-- Splitting the last coordinate in a normal-coordinate pairing. -/
theorem inner_point_right {m : ℕ} (e : Space (m + 1)) (y : Space m) (t : ℝ) :
    inner ℝ e (point y t) = inner ℝ (horizontal e) y + e (Fin.last m) * t := by
  calc
    inner ℝ e (point y t) =
        inner ℝ (point (horizontal e) (e (Fin.last m))) (point y t) := by simp
    _ = _ := inner_point_point _ _ _ _

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- For an entire epigraph, a normal determining all translation orders points
strictly upwards. -/
theorem Hypotheses.normal_last_pos_of_translation_order (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z →
      zeroExtension g u x ≤ zeroExtension g u (x + z)) : 0 < e (Fin.last m) := by
  by_contra hn
  have hn' : e (Fin.last m) ≤ 0 := le_of_not_gt hn
  let p := point (0 : Space m) (g 0)
  let q := point (0 : Space m) (g 0 + 1)
  have hp : zeroExtension g u p = 0 :=
    zeroExtension_of_notMem (by simp [p, epigraph])
  have hq : 0 < zeroExtension g u q :=
    (h.zeroExtension_pos_iff q).mpr (by simp [q, epigraph])
  have hi : 0 ≤ inner ℝ e (p - q) := by
    simp only [p, q, inner_sub_right, inner_point_right, inner_zero_right, zero_add]
    linarith
  have ho := translation_le_of_inner_nonneg h.zeroExtension_continuous he horder q (p - q) hi
  have hadd : q + (p - q) = p := by abel
  rw [hadd, hp] at ho
  exact (not_lt_of_ge ho) hq

/-- All-space directional order identifies the positive phase by one normal
coordinate, using the original vertical line through the origin. -/
theorem Hypotheses.mem_epigraph_iff_normal_coordinate (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z →
      zeroExtension g u x ≤ zeroExtension g u (x + z)) (x : Space (m + 1)) :
    x ∈ epigraph g ↔ g 0 < inner ℝ e x / e (Fin.last m) := by
  have hn := h.normal_last_pos_of_translation_order he horder
  have hi : inner ℝ e x =
      inner ℝ e (point (0 : Space m) (inner ℝ e x / e (Fin.last m))) := by
    simp only [inner_point_right, inner_zero_right, zero_add]
    field_simp
  have hv := value_eq_of_inner_eq h.zeroExtension_continuous he horder hi
  rw [← h.zeroExtension_pos_iff x, hv, h.zeroExtension_pos_iff]
  simp [epigraph]

/-- Directional translation order determines the affine graph explicitly. -/
theorem Hypotheses.graph_eq_of_translation_order (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z →
      zeroExtension g u x ≤ zeroExtension g u (x + z)) (y : Space m) :
    g y = inner ℝ (-(e (Fin.last m))⁻¹ • horizontal e) y + g 0 := by
  have hn := h.normal_last_pos_of_translation_order he horder
  have hc : e (Fin.last m) * (-(e (Fin.last m))⁻¹ * inner ℝ (horizontal e) y) =
      -inner ℝ (horizontal e) y := by field_simp
  apply eq_of_forall_gt_iff
  intro t
  have hm := h.mem_epigraph_iff_normal_coordinate he horder (point y t)
  simp only [epigraph, mem_ofPred_eq, horizontal_point, last_point] at hm
  rw [hm, inner_point_right, lt_div_iff₀ hn, real_inner_smul_left]
  constructor
  · intro ht
    apply (mul_lt_mul_iff_left₀ hn).mp
    nlinarith
  · intro ht
    have hmul := (mul_lt_mul_iff_left₀ hn).mpr ht
    nlinarith

/-- The exact terminal implication used by both rigidity theorems: once global
sliding provides all positive normal translation orders, the graph is affine and
the solution depends only on inward normal distance. -/
theorem Hypotheses.isAffineOneDimensional_of_translation_order (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : e ≠ 0)
    (horder : ∀ x z, 0 < inner ℝ e z →
      zeroExtension g u x ≤ zeroExtension g u (x + z)) : IsAffineOneDimensional g u := by
  let a : Space m := -(e (Fin.last m))⁻¹ • horizontal e
  let c : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)
  have hc : c ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 1 + ‖a‖ ^ 2)).ne'
  have hn := h.normal_last_pos_of_translation_order he horder
  refine ⟨a, g 0, fun t ↦ zeroExtension g u (point 0 (g 0 + c * t)),
    h.graph_eq_of_translation_order he horder, ?_⟩
  intro x hx
  rw [← zeroExtension_of_mem (u := u) hx]
  apply value_eq_of_inner_eq h.zeroExtension_continuous he horder
  have hs : inner ℝ e x =
      inner ℝ (horizontal e) (horizontal x) + e (Fin.last m) * x (Fin.last m) := by
    simpa using inner_point_right e (horizontal x) (x (Fin.last m))
  rw [hs, inner_point_right, inner_zero_right, zero_add]
  change _ = e (Fin.last m) *
    (g 0 + c * ((x (Fin.last m) - inner ℝ a (horizontal x) - g 0) / c))
  simp only [a, real_inner_smul_left]
  field_simp
  ring

end SerrinEpigraph
