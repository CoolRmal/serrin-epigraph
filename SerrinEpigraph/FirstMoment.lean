module

public import SerrinEpigraph.CauchyEnergy
public import SerrinEpigraph.CutoffDerivative
public import SerrinEpigraph.CutoffMoments
public import SerrinEpigraph.IntegrationByParts
public import SerrinEpigraph.QuotientTests
public import SerrinEpigraph.WeakQuotient
public import SerrinEpigraph.PowerEnergy

/-!
# The first-order estimate for odd cutoff moments

Vertical integration by parts supplies the extra quotient power, and Cauchy's inequality bounds
the result using the power-test energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace Metric
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- The interior test whose square supplies the even power below an odd moment. -/
def quotientMomentTest (g : Space m → ℝ) (u χ : Space (m + 1) → ℝ) (n : ℕ) :
    Space (m + 1) → ℝ :=
  (epigraph g).indicator (fun x ↦ negativeQuotient u x ^ (n + 2) * χ x ^ (2 * n + 5))

private theorem cutoff_test_sq_le_aux {z c : ℝ} (hz : 0 ≤ z) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (n : ℕ) : (z ^ (n + 2) * c ^ (2 * n + 5)) ^ 2 ≤ (z * c ^ 2) ^ (2 * n + 4) := by
  simp only [mul_pow, ← pow_mul]
  have heq : (n + 2) * 2 = 2 * n + 4 := by omega
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hc0 hc1 (by omega : 2 * (2 * n + 4) ≤ (2 * n + 5) * 2))
    (pow_nonneg hz _)

private theorem extra_moment_identity_aux {u v z c : ℝ} (n : ℕ)
    (hv : v * z ^ (2 * n + 4) = -u * z ^ (2 * n + 5)) :
    -(u * v * (z ^ (n + 2) * c ^ (2 * n + 5)) ^ 2) = u ^ 2 * (z * c ^ 2) ^ (2 * n + 5) := by
  have hz : (z ^ (n + 2)) ^ 2 = z ^ (2 * n + 4) := by
    rw [← pow_mul]
    congr 1
    omega
  have hc : (c ^ (2 * n + 5)) ^ 2 = (c ^ 2) ^ (2 * n + 5) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [mul_pow, hz, hc, mul_pow]
  calc
    _ = -u * (v * z ^ (2 * n + 4)) * (c ^ 2) ^ (2 * n + 5) := by ring
    _ = _ := by rw [hv]; ring

/-- The moment test is a compactly supported `C¹` function with support inside the epigraph. -/
theorem quotientMomentTest_regular (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ContDiff ℝ 1 (quotientMomentTest g u χ n) ∧
      HasCompactSupport (quotientMomentTest g u χ n) ∧
      tsupport (quotientMomentTest g u χ n) ⊆ epigraph g := by
  have hc : HasCompactSupport (fun x ↦ χ x ^ (2 * n + 5)) := by
    apply hχc.of_isClosed_subset (isClosed_tsupport _)
    simp only [tsupport, Function.support_pow _ (by omega : 2 * n + 5 ≠ 0)]
    exact Set.Subset.rfl
  exact ⟨contDiff_indicator_negativeQuotient_pow_mul h (by omega) (hχ.pow _) hc,
    hasCompactSupport_indicator_negativeQuotient_pow_mul h (by omega) hc⟩

/-- Vertical integration by parts identifies the pairing with the next odd cutoff moment. -/
theorem integral_quotientMomentTest_vertical (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    (∫ x, u x ^ 2 * quotientMomentTest g u χ n x *
      verticalDerivative (quotientMomentTest g u χ n) x) =
      ∫ x in epigraph g, u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 5) := by
  obtain ⟨hψ, hψc, hψsub⟩ := quotientMomentTest_regular h n hχ hχc
  rw [integral_sq_mul_mul_verticalDerivative_eq_neg
    (isOpen_epigraph h.graph_contDiff.continuous) (h.solution_contDiffOn.of_le (by norm_num))
    hψ hψc hψsub, ← integral_neg,
    ← integral_indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ epigraph g
  · simp only [quotientMomentTest, Set.indicator_of_mem hx]
    apply extra_moment_identity_aux
    exact verticalDerivative_mul_negativeQuotient_pow (h.positive x hx) (by omega)
  · simp [quotientMomentTest, hx]

private theorem support_quotientMomentTest_subset_aux {χ : Space (m + 1) → ℝ} (n : ℕ) :
    Function.support (quotientMomentTest g u χ n) ⊆ epigraph g ∩ Function.support χ := by
  simp only [quotientMomentTest, Set.support_indicator]
  apply Set.inter_subset_inter_right
  exact (Function.support_mul_subset_right _ _).trans
    (by rw [Function.support_pow _ (by omega : 2 * n + 5 ≠ 0)])

private theorem integrable_sq_mul_sq_aux {Ω : Set (Space (m + 1))}
    {u ψ : Space (m + 1) → ℝ} (hu : ContinuousOn u Ω) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) :
    Integrable (fun x ↦ u x ^ 2 * ψ x ^ 2) := by
  have hc : HasCompactSupport (fun x ↦ ψ x ^ 2) :=
    hψc.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hs : tsupport (fun x ↦ ψ x ^ 2) ⊆ Ω := by
    simpa only [tsupport, Function.support_pow _ (by norm_num : (2 : ℕ) ≠ 0)] using hsub
  exact integrable_mul_of_tsupport_subset (μ := volume) (hu.pow 2) (hψ.pow 2) hc hs

private theorem integrable_sq_mul_vertical_sq_aux {Ω : Set (Space (m + 1))}
    {u ψ : Space (m + 1) → ℝ} (hu : ContinuousOn u Ω) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ Ω) :
    Integrable (fun x ↦ u x ^ 2 * verticalDerivative ψ x ^ 2) := by
  apply integrable_sq_mul_sq_aux hu
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hψc.fderiv_apply ℝ (verticalDirection m))
  exact (tsupport_fderiv_apply_subset ℝ (verticalDirection m)).trans hsub

private theorem cutoff_moment_restrict_aux (h : Hypotheses g u f κ)
    {χ : Space (m + 1) → ℝ} {r : ℝ} {k : ℕ}
    (hχsupport : Function.support χ ⊆ ball 0 r) (hk : k ≠ 0) :
    (∫ x in epigraph g, u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k) =
      ∫ x in epigraph g ∩ ball 0 r, u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ k := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isOpen_epigraph h.graph_contDiff.continuous).measurableSet Set.inter_subset_left
  intro x hx
  have hb : x ∉ ball 0 r := fun hb ↦ hx.2 ⟨hx.1, hb⟩
  have hz : χ x = 0 := Function.notMem_support.mp (fun hx' ↦ hb (hχsupport hx'))
  simp [hz, hk]

private theorem integral_test_sq_le_lower_moment_aux (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} {r : ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupport : Function.support χ ⊆ ball 0 r) (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x, u x ^ 2 * quotientMomentTest g u χ n x ^ 2) ≤
      ∫ x in epigraph g ∩ ball 0 r,
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 4) := by
  obtain ⟨hψ, hψc, hψsub⟩ := quotientMomentTest_regular h n hχ hχc
  have hi := integrable_sq_mul_sq_aux h.solution_contDiffOn.continuousOn hψ.continuous hψc hψsub
  have hs : Function.support (quotientMomentTest g u χ n) ⊆ epigraph g ∩ ball 0 r :=
    (support_quotientMomentTest_subset_aux n).trans (Set.inter_subset_inter_right _ hχsupport)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := epigraph g ∩ ball 0 r)
    (fun x hx ↦ by simp [Function.notMem_support.mp (fun hx' ↦ hx (hs hx'))])]
  apply integral_mono_ae hi.integrableOn (integrableOn_cutoff_moment h hχ.continuous _ r)
  filter_upwards [ae_restrict_mem
    ((isOpen_epigraph h.graph_contDiff.continuous).measurableSet.inter measurableSet_ball)]
    with x hx
  simp only [quotientMomentTest, Set.indicator_of_mem hx.1]
  exact mul_le_mul_of_nonneg_left
    (cutoff_test_sq_le_aux (negativeQuotient_nonneg u x) (hχbounds x).1 (hχbounds x).2 n)
    (sq_nonneg _)

private theorem cutoff_power_gradient_error_le_aux (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} {r B : ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupport : Function.support χ ⊆ ball 0 r) (hχ0 : ∀ x, 0 ≤ χ x)
    (hderiv : ∀ x, ‖fderiv ℝ χ x‖ ≤ B) :
    (∫ x in epigraph g, u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) *
      ‖gradient (fun y ↦ χ y ^ (2 * n + 5)) x‖ ^ 2) ≤
      ((2 * n + 5 : ℕ) * B) ^ 2 * ∫ x in epigraph g ∩ ball 0 r,
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 4) := by
  let η := fun x ↦ χ x ^ (2 * n + 5)
  have hη : ContDiff ℝ 1 η := hχ.pow _
  have hηc : HasCompactSupport η :=
    hχc.comp_left (g := fun t : ℝ ↦ t ^ (2 * n + 5)) (by simp)
  have hi : IntegrableOn (fun x ↦ u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) *
      ‖gradient η x‖ ^ 2) (epigraph g) :=
    (integrable_indicator_iff (isOpen_epigraph h.graph_contDiff.continuous).measurableSet).mp
      (integrable_indicator_power_gradient_error h (by omega) hη hηc)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isOpen_epigraph h.graph_contDiff.continuous).measurableSet Set.inter_subset_left ?_,
    ← integral_const_mul]
  · apply integral_mono_ae (hi.mono_set Set.inter_subset_left)
      ((integrableOn_cutoff_moment h hχ.continuous _ r).const_mul _)
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [show 2 * n + 5 - 1 = 2 * n + 4 by omega, mul_assoc] using
        weighted_gradient_cutoff_pow_le (k := 2 * n + 5) (hχ.differentiable_one x)
          (hχ0 x) (hderiv x) (sq_nonneg (u x)) (negativeQuotient_nonneg u x)
  · intro x hx
    have hb : x ∉ ball 0 r := fun hb ↦ hx.2 ⟨hx.1, hb⟩
    have hz : χ x = 0 := Function.notMem_support.mp (fun hx' ↦ hb (hχsupport hx'))
    simp [gradient_nat_pow _ (hχ.differentiable_one x), hz]

private theorem integral_test_vertical_sq_le_aux (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} {r B : ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupport : Function.support χ ⊆ ball 0 r) (hχ0 : ∀ x, 0 ≤ χ x)
    (hderiv : ∀ x, ‖fderiv ℝ χ x‖ ≤ B) :
    (∫ x, u x ^ 2 * verticalDerivative (quotientMomentTest g u χ n) x ^ 2) ≤
      ((2 * n + 5 : ℕ) * B) ^ 2 * ∫ x in epigraph g ∩ ball 0 r,
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 4) := by
  obtain ⟨hψ, hψc, hψsub⟩ := quotientMomentTest_regular h n hχ hχc
  have hi := integrable_sq_mul_vertical_sq_aux h.solution_contDiffOn.continuousOn hψ hψc hψsub
  have hG := integrable_weight_mul_norm_gradient_sq (μ := volume)
    (h.solution_contDiffOn.continuousOn.pow 2) hψ hψc hψsub
  have hc : HasCompactSupport (fun x ↦ χ x ^ (2 * n + 5)) :=
    hχc.comp_left (g := fun t : ℝ ↦ t ^ (2 * n + 5)) (by simp)
  calc
    _ ≤ ∫ x, u x ^ 2 * ‖gradient (quotientMomentTest g u χ n) x‖ ^ 2 := by
      apply integral_mono hi hG
      exact fun x ↦ mul_le_mul_of_nonneg_left
        (verticalDerivative_sq_le_gradient_sq _ _) (sq_nonneg _)
    _ ≤ ∫ x in epigraph g, u x ^ 2 * negativeQuotient u x ^ (2 * n + 4) *
        ‖gradient (fun y ↦ χ y ^ (2 * n + 5)) x‖ ^ 2 := h.power_energy n (hχ.pow _) hc
    _ ≤ _ := cutoff_power_gradient_error_le_aux h n hχ hχc hχsupport hχ0 hderiv

private theorem integral_test_product_eq_moment_aux (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} {r : ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupport : Function.support χ ⊆ ball 0 r) :
    (∫ x, (u x * quotientMomentTest g u χ n x) *
      (u x * verticalDerivative (quotientMomentTest g u χ n) x)) =
      ∫ x in epigraph g ∩ ball 0 r,
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 5) := by
  calc
    _ = ∫ x, u x ^ 2 * quotientMomentTest g u χ n x *
        verticalDerivative (quotientMomentTest g u χ n) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = _ := (integral_quotientMomentTest_vertical h n hχ hχc).trans
      (cutoff_moment_restrict_aux h hχsupport (by omega))

/-- The PDE energy estimate gives the first-order recursion for every odd cutoff moment. -/
theorem Hypotheses.cutoff_first_moment (h : Hypotheses g u f κ) (n : ℕ)
    {χ : Space (m + 1) → ℝ} {r B : ℝ} (hB : 0 ≤ B)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupport : Function.support χ ⊆ ball 0 r) (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hderiv : ∀ x, ‖fderiv ℝ χ x‖ ≤ B) :
    (∫ x in epigraph g ∩ ball 0 r,
      u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 5)) ≤
      ((2 * n + 5 : ℕ) * B) * ∫ x in epigraph g ∩ ball 0 r,
        u x ^ 2 * (negativeQuotient u x * χ x ^ 2) ^ (2 * n + 4) := by
  obtain ⟨hψ, hψc, hψsub⟩ := quotientMomentTest_regular h n hχ hχc
  have hA := integrable_sq_mul_sq_aux h.solution_contDiffOn.continuousOn hψ.continuous hψc hψsub
  have hD := integrable_sq_mul_vertical_sq_aux h.solution_contDiffOn.continuousOn hψ hψc hψsub
  rw [← integral_test_product_eq_moment_aux h n hχ hχc hχsupport]
  apply integral_mul_le_of_square_bounds
    (by simpa only [mul_pow] using hA) (by simpa only [mul_pow] using hD)
  · apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _) (pow_nonneg
      (mul_nonneg (negativeQuotient_nonneg u x) (sq_nonneg _)) _)
  · exact mul_nonneg (Nat.cast_nonneg _) hB
  · simpa only [mul_pow] using
      integral_test_sq_le_lower_moment_aux h n hχ hχc hχsupport hχbounds
  · simpa only [mul_pow] using integral_test_vertical_sq_le_aux h n hχ hχc hχsupport
      (fun x ↦ (hχbounds x).1) hderiv

end SerrinEpigraph
