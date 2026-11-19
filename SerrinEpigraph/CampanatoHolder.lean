module

public import SerrinEpigraph.SobolevBallCompactness
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Campanato estimates, Hölder continuity and the excess-decay iteration

* `le_of_excess_decay`, `le_of_excess_decay_pure`, `exists_excess_decay_constant`: the iteration
  lemma turning a one-step decay `ψ (θ r) ≤ θ ^ σ ψ r + A r ^ τ` (`σ < τ`) of a quasi-monotone
  quantity into the decay `ψ r ≤ C (r / r₀) ^ σ (ψ r₀ + A r₀ ^ τ)`; `ball_excess_le_of_decay`
  applies it to the un-normalized excess `∫_{B_r} |f - f_{B_r}|²`, which is monotone in `r`
  (`setIntegral_sq_sub_setAverage_mono`).
* `campanato_holder` (values in any Banach space), `campanato_holder_real`: Campanato's
  theorem. Mean oscillation `⨍_{B(x,r)} ‖f - f_{B(x,r)}‖² ≤ M² r^(2α)` makes the limit of ball
  averages `ballAverageLimit f` a continuous representative with
  `‖f̃ x - f_{B(x,r)}‖ ≤ C M r^α` and `‖f̃ x - f̃ y‖ ≤ C M |x - y|^α`; the proof combines dyadic
  telescoping of averages (`norm_ballAverage_sub_le_of_campanato_chain`) with Lebesgue's
  differentiation theorem (`ae_tendsto_ballAverage`).
* `campanato_fderiv_holder`: a Lipschitz function whose a.e. gradient satisfies the Campanato
  condition is differentiable with derivative the continuous representative, `C¹`, and its
  derivative is `α`-Hölder (`hasFDerivAt_of_ae_eq_fderiv` is the underlying regularity lemma).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric ContinuousLinearMap
open scoped Topology Convolution

namespace SerrinEpigraph

/-! ### The excess-decay iteration lemma -/

/-- A recursion `a (k + 1) ≤ q a k + B p ^ k` with `0 ≤ p < q` gives
`a k ≤ q ^ k (a 0 + B / (q - p))`. -/
theorem le_geometric_of_recursion {a : ℕ → ℝ} {q p B : ℝ} (hp : 0 ≤ p) (hpq : p < q)
    (hB : 0 ≤ B) (hrec : ∀ k, a (k + 1) ≤ q * a k + B * p ^ k) (k : ℕ) :
    a k ≤ q ^ k * (a 0 + B / (q - p)) := by
  have hq : 0 < q := hp.trans_lt hpq
  have hqp : 0 < q - p := sub_pos.2 hpq
  have hqpne : q - p ≠ 0 := hqp.ne'
  have key : ∀ k : ℕ, a k ≤ q ^ k * a 0 + B * ((q ^ k - p ^ k) / (q - p)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a (k + 1) ≤ q * a k + B * p ^ k := hrec k
        _ ≤ q * (q ^ k * a 0 + B * ((q ^ k - p ^ k) / (q - p))) + B * p ^ k := by
            have h := mul_le_mul_of_nonneg_left ih hq.le
            linarith
        _ = q ^ (k + 1) * a 0 + B * ((q ^ (k + 1) - p ^ (k + 1)) / (q - p)) := by
            field_simp
            ring
  have hle : (q ^ k - p ^ k) / (q - p) ≤ q ^ k / (q - p) :=
    div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hp k)) hqp.le
  calc a k ≤ q ^ k * a 0 + B * ((q ^ k - p ^ k) / (q - p)) := key k
    _ ≤ q ^ k * a 0 + B * (q ^ k / (q - p)) := by
        have h := mul_le_mul_of_nonneg_left hle hB
        linarith
    _ = q ^ k * (a 0 + B / (q - p)) := by ring

/-- Bounds at the geometric scales `θ ^ k r₀` together with quasi-monotonicity on comparable
scales give `ψ r ≤ K θ^(-σ) (r / r₀) ^ σ B` for every `0 < r ≤ r₀`. -/
private theorem le_of_geometric_scales {ψ : ℝ → ℝ} {θ σ K B r₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hσ : 0 ≤ σ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hr₀ : 0 < r₀)
    (hmono : ∀ s r, 0 < s → θ * r ≤ s → s ≤ r → r ≤ r₀ → ψ s ≤ K * ψ r)
    (hgeom : ∀ k : ℕ, ψ (θ ^ k * r₀) ≤ (θ ^ σ) ^ k * B) {r : ℝ} (hr : 0 < r)
    (hrr₀ : r ≤ r₀) :
    ψ r ≤ K / θ ^ σ * (r / r₀) ^ σ * B := by
  classical
  have hex : ∃ m : ℕ, θ ^ m * r₀ < r := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hr hr₀) hθ1
    exact ⟨m, by rwa [lt_div_iff₀ hr₀] at hm⟩
  have hm_spec : θ ^ Nat.find hex * r₀ < r := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hm_spec
    linarith
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  have hk_le : r ≤ θ ^ k * r₀ := by
    have hkm : ¬(θ ^ k * r₀ < r) := Nat.find_min hex (by omega)
    exact not_lt.mp hkm
  have hθk : 0 < θ ^ k := pow_pos hθ0 k
  have hθk1 : θ ^ k ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
  have hsucc : θ ^ k * θ = θ ^ Nat.find hex := by rw [hk, pow_succ]
  have hstep : ψ r ≤ K * ψ (θ ^ k * r₀) := by
    refine hmono r (θ ^ k * r₀) hr ?_ hk_le (by nlinarith)
    have h1 : θ * (θ ^ k * r₀) = θ ^ Nat.find hex * r₀ := by rw [← hsucc]; ring
    rw [h1]
    exact hm_spec.le
  have hpow : (θ ^ σ) ^ k ≤ (r / r₀) ^ σ / θ ^ σ := by
    rw [Real.rpow_pow_comm hθ0.le, le_div_iff₀ (Real.rpow_pos_of_pos hθ0 σ),
      ← Real.mul_rpow hθk.le hθ0.le]
    apply Real.rpow_le_rpow (by positivity) _ hσ
    rw [hsucc, le_div_iff₀ hr₀]
    exact hm_spec.le
  calc ψ r ≤ K * ψ (θ ^ k * r₀) := hstep
    _ ≤ K * ((θ ^ σ) ^ k * B) := mul_le_mul_of_nonneg_left (hgeom k) hK
    _ ≤ K * ((r / r₀) ^ σ / θ ^ σ * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hB) hK
    _ = K / θ ^ σ * (r / r₀) ^ σ * B := by ring

/-- **Excess-decay iteration lemma.** Let `ψ` be quasi-monotone on comparable scales
(`ψ s ≤ K ψ r` whenever `θ r ≤ s ≤ r ≤ r₀`) with `ψ r₀ ≥ 0`, and suppose the one-step decay
`ψ (θ r) ≤ θ ^ σ ψ r + A r ^ τ` holds for `0 < r ≤ r₀`, where `0 < θ < 1`, `0 ≤ σ < τ`,
`A ≥ 0`. Then `ψ r ≤ K / (θ^σ (θ^σ - θ^τ)) (r / r₀) ^ σ (ψ r₀ + A r₀ ^ τ)` for `0 < r ≤ r₀`. -/
theorem le_of_excess_decay {ψ : ℝ → ℝ} {θ σ τ K A r₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hσ : 0 ≤ σ) (hστ : σ < τ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hr₀ : 0 < r₀) (hψr₀ : 0 ≤ ψ r₀)
    (hmono : ∀ s r, 0 < s → θ * r ≤ s → s ≤ r → r ≤ r₀ → ψ s ≤ K * ψ r)
    (hdecay : ∀ r, 0 < r → r ≤ r₀ → ψ (θ * r) ≤ θ ^ σ * ψ r + A * r ^ τ)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r ≤ r₀) :
    ψ r ≤ K / (θ ^ σ * (θ ^ σ - θ ^ τ)) * (r / r₀) ^ σ * (ψ r₀ + A * r₀ ^ τ) := by
  have hp0 : 0 ≤ θ ^ τ := Real.rpow_nonneg hθ0.le τ
  have hpq : θ ^ τ < θ ^ σ := Real.rpow_lt_rpow_of_exponent_gt hθ0 hθ1 hστ
  have hq0 : 0 < θ ^ σ := Real.rpow_pos_of_pos hθ0 σ
  have hq1 : θ ^ σ ≤ 1 := Real.rpow_le_one hθ0.le hθ1.le hσ
  have hqp : 0 < θ ^ σ - θ ^ τ := sub_pos.2 hpq
  have hqp1 : θ ^ σ - θ ^ τ ≤ 1 := by linarith
  have hBnn : 0 ≤ A * r₀ ^ τ := mul_nonneg hA (Real.rpow_nonneg hr₀.le τ)
  have hrec : ∀ k : ℕ, ψ (θ ^ (k + 1) * r₀) ≤
      θ ^ σ * ψ (θ ^ k * r₀) + A * r₀ ^ τ * (θ ^ τ) ^ k := by
    intro k
    have hθk : 0 < θ ^ k := pow_pos hθ0 k
    have hθk1 : θ ^ k ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
    have h1 := hdecay (θ ^ k * r₀) (by positivity) (by nlinarith)
    have h2 : θ * (θ ^ k * r₀) = θ ^ (k + 1) * r₀ := by rw [pow_succ]; ring
    have h3 : (θ ^ k * r₀) ^ τ = r₀ ^ τ * (θ ^ τ) ^ k := by
      rw [Real.mul_rpow hθk.le hr₀.le, Real.rpow_pow_comm hθ0.le]
      ring
    rw [h2, h3] at h1
    linarith
  have hgeom := le_geometric_of_recursion (a := fun k ↦ ψ (θ ^ k * r₀)) hp0 hpq hBnn hrec
  have hgeom' : ∀ k : ℕ, ψ (θ ^ k * r₀) ≤
      (θ ^ σ) ^ k * ((ψ r₀ + A * r₀ ^ τ) / (θ ^ σ - θ ^ τ)) := by
    intro k
    refine (hgeom k).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0.le k))
    simp only [pow_zero, one_mul]
    rw [add_div]
    have : ψ r₀ ≤ ψ r₀ / (θ ^ σ - θ ^ τ) := le_div_self hψr₀ hqp hqp1
    linarith
  have hfin := le_of_geometric_scales hθ0 hθ1 hσ hK
    (div_nonneg (add_nonneg hψr₀ hBnn) hqp.le) hr₀ hmono hgeom' hr hrr₀
  have hq0' : θ ^ σ ≠ 0 := hq0.ne'
  have hqp' : θ ^ σ - θ ^ τ ≠ 0 := hqp.ne'
  calc ψ r ≤ K / θ ^ σ * (r / r₀) ^ σ * ((ψ r₀ + A * r₀ ^ τ) / (θ ^ σ - θ ^ τ)) := hfin
    _ = K / (θ ^ σ * (θ ^ σ - θ ^ τ)) * (r / r₀) ^ σ * (ψ r₀ + A * r₀ ^ τ) := by
        field_simp

/-- **Excess-decay iteration lemma, pure form.** If `ψ (θ r) ≤ θ ^ σ ψ r` for `0 < r ≤ r₀` and
`ψ` is quasi-monotone on comparable scales, then `ψ r ≤ K θ^(-σ) (r / r₀) ^ σ ψ r₀`. -/
theorem le_of_excess_decay_pure {ψ : ℝ → ℝ} {θ σ K r₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hσ : 0 ≤ σ) (hK : 0 ≤ K) (hr₀ : 0 < r₀) (hψr₀ : 0 ≤ ψ r₀)
    (hmono : ∀ s r, 0 < s → θ * r ≤ s → s ≤ r → r ≤ r₀ → ψ s ≤ K * ψ r)
    (hdecay : ∀ r, 0 < r → r ≤ r₀ → ψ (θ * r) ≤ θ ^ σ * ψ r)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r ≤ r₀) :
    ψ r ≤ K / θ ^ σ * (r / r₀) ^ σ * ψ r₀ := by
  have hq0 : 0 < θ ^ σ := Real.rpow_pos_of_pos hθ0 σ
  have hgeom : ∀ k : ℕ, ψ (θ ^ k * r₀) ≤ (θ ^ σ) ^ k * ψ r₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hθk : 0 < θ ^ k := pow_pos hθ0 k
      have hθk1 : θ ^ k ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
      have h1 := hdecay (θ ^ k * r₀) (by positivity) (by nlinarith)
      have h2 : θ * (θ ^ k * r₀) = θ ^ (k + 1) * r₀ := by rw [pow_succ]; ring
      rw [h2] at h1
      calc ψ (θ ^ (k + 1) * r₀) ≤ θ ^ σ * ψ (θ ^ k * r₀) := h1
        _ ≤ θ ^ σ * ((θ ^ σ) ^ k * ψ r₀) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = (θ ^ σ) ^ (k + 1) * ψ r₀ := by ring
  exact le_of_geometric_scales hθ0 hθ1 hσ hK hψr₀ hr₀ hmono hgeom hr hrr₀

/-- **Excess-decay iteration lemma** with a constant depending only on `θ, σ, τ, K`. -/
theorem exists_excess_decay_constant {θ σ τ K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ : 0 ≤ σ)
    (hστ : σ < τ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℝ → ℝ) (A r₀ : ℝ), 0 ≤ A → 0 < r₀ → 0 ≤ ψ r₀ →
      (∀ s r, 0 < s → θ * r ≤ s → s ≤ r → r ≤ r₀ → ψ s ≤ K * ψ r) →
      (∀ r, 0 < r → r ≤ r₀ → ψ (θ * r) ≤ θ ^ σ * ψ r + A * r ^ τ) →
      ∀ r, 0 < r → r ≤ r₀ → ψ r ≤ C * (r / r₀) ^ σ * (ψ r₀ + A * r₀ ^ τ) := by
  have hq0 : 0 < θ ^ σ := Real.rpow_pos_of_pos hθ0 σ
  have hqp : 0 < θ ^ σ - θ ^ τ := sub_pos.2 (Real.rpow_lt_rpow_of_exponent_gt hθ0 hθ1 hστ)
  exact ⟨K / (θ ^ σ * (θ ^ σ - θ ^ τ)), by positivity,
    fun ψ A r₀ hA hr₀ hψr₀ hmono hdecay r hr hrr₀ ↦
      le_of_excess_decay hθ0 hθ1 hσ hστ hK hA hr₀ hψr₀ hmono hdecay hr hrr₀⟩

/-! ### Monotonicity of the un-normalized excess -/

/-- The mean minimizes the squared deviation: `∫_S |f - f_S|² ≤ ∫_S |f - c|²`. -/
theorem setIntegral_sq_sub_setAverage_le {d : ℕ} {S : Set (Space d)} (hSf : volume S ≠ ⊤)
    {f : Space d → ℝ} (hf : MemLp f 2 (volume.restrict S)) (c : ℝ) :
    ∫ y in S, (f y - ⨍ z in S, f z) ^ 2 ≤ ∫ y in S, (f y - c) ^ 2 := by
  by_cases hS0 : volume S = 0
  · simp [Measure.restrict_eq_zero.2 hS0]
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have hm : 0 < volume.real S := ENNReal.toReal_pos hS0 hSf
  have hfi : IntegrableOn f S := hf.integrable one_le_two
  have hf2 : IntegrableOn (fun y ↦ f y ^ 2) S := hf.integrable_sq
  have hquad : ∀ a : ℝ, ∫ y in S, (f y - a) ^ 2 =
      (∫ y in S, f y ^ 2) - 2 * a * (∫ y in S, f y) + volume.real S * a ^ 2 := by
    intro a
    have he : (fun z ↦ (f z - a) ^ 2) = fun z ↦ (f z ^ 2 - (2 * a) * f z) + a ^ 2 := by
      funext z
      ring
    have h1 : IntegrableOn (fun z ↦ f z ^ 2 - (2 * a) * f z) S := hf2.sub (hfi.const_mul _)
    have h2 : IntegrableOn (fun z ↦ (2 * a) * f z) S := hfi.const_mul _
    have h3 : IntegrableOn (fun _ : Space d ↦ a ^ 2) S := integrableOn_const hSf
    rw [he, integral_add h1 h3, integral_sub hf2 h2, integral_const_mul, setIntegral_const,
      smul_eq_mul]
  rw [hquad, hquad, setAverage_eq, smul_eq_mul]
  set m := volume.real S
  set A := ∫ y in S, f y
  have hmne : m ≠ 0 := hm.ne'
  have key : 2 * c * A - 2 * (m⁻¹ * A) * A + m * (m⁻¹ * A) ^ 2 - m * c ^ 2 =
      -(m * (c - m⁻¹ * A) ^ 2) := by
    field_simp
    ring
  nlinarith [mul_nonneg hm.le (sq_nonneg (c - m⁻¹ * A))]

/-- The un-normalized excess `∫_S |f - f_S|²` is monotone in the domain `S`. -/
theorem setIntegral_sq_sub_setAverage_mono {d : ℕ} {S T : Set (Space d)} (hST : S ⊆ T)
    (hTf : volume T ≠ ⊤) {f : Space d → ℝ} (hf : MemLp f 2 (volume.restrict T)) :
    ∫ y in S, (f y - ⨍ z in S, f z) ^ 2 ≤ ∫ y in T, (f y - ⨍ z in T, f z) ^ 2 := by
  have hSf : volume S ≠ ⊤ := ne_top_of_le_ne_top hTf (measure_mono hST)
  have hfS : MemLp f 2 (volume.restrict S) := hf.mono_measure (Measure.restrict_mono hST le_rfl)
  refine (setIntegral_sq_sub_setAverage_le hSf hfS (⨍ z in T, f z)).trans ?_
  have : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hTf
  have hint : IntegrableOn (fun y ↦ (f y - ⨍ z in T, f z) ^ 2) T :=
    (hf.sub (memLp_const _)).integrable_sq
  exact setIntegral_mono_set hint (Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (Eventually.of_forall hST)

/-- **Excess decay on balls.** If the un-normalized excess `ψ r = ∫_{B_r} |f - f_{B_r}|²` of
`f ∈ L²(B_{r₀})` satisfies `ψ (θ r) ≤ θ^(d+2α) ψ r + A r^(d+2β)` for `0 < r ≤ r₀` with
`0 < θ < 1`, `0 ≤ α < β`, `A ≥ 0`, then
`ψ r ≤ C (r / r₀)^(d+2α) (ψ r₀ + A r₀^(d+2β))` for all `0 < r ≤ r₀`, with
`C = 1 / (θ^(d+2α) (θ^(d+2α) - θ^(d+2β)))`. -/
theorem ball_excess_le_of_decay {d : ℕ} {x : Space d} {f : Space d → ℝ} {θ α β A r₀ : ℝ}
    (hf : MemLp f 2 (volume.restrict (ball x r₀))) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hα : 0 ≤ α)
    (hαβ : α < β) (hA : 0 ≤ A) (hr₀ : 0 < r₀)
    (hdecay : ∀ r, 0 < r → r ≤ r₀ →
      ∫ y in ball x (θ * r), (f y - ⨍ z in ball x (θ * r), f z) ^ 2 ≤
        θ ^ ((d : ℝ) + 2 * α) * (∫ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2) +
          A * r ^ ((d : ℝ) + 2 * β))
    {r : ℝ} (hr : 0 < r) (hrr₀ : r ≤ r₀) :
    ∫ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2 ≤
      1 / (θ ^ ((d : ℝ) + 2 * α) * (θ ^ ((d : ℝ) + 2 * α) - θ ^ ((d : ℝ) + 2 * β))) *
        (r / r₀) ^ ((d : ℝ) + 2 * α) *
          ((∫ y in ball x r₀, (f y - ⨍ z in ball x r₀, f z) ^ 2) + A * r₀ ^ ((d : ℝ) + 2 * β)) := by
  have hσ : (0 : ℝ) ≤ (d : ℝ) + 2 * α := by positivity
  have hστ : (d : ℝ) + 2 * α < (d : ℝ) + 2 * β := by linarith
  refine le_of_excess_decay (ψ := fun r ↦ ∫ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2)
    hθ0 hθ1 hσ hστ zero_le_one hA hr₀ (integral_nonneg (fun _ ↦ sq_nonneg _)) ?_ hdecay hr hrr₀
  intro s t _ _ hst htr₀
  rw [one_mul]
  exact setIntegral_sq_sub_setAverage_mono (ball_subset_ball hst) measure_ball_lt_top.ne
    (hf.mono_measure (Measure.restrict_mono (ball_subset_ball htr₀) le_rfl))

/-! ### Comparison of averages over nested balls -/

section Campanato

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The limit of the averages of `f` over the balls `B(x, r)` as `r → 0⁺`; by Lebesgue's
differentiation theorem it is a representative of `f`. -/
def ballAverageLimit {d : ℕ} (f : Space d → E) (x : Space d) : E :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r ↦ ⨍ y in ball x r, f y)

/-- The constant `√(2^d) / (1 - 2^(-α))` of the Campanato estimate
`‖f̃ x - f_{B(x,r)}‖ ≤ C M r ^ α`. -/
def campanatoConstant (d : ℕ) (α : ℝ) : ℝ :=
  Real.sqrt (2 ^ d) / (1 - (2 ^ α)⁻¹)

/-- The constant of the Hölder estimate `‖f̃ x - f̃ y‖ ≤ C M |x - y| ^ α`. -/
def campanatoHolderConstant (d : ℕ) (α : ℝ) : ℝ :=
  2 ^ α * (campanatoConstant d α + Real.sqrt (2 ^ d)) + campanatoConstant d α

private theorem two_rpow_inv_lt_one {α : ℝ} (hα : 0 < α) : ((2 : ℝ) ^ α)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hα)

theorem sqrt_two_pow_le_campanatoConstant (d : ℕ) {α : ℝ} (hα : 0 < α) :
    Real.sqrt (2 ^ d) ≤ campanatoConstant d α := by
  have h1 : 0 < 1 - ((2 : ℝ) ^ α)⁻¹ := sub_pos.2 (two_rpow_inv_lt_one hα)
  have h2 : 1 - ((2 : ℝ) ^ α)⁻¹ ≤ 1 := by
    have : 0 ≤ ((2 : ℝ) ^ α)⁻¹ := inv_nonneg.2 (Real.rpow_nonneg zero_le_two α)
    linarith
  exact le_div_self (Real.sqrt_nonneg _) h1 h2

theorem campanatoConstant_nonneg (d : ℕ) {α : ℝ} (hα : 0 < α) : 0 ≤ campanatoConstant d α :=
  (Real.sqrt_nonneg _).trans (sqrt_two_pow_le_campanatoConstant d hα)

private theorem campanatoConstant_identity (d : ℕ) {α : ℝ} (hα : 0 < α) :
    campanatoConstant d α / 2 ^ α + Real.sqrt (2 ^ d) = campanatoConstant d α := by
  unfold campanatoConstant
  have h2α : (2 : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos two_pos α).ne'
  have h1 : 1 - ((2 : ℝ) ^ α)⁻¹ ≠ 0 := (sub_pos.2 (two_rpow_inv_lt_one hα)).ne'
  have h3 : (2 : ℝ) ^ α - 1 ≠ 0 := by
    intro h
    apply h1
    field_simp
    linarith
  field_simp
  ring

/-- Euclidean balls of positive radius have positive volume. -/
private theorem measureReal_ball_pos_aux {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball x r) :=
  ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

/-- The ratio of the volumes of two balls. -/
private theorem measureReal_ball_div {d : ℕ} (x y : Space d) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) : volume.real (ball x t) / volume.real (ball y s) = (t / s) ^ d := by
  have hc : 0 < (volume (ball (0 : Space d) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  rw [measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume x ht,
    Measure.addHaar_ball_of_pos volume y hs, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), div_pow]
  have hsd : s ^ d ≠ 0 := pow_ne_zero d hs.ne'
  field_simp

/-- `t ^ (2 α) = (t ^ α) ^ 2` for `t ≥ 0`. -/
private theorem rpow_two_mul_eq_sq {t α : ℝ} (ht : 0 ≤ t) : t ^ (2 * α) = (t ^ α) ^ 2 := by
  rw [mul_comm, Real.rpow_mul ht, Real.rpow_two]

/-- **Averages over nested sets**: for `S ⊆ T`,
`‖f_S - f_T‖² ≤ (|T| / |S|) ⨍_T ‖f - f_T‖²`. -/
theorem norm_setAverage_sub_setAverage_sq_le {d : ℕ} {S T : Set (Space d)} (hST : S ⊆ T)
    (hS : 0 < volume.real S) (hTf : volume T ≠ ⊤) {f : Space d → E}
    (hf : MemLp f 2 (volume.restrict T)) :
    ‖(⨍ y in S, f y) - ⨍ y in T, f y‖ ^ 2 ≤
      volume.real T / volume.real S * ⨍ y in T, ‖f y - ⨍ z in T, f z‖ ^ 2 := by
  have hSf : volume S ≠ ⊤ := ne_top_of_le_ne_top hTf (measure_mono hST)
  have hT : 0 < volume.real T := hS.trans_le (measureReal_mono hST hTf)
  have : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hTf
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  set c := ⨍ y in T, f y with hc
  have hfS : MemLp f 2 (volume.restrict S) := hf.mono_measure (Measure.restrict_mono hST le_rfl)
  have hhT : MemLp (fun y ↦ f y - c) 2 (volume.restrict T) := hf.sub (memLp_const c)
  have hhS : MemLp (fun y ↦ f y - c) 2 (volume.restrict S) := hfS.sub (memLp_const c)
  have hfiS : IntegrableOn f S := hfS.integrable one_le_two
  have hnS : IntegrableOn (fun y ↦ ‖f y - c‖) S := (hhS.integrable one_le_two).norm
  have hn2S : IntegrableOn (fun y ↦ ‖f y - c‖ ^ 2) S :=
    (memLp_two_iff_integrable_sq_norm hhS.aestronglyMeasurable).1 hhS
  have hn2T : IntegrableOn (fun y ↦ ‖f y - c‖ ^ 2) T :=
    (memLp_two_iff_integrable_sq_norm hhT.aestronglyMeasurable).1 hhT
  have h1 : (⨍ y in S, f y) - c = (volume.real S)⁻¹ • ∫ y in S, (f y - c) := by
    rw [integral_sub hfiS (integrableOn_const hSf), setIntegral_const, setAverage_eq, smul_sub,
      smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
  have h2 : ‖(⨍ y in S, f y) - c‖ ≤ (volume.real S)⁻¹ * ∫ y in S, ‖f y - c‖ := by
    rw [h1, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS.le)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.2 hS.le)
  have h3 : (∫ y in S, ‖f y - c‖) ^ 2 ≤ volume.real S * ∫ y in S, ‖f y - c‖ ^ 2 := by
    have h := sq_integral_le_measureReal_mul_integral_sq (μ := volume.restrict S) hnS hn2S
    rwa [measureReal_restrict_apply_univ] at h
  have h4 : ∫ y in S, ‖f y - c‖ ^ 2 ≤ ∫ y in T, ‖f y - c‖ ^ 2 :=
    setIntegral_mono_set hn2T (Eventually.of_forall (fun _ ↦ by positivity))
      (Eventually.of_forall hST)
  have hsq : ‖(⨍ y in S, f y) - c‖ ^ 2 ≤ ((volume.real S)⁻¹ * ∫ y in S, ‖f y - c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [setAverage_eq volume (fun y ↦ ‖f y - c‖ ^ 2) T, smul_eq_mul]
  have hSne : volume.real S ≠ 0 := hS.ne'
  have hTne : volume.real T ≠ 0 := hT.ne'
  calc ‖(⨍ y in S, f y) - c‖ ^ 2 ≤ ((volume.real S)⁻¹ * ∫ y in S, ‖f y - c‖) ^ 2 := hsq
    _ = (volume.real S)⁻¹ ^ 2 * (∫ y in S, ‖f y - c‖) ^ 2 := by ring
    _ ≤ (volume.real S)⁻¹ ^ 2 * (volume.real S * ∫ y in T, ‖f y - c‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hS.le))
          (by positivity)
    _ = volume.real T / volume.real S * ((volume.real T)⁻¹ * ∫ y in T, ‖f y - c‖ ^ 2) := by
        field_simp

/-- **Averages over nested balls**: for `B(y, s) ⊆ B(x, t)`,
`‖f_{B(y,s)} - f_{B(x,t)}‖² ≤ (t / s)^d ⨍_{B(x,t)} ‖f - f_{B(x,t)}‖²`. -/
theorem norm_ballAverage_sub_sq_le {d : ℕ} {x y : Space d} {s t : ℝ} (hs : 0 < s)
    (hsub : ball y s ⊆ ball x t) {f : Space d → E}
    (hf : MemLp f 2 (volume.restrict (ball x t))) :
    ‖(⨍ z in ball y s, f z) - ⨍ z in ball x t, f z‖ ^ 2 ≤
      (t / s) ^ d * ⨍ z in ball x t, ‖f z - ⨍ w in ball x t, f w‖ ^ 2 := by
  have ht : 0 < t := dist_nonneg.trans_lt (hsub (mem_ball_self hs))
  have h := norm_setAverage_sub_setAverage_sq_le hsub (measureReal_ball_pos_aux y hs)
    measure_ball_lt_top.ne hf
  rwa [measureReal_ball_div x y hs ht] at h

/-- One comparison step under the Campanato bound at the outer ball, for comparable radii. -/
private theorem norm_ballAverage_sub_le_of_campanato {d : ℕ} {f : Space d → E} {x y : Space d}
    {s t M α : ℝ} (hs : 0 < s) (ht : 0 < t) (hM : 0 ≤ M) (hsub : ball y s ⊆ ball x t)
    (hts : t ≤ 2 * s) (hf : MemLp f 2 (volume.restrict (ball x t)))
    (hcamp : ⨍ z in ball x t, ‖f z - ⨍ w in ball x t, f w‖ ^ 2 ≤ M ^ 2 * t ^ (2 * α)) :
    ‖(⨍ z in ball y s, f z) - ⨍ z in ball x t, f z‖ ≤ Real.sqrt (2 ^ d) * M * t ^ α := by
  have h := norm_ballAverage_sub_sq_le hs hsub hf
  have hE0 : 0 ≤ ⨍ z in ball x t, ‖f z - ⨍ w in ball x t, f w‖ ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 measureReal_nonneg)
      (integral_nonneg (fun _ ↦ by positivity))
  have hratio : (t / s) ^ d ≤ 2 ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ hs]
    linarith
  have hnn : 0 ≤ Real.sqrt (2 ^ d) * M * t ^ α :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (Real.rpow_nonneg ht.le α)
  have hb : ‖(⨍ z in ball y s, f z) - ⨍ z in ball x t, f z‖ ^ 2 ≤
      (Real.sqrt (2 ^ d) * M * t ^ α) ^ 2 := by
    calc _ ≤ (t / s) ^ d * ⨍ z in ball x t, ‖f z - ⨍ w in ball x t, f w‖ ^ 2 := h
      _ ≤ 2 ^ d * (M ^ 2 * t ^ (2 * α)) := mul_le_mul hratio hcamp hE0 (by positivity)
      _ = (Real.sqrt (2 ^ d) * M * t ^ α) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), rpow_two_mul_eq_sq ht.le]
          ring
  exact (sq_le_sq₀ (norm_nonneg _) hnn).1 hb

/-- **Dyadic chaining**: if the Campanato bound holds on all balls `B(x, r)`, `r ≤ t`, then
`‖f_{B(x,s)} - f_{B(x,t)}‖ ≤ D M t ^ α` for all `0 < s ≤ t`, with `D = campanatoConstant d α`. -/
theorem norm_ballAverage_sub_le_of_campanato_chain {d : ℕ} {f : Space d → E} {x : Space d}
    {α M t : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (ht : 0 < t)
    (hf : MemLp f 2 (volume.restrict (ball x t)))
    (hcamp : ∀ r, 0 < r → r ≤ t →
      ⨍ z in ball x r, ‖f z - ⨍ w in ball x r, f w‖ ^ 2 ≤ M ^ 2 * r ^ (2 * α))
    {s : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ‖(⨍ z in ball x s, f z) - ⨍ z in ball x t, f z‖ ≤ campanatoConstant d α * M * t ^ α := by
  have hD := sqrt_two_pow_le_campanatoConstant d hα
  have hD0 := campanatoConstant_nonneg d hα
  have hfr : ∀ r, r ≤ t → MemLp f 2 (volume.restrict (ball x r)) := fun r hr ↦
    hf.mono_measure (Measure.restrict_mono (ball_subset_ball hr) le_rfl)
  have key : ∀ k : ℕ, ∀ t', 0 < t' → t' ≤ t → ∀ s, t' / 2 ^ k ≤ s → s ≤ t' →
      ‖(⨍ z in ball x s, f z) - ⨍ z in ball x t', f z‖ ≤
        campanatoConstant d α * M * t' ^ α := by
    intro k
    induction k with
    | zero =>
      intro t' ht' _ s hs hst
      rw [pow_zero, div_one] at hs
      have hst' : s = t' := le_antisymm hst hs
      rw [hst', sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg hD0 hM) (Real.rpow_nonneg ht'.le α)
    | succ k ih =>
      intro t' ht' ht't s hs hst
      have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
      have hstep : ∀ s', t' / 2 ≤ s' → s' ≤ t' →
          ‖(⨍ z in ball x s', f z) - ⨍ z in ball x t', f z‖ ≤
            Real.sqrt (2 ^ d) * M * t' ^ α := fun s' hs'1 hs'2 ↦
        norm_ballAverage_sub_le_of_campanato (by linarith) ht' hM (ball_subset_ball hs'2)
          (by linarith) (hfr t' ht't) (hcamp t' ht' ht't)
      by_cases hs2 : t' / 2 ≤ s
      · calc _ ≤ Real.sqrt (2 ^ d) * M * t' ^ α := hstep s hs2 hst
          _ ≤ campanatoConstant d α * M * t' ^ α :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hM)
                (Real.rpow_nonneg ht'.le α)
      · have hs2 : s < t' / 2 := not_le.mp hs2
        have hh : 0 < t' / 2 := by positivity
        have hs' : t' / 2 / 2 ^ k ≤ s := by
          rw [div_div, ← pow_succ']
          exact hs
        have h1 := ih (t' / 2) hh (by linarith) s hs' hs2.le
        have h2 := hstep (t' / 2) le_rfl (by linarith)
        have h3 : (t' / 2) ^ α = t' ^ α / 2 ^ α := Real.div_rpow ht'.le zero_le_two α
        calc ‖(⨍ z in ball x s, f z) - ⨍ z in ball x t', f z‖
            ≤ ‖(⨍ z in ball x s, f z) - ⨍ z in ball x (t' / 2), f z‖ +
              ‖(⨍ z in ball x (t' / 2), f z) - ⨍ z in ball x t', f z‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ campanatoConstant d α * M * (t' / 2) ^ α + Real.sqrt (2 ^ d) * M * t' ^ α :=
              add_le_add h1 h2
          _ = M * t' ^ α * (campanatoConstant d α / 2 ^ α + Real.sqrt (2 ^ d)) := by
              rw [h3]
              ring
          _ = campanatoConstant d α * M * t' ^ α := by
              rw [campanatoConstant_identity d hα]
              ring
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hs ht) (by norm_num : (1 / 2 : ℝ) < 1)
  have hk' : t / 2 ^ k ≤ s := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_pow, one_pow, div_lt_div_iff₀ h2k ht] at hk
    rw [div_le_iff₀ h2k]
    linarith
  exact key k t ht le_rfl s hk' hst

/-- Under the Campanato bound on all balls `B(x, r)`, `r ≤ t₀`, the ball averages converge as
`r → 0⁺` to `ballAverageLimit f x`, with `‖ballAverageLimit f x - f_{B(x,t)}‖ ≤ D M t ^ α`. -/
theorem tendsto_ballAverage_of_campanato {d : ℕ} {f : Space d → E} {x : Space d}
    {α M t₀ : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (ht₀ : 0 < t₀)
    (hf : MemLp f 2 (volume.restrict (ball x t₀)))
    (hcamp : ∀ r, 0 < r → r ≤ t₀ →
      ⨍ z in ball x r, ‖f z - ⨍ w in ball x r, f w‖ ^ 2 ≤ M ^ 2 * r ^ (2 * α)) :
    Tendsto (fun r ↦ ⨍ y in ball x r, f y) (𝓝[>] 0) (𝓝 (ballAverageLimit f x)) ∧
      ∀ t, 0 < t → t ≤ t₀ →
        ‖ballAverageLimit f x - ⨍ y in ball x t, f y‖ ≤ campanatoConstant d α * M * t ^ α := by
  set g : ℝ → E := fun r ↦ ⨍ y in ball x r, f y with hg
  have hchain : ∀ t, 0 < t → t ≤ t₀ → ∀ s, 0 < s → s ≤ t →
      ‖g s - g t‖ ≤ campanatoConstant d α * M * t ^ α := by
    intro t ht htt₀ s hs hst
    exact norm_ballAverage_sub_le_of_campanato_chain hα hM ht
      (hf.mono_measure (Measure.restrict_mono (ball_subset_ball htt₀) le_rfl))
      (fun r hr hrt ↦ hcamp r hr (hrt.trans htt₀)) hs hst
  have hlim0 : Tendsto (fun δ : ℝ ↦ 2 * (campanatoConstant d α * M * δ ^ α)) (𝓝[>] 0)
      (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ ↦ δ ^ α) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
      rwa [Real.zero_rpow hα.ne'] at h
    have h2 : Tendsto (fun δ : ℝ ↦ 2 * (campanatoConstant d α * M * δ ^ α)) (𝓝[>] 0)
        (𝓝 (2 * (campanatoConstant d α * M * 0))) :=
      ((h1.const_mul (campanatoConstant d α * M)).const_mul 2).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [mul_zero, mul_zero] at h2
  have hcauchy : Cauchy (map g (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε ↦ ?_⟩
    have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioc 0 t₀ := Ioc_mem_nhdsGT ht₀
    obtain ⟨δ, ⟨hδ0, hδt₀⟩, hδε⟩ := (hev1.and (hlim0.eventually (gt_mem_nhds hε))).exists
    refine ⟨g '' Set.Ioc 0 δ, image_mem_map (Ioc_mem_nhdsGT hδ0), ?_⟩
    rintro _ ⟨s, ⟨hs0, hsδ⟩, rfl⟩ _ ⟨s', ⟨hs'0, hs'δ⟩, rfl⟩
    have h1 := hchain δ hδ0 hδt₀ s hs0 hsδ
    have h2 := hchain δ hδ0 hδt₀ s' hs'0 hs'δ
    rw [dist_eq_norm]
    calc ‖g s - g s'‖ ≤ ‖g s - g δ‖ + ‖g δ - g s'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖g s - g δ‖ + ‖g s' - g δ‖ := by rw [norm_sub_rev (g δ)]
      _ ≤ 2 * (campanatoConstant d α * M * δ ^ α) := by linarith
      _ < ε := hδε
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hcauchy
  have hlimL : ballAverageLimit f x = L := hL.limUnder_eq
  refine ⟨by rw [hlimL]; exact hL, fun t ht htt₀ ↦ ?_⟩
  rw [hlimL]
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖g s - g t‖ ≤ campanatoConstant d α * M * t ^ α := by
    filter_upwards [Ioc_mem_nhdsGT ht] with s hs
    exact hchain t ht htt₀ s hs.1 hs.2
  exact le_of_tendsto ((hL.sub_const (g t)).norm) hev

/-! ### Lebesgue differentiation on balls -/

omit [CompleteSpace E] in
/-- For `r > 0`, averages over open and closed balls agree. -/
private theorem setAverage_closedBall_eq_ball {d : ℕ} (f : Space d → E) (x : Space d) {r : ℝ}
    (hr : 0 < r) : ⨍ y in closedBall x r, f y = ⨍ y in ball x r, f y := by
  rcases subsingleton_or_nontrivial (Space d) with h | h
  · have hsets : closedBall x r = ball x r := by
      ext y
      rw [Subsingleton.elim y x]
      simp only [mem_closedBall, mem_ball, dist_self]
      exact ⟨fun _ ↦ hr, fun _ ↦ hr.le⟩
    rw [hsets]
  · have hae : ball x r =ᵐ[volume] closedBall x r :=
      ae_eq_of_subset_of_measure_ge ball_subset_closedBall
        (Measure.addHaar_closedBall_eq_addHaar_ball volume x r).le
        measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
    rw [setAverage_eq, setAverage_eq, setIntegral_congr_set hae.symm, measureReal_def,
      measureReal_def, measure_congr hae.symm]

/-- **Lebesgue's differentiation theorem on a ball**: a function integrable on every ball
`B(x₀, r)`, `r < R`, is almost everywhere on `B(x₀, R)` the limit of its ball averages. -/
theorem ae_tendsto_ballAverage {d : ℕ} {f : Space d → E} {x₀ : Space d} {R : ℝ}
    (hf : ∀ r < R, IntegrableOn f (ball x₀ r)) :
    ∀ᵐ x ∂(volume.restrict (ball x₀ R)),
      Tendsto (fun r ↦ ⨍ y in ball x r, f y) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [ae_restrict_iff' measurableSet_ball]
  have hk : ∀ k : ℕ, ∀ᵐ x ∂(volume : Measure (Space d)),
      x ∈ ball x₀ (R - 1 / ((k : ℝ) + 1)) →
        Tendsto (fun r ↦ ⨍ y in ball x r, f y) (𝓝[>] 0) (𝓝 (f x)) := by
    intro k
    have hk0 : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have hr₁ : R - 1 / ((k : ℝ) + 1) < R := by linarith
    have hF : LocallyIntegrable ((ball x₀ (R - 1 / ((k : ℝ) + 1))).indicator f) volume :=
      ((integrable_indicator_iff measurableSet_ball).2 (hf _ hr₁)).locallyIntegrable
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hF 1] with x hx hxb
    have h1 : Tendsto (fun r ↦ ⨍ y in closedBall x r,
        (ball x₀ (R - 1 / ((k : ℝ) + 1))).indicator f y) (𝓝[>] 0)
        (𝓝 ((ball x₀ (R - 1 / ((k : ℝ) + 1))).indicator f x)) := by
      refine hx (fun _ : ℝ ↦ x) id tendsto_id ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) < r := hr
      exact mem_closedBall_self (by simp only [id, one_mul]; exact hr'.le)
    rw [Set.indicator_of_mem hxb f] at h1
    apply h1.congr'
    have hpos : 0 < R - 1 / ((k : ℝ) + 1) - dist x x₀ := sub_pos.2 hxb
    filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
    have hsub : closedBall x r ⊆ ball x₀ (R - 1 / ((k : ℝ) + 1)) := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [mem_ball]
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ < R - 1 / ((k : ℝ) + 1) := by linarith [hr.2]
    rw [setAverage_closedBall_eq_ball _ x hr.1, setAverage_eq, setAverage_eq,
      setIntegral_congr_fun measurableSet_ball
        (fun y hy ↦ Set.indicator_of_mem (hsub (ball_subset_closedBall hy)) f)]
  filter_upwards [ae_all_iff.2 hk] with x hx hxR
  have hxR' : dist x x₀ < R := hxR
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hxR')
  exact hx k (by rw [mem_ball]; linarith)

/-! ### Campanato's theorem -/

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem memLp_ball_of_closedBall_subset {d : ℕ} {f : Space d → E} {x₀ : Space d}
    {R : ℝ} (hf : ∀ r < R, MemLp f 2 (volume.restrict (ball x₀ r))) {x : Space d} {t : ℝ}
    (ht : closedBall x t ⊆ ball x₀ R) : MemLp f 2 (volume.restrict (ball x t)) := by
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball isClosed_closedBall ht
  exact (hf r hr).mono_measure (Measure.restrict_mono (ball_subset_closedBall.trans hsub) le_rfl)

/-- **Campanato's theorem.** Let `f` be square integrable on every ball `B(x₀, r)`, `r < R`, and
suppose that for every center `x ∈ B(x₀, R')` (`R' ≤ R`) and every radius `0 < r ≤ ρ₀` with
`closedBall x r ⊆ B(x₀, R)`, `⨍_{B(x,r)} ‖f - f_{B(x,r)}‖² ≤ M² r^(2α)`, where `0 < α`, `M ≥ 0`.
Then the limit of ball averages `f̃ = ballAverageLimit f` is continuous on `B(x₀, R')`, equals `f`
almost everywhere there, satisfies `‖f̃ x - f_{B(x,r)}‖ ≤ C₁ M r^α` at all such `(x, r)`, and
`‖f̃ x - f̃ y‖ ≤ C₂ M |x - y|^α` for `x, y ∈ B(x₀, R')` with `2|x - y| ≤ ρ₀` and
`closedBall x (2|x - y|) ⊆ B(x₀, R)`, with `C₁ = campanatoConstant d α`,
`C₂ = campanatoHolderConstant d α`. -/
theorem campanato_holder {d : ℕ} {f : Space d → E} {x₀ : Space d} {R R' ρ₀ α M : ℝ}
    (hR' : R' ≤ R) (hρ₀ : 0 < ρ₀) (hα : 0 < α) (hM : 0 ≤ M)
    (hf : ∀ r < R, MemLp f 2 (volume.restrict (ball x₀ r)))
    (hcamp : ∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
      ⨍ y in ball x r, ‖f y - ⨍ z in ball x r, f z‖ ^ 2 ≤ M ^ 2 * r ^ (2 * α)) :
    ContinuousOn (ballAverageLimit f) (ball x₀ R') ∧
      f =ᵐ[volume.restrict (ball x₀ R')] ballAverageLimit f ∧
      (∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
        ‖ballAverageLimit f x - ⨍ y in ball x r, f y‖ ≤ campanatoConstant d α * M * r ^ α) ∧
      (∀ x ∈ ball x₀ R', ∀ y ∈ ball x₀ R', 2 * dist x y ≤ ρ₀ →
        closedBall x (2 * dist x y) ⊆ ball x₀ R →
          ‖ballAverageLimit f x - ballAverageLimit f y‖ ≤
            campanatoHolderConstant d α * M * dist x y ^ α) := by
  have hloc : ∀ x ∈ ball x₀ R', ∀ t, 0 < t → t ≤ ρ₀ → closedBall x t ⊆ ball x₀ R →
      ∀ s, 0 < s → s ≤ t →
        ‖ballAverageLimit f x - ⨍ y in ball x s, f y‖ ≤ campanatoConstant d α * M * s ^ α := by
    intro x hx t ht htρ htB
    exact (tendsto_ballAverage_of_campanato hα hM ht (memLp_ball_of_closedBall_subset hf htB)
      (fun r hr hrt ↦ hcamp x hx r hr (hrt.trans htρ)
        ((closedBall_subset_closedBall hrt).trans htB))).2
  have hbound : ∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
      ‖ballAverageLimit f x - ⨍ y in ball x r, f y‖ ≤ campanatoConstant d α * M * r ^ α :=
    fun x hx r hr hrρ hrB ↦ hloc x hx r hr hrρ hrB r hr le_rfl
  have hholder : ∀ x ∈ ball x₀ R', ∀ y ∈ ball x₀ R', 2 * dist x y ≤ ρ₀ →
      closedBall x (2 * dist x y) ⊆ ball x₀ R →
        ‖ballAverageLimit f x - ballAverageLimit f y‖ ≤
          campanatoHolderConstant d α * M * dist x y ^ α := by
    intro x hx y hy hρ hB
    rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with h0 | hpos
    · have hxy : x = y := dist_eq_zero.mp h0.symm
      rw [hxy, sub_self, norm_zero, dist_self, Real.zero_rpow hα.ne', mul_zero]
    have h2ρ : 0 < 2 * dist x y := by positivity
    have hyB : closedBall y (dist x y) ⊆ ball x₀ R := by
      refine (closedBall_subset_closedBall' ?_).trans hB
      rw [dist_comm]
      linarith
    have hsub : ball y (dist x y) ⊆ ball x (2 * dist x y) :=
      ball_subset_ball' (by rw [dist_comm]; linarith)
    have h1 := hbound x hx (2 * dist x y) h2ρ hρ hB
    have h2 := hbound y hy (dist x y) hpos (by linarith) hyB
    have h3 := norm_ballAverage_sub_le_of_campanato hpos h2ρ hM hsub (by linarith)
      (memLp_ball_of_closedBall_subset hf hB) (hcamp x hx (2 * dist x y) h2ρ hρ hB)
    have h4 : (2 * dist x y) ^ α = 2 ^ α * dist x y ^ α := Real.mul_rpow zero_le_two hpos.le
    have htri : ‖ballAverageLimit f x - ballAverageLimit f y‖ ≤
        ‖ballAverageLimit f x - ⨍ z in ball x (2 * dist x y), f z‖ +
          ‖(⨍ z in ball y (dist x y), f z) - ⨍ z in ball x (2 * dist x y), f z‖ +
            ‖ballAverageLimit f y - ⨍ z in ball y (dist x y), f z‖ := by
      have e : ballAverageLimit f x - ballAverageLimit f y =
          (ballAverageLimit f x - ⨍ z in ball x (2 * dist x y), f z) -
            ((⨍ z in ball y (dist x y), f z) - ⨍ z in ball x (2 * dist x y), f z) -
              (ballAverageLimit f y - ⨍ z in ball y (dist x y), f z) := by abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    calc ‖ballAverageLimit f x - ballAverageLimit f y‖
        ≤ campanatoConstant d α * M * (2 * dist x y) ^ α +
            Real.sqrt (2 ^ d) * M * (2 * dist x y) ^ α +
              campanatoConstant d α * M * dist x y ^ α :=
          htri.trans (add_le_add (add_le_add h1 h3) h2)
      _ = campanatoHolderConstant d α * M * dist x y ^ α := by
          rw [h4]
          unfold campanatoHolderConstant
          ring
  have hae : f =ᵐ[volume.restrict (ball x₀ R')] ballAverageLimit f := by
    have hint : ∀ r < R, IntegrableOn f (ball x₀ r) := fun r hr ↦ by
      have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
        isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
      exact (hf r hr).integrable one_le_two
    have h := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hR')
      (ae_tendsto_ballAverage hint)
    filter_upwards [h] with x hx
    exact hx.limUnder_eq.symm
  have hcont : ContinuousOn (ballAverageLimit f) (ball x₀ R') := by
    intro x hx
    have hxR : dist x x₀ < R := (mem_ball.mp hx).trans_le hR'
    have hδ : 0 < min (ρ₀ / 2) ((R - dist x x₀) / 3) := lt_min (by positivity) (by linarith)
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun y ↦ campanatoHolderConstant d α * M * dist y x ^ α)
        (𝓝[ball x₀ R'] x) (𝓝 0) := by
      have hc : Continuous (fun y ↦ campanatoHolderConstant d α * M * dist y x ^ α) :=
        continuous_const.mul
          ((continuous_id.dist continuous_const).rpow_const (fun _ ↦ Or.inr hα.le))
      have h := (hc.tendsto x).mono_left (nhdsWithin_le_nhds (s := ball x₀ R'))
      rwa [dist_self, Real.zero_rpow hα.ne', mul_zero] at h
    refine squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hlim
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ), self_mem_nhdsWithin]
      with y hyδ hyR'
    have hdist : dist x y < min (ρ₀ / 2) ((R - dist x x₀) / 3) := by
      rw [dist_comm]
      exact hyδ
    have hm1 := min_le_left (ρ₀ / 2) ((R - dist x x₀) / 3)
    have hm2 := min_le_right (ρ₀ / 2) ((R - dist x x₀) / 3)
    have h2 : 2 * dist x y ≤ ρ₀ := by linarith
    have hB : closedBall x (2 * dist x y) ⊆ ball x₀ R := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball]
      calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
        _ < R := by linarith
    rw [norm_sub_rev, dist_comm]
    exact hholder x hx y hyR' h2 hB
  exact ⟨hcont, hae, hbound, hholder⟩

end Campanato

/-- **Campanato's theorem** for real-valued functions, with the mean oscillation written as
`⨍_{B(x,r)} (f - f_{B(x,r)})²`. -/
theorem campanato_holder_real {d : ℕ} {f : Space d → ℝ} {x₀ : Space d} {R R' ρ₀ α M : ℝ}
    (hR' : R' ≤ R) (hρ₀ : 0 < ρ₀) (hα : 0 < α) (hM : 0 ≤ M)
    (hf : ∀ r < R, MemLp f 2 (volume.restrict (ball x₀ r)))
    (hcamp : ∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
      ⨍ y in ball x r, (f y - ⨍ z in ball x r, f z) ^ 2 ≤ M ^ 2 * r ^ (2 * α)) :
    ContinuousOn (ballAverageLimit f) (ball x₀ R') ∧
      f =ᵐ[volume.restrict (ball x₀ R')] ballAverageLimit f ∧
      (∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
        |ballAverageLimit f x - ⨍ y in ball x r, f y| ≤ campanatoConstant d α * M * r ^ α) ∧
      (∀ x ∈ ball x₀ R', ∀ y ∈ ball x₀ R', 2 * dist x y ≤ ρ₀ →
        closedBall x (2 * dist x y) ⊆ ball x₀ R →
          |ballAverageLimit f x - ballAverageLimit f y| ≤
            campanatoHolderConstant d α * M * dist x y ^ α) := by
  have hcamp' : ∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
      ⨍ y in ball x r, ‖f y - ⨍ z in ball x r, f z‖ ^ 2 ≤ M ^ 2 * r ^ (2 * α) := by
    intro x hx r hr hrρ hrB
    simpa only [Real.norm_eq_abs, sq_abs] using hcamp x hx r hr hrρ hrB
  obtain ⟨h1, h2, h3, h4⟩ := campanato_holder hR' hρ₀ hα hM hf hcamp'
  refine ⟨h1, h2, fun x hx r hr hrρ hrB ↦ ?_, fun x hx y hy h h' ↦ ?_⟩
  · simpa only [Real.norm_eq_abs] using h3 x hx r hr hrρ hrB
  · simpa only [Real.norm_eq_abs] using h4 x hx y hy h h'

/-! ### Lipschitz functions with Campanato gradient are `C^{1,α}` -/

/-- Averaging does not increase a global Lipschitz constant. -/
private theorem mollify_lipschitzWith_aux {d : ℕ} {v : Space d → ℝ} {K : NNReal}
    (hv : LipschitzWith K v) (n : ℕ) : LipschitzWith K (mollify v n) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  apply mollify_dist_le hv.continuous n y z
  intro t _
  have hd := hv.dist_le_mul (y - t) (z - t)
  rwa [dist_sub_right] at hd

/-- If the a.e. derivative of a Lipschitz function agrees a.e. on an open set `U` with a
function `G` continuous on `U`, then the derivatives of the averages converge to `G` on `U`. -/
private theorem tendsto_fderiv_mollify_of_ae_eq {d : ℕ} {g : Space d → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) {U : Set (Space d)} (hU : IsOpen U)
    {G : Space d → Space d →L[ℝ] ℝ} (hG : ContinuousOn G U)
    (hae : fderiv ℝ g =ᵐ[volume.restrict U] G) {z : Space d} (hz : z ∈ U) :
    Tendsto (fun n ↦ fderiv ℝ (mollify g n) z) atTop (𝓝 (G z)) := by
  have hUm : MeasurableSet U := hU.measurableSet
  have hG'm : AEStronglyMeasurable (U.indicator G) volume :=
    (aestronglyMeasurable_indicator_iff hUm).2 (hG.aestronglyMeasurable hUm)
  have hG'z : U.indicator G z = G z := Set.indicator_of_mem hz G
  have hcont : ContinuousAt (U.indicator G) z := by
    apply (hG.continuousAt (hU.mem_nhds hz)).congr
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (Set.indicator_of_mem hy G).symm
  have hae' : ∀ᵐ y ∂(volume : Measure (Space d)), y ∈ U → fderiv ℝ g y = G y :=
    (ae_restrict_iff' hUm).1 hae
  have hpull : ∀ᵐ t ∂(volume : Measure (Space d)),
      z - t ∈ U → fderiv ℝ g (z - t) = G (z - t) :=
    (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hae'
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.1 hU z hz
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hδ₀ hδ₁)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hrn : (averagingBump d n).rOut < min δ₀ δ₁ := by
    have h1 : (averagingBump d n).rOut = 1 / ((n : ℝ) + 1) := rfl
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    rw [h1]
    exact h2.trans_lt hN
  have hderiv : fderiv ℝ (mollify g n) z =
      ((averagingBump d n).normed volume ⋆[lsmul ℝ ℝ, volume] U.indicator G) z := by
    rw [(mollify_hasFDerivAt_of_lipschitz hg n z).fderiv, convolution_def, convolution_def]
    apply integral_congr_ae
    filter_upwards [hpull] with t ht
    by_cases hk : (averagingBump d n).normed volume t = 0
    · simp only [hk, map_zero, zero_apply]
    · have htb : t ∈ ball (0 : Space d) (averagingBump d n).rOut := by
        rw [← (averagingBump d n).support_normed_eq (μ := volume)]
        exact hk
      have hzt : z - t ∈ ball z δ₀ := by
        rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
        rw [mem_ball, dist_zero_right] at htb
        exact htb.trans (hrn.trans_le (min_le_left _ _))
      have hU' : z - t ∈ U := hball₀ hzt
      rw [ht hU', Set.indicator_of_mem hU' G]
  rw [hderiv, ← hG'z]
  have hle := (averagingBump d n).dist_normed_convolution_le (μ := volume) (x₀ := z)
    (ε := ε / 2) hG'm (fun y hy ↦ (hδ₁c (lt_of_lt_of_le (mem_ball.mp hy)
      (hrn.le.trans (min_le_right _ _)))).le)
  exact hle.trans_lt (half_lt_self hε)

/-- A Lipschitz function whose a.e. derivative agrees a.e. on an open set `U` with a function
`G` continuous on `U` satisfies `g (x + h) - g x = ∫₀¹ G (x + t h) h dt` along segments in `U`. -/
theorem sub_eq_integral_of_ae_eq_fderiv {d : ℕ} {g : Space d → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) {U : Set (Space d)} (hU : IsOpen U)
    {G : Space d → Space d →L[ℝ] ℝ} (hG : ContinuousOn G U)
    (hae : fderiv ℝ g =ᵐ[volume.restrict U] G) {x h : Space d}
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ U) :
    g (x + h) - g x = ∫ t in (0 : ℝ)..1, G (x + t • h) h := by
  have hL : Tendsto (fun n ↦ mollify g n (x + h) - mollify g n x) atTop
      (𝓝 (g (x + h) - g x)) :=
    (mollify_tendsto hg.continuous (x + h)).sub (mollify_tendsto hg.continuous x)
  have hE : ∀ n, mollify g n (x + h) - mollify g n x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (mollify g n) (x + t • h) h := fun n ↦
    sub_eq_integral_segment_fderiv ((mollify_contDiff hg.continuous n).of_le (by simp)) x h
  have hR : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, fderiv ℝ (mollify g n) (x + t • h) h) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, G (x + t • h) h)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (K : ℝ) * ‖h‖)
    · apply Eventually.of_forall
      intro n
      have hc : Continuous (fun t : ℝ ↦ fderiv ℝ (mollify g n) (x + t • h) h) :=
        (((mollify_contDiff hg.continuous n).continuous_fderiv (by simp)).comp
          (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
            continuous_const
      exact hc.aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro t _
      exact ((fderiv ℝ (mollify g n) (x + t • h)).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_le_of_lipschitz ℝ (mollify_lipschitzWith_aux hg n)) (norm_nonneg _))
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Set.Ioc_subset_Icc_self ht
      have h1 := tendsto_fderiv_mollify_of_ae_eq hg hU hG hae (hseg t ht')
      exact ((ContinuousLinearMap.apply ℝ ℝ h).continuous.tendsto _).comp h1
  exact tendsto_nhds_unique (hL.congr hE) hR

/-- A Lipschitz function whose a.e. derivative agrees a.e. on an open set `U` with a function
`G` continuous on `U` is differentiable at every point of `U`, with derivative `G`. -/
theorem hasFDerivAt_of_ae_eq_fderiv {d : ℕ} {g : Space d → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) {U : Set (Space d)} (hU : IsOpen U)
    {G : Space d → Space d →L[ℝ] ℝ} (hG : ContinuousOn G U)
    (hae : fderiv ℝ g =ᵐ[volume.restrict U] G) {x : Space d} (hx : x ∈ U) :
    HasFDerivAt g (G x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.continuousAt_iff.1 (hG.continuousAt (hU.mem_nhds hx)) c hc
  filter_upwards [ball_mem_nhds (0 : Space d) (lt_min hδ₀ hδ₁)] with h hh
  have hh' : ‖h‖ < min δ₀ δ₁ := by simpa using hh
  have hth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖t • h‖ ≤ ‖h‖ := fun t ht ↦ by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ U := fun t ht ↦ hball₀ (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hth t ht).trans_lt (hh'.trans_le (min_le_left _ _)))
  rw [sub_eq_integral_of_ae_eq_fderiv hg hU hG hae hseg]
  have hcont : ContinuousOn (fun t : ℝ ↦ G (x + t • h) h) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (hG.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht ↦ hseg t ht)).clm_apply continuousOn_const
  have hint : IntervalIntegrable (fun t : ℝ ↦ G (x + t • h) h) volume 0 1 :=
    hcont.intervalIntegrable
  have hsplit : (∫ t in (0 : ℝ)..1, G (x + t • h) h) - G x h =
      ∫ t in (0 : ℝ)..1, (G (x + t • h) h - G x h) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul]
  rw [hsplit]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := c * ‖h‖) (f := fun t ↦ G (x + t • h) h - G x h) (fun t ht ↦ by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Set.Ioc_subset_Icc_self ht
      rw [← _root_.sub_apply]
      refine ((G (x + t • h) - G x).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      have hd : dist (x + t • h) x < δ₁ := by
        rw [dist_eq_norm, add_sub_cancel_left]
        exact (hth t ht').trans_lt (hh'.trans_le (min_le_right _ _))
      rw [← dist_eq_norm]
      exact (hδ₁c hd).le)
  simpa using hb

/-- **Lipschitz functions with Campanato gradient are `C^{1,α}`.** If `g` is globally Lipschitz
and its a.e. derivative satisfies the Campanato bound
`⨍_{B(x,r)} ‖Dg - (Dg)_{B(x,r)}‖² ≤ M² r^(2α)` for centers `x ∈ B(x₀, R')` (`R' ≤ R`), radii
`0 < r ≤ ρ₀` and `closedBall x r ⊆ B(x₀, R)`, then `g` is differentiable at every point of
`B(x₀, R')` with derivative the continuous representative `ballAverageLimit (fderiv ℝ g)`, it is
`C¹` there, and `fderiv ℝ g` satisfies the Campanato and Hölder estimates of `campanato_holder`. -/
theorem campanato_fderiv_holder {d : ℕ} {g : Space d → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    {x₀ : Space d} {R R' ρ₀ α M : ℝ} (hR' : R' ≤ R) (hρ₀ : 0 < ρ₀) (hα : 0 < α) (hM : 0 ≤ M)
    (hcamp : ∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
      ⨍ y in ball x r, ‖fderiv ℝ g y - ⨍ z in ball x r, fderiv ℝ g z‖ ^ 2 ≤
        M ^ 2 * r ^ (2 * α)) :
    (∀ x ∈ ball x₀ R', HasFDerivAt g (ballAverageLimit (fderiv ℝ g) x) x) ∧
      ContDiffOn ℝ 1 g (ball x₀ R') ∧
      (∀ x ∈ ball x₀ R', ∀ r, 0 < r → r ≤ ρ₀ → closedBall x r ⊆ ball x₀ R →
        ‖fderiv ℝ g x - ⨍ y in ball x r, fderiv ℝ g y‖ ≤ campanatoConstant d α * M * r ^ α) ∧
      (∀ x ∈ ball x₀ R', ∀ y ∈ ball x₀ R', 2 * dist x y ≤ ρ₀ →
        closedBall x (2 * dist x y) ⊆ ball x₀ R →
          ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ campanatoHolderConstant d α * M * dist x y ^ α) := by
  have hL2 : ∀ r < R, MemLp (fderiv ℝ g) 2 (volume.restrict (ball x₀ r)) := by
    intro r _
    have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact MemLp.of_bound (measurable_fderiv ℝ g).aestronglyMeasurable K
      (Eventually.of_forall (fun y ↦ norm_fderiv_le_of_lipschitz ℝ hg))
  obtain ⟨hcont, hae, hbound, hholder⟩ := campanato_holder hR' hρ₀ hα hM hL2 hcamp
  have hderiv : ∀ x ∈ ball x₀ R', HasFDerivAt g (ballAverageLimit (fderiv ℝ g) x) x :=
    fun x hx ↦ hasFDerivAt_of_ae_eq_fderiv hg isOpen_ball hcont hae hx
  have heq : ∀ x ∈ ball x₀ R', fderiv ℝ g x = ballAverageLimit (fderiv ℝ g) x :=
    fun x hx ↦ (hderiv x hx).fderiv
  have hcontD : ContinuousOn (fderiv ℝ g) (ball x₀ R') := hcont.congr heq
  have hC1 : ContDiffOn ℝ 1 g (ball x₀ R') := by
    have h : ContDiffOn ℝ (0 + 1) g (ball x₀ R') :=
      (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).2
        ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, by simp,
          contDiffOn_zero.2 hcontD⟩
    simpa using h
  refine ⟨hderiv, hC1, fun x hx r hr hrρ hrB ↦ ?_, fun x hx y hy h1 h2 ↦ ?_⟩
  · rw [heq x hx]
    exact hbound x hx r hr hrρ hrB
  · rw [heq x hx, heq y hy]
    exact hholder x hx y hy h1 h2

end SerrinEpigraph
