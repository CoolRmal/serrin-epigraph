module

public import SerrinEpigraph.PhaseClearingGaussian

/-!
# Scale bounds for the signed Gaussian clearing barrier
-/

public section
noncomputable section

open Set InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

@[expose] def phaseClearingGaussianAmplitude (m : ℕ) (δ F r : ℝ) : ℝ :=
  Real.exp (3 * ((m : ℝ) + 1)) * (δ + F * r ^ 2)

@[expose] def phaseClearingGaussianRate (m : ℕ) (r : ℝ) : ℝ :=
  4 * ((m : ℝ) + 1) / r ^ 2

@[expose] def phaseClearingGaussianGradientConstant (m : ℕ) : ℝ :=
  4 * ((m : ℝ) + 1) * Real.exp (4 * ((m : ℝ) + 1))

@[expose] def phaseClearingGaussianLaplacianConstant (m : ℕ) : ℝ :=
  8 * ((m : ℝ) + 1) ^ 2 * Real.exp (4 * ((m : ℝ) + 1))

theorem phaseClearingGaussianCoefficient_nonneg {d : ℕ} {A b s : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (c x : Space d) :
    0 ≤ phaseClearingGaussianCoefficient A b s c x := by
  unfold phaseClearingGaussianCoefficient
  positivity

theorem phaseClearingGaussianCoefficient_le {d : ℕ} {A b s : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (c x : Space d) :
    phaseClearingGaussianCoefficient A b s c x ≤ 2 * A * b * Real.exp (b * s ^ 2) := by
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hb (sq_nonneg ‖x - c‖)]

theorem phaseClearingGaussian_gradient_bound {d : ℕ} {A b s : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) {c x : Space d} (hx : ‖x - c‖ ≤ s) :
    ‖gradient (phaseClearingGaussian A b s c) x‖ ≤
      2 * A * b * Real.exp (b * s ^ 2) * s := by
  rw [(phaseClearingGaussian_hasGradientAt A b s c x).gradient, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (phaseClearingGaussianCoefficient_nonneg hA hb c x)]
  exact mul_le_mul (phaseClearingGaussianCoefficient_le hA hb c x) hx
    (norm_nonneg _) (by positivity)

theorem phaseClearingGaussian_laplacian_bound {d : ℕ} {A b s : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (c x : Space d) :
    (Δ (phaseClearingGaussian A b s c)) x ≤
      2 * A * b * Real.exp (b * s ^ 2) * (d : ℝ) := by
  rw [phaseClearingGaussian_laplacian]
  calc
    _ ≤ phaseClearingGaussianCoefficient A b s c x * (d : ℝ) := by
      apply mul_le_mul_of_nonneg_left ?_ (phaseClearingGaussianCoefficient_nonneg hA hb c x)
      nlinarith [mul_nonneg hb (sq_nonneg ‖x - c‖)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (phaseClearingGaussianCoefficient_le hA hb c x)
      (Nat.cast_nonneg _)

theorem phaseClearingGaussianRate_pos (m : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < phaseClearingGaussianRate m r := by
  unfold phaseClearingGaussianRate
  positivity

theorem phaseClearingGaussianAmplitude_pos (m : ℕ) {δ F r : ℝ}
    (hδ : 0 < δ) (hF : 0 ≤ F) :
    0 < phaseClearingGaussianAmplitude m δ F r := by
  unfold phaseClearingGaussianAmplitude
  positivity

theorem phaseClearingGaussianRate_inner (m : ℕ) {r : ℝ} (hr : 0 < r) :
    phaseClearingGaussianRate m r * (r / 2) ^ 2 = (m : ℝ) + 1 := by
  unfold phaseClearingGaussianRate
  field_simp
  ring

theorem phaseClearingGaussianRate_outer (m : ℕ) {r : ℝ} (hr : 0 < r) :
    phaseClearingGaussianRate m r * (r ^ 2 - (r / 2) ^ 2) = 3 * ((m : ℝ) + 1) := by
  unfold phaseClearingGaussianRate
  field_simp
  ring

theorem phaseClearingGaussian_pos_outer {d : ℕ} {A b s : ℝ}
    (hA : 0 < A) (hb : 0 < b) {c x : Space d} (hx : s ^ 2 < ‖x - c‖ ^ 2) :
    0 < phaseClearingGaussian A b s c x := by
  apply mul_pos hA
  have he : Real.exp (-b * (‖x - c‖ ^ 2 - s ^ 2)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

/-- The barrier already dominates the amplitude before the cutoff starts to vary. -/
theorem phaseClearingGaussian_buffer_ge (m : ℕ) {δ F r : ℝ}
    (hδ : 0 < δ) (hF : 0 ≤ F) (hr : 0 < r) {c x : Space (m + 1)}
    (hx : 3 * r / 4 ≤ ‖x - c‖) :
    δ ≤ phaseClearingGaussian (phaseClearingGaussianAmplitude m δ F r)
      (phaseClearingGaussianRate m r) (r / 2) c x := by
  let n : ℝ := (m : ℝ) + 1
  let A := phaseClearingGaussianAmplitude m δ F r
  let b := phaseClearingGaussianRate m r
  have hn : 1 ≤ n := by dsimp [n]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : 0 < b := phaseClearingGaussianRate_pos m hr
  have hbi : b * (r / 2) ^ 2 = n := phaseClearingGaussianRate_inner m hr
  have hρ : r ^ 2 / 2 ≤ ‖x - c‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x - c‖ - 3 * r / 4), norm_nonneg (x - c)]
  have hpow : -b * (‖x - c‖ ^ 2 - (r / 2) ^ 2) ≤ -n := by
    nlinarith [mul_le_mul_of_nonneg_left hρ hb.le]
  have hen : 2 ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
  have he3 : 2 ≤ Real.exp (3 * n) := by linarith [Real.add_one_le_exp (3 * n)]
  have hp : Real.exp n * Real.exp (-n) = 1 := by rw [← Real.exp_add]; simp
  have hehalf : Real.exp (-b * (‖x - c‖ ^ 2 - (r / 2) ^ 2)) ≤ 1 / 2 := by
    have hne : Real.exp (-n) ≤ 1 / 2 := by nlinarith [Real.exp_pos (-n)]
    exact (Real.exp_le_exp.mpr hpow).trans hne
  have hA : 2 * δ ≤ A := by
    dsimp [A, phaseClearingGaussianAmplitude]
    change 2 * δ ≤ Real.exp (3 * n) * (δ + F * r ^ 2)
    nlinarith [mul_nonneg hF (sq_nonneg r)]
  change δ ≤ A * (1 - Real.exp (-b * (‖x - c‖ ^ 2 - (r / 2) ^ 2)))
  nlinarith

theorem phaseClearingGaussian_scaled_gradient_bound (m : ℕ) {δ F r : ℝ}
    (hδ : 0 < δ) (hF : 0 ≤ F) (hr : 0 < r) {c x : Space (m + 1)}
    (hx : ‖x - c‖ ≤ r / 2) :
    ‖gradient (phaseClearingGaussian (phaseClearingGaussianAmplitude m δ F r)
      (phaseClearingGaussianRate m r) (r / 2) c) x‖ ≤
      phaseClearingGaussianGradientConstant m * (δ / r + F * r) := by
  have hh := phaseClearingGaussian_gradient_bound
    (phaseClearingGaussianAmplitude_pos m (r := r) hδ hF).le
    (phaseClearingGaussianRate_pos m hr).le hx
  rw [phaseClearingGaussianRate_inner m hr] at hh
  have he : Real.exp (3 * ((m : ℝ) + 1)) * Real.exp ((m : ℝ) + 1) =
      Real.exp (4 * ((m : ℝ) + 1)) := by rw [← Real.exp_add]; congr 1; ring
  convert hh using 1
  unfold phaseClearingGaussianAmplitude phaseClearingGaussianRate
    phaseClearingGaussianGradientConstant
  field_simp
  ring_nf at he ⊢
  nlinarith [he]

theorem phaseClearingGaussian_scaled_laplacian_bound (m : ℕ) {δ F r : ℝ}
    (hδ : 0 < δ) (hF : 0 ≤ F) (hr : 0 < r) (c x : Space (m + 1)) :
    (Δ (phaseClearingGaussian (phaseClearingGaussianAmplitude m δ F r)
      (phaseClearingGaussianRate m r) (r / 2) c)) x ≤
      phaseClearingGaussianLaplacianConstant m * (δ / r ^ 2 + F) := by
  have hh := phaseClearingGaussian_laplacian_bound (s := r / 2)
    (phaseClearingGaussianAmplitude_pos m (r := r) hδ hF).le
    (phaseClearingGaussianRate_pos m hr).le c x
  rw [phaseClearingGaussianRate_inner m hr] at hh
  have he : Real.exp (3 * ((m : ℝ) + 1)) * Real.exp ((m : ℝ) + 1) =
      Real.exp (4 * ((m : ℝ) + 1)) := by rw [← Real.exp_add]; congr 1; ring
  convert hh using 1
  unfold phaseClearingGaussianAmplitude phaseClearingGaussianRate
    phaseClearingGaussianLaplacianConstant
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring_nf at he ⊢
  nlinarith [he]

/-- On the entire half-radius annulus the negative Laplacian dominates the reaction. -/
theorem phaseClearingGaussian_supersolution (m : ℕ) {δ F r : ℝ}
    (hδ : 0 < δ) (hF : 0 ≤ F) (hr : 0 < r) {c x : Space (m + 1)}
    (hx : ‖x - c‖ ∈ Icc (r / 2) r) :
    F ≤ -(Δ (phaseClearingGaussian (phaseClearingGaussianAmplitude m δ F r)
      (phaseClearingGaussianRate m r) (r / 2) c)) x := by
  let A := phaseClearingGaussianAmplitude m δ F r
  let b := phaseClearingGaussianRate m r
  let n : ℝ := (m : ℝ) + 1
  have hn : 1 ≤ n := by dsimp [n]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : 0 < b := phaseClearingGaussianRate_pos m hr
  have hA : 0 < A := phaseClearingGaussianAmplitude_pos m hδ hF
  have hρlo : (r / 2) ^ 2 ≤ ‖x - c‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x - c‖ - r / 2), hx.1, norm_nonneg (x - c)]
  have hρhi : ‖x - c‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - ‖x - c‖), hx.2, norm_nonneg (x - c)]
  have hbi : b * (r / 2) ^ 2 = n := phaseClearingGaussianRate_inner m hr
  have hbo : b * (r ^ 2 - (r / 2) ^ 2) = 3 * n := phaseClearingGaussianRate_outer m hr
  have hcoef : n ≤ 2 * b * ‖x - c‖ ^ 2 - n := by
    nlinarith [mul_le_mul_of_nonneg_left hρlo hb.le]
  have hexp : Real.exp (-3 * n) ≤ Real.exp (-b * (‖x - c‖ ^ 2 - (r / 2) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hρhi hb.le]
  have heprod : Real.exp (3 * n) * Real.exp (-3 * n) = 1 := by
    rw [← Real.exp_add]; simp
  have hbase : 2 * A * b * Real.exp (-3 * n) = 8 * n * (δ / r ^ 2 + F) := by
    dsimp [A, b, phaseClearingGaussianAmplitude, phaseClearingGaussianRate]
    change 2 * (Real.exp (3 * n) * (δ + F * r ^ 2)) *
      (4 * n / r ^ 2) * Real.exp (-3 * n) = _
    field_simp
    ring_nf at heprod ⊢
    nlinarith [heprod]
  have hlower : 8 * n * F ≤
      phaseClearingGaussianCoefficient A b (r / 2) c x := by
    calc
      _ ≤ 8 * n * (δ / r ^ 2 + F) := by
        have hdiv : 0 ≤ δ / r ^ 2 := by positivity
        nlinarith
      _ = 2 * A * b * Real.exp (-3 * n) := hbase.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  rw [phaseClearingGaussian_laplacian]
  change F ≤ -(phaseClearingGaussianCoefficient A b (r / 2) c x *
    (((m + 1 : ℕ) : ℝ) - 2 * b * ‖x - c‖ ^ 2))
  simp only [Nat.cast_add, Nat.cast_one]
  change F ≤ -(phaseClearingGaussianCoefficient A b (r / 2) c x *
    (n - 2 * b * ‖x - c‖ ^ 2))
  have hnon := phaseClearingGaussianCoefficient_nonneg (s := r / 2) hA.le hb.le c x
  have hh := mul_le_mul_of_nonneg_left hcoef hnon
  have hh' := mul_le_mul_of_nonneg_right hlower (show 0 ≤ n by linarith)
  nlinarith [mul_nonneg hF (sq_nonneg (n - 1))]

end SerrinEpigraph
