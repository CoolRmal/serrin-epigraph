module

public import SerrinEpigraph.GluedCompetitor

/-!
# Quantitative quadratic gradient cost of cutoff gluing
-/

public section

namespace SerrinEpigraph

/-- Young's inequality with an adjustable multiplicative loss. -/
theorem add_sq_le_with_parameter (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 := by
  have hn := div_nonneg (sq_nonneg (δ * a - b)) hδ.le
  have he : (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 - (a + b) ^ 2 =
      (δ * a - b) ^ 2 / δ := by
    field_simp
    ring
  rw [← he] at hn
  linarith

/-- The square of a convex average is bounded by the average of the squares. -/
theorem convex_average_sq_le (a b : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - t) * a + t * b) ^ 2 ≤ (1 - t) * a ^ 2 + t * b ^ 2 := by
  have hn := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (a - b))
  nlinarith

/-- Gluing preserves the principal quadratic gradient energy up to an arbitrary small loss,
with a separate cutoff mismatch error. -/
theorem norm_gradient_gluedCompetitor_sq_le {d : ℕ} {U v η : Space d → ℝ} {x : Space d}
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x)
    (hη : DifferentiableAt ℝ η x) (hval : η x ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖gradient (gluedCompetitor U v η) x‖ ^ 2 ≤
      (1 + δ) * ((1 - η x) * ‖gradient U x‖ ^ 2 + η x * ‖gradient v x‖ ^ 2) +
        (1 + 1 / δ) * ‖v x - U x‖ ^ 2 * ‖gradient η x‖ ^ 2 := by
  have hlin := norm_gradient_gluedCompetitor_le hU hv hη hval
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hlin 2
  have hy := add_sq_le_with_parameter
    ((1 - η x) * ‖gradient U x‖ + η x * ‖gradient v x‖)
    (‖v x - U x‖ * ‖gradient η x‖) hδ
  have hc := mul_le_mul_of_nonneg_left
    (convex_average_sq_le ‖gradient U x‖ ‖gradient v x‖ hval)
    (show 0 ≤ 1 + δ by linarith)
  calc
    _ ≤ _ := hsq.trans hy
    _ ≤ (1 + δ) * ((1 - η x) * ‖gradient U x‖ ^ 2 + η x * ‖gradient v x‖ ^ 2) +
        (1 + 1 / δ) * (‖v x - U x‖ * ‖gradient η x‖) ^ 2 := add_le_add hc le_rfl
    _ = _ := by ring

/-- The quadratic gluing estimate has the inverse-scale coefficient of diffuse energy. -/
theorem gluedCompetitor_kinetic_energy_le {d : ℕ} {U v η : Space d → ℝ} {x : Space d}
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x)
    (hη : DifferentiableAt ℝ η x) (hval : η x ∈ Set.Icc (0 : ℝ) 1)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ‖gradient (gluedCompetitor U v η) x‖ ^ 2 / (2 * R) ≤
      (1 + δ) * ((1 - η x) * (‖gradient U x‖ ^ 2 / (2 * R)) +
        η x * (‖gradient v x‖ ^ 2 / (2 * R))) +
      (1 + 1 / δ) * ‖v x - U x‖ ^ 2 * ‖gradient η x‖ ^ 2 / (2 * R) := by
  have he := div_le_div_of_nonneg_right
    (norm_gradient_gluedCompetitor_sq_le hU hv hη hval hδ)
    (show 0 ≤ 2 * R by positivity)
  convert he using 1
  ring

/-- The kinetic gluing bound holds almost everywhere for locally Lipschitz inputs. -/
theorem gluedCompetitor_kinetic_energy_le_ae {d : ℕ} {U v η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hval : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ∀ᵐ x ∂MeasureTheory.volume,
      ‖gradient (gluedCompetitor U v η) x‖ ^ 2 / (2 * R) ≤
        (1 + δ) * ((1 - η x) * (‖gradient U x‖ ^ 2 / (2 * R)) +
          η x * (‖gradient v x‖ ^ 2 / (2 * R))) +
        (1 + 1 / δ) * ‖v x - U x‖ ^ 2 * ‖gradient η x‖ ^ 2 / (2 * R) := by
  filter_upwards [ae_differentiableAt_of_locallyLipschitz hU,
    ae_differentiableAt_of_locallyLipschitz hv,
    ae_differentiableAt_of_locallyLipschitz hη] with x hxU hxv hxη
  exact gluedCompetitor_kinetic_energy_le hxU hxv hxη (hval x) hδ hR

end SerrinEpigraph
