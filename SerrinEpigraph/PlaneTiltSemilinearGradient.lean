module

public import SerrinEpigraph.PlaneTiltPoissonScaling

/-!
# Comparing gradients of two semilinear solutions
-/

public section
noncomputable section

open Set Metric MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SerrinEpigraph

/-- The reaction-gradient difference has a lower quadratic bound with an error
depending only on the oscillation of the first derivative of the reaction. -/
theorem reaction_gradient_difference_lower_bound {d : ℕ}
    {p q : Space d} {a b B ω K : ℝ} (ha : a ≤ B) (hω : |b - a| ≤ ω)
    (hK : ‖q‖ ≤ K) :
    -((B + 1) * ‖p - q‖ ^ 2) - (ω * K) ^ 2 ≤
      inner ℝ (p - q) (b • q - a • p) := by
  have hωn : 0 ≤ ω := (abs_nonneg _).trans hω
  have hKn : 0 ≤ K := (norm_nonneg _).trans hK
  have hid : b • q - a • p = -a • (p - q) + (b - a) • q := by module
  rw [hid, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hi : |(b - a) * inner ℝ (p - q) q| ≤ ω * K * ‖p - q‖ := by
    rw [abs_mul]
    calc
      _ ≤ ω * (‖p - q‖ * K) :=
        mul_le_mul hω ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left hK (norm_nonneg _))) (abs_nonneg _) hωn
      _ = _ := by ring
  have hh := (abs_le.mp hi).1
  have ha' := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖p - q‖)
  nlinarith [sq_nonneg (‖p - q‖ - ω * K)]

/-- Quantitative interior gradient comparison for two positive C2 solutions of
the same C1 semilinear equation. All coefficients depend only on a ball radius,
the uniform solution difference, and the reaction-derivative oscillation. -/
theorem semilinear_gradient_difference_sq_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {u v : Space d → ℝ} {f : ℝ → ℝ}
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hv : ContDiffOn ℝ 2 v Ω) (hf : ContDiffOn ℝ 1 f (Ioi 0))
    (hup : ∀ x ∈ Ω, 0 < u x) (hvp : ∀ x ∈ Ω, 0 < v x)
    (hueq : ∀ x ∈ Ω, -(Δ u) x = f (u x))
    (hveq : ∀ x ∈ Ω, -(Δ v) x = f (v x))
    {c : Space d} {r B ω K δ M : ℝ} (hr : 0 < r) (hc : closedBall c r ⊆ Ω)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hval : ∀ x ∈ closedBall c r, |u x - v x| ≤ δ)
    (hsrcu : ∀ x ∈ closedBall c r, |f (u x)| ≤ M)
    (hsrcv : ∀ x ∈ closedBall c r, |f (v x)| ≤ M)
    (hderiv : ∀ x ∈ closedBall c r, deriv f (u x) ≤ B)
    (hosc : ∀ x ∈ closedBall c r, |deriv f (v x) - deriv f (u x)| ≤ ω)
    (hgrad : ∀ x ∈ closedBall c r, ‖gradient v x‖ ≤ K) :
    r ^ 2 * ‖gradient u c - gradient v c‖ ^ 2 ≤ r ^ 4 * (ω * K) ^ 2 +
      (r ^ 2 * (B + 1) + 2 * (d : ℝ) + 13) * δ * (r ^ 2 * (2 * M)) +
      (r ^ 2 * (B + 1) + 2 * (d : ℝ) + 13) * δ ^ 2 := by
  let w := fun x ↦ u x - v x
  let F := fun x ↦ f (v x) - f (u x)
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  have hv1 : ContDiffOn ℝ 1 v Ω := hv.of_le (by norm_num)
  have hw : ContDiffOn ℝ 2 w Ω := hu.sub hv
  have hF : ContDiffOn ℝ 1 F Ω := (hf.comp hv1 hvp).sub (hf.comp hu1 hup)
  have hgw {x : Space d} (hx : x ∈ Ω) :
      gradient w x = gradient u x - gradient v x := by
    simp only [w, gradient, fderiv_fun_sub
      ((hu1.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx))
      ((hv1.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)), map_sub]
  have hgf {x : Space d} (hx : x ∈ Ω) :
      gradient F x = deriv f (v x) • gradient v x - deriv f (u x) • gradient u x := by
    have hfu := (hf.differentiableOn_one (u x) (hup x hx)).differentiableAt
      (isOpen_Ioi.mem_nhds (hup x hx))
    have hfv := (hf.differentiableOn_one (v x) (hvp x hx)).differentiableAt
      (isOpen_Ioi.mem_nhds (hvp x hx))
    have hud := (hu1.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
    have hvd := (hv1.differentiableOn_one x hx).differentiableAt (hΩ.mem_nhds hx)
    have hh := (hfv.hasDerivAt.comp_hasFDerivAt x hvd.hasFDerivAt).sub
      (hfu.hasDerivAt.comp_hasFDerivAt x hud.hasFDerivAt)
    change HasFDerivAt F _ x at hh
    simp only [gradient, hh.fderiv, map_sub, map_smul]
  have heq (x : Space d) (hx : x ∈ Ω) : (Δ w) x = F x := by
    change (Δ (u - v)) x = F x
    rw [(hu.contDiffAt (hΩ.mem_nhds hx)).laplacian_sub
      (hv.contDiffAt (hΩ.mem_nhds hx))]
    dsimp only [F]
    linarith [hueq x hx, hveq x hx]
  have hh := poisson_gradient_sq_le_on_closedBall b hΩ hw hF heq hr hc
    (B := B + 1) (D := (ω * K) ^ 2) (δ := δ) (M := 2 * M)
    (by linarith) (sq_nonneg _) hδ (by positivity) hval
    (fun x hx ↦ (abs_sub _ _).trans (by linarith [hsrcu x hx, hsrcv x hx]))
    (fun x hx ↦ by
      rw [hgw (hc hx), hgf (hc hx)]
      exact reaction_gradient_difference_lower_bound (hderiv x hx) (hosc x hx) (hgrad x hx))
  rwa [hgw (hc (mem_closedBall_self hr.le))] at hh

end SerrinEpigraph
