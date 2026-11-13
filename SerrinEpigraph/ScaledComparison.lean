module

public import SerrinEpigraph.Reaction
public import SerrinEpigraph.StrongMaximum

/-!
# Strong comparison with a scaled positive solution
-/

public section

open MeasureTheory InnerProductSpace
open scoped Laplacian NNReal

namespace SerrinEpigraph

/-- The reaction quotient condition makes scaling by a factor at least one a supersolution. -/
theorem reaction_scaling_le {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    {t s : ℝ} (ht : 1 ≤ t) (hs : 0 < s) : f (t * s) ≤ t * f s := by
  have hts : 0 < t * s := mul_pos (by linarith) hs
  have hle : s ≤ t * s := by nlinarith
  have hh := antitoneOn_reaction_div hf hstructure hs hts hle
  have hh' := (div_le_div_iff₀ hts hs).mp hh
  nlinarith

/-- Lipschitz control turns the scaled reaction inequality into a linear lower bound. -/
theorem scaled_reaction_difference_nonneg {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    {L : ℝ≥0} {B t a b : ℝ} (hL : LipschitzOnWith L f (Set.Icc 0 B))
    (ht : 1 ≤ t) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ t * a)
    (hB : t * a ≤ B) : 0 ≤ t * f a - f b + (L : ℝ) * (t * a - b) := by
  have hscale := reaction_scaling_le hf hstructure ht ha
  have hdist := hL.dist_le_mul b ⟨hb, hba.trans hB⟩ (t * a)
    ⟨by positivity, hB⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hba)] at hdist
  have hdiff := le_abs_self (f b - f (t * a))
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The difference between a scaled solution and an ordered solution is a weak supersolution. -/
theorem scaled_difference_isWeakSupersolution {Ω : Set E} {u v : E → ℝ} {f : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    (hueq : ∀ x ∈ Ω, -(Δ u) x = f (u x))
    (hveq : ∀ x ∈ Ω, -(Δ v) x = f (v x))
    {L : ℝ≥0} {B t : ℝ} (hL : LipschitzOnWith L f (Set.Icc 0 B)) (ht : 1 ≤ t)
    (hu0 : ∀ x ∈ Ω, 0 < u x) (hv0 : ∀ x ∈ Ω, 0 ≤ v x)
    (horder : ∀ x ∈ Ω, v x ≤ t * u x) (hB : ∀ x ∈ Ω, t * u x ≤ B) :
    IsWeakSupersolution μ Ω ((L : ℝ) + 1) (fun x ↦ t * u x - v x) := by
  apply isWeakSupersolution_of_classical hΩ ((contDiffOn_const.mul hu).sub hv)
  intro x hx
  have hux := (hu x hx).contDiffAt (hΩ.mem_nhds hx)
  have hvx := (hv x hx).contDiffAt (hΩ.mem_nhds hx)
  have hlap : (Δ (fun y ↦ t * u y - v y)) x = t * (Δ u) x - (Δ v) x := by
    change (Δ (t • u - v)) x = _
    have htu : ContDiffAt ℝ 2 (t • u) x := by
      convert hux.const_smul t using 1
    rw [htu.laplacian_sub hvx, laplacian_smul t hux]
    rfl
  have hreac := scaled_reaction_difference_nonneg hf hstructure hL ht
    (hu0 x hx) (hv0 x hx) (horder x hx) (hB x hx)
  rw [hlap]
  have hue := hueq x hx
  have hve := hveq x hx
  nlinarith [horder x hx]

include μ in
/-- Ordered solutions cannot meet an enlarged positive solution at an interior point unless
they agree with it throughout the connected domain. -/
theorem scaled_solution_eq_of_contact {Ω : Set E} {u v : E → ℝ} {f : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hstructure : ∀ s : ℝ, 0 < s → 0 ≤ f s - s * deriv f s)
    (hueq : ∀ x ∈ Ω, -(Δ u) x = f (u x))
    (hveq : ∀ x ∈ Ω, -(Δ v) x = f (v x))
    {B t : ℝ} (ht : 1 ≤ t) (hu0 : ∀ x ∈ Ω, 0 < u x)
    (hv0 : ∀ x ∈ Ω, 0 ≤ v x) (horder : ∀ x ∈ Ω, v x ≤ t * u x)
    (hB : ∀ x ∈ Ω, t * u x ≤ B)
    {x : E} (hx : x ∈ Ω) (hcontact : v x = t * u x) :
    ∀ y ∈ Ω, v y = t * u y := by
  have hfB : ContDiffOn ℝ 1 f (Set.Icc 0 B) :=
    hf.mono fun _ hs ↦ hs.1
  obtain ⟨L, hL⟩ := hfB.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 B) isCompact_Icc
  have hweak : IsWeakSupersolution μ Ω ((L : ℝ) + 1) (fun y ↦ t * u y - v y) :=
    scaled_difference_isWeakSupersolution hΩ hu hv hf hstructure hueq hveq
      hL ht hu0 hv0 horder hB
  have hw : ContDiffOn ℝ 1 (fun y ↦ t * u y - v y) Ω :=
    ((contDiffOn_const.mul hu).sub hv).of_le (by norm_num)
  have heq := hweak.eq_zero_of_zero hΩ hconn hw
    (fun y hy ↦ sub_nonneg.mpr (horder y hy)) (by positivity) hx
    (sub_eq_zero.mpr hcontact.symm)
  intro y hy
  exact (sub_eq_zero.mp (heq y hy)).symm

end SerrinEpigraph
