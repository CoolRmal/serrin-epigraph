module

public import SerrinEpigraph.DirectionalRigidity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Translation orders and the parameter-space tangent ball

The closed order set encodes the global inequalities retained under physical
translations. Interior parameter balls yield strict positive-phase balls and
opposite zero-phase balls at a critical contact.
-/

public section

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

/-- All translations that increase a function at every point. -/
@[expose] def translationOrderSet {d : ℕ} (U : Space d → ℝ) : Set (Space d) :=
  {a | ∀ x, U x ≤ U (x + a)}

/-- Continuity makes the full-space order condition closed in the translation. -/
theorem isClosed_translationOrderSet {d : ℕ} {U : Space d → ℝ} (hU : Continuous U) :
    IsClosed (translationOrderSet U) := by
  have he : translationOrderSet U = ⋂ x, {a | U x ≤ U (x + a)} := by
    ext
    simp [translationOrderSet]
  rw [he]
  exact isClosed_iInter (fun x ↦ isClosed_le continuous_const (hU.comp (by fun_prop)))

/-- The zero translation is always allowed. -/
theorem zero_mem_translationOrderSet {d : ℕ} (U : Space d → ℝ) :
    0 ∈ translationOrderSet U := by simp [translationOrderSet]

/-- Consecutive allowed translations give another allowed translation. -/
theorem add_mem_translationOrderSet {d : ℕ} {U : Space d → ℝ} {a b : Space d}
    (ha : a ∈ translationOrderSet U) (hb : b ∈ translationOrderSet U) :
    a + b ∈ translationOrderSet U := by
  intro x
  simpa only [add_assoc] using (ha x).trans (hb (x + a))

/-- An interior ball of translation orders becomes a positive-phase ball whenever
positive points accumulate at the origin. -/
theorem ball_subset_positive_of_translation_orders {d : ℕ} {U : Space d → ℝ}
    {K : Set (Space d)} (horder : K ⊆ translationOrderSet U)
    (hzero : (0 : Space d) ∈ closure {x | 0 < U x})
    {c : Space d} {r : ℝ} (hball : ball c r ⊆ K) : ball c r ⊆ {x | 0 < U x} := by
  intro z hz
  have hgap : 0 < r - dist z c := sub_pos.mpr hz
  obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hzero (r - dist z c) hgap
  have hyd' : ‖y‖ < r - dist z c := by simpa [dist_comm, dist_eq_norm] using hyd
  have hyball : z - y ∈ ball c r := by
    rw [mem_ball, dist_eq_norm]
    have he : z - y - c = (z - c) - y := by abel
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by rw [dist_eq_norm] at hyd'; linarith)
  have ho := horder (hball hyball) y
  have he : y + (z - y) = z := by abel
  rw [he] at ho
  exact hy.trans_le ho

/-- A zero value at an allowed contact produces the opposite zero-phase ball. -/
theorem ball_subset_zero_of_translation_orders {d : ℕ} {U : Space d → ℝ}
    (hU : ∀ x, 0 ≤ U x) {K : Set (Space d)} (horder : K ⊆ translationOrderSet U)
    {a c : Space d} {r : ℝ} (ha : U a = 0) (hball : ball c r ⊆ K) :
    ball (a - c) r ⊆ {x | U x = 0} := by
  intro x hx
  have ha' : a - x ∈ ball c r := by
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have he : a - x - c = -(x - (a - c)) := by abel
    rw [he, norm_neg]
    exact hx
  have ho := horder (hball ha') x
  have he : x + (a - x) = a := by abel
  rw [he, ha] at ho
  exact le_antisymm ho (hU x)

/-- A missing positive direction and eventual interior points on the positive
normal ray produce an interior tangent ball with a positive-projection contact.
No regularity of the parameter-set boundary is assumed. -/
theorem exists_positive_contact_tangent_ball {d : ℕ} {K : Set (Space d)}
    {e : Space d} (he : ‖e‖ = 1)
    (hfar : ∀ᶠ T : ℝ in atTop, T • e ∈ interior K)
    {b : Space d} (hb : b ∉ K) (hbe : 0 < inner ℝ e b) :
    ∃ (c a : Space d) (r : ℝ), 0 < r ∧ a ∈ frontier K ∧
      ball c r ⊆ K ∧ dist a c = r ∧ 0 < inner ℝ e a := by
  obtain ⟨T, ⟨hTin, hT⟩, hTb⟩ :=
    ((hfar.and (eventually_gt_atTop 0)).and
      (eventually_gt_atTop (‖b‖ ^ 2 / (2 * inner ℝ e b)))).exists
  have hdist : dist (T • e) b < T := by
    have hs := norm_sub_sq_real (T • e) b
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT, he, mul_one,
      real_inner_smul_left] at hs
    have hbound := (div_lt_iff₀ (by positivity : 0 < 2 * inner ℝ e b)).mp hTb
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (T • e - b)]
  have hK : K ≠ univ := by intro hh; exact hb (hh.symm ▸ mem_univ b)
  obtain ⟨a, ha, har⟩ := exists_mem_frontier_infDist_compl_eq_dist
    (interior_subset hTin) hK
  have hr : 0 < infDist (T • e) Kᶜ := by
    apply (infDist_pos_iff_notMem_closure ⟨b, hb⟩).mp
    simpa only [closure_compl, mem_compl_iff, not_not] using hTin
  have hrT : infDist (T • e) Kᶜ < T :=
    (infDist_le_dist_of_mem hb).trans_lt hdist
  refine ⟨T • e, a, infDist (T • e) Kᶜ, hr, ha, ball_infDist_compl_subset, ?_, ?_⟩
  · exact (dist_comm _ _).trans har.symm
  · have hi := real_inner_le_norm e (T • e - a)
    have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    rw [inner_sub_right, real_inner_smul_right, hee, mul_one, he, one_mul,
      ← dist_eq_norm, ← har] at hi
    linarith

/-- At a critical zero contact the parameter-space ball gives the opposite
positive and zero balls required by the tangent-ball comparison argument. -/
theorem opposite_phase_balls_of_translation_orders {d : ℕ} {V : Space d → ℝ}
    (hV : ∀ x, 0 ≤ V x) {K : Set (Space d)} (horder : K ⊆ translationOrderSet V)
    (hzero : (0 : Space d) ∈ closure {x | 0 < V x})
    {a c : Space d} {r : ℝ} (hr : 0 < r) (ha : V a = 0)
    (hball : ball c r ⊆ K) (htangent : dist a c = r) :
    ∃ n : Space d, ‖n‖ = 1 ∧
      ball (r • n) r ⊆ {x | 0 < V (x + a)} ∧
      ball (-(r • n)) r ⊆ {x | V x = 0} := by
  let n := r⁻¹ • (c - a)
  have hn : r • n = c - a := by simp [n, smul_smul, hr.ne']
  refine ⟨n, ?_, ?_, ?_⟩
  · simp only [n, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    rw [← dist_eq_norm, dist_comm, htangent, inv_mul_cancel₀ hr.ne']
  · rw [hn]
    intro x hx
    apply ball_subset_positive_of_translation_orders horder hzero hball
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have he : x + a - c = x - (c - a) := by abel
    simpa only [he] using hx
  · rw [hn, neg_sub]
    exact ball_subset_zero_of_translation_orders hV horder ha hball

/-- Every fixed translation order survives pointwise limits of physical
translations; no countable exceptional set is involved. -/
theorem translationOrderSet_subset_of_translates_tendsto {d : ℕ}
    {U V : Space d → ℝ} {p : ℕ → Space d}
    (hlim : ∀ x, Tendsto (fun j ↦ U (p j + x)) atTop (𝓝 (V x))) :
    translationOrderSet U ⊆ translationOrderSet V := by
  intro a ha x
  apply le_of_tendsto_of_tendsto (hlim x) (hlim (x + a))
  exact Eventually.of_forall (fun j ↦ by simpa [add_assoc] using ha (p j + x))

/-- Failure points for translations approaching an allowed translation yield
equality at the two limiting points. The global Lipschitz bound controls the
moving translation argument. -/
theorem contact_eq_of_failed_translations {d : ℕ} {U V : Space d → ℝ} {L : ℝ≥0}
    (hU : LipschitzWith L U) {p a : ℕ → Space d} {a₀ : Space d}
    (ha : Tendsto a atTop (𝓝 a₀)) (ha₀ : a₀ ∈ translationOrderSet U)
    (hfail : ∀ j, U (p j + a j) < U (p j))
    (hlim : ∀ x, Tendsto (fun j ↦ U (p j + x)) atTop (𝓝 (V x))) : V a₀ = V 0 := by
  have hzero : Tendsto (fun j ↦ U (p j)) atTop (𝓝 (V 0)) := by simpa using hlim 0
  have hdist : Tendsto (fun j ↦ (L : ℝ) * dist a₀ (a j)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (L : ℝ))).mul
      ((tendsto_const_nhds (x := a₀)).dist ha)
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto (hlim a₀) (by simpa using hzero.add hdist)
    apply Eventually.of_forall
    intro j
    have hb := hU.dist_le_mul (p j + a₀) (p j + a j)
    rw [Real.dist_eq, dist_add_left] at hb
    have hi := (le_abs_self (U (p j + a₀) - U (p j + a j))).trans hb
    linarith [hfail j]
  · exact le_of_tendsto_of_tendsto hzero (hlim a₀)
      (Eventually.of_forall (fun j ↦ ha₀ (p j)))

end SerrinEpigraph
