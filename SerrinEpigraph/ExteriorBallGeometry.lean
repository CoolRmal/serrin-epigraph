module

public import SerrinEpigraph.TangentBalls

/-!
# Strict separation after translating exterior balls downward
-/

public section

open Set Metric

namespace SerrinEpigraph

/-- Moving a point outside the open epigraph downward puts it outside the closed epigraph. -/
theorem downward_notMem_closure_epigraph {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {x : Space (m + 1)} (hx : x ∉ epigraph g)
    {t : ℝ} (ht : 0 < t) : x - t • verticalDirection m ∉ closure (epigraph g) := by
  rw [sub_eq_add_neg, ← neg_smul, add_vertical_eq_point, closure_epigraph hg]
  simp only [mem_ofPred_eq, horizontal_point, last_point]
  have hx' : x (Fin.last m) ≤ g (horizontal x) := not_lt.mp hx
  linarith

/-- The closed ball of an exterior open ball stays outside the open epigraph. -/
theorem exterior_closedBall_subset_compl {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {c : Space (m + 1)} {a : ℝ} (ha : 0 < a)
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ) :
    closedBall c a ⊆ (epigraph g)ᶜ := by
  rw [← closure_ball c ha.ne']
  apply closure_minimal ?_ (isOpen_epigraph hg).isClosed_compl
  intro x hx he
  exact hball hx (subset_closure he)

/-- Every positive downward translation of an exterior ball is strictly separated from
the closed epigraph, including its entire boundary sphere. -/
theorem downward_exterior_closedBall_subset_compl_closure {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {c : Space (m + 1)} {a : ℝ} (ha : 0 < a)
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ) {t : ℝ} (ht : 0 < t) :
    closedBall (c - t • verticalDirection m) a ⊆ (closure (epigraph g))ᶜ := by
  intro x hx
  have hx' : x + t • verticalDirection m ∈ closedBall c a := by
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    convert hx using 1
    congr 1
    abel
  have he := downward_notMem_closure_epigraph hg
    (exterior_closedBall_subset_compl hg ha hball hx') ht
  simpa only [add_sub_cancel_right, mem_compl_iff] using he

/-- Every closed-epigraph point lies strictly beyond the radius of the translated exterior ball. -/
theorem dist_gt_radius_of_downward_exterior_ball {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {c x : Space (m + 1)} {a : ℝ} (ha : 0 < a)
    (hball : ball c a ⊆ (closure (epigraph g))ᶜ) {t : ℝ} (ht : 0 < t)
    (hx : x ∈ closure (epigraph g)) : a < dist x (c - t • verticalDirection m) := by
  by_contra hn
  exact downward_exterior_closedBall_subset_compl_closure hg ha hball ht
    (not_lt.mp hn) hx

end SerrinEpigraph
