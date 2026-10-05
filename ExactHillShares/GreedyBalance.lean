import Mathlib

namespace ExactHillShares

def listCost {ι : Type*} (cost : ι → ℝ) (xs : List ι) : ℝ := (xs.map cost).sum

/-- The actual greedy two-bin construction used in Appendix B: process the
finite list, placing the next item in a currently cheaper bin. Returning the
two lists retains original item identities, including zero-valued items. -/
noncomputable def greedySplit {ι : Type*} (cost : ι → ℝ) : List ι → List ι × List ι
  | [] => ([], [])
  | x :: xs =>
    let previous := greedySplit cost xs
    if listCost cost previous.1 ≤ listCost cost previous.2 then
      (x :: previous.1, previous.2)
    else (previous.1, x :: previous.2)

theorem greedySplit_perm {ι : Type*} (cost : ι → ℝ) (xs : List ι) :
    ((greedySplit cost xs).1 ++ (greedySplit cost xs).2).Perm xs := by
  induction xs with
  | nil => simp [greedySplit]
  | cons x xs ih =>
    simp only [greedySplit]
    split
    · simpa using ih.cons x
    · exact (List.perm_middle).trans (ih.cons x)

theorem greedySplit_total {ι : Type*} (cost : ι → ℝ) (xs : List ι) :
    listCost cost (greedySplit cost xs).1 + listCost cost (greedySplit cost xs).2 =
      listCost cost xs := by
  have h := ((greedySplit_perm cost xs).map cost).sum_eq
  simpa [listCost, List.map_append, List.sum_append] using h

theorem greedySplit_partition {ι : Type*} (cost : ι → ℝ) (xs : List ι)
    (hx : xs.Nodup) :
    (greedySplit cost xs).1.Nodup ∧ (greedySplit cost xs).2.Nodup ∧
      (greedySplit cost xs).1.Disjoint (greedySplit cost xs).2 := by
  exact List.nodup_append.mp ((greedySplit_perm cost xs).nodup_iff.mpr hx)

/-- Every step preserves load discrepancy at most the largest allowed item. -/
theorem greedySplit_discrepancy {ι : Type*} (cost : ι → ℝ) (xs : List ι)
    (p : ℝ) (hp : 0 ≤ p) (hc : ∀ x ∈ xs, 0 ≤ cost x ∧ cost x ≤ p) :
    |listCost cost (greedySplit cost xs).1 - listCost cost (greedySplit cost xs).2| ≤ p := by
  induction xs with
  | nil => simpa [greedySplit, listCost] using hp
  | cons x xs ih =>
    have hx := hc x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    obtain ⟨hlo, hhi⟩ := abs_le.mp ht
    simp only [greedySplit]
    split
    · simp only [listCost, List.map_cons, List.sum_cons, Prod.fst, Prod.snd] at *
      apply abs_le.mpr
      constructor <;> linarith
    · simp only [listCost, List.map_cons, List.sum_cons, Prod.fst, Prod.snd] at *
      apply abs_le.mpr
      constructor <;> linarith

/-- Universal greedy two-bin bound for each actual finite input, not merely
for one selected tail. This is the constructive discrepancy claim of Appendix B. -/
theorem greedySplit_max_bound {ι : Type*} (cost : ι → ℝ) (xs : List ι)
    (p : ℝ) (hp : 0 ≤ p) (hc : ∀ x ∈ xs, 0 ≤ cost x ∧ cost x ≤ p) :
    max (listCost cost (greedySplit cost xs).1) (listCost cost (greedySplit cost xs).2) ≤
      (listCost cost xs + p) / 2 := by
  have ht := greedySplit_total cost xs
  obtain ⟨hlo, hhi⟩ := abs_le.mp (greedySplit_discrepancy cost xs p hp hc)
  exact max_le (by linarith) (by linarith)

end ExactHillShares
