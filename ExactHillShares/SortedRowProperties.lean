import ExactHillShares.OriginalAlgorithm

namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- The first decreasing sorted entry bounds every original item. -/
theorem originalRows_le_zero {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (hm : 0 < m) (i : Fin n) (j : Fin m) :
    cost i j ≤ originalRows cost i 0 := by
  let z : Fin m := ⟨0, hm⟩
  have hr : (Tuple.sort (cost i)).symm j ≤ z.rev := by
    change ((Tuple.sort (cost i)).symm j).val ≤ m - (0 + 1)
    have hj := ((Tuple.sort (cost i)).symm j).isLt
    omega
  have h := Tuple.monotone_sort (cost i) hr
  simpa [Function.comp_def, z, originalRows, hm, rationalDescendingCost,
    rationalSortedCost] using h

/-- The first decreasing sorted entry is an actual original value. -/
theorem originalRows_zero_attained {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (hm : 0 < m) (i : Fin n) : ∃ j, cost i j = originalRows cost i 0 := by
  refine ⟨Tuple.sort (cost i) (⟨0, hm⟩ : Fin m).rev, ?_⟩
  simp [originalRows, hm, rationalDescendingCost, rationalSortedCost]

/-- A normalized original rational row has precisely the maximum supplied by
its first decreasing sorted entry. This is the real-valued certificate used
by the singleton preprocessing branch. -/
theorem originalRows_isNormalizedExact {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (hc : ∀ i j, 0 ≤ cost i j) (hnorm : ∀ i, ∑ j, cost i j = 1) :
    ∀ i, IsNormalizedExact (fun j => (cost i j : ℝ)) (originalRows cost i 0 : ℝ) := by
  intro i
  have hm : 0 < m := by
    by_contra h
    have hm : m = 0 := by omega
    subst m
    have hi := hnorm i
    simp at hi
  refine ⟨fun j => ⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp only
    exact_mod_cast hc i j
  · dsimp only
    exact_mod_cast originalRows_le_zero cost hm i j
  · dsimp only
    exact_mod_cast hnorm i
  · obtain ⟨j, hj⟩ := originalRows_zero_attained cost hm i
    exact ⟨j, by dsimp only; exact_mod_cast hj⟩

end ExactHillShares.Algorithm
