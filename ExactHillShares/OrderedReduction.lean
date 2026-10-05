import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev

namespace ExactHillShares

/-- A ranked family has a matching if the eligible set for rank `r`
has at least `r+1` members. This proves the ordered-instance lifting
without imposing a shared ordering on the original item identities. -/
theorem ranked_matching {m : ℕ} (eligible : Fin m → Finset (Fin m))
    (hcard : ∀ r, r.val + 1 ≤ (eligible r).card) :
    ∃ e : Equiv.Perm (Fin m), ∀ r, e r ∈ eligible r := by
  classical
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion eligible).card := by
    intro s
    by_cases hs : s.Nonempty
    · let r := s.max' hs
      have hr : r ∈ s := Finset.max'_mem s hs
      have hsub : s ⊆ Finset.Iic r := by
        intro x hx
        exact Finset.mem_Iic.mpr (Finset.le_max' s x hx)
      have hfirst : s.card ≤ r.val + 1 := by
        simpa using Finset.card_le_card hsub
      have hsecond : eligible r ⊆ s.biUnion eligible := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨r, hr, hx⟩
      exact hfirst.trans ((hcard r).trans (Finset.card_le_card hsecond))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective eligible).mp hall
  exact ⟨Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩, hmem⟩

/-- Lemma 3.1's itemwise domination, with ranks written cheapest-first.
Reversing the ranks gives the paper's most-expensive-first convention. -/
theorem ordered_itemwise_lift {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (order : Fin n → Equiv.Perm (Fin m))
    (horder : ∀ i, Monotone (fun r => cost i (order i r)))
    (owner : Fin m → Fin n) :
    ∃ e : Equiv.Perm (Fin m),
      ∀ r, cost (owner r) (e r) ≤ cost (owner r) (order (owner r) r) := by
  classical
  let eligible : Fin m → Finset (Fin m) := fun r =>
    Finset.univ.filter (fun x => cost (owner r) x ≤ cost (owner r) (order (owner r) r))
  have hcard : ∀ r, r.val + 1 ≤ (eligible r).card := by
    intro r
    have hsub : (Finset.Iic r).image (order (owner r)) ⊆ eligible r := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, horder (owner r) (Finset.mem_Iic.mp hj)⟩
    have hc := Finset.card_le_card hsub
    simpa [Finset.card_image_of_injective _ (order (owner r)).injective] using hc
  obtain ⟨e, he⟩ := ranked_matching eligible hcard
  exact ⟨e, fun r => (Finset.mem_filter.mp (he r)).2⟩

/-- The original-item allocation obtained by a matching has no larger
total cost for any agent than the given allocation of ordered ranks. -/
theorem ordered_allocation_lift {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (order : Fin n → Equiv.Perm (Fin m))
    (horder : ∀ i, Monotone (fun r => cost i (order i r)))
    (owner : Fin m → Fin n) :
    ∃ original : Fin m → Fin n, ∀ i,
      (∑ x, if original x = i then cost i x else 0) ≤
        ∑ r, if owner r = i then cost i (order i r) else 0 := by
  classical
  obtain ⟨e, he⟩ := ordered_itemwise_lift cost order horder owner
  refine ⟨fun x => owner (e.symm x), fun i => ?_⟩
  have hsum : (∑ x, if owner (e.symm x) = i then cost i x else 0) =
      ∑ r, if owner r = i then cost i (e r) else 0 := by
    symm
    convert Equiv.sum_comp e (fun x => if owner (e.symm x) = i then cost i x else 0) using 1
    simp
  rw [hsum]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hi : owner r = i
  · simpa [hi] using he r
  · simp [hi]

/-- The actual sorted rank cost, with cheapest rank first. -/
noncomputable def sortedRankCost {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (i : Fin n) (r : Fin m) : ℝ := cost i (Tuple.sort (cost i) r)

/-- Lemma 3.1 for actual sorted rows, with no sorting-permutation hypothesis. -/
theorem sorted_allocation_lift {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (owner : Fin m → Fin n) :
    ∃ original : Fin m → Fin n, ∀ i,
      (∑ x, if original x = i then cost i x else 0) ≤
        ∑ r, if owner r = i then sortedRankCost cost i r else 0 := by
  exact ordered_allocation_lift cost (fun i => Tuple.sort (cost i))
    (fun i => Tuple.monotone_sort (cost i)) owner

/-- Paper convention: decreasing ranked costs. -/
noncomputable def descendingRankCost {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (i : Fin n) (r : Fin m) : ℝ := sortedRankCost cost i r.rev

theorem descendingRankCost_antitone {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (i : Fin n) : Antitone (descendingRankCost cost i) := by
  intro r s hrs
  exact Tuple.monotone_sort (cost i) (Fin.rev_le_rev.mpr hrs)

/-- Lemma 3.1 in the paper's decreasing rank convention. -/
theorem descending_allocation_lift {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (owner : Fin m → Fin n) :
    ∃ original : Fin m → Fin n, ∀ i,
      (∑ x, if original x = i then cost i x else 0) ≤
        ∑ r, if owner r = i then descendingRankCost cost i r else 0 := by
  classical
  obtain ⟨original, h⟩ := sorted_allocation_lift cost (fun r => owner r.rev)
  refine ⟨original, fun i => ?_⟩
  have heq : (∑ r, if owner r.rev = i then sortedRankCost cost i r else 0) =
      ∑ r, if owner r = i then descendingRankCost cost i r else 0 := by
    symm
    convert Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m))
      (fun r => if owner r.rev = i then sortedRankCost cost i r else 0) using 1
    simp [descendingRankCost, Fin.revPerm]
  simpa only [heq] using h i

end ExactHillShares
