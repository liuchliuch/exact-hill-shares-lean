import ExactHillShares.PointerLift
import ExactHillShares.MergeSorting
import ExactHillShares.GreedyMatching

/-!
# Lemma 3.1: counted merge-sort plus the moving-pointer reduction

This is the concrete implementation of manuscript Lemma 3.1. It sorts each
row once, retains original indices, and processes the paper's decreasing ranks
from last to first. Array wrappers share the stored sorted-index arrays.
-/
namespace ExactHillShares.PointerLift
open scoped BigOperators
open MergeSorting

/-- O(n) outer-array construction; each inner vector wraps the existing array,
without copying its m entries or reconstructing a sorting closure. -/
def storedIndices {n m : ℕ} (cached : Vector (CountedRow m) n) :
    Vector (Vector (Fin m) m) n :=
  Vector.ofFn (fun i => let row := read cached i; ⟨row.indices, row.indices_size⟩)

@[simp] theorem storedIndices_read {n m : ℕ} (cached : Vector (CountedRow m) n)
    (i : Fin n) (r : Fin m) :
    read (read (storedIndices cached) i) r = (read cached i).order r := by
  simp [storedIndices, read, CountedRow.order]

@[simp] theorem sortedIndices_read {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (i : Fin n) (r : Fin m) :
    read (read (storedIndices (countedSortRows cost)) i) r = sortOrder (cost i) r := by
  simp only [storedIndices_read]
  simp only [read, countedSortRows, Vector.getElem_ofFn]
  rfl

/-- Shared sorted rows, eagerly cached rank owners, and the actual completed
pointer execution. Certificates are erased by the compiler. -/
structure SortedRun {n m : ℕ} (cost : Fin n → Fin m → ℚ) (owner : Fin m → Fin n) where
  cached : Vector (CountedRow m) n
  owners : Vector (Fin n) m
  cached_eq : cached = countedSortRows cost
  owners_eq : ∀ r, read owners r = owner r
  result : State (storedIndices cached) (fun i x => (cost i x : ℝ)) (read owners) m

/-- Lift from an already-computed sorting cache. This performs no sort, and
allows an ordered allocation algorithm and this lift to share exactly the same
cached rows. Every owner callback is evaluated once into its input array. -/
def executeCachedSorted {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (cached : Vector (CountedRow m) n) (hcached : cached = countedSortRows cost)
    (owner : Fin m → Fin n) : SortedRun cost owner := by
  let rows := storedIndices cached
  let owners := Vector.ofFn owner
  have hinj : ∀ i, Function.Injective (read (read rows i)) := by
    intro i a b h
    apply (sortOrder (cost i)).injective
    change read (read (storedIndices cached) i) a =
      read (read (storedIndices cached) i) b at h
    rw [hcached, sortedIndices_read, sortedIndices_read] at h
    exact h
  have hsorted : ∀ i, Monotone (fun r => (cost i (read (read rows i) r) : ℝ)) := by
    intro i a b hab
    have h := monotone_sortOrder (cost i) hab
    simpa only [rows, hcached, sortedIndices_read] using
      (show (cost i (sortOrder (cost i) a) : ℝ) ≤ cost i (sortOrder (cost i) b) by
        exact_mod_cast h)
  exact ⟨cached, owners, hcached, by simp [owners],
    execute rows (fun i x => (cost i x : ℝ)) (read owners) hinj hsorted⟩

/-- Sort each input row exactly once, then call the same cache-consuming lift. -/
def executeSorted {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) : SortedRun cost owner :=
  let cached := countedSortRows cost
  executeCachedSorted cost cached rfl owner

def sortedAllocation {n m : ℕ} {cost : Fin n → Fin m → ℚ} {owner : Fin m → Fin n}
    (out : SortedRun cost owner) : Vector (Fin n) m := allocation out.result

lemma stored_cost_eq {n m : ℕ} {cost : Fin n → Fin m → ℚ} {owner : Fin m → Fin n}
    (out : SortedRun cost owner) (i : Fin n) (r : Fin m) :
    cost i (read (read (storedIndices out.cached) i) r) = rationalSortedCost cost i r := by
  rw [out.cached_eq, sortedIndices_read]
  exact congrFun (sortOrder_cost_eq_tuple (cost i)) r

/-- The concrete merge-sort/pointer result dominates each assigned rank
itemwise, before summing over an agent's bundle. -/
theorem sorted_itemwise {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) (r : Fin m) :
    cost (owner r) (ranksOf out.result r) ≤ rationalSortedCost cost (owner r) r := by
  have h := itemwise out.result r
  simp only [out.owners_eq, stored_cost_eq] at h
  exact_mod_cast h

/-- Lemma 3.1, cheapest-first coordinates: no agent's load increases. This
uses the actual computed merge-sort and pointer scan, not existential matching. -/
theorem lemma3_1_ascending {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) (i : Fin n) :
    (∑ x, if read (sortedAllocation out) x = i then (cost i x : ℝ) else 0) ≤
      ∑ r, if owner r = i then (rationalSortedCost cost i r : ℝ) else 0 := by
  have h := allocation_safe out.result i
  simpa only [sortedAllocation, out.owners_eq, stored_cost_eq] using h

/-- The rational statement of the same allocation certificate. -/
theorem lemma3_1_ascending_rat {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) (i : Fin n) :
    (∑ x, if read (sortedAllocation out) x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then rationalSortedCost cost i r else 0 := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using lemma3_1_ascending out i

/-- Paper coordinates: decreasing ranks are visited from last to first. -/
def descendingPointerLift {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) : Vector (Fin n) m :=
  sortedAllocation (executeSorted cost (fun r => owner r.rev))

/-- Manuscript Lemma 3.1 in its original decreasing-rank convention. -/
theorem lemma3_1 {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (i : Fin n) :
    (∑ x, if read (descendingPointerLift cost owner) x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then rationalDescendingCost cost i r else 0 := by
  have h := lemma3_1_ascending_rat (executeSorted cost (fun r => owner r.rev)) i
  have heq : (∑ r, if owner r.rev = i then rationalSortedCost cost i r else 0) =
      ∑ r, if owner r = i then rationalDescendingCost cost i r else 0 := by
    symm
    convert Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m))
      (fun r => if owner r.rev = i then rationalSortedCost cost i r else 0) using 1
    simp [rationalDescendingCost, Fin.revPerm]
  simpa only [heq, descendingPointerLift] using h

/-- The decreasing-rank interface for an existing sorted-row cache. -/
def descendingPointerLiftCached {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (cached : Vector (CountedRow m) n) (hcached : cached = countedSortRows cost)
    (owner : Fin m → Fin n) : Vector (Fin n) m :=
  sortedAllocation (executeCachedSorted cost cached hcached (fun r => owner r.rev))

/-- Lemma 3.1 for the cache-consuming implementation, with no sorting rerun. -/
theorem lemma3_1_cached {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (cached : Vector (CountedRow m) n) (hcached : cached = countedSortRows cost)
    (owner : Fin m → Fin n) (i : Fin n) :
    (∑ x, if read (descendingPointerLiftCached cost cached hcached owner) x = i
      then cost i x else 0) ≤
      ∑ r, if owner r = i then rationalDescendingCost cost i r else 0 := by
  subst cached
  exact lemma3_1 cost owner i

/-- After sorting: pointer loop, O(n) array wrappers and O(m) owner input
materialization. The O(m) final original-owner output is already charged. -/
def afterSortingOperations {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) : ℕ :=
  operations out.result + 3 * n + 2 * m

/-- The explicit O(nm) claim in the final sentence of manuscript Lemma 3.1. -/
theorem lemma3_1_after_sorting {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) (hn : 0 < n) (hm : 0 < m) :
    afterSortingOperations out ≤ 34 * (n * m) := by
  have h := operations_linear out.result hn hm
  have hn' : n ≤ n * m := Nat.le_mul_of_pos_right n hm
  have hm' : m ≤ n * m := Nat.le_mul_of_pos_left m hn
  unfold afterSortingOperations
  omega

/-- Full charge reads counters from the actual, shared sorting executions. -/
def sortedOperations {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) : ℕ :=
  rowsOperations out.cached + afterSortingOperations out

/-- Complete reduction, including all actual row sorts and the original-item
output: O(n*m*log(m+1)) in the stated array/arithmetic model. -/
theorem lemma3_1_with_sorting {n m : ℕ} {cost : Fin n → Fin m → ℚ}
    {owner : Fin m → Fin n} (out : SortedRun cost owner) (hn : 0 < n) (hm : 0 < m) :
    sortedOperations out ≤ 84 * n * m * (Nat.log2 m + 1) := by
  have hs := countedSortRows_operations_le hm cost
  rw [← out.cached_eq] at hs
  have hp := lemma3_1_after_sorting out hn hm
  have hh : n * m ≤ n * m * (Nat.log2 m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold sortedOperations
  nlinarith

end ExactHillShares.PointerLift
