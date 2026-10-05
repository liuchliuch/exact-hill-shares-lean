import ExactHillShares.PointerLiftSorting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace ExactHillShares.PointerLift.Tests

def rows : Vector (Vector (Fin 4) 4) 2 := #v[#v[0, 1, 2, 3], #v[0, 2, 1, 3]]
def rationalCost (i : Fin 2) (x : Fin 4) : ℚ :=
  if i.val = 0 then x.val else if x.val = 1 then 2 else if x.val = 2 then 1 else x.val
def cost (i : Fin 2) (x : Fin 4) : ℝ := rationalCost i x
def owner : Fin 4 → Fin 2 := ![0, 1, 0, 1]

lemma rows_injective : ∀ i, Function.Injective (read (read rows i)) := by decide

lemma row_cost (i : Fin 2) (r : Fin 4) : cost i (read (read rows i) r) = r.val := by
  fin_cases i <;> fin_cases r <;> norm_num [cost, rationalCost, rows, read, Fin.val_ofNat', Fin.instOfNat, Fin.ofNat']
  all_goals change ((3 : ℚ) : ℝ) = (3 : ℝ); norm_num

lemma rows_sorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r)) := by
  intro i a b h
  dsimp only
  rw [row_cost, row_cost]
  exact_mod_cast h

def result := execute rows cost owner rows_injective rows_sorted

/- Both agents share the cheapest original. The second agent must skip it,
then skips the first agent's later choice on its next visit. -/
#eval (result.visits, result.pointers.toArray, result.ranks.toArray,
  (allocation result).toArray)

#eval show IO Unit from do
  unless result.visits == 6 do throw (IO.userError "wrong probe count")
  unless result.pointers.toArray == #[2, 4] do throw (IO.userError "wrong pointers")
  unless result.ranks.toArray == #[some 0, some 2, some 1, some 3] do
    throw (IO.userError "wrong rank permutation")
  unless (allocation result).toArray == #[0, 0, 1, 1] do
    throw (IO.userError "wrong original owners")
  unless operations result == 123 do throw (IO.userError "wrong operation count")
example (i : Fin 2) :
    (∑ x, if read (allocation result) x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then cost i (read (read rows i) r) else 0 :=
  allocation_safe result i

/-- The empty instance does not need a fabricated agent or item. -/
def emptyRows : Vector (Vector (Fin 0) 0) 0 := #v[]
def emptyResult := execute emptyRows (fun i => Fin.elim0 i) Fin.elim0
  (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

#eval show IO Unit from do
  unless emptyResult.visits == 0 do throw (IO.userError "empty scan")
  unless (allocation emptyResult).toArray == #[] do throw (IO.userError "empty owners")


/-- Single-agent exhaustion reaches pointer m without a sentinel item. -/
def oneRows : Vector (Vector (Fin 3) 3) 1 := #v[#v[0, 1, 2]]
lemma one_injective : ∀ i, Function.Injective (read (read oneRows i)) := by decide
lemma one_sorted : ∀ i, Monotone (fun r => (0 : ℝ) + (read (read oneRows i) r).val) := by
  intro i a b h
  have he : ∀ j : Fin 3, read (read oneRows i) j = j := by
    fin_cases i; decide
  simp only [he, zero_add]
  exact_mod_cast h
def oneResult := execute oneRows (fun _ x => (0 : ℝ) + x.val) (fun _ => 0)
  one_injective one_sorted
#eval show IO Unit from do
  unless oneResult.visits == 3 do throw (IO.userError "singleton probes")
  unless oneResult.pointers.toArray == #[3] do throw (IO.userError "singleton cursor")
  unless (allocation oneResult).toArray == #[0, 0, 0] do
    throw (IO.userError "singleton owners")

/-- The complete computation sorts each rational row, retains original indices,
and then executes the shared moving-pointer lift. -/
def mergedResult := executeSorted rationalCost owner
#eval (mergedResult.result.visits, (sortedAllocation mergedResult).toArray,
  afterSortingOperations mergedResult, sortedOperations mergedResult)
#eval show IO Unit from do
  unless mergedResult.result.visits == 6 do throw (IO.userError "merge-plus-pointer probes")
  unless (sortedAllocation mergedResult).toArray == #[0, 0, 1, 1] do
    throw (IO.userError "merge-plus-pointer owners")
  unless (descendingPointerLift rationalCost (fun r => owner r.rev)).toArray == #[0, 0, 1, 1] do
    throw (IO.userError "descending coordinate conversion")

example (i : Fin 2) :
    (∑ x, if read (sortedAllocation mergedResult) x = i then rationalCost i x else 0) ≤
      ∑ r, if owner r = i then rationalSortedCost rationalCost i r else 0 :=
  lemma3_1_ascending_rat mergedResult i

example : afterSortingOperations mergedResult ≤ 34 * (2 * 4) :=
  lemma3_1_after_sorting mergedResult (by decide) (by decide)
example : sortedOperations mergedResult ≤ 84 * 2 * 4 * (Nat.log2 4 + 1) :=
  lemma3_1_with_sorting mergedResult (by decide) (by decide)

/-- Reuse an existing cache, as the full ordered-allocation pipeline does. -/
def sharedCache := MergeSorting.countedSortRows rationalCost
def cachedResult := executeCachedSorted rationalCost sharedCache rfl owner
#eval show IO Unit from do
  unless (sortedAllocation cachedResult).toArray == #[0, 0, 1, 1] do
    throw (IO.userError "cache-consuming lift")
  unless cachedResult.result.visits == mergedResult.result.visits do
    throw (IO.userError "cache-consuming probe count")

def mergedEmpty := executeSorted (fun (_ : Fin 3) (x : Fin 0) => (Fin.elim0 x : ℚ)) Fin.elim0
#eval show IO Unit from do
  unless (sortedAllocation mergedEmpty).toArray == #[] do
    throw (IO.userError "full sorting/lifting empty input")

example (r : Fin 4) : rationalCost (owner r) (ranksOf cachedResult.result r) ≤
    rationalSortedCost rationalCost (owner r) r := sorted_itemwise cachedResult r

#print axioms lemma3_1
#print axioms lemma3_1_after_sorting
#print axioms lemma3_1_with_sorting

end ExactHillShares.PointerLift.Tests
