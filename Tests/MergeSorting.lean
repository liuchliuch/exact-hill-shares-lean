import ExactHillShares.MergeSorting

namespace ExactHillShares.MergeSorting.Tests

/-- Odd size, repeated costs, a negative value, and a zero. -/
def sample : Fin 7 → ℚ := ![3, 1, 2, 1, -1, 3, 0]
def row := countedSortRow sample

#eval (row.indices.toList.map Fin.val, row.values.toList, row.descending.toList,
  row.comparisons, row.operations)

#eval show IO Unit from do
  unless row.indices.toList.map Fin.val == [4, 6, 1, 3, 2, 0, 5] do
    throw (IO.userError "merge sort lost an original index or mishandled a tie")
  unless row.values == #[-1, 0, 1, 1, 2, 3, 3] do
    throw (IO.userError "incorrect ascending values")
  unless row.descending == #[3, 3, 2, 1, 1, 0, -1] do
    throw (IO.userError "incorrect shared descending values")
  unless row.comparisons == 14 do
    throw (IO.userError "incorrect branch-following comparison count")
  unless row.operations ≤ 44 * 7 * (Nat.log2 7 + 1) do
    throw (IO.userError "incorrect operation bound")
  for r in List.finRange 7 do
    unless row.order r == row.indices[r.val]'(by rw [row.indices_size]; exact r.isLt) do
      throw (IO.userError "permutation does not read the stored index array")
    unless row.order.symm (row.order r) == r do
      throw (IO.userError "computed index map is not a permutation")

/-- Base cases are total and retain their precise lengths. -/
def empty := countedSortRow (fun j : Fin 0 => Fin.elim0 j)
def singleton := countedSortRow (fun _j : Fin 1 => (-2 : ℚ))
#eval show IO Unit from do
  unless empty.values.isEmpty && empty.indices.isEmpty && empty.descending.isEmpty do
    throw (IO.userError "empty sorting result")
  unless empty.comparisons == 0 do throw (IO.userError "empty comparison count")
  unless singleton.values == #[-2] && singleton.descending == #[-2] do
    throw (IO.userError "singleton sorting result")
  unless singleton.comparisons == 0 do throw (IO.userError "singleton comparison count")

def batchCost (i : Fin 2) (j : Fin 7) : ℚ := if i.val = 0 then sample j else -sample j
def batch := countedSortRows batchCost
#eval rowsOperations batch
#eval show IO Unit from do
  unless rowsOperations batch ≤ 50 * 2 * 7 * (Nat.log2 7 + 1) do
    throw (IO.userError "batch operation bound")
  for i in List.finRange 2 do
    for r in List.finRange 7 do
      unless (indexRows batch)[i][r] == batch[i].order r do
        throw (IO.userError "batch projection changed original index")

example : row.operations ≤ 44 * 7 * (Nat.log2 7 + 1) :=
  countedSortRow_operations_le (by decide) sample
example : rowsOperations batch ≤ 50 * 2 * 7 * (Nat.log2 7 + 1) :=
  countedSortRows_operations_le (by decide) batchCost
example : rowsOperations batch ≤ 100 * 2 * 7 * Nat.log2 7 :=
  countedSortRows_operations_log_bound (by decide) batchCost
example : Monotone (sample ∘ sortOrder sample) := monotone_sortOrder sample

#print axioms sortFuel_values
#print axioms sort_operations_le
#print axioms monotone_sortOrder
#print axioms countedSortRows_operations_log_bound

end ExactHillShares.MergeSorting.Tests
