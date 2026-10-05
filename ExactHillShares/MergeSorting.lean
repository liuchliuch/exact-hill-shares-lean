import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Counted comparison-based merge sorting

The output and counters are produced together. `comparisons` counts calls to
an input comparison. `operations` charges the executed list branches, cells,
and unit-cost arithmetic. It is not a bit-complexity claim for rational numbers.
The split counter follows its actual traversal; the length traversal is charged
one unit per cell and terminator. All intermediate results are bound once.
-/
namespace ExactHillShares.MergeSorting

structure CountedList (α : Type*) where
  values : List α
  comparisons : ℕ
  operations : ℕ
  deriving Repr

structure CountedSplit (α : Type*) where
  left : List α
  right : List α
  operations : ℕ
  deriving Repr

/-- Split after `k` cells, counting the traversal and reconstruction. -/
def split (k : ℕ) (xs : List α) : CountedSplit α :=
  match k, xs with
  | 0, xs => ⟨[], xs, 1⟩
  | _ + 1, [] => ⟨[], [], 1⟩
  | k + 1, a :: xs =>
      let s := split k xs
      ⟨a :: s.left, s.right, s.operations + 3⟩

@[simp] theorem split_left (k : ℕ) (xs : List α) : (split k xs).left = xs.take k := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => cases xs <;> simp [split, ih]

@[simp] theorem split_right (k : ℕ) (xs : List α) : (split k xs).right = xs.drop k := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => cases xs <;> simp [split, ih]

theorem split_operations_le (k : ℕ) (xs : List α) :
    (split k xs).operations ≤ 3 * k + 1 := by
  induction k generalizing xs with
  | zero => simp [split]
  | succ k ih =>
      cases xs with
      | nil => simp [split]
      | cons a xs => have := ih xs; simp only [split]; omega

/-- Every nonterminal merge branch evaluates exactly one comparison. -/
def merge (le : α → α → Bool) (xs ys : List α) : CountedList α :=
  match xs, ys with
  | [], ys => ⟨ys, 0, 1⟩
  | xs, [] => ⟨xs, 0, 1⟩
  | a :: xs, b :: ys =>
      if le a b then
        let t := merge le xs (b :: ys)
        ⟨a :: t.values, t.comparisons + 1, t.operations + 5⟩
      else
        let t := merge le (a :: xs) ys
        ⟨b :: t.values, t.comparisons + 1, t.operations + 5⟩
termination_by xs.length + ys.length

@[simp] theorem merge_values (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).values = List.merge xs ys le := by
  induction xs, ys using merge.induct le with
  | case1 ys => simp [merge, List.merge]
  | case2 a xs => simp [merge, List.merge]
  | case3 a xs b ys h ih => simp [merge, List.merge, h, ih]
  | case4 a xs b ys h ih => simp [merge, List.merge, h, ih]

@[simp] theorem merge_length (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).values.length = xs.length + ys.length := by simp

theorem merge_comparisons_le (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).comparisons ≤ xs.length + ys.length := by
  induction xs, ys using merge.induct le with
  | case1 ys => simp [merge]
  | case2 a xs => simp [merge]
  | case3 a xs b ys h ih => simp only [merge, if_pos h, List.length_cons] at *; omega
  | case4 a xs b ys h ih => simp only [merge, if_neg h, List.length_cons] at *; omega

theorem merge_operations_le (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).operations ≤ 5 * (xs.length + ys.length) + 1 := by
  induction xs, ys using merge.induct le with
  | case1 ys => simp [merge]
  | case2 a xs => simp [merge]
  | case3 a xs b ys h ih => simp only [merge, if_pos h, List.length_cons] at *; omega
  | case4 a xs b ys h ih => simp only [merge, if_neg h, List.length_cons] at *; omega

/-- Top-down mergesort with a sufficient logarithmic recursion budget.
The zero-budget branch is proved unreachable on nonsingletons at the public entry.
The linear charge records the length traversal; `split` and `merge` supply their
own branch-following charges. -/
def sortFuel (le : α → α → Bool) : ℕ → List α → CountedList α
  | 0, xs => ⟨xs, 0, 2⟩
  | _ + 1, [] => ⟨[], 0, 2⟩
  | _ + 1, [a] => ⟨[a], 0, 2⟩
  | d + 1, a :: b :: xs =>
      let input := a :: b :: xs
      let size := input.length
      let sides := split ((size + 1) / 2) input
      let left := sortFuel le d sides.left
      let right := sortFuel le d sides.right
      let result := merge le left.values right.values
      ⟨result.values, left.comparisons + right.comparisons + result.comparisons,
        left.operations + right.operations + result.operations + sides.operations + size + 7⟩

@[simp] theorem sortFuel_length (le : α → α → Bool) (d : ℕ) (xs : List α) :
    (sortFuel le d xs).values.length = xs.length := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih =>
      match xs with
      | [] => rfl
      | [a] => rfl
      | a :: b :: xs => simp [sortFuel, ih]; omega

theorem sortFuel_values (le : α → α → Bool) (d : ℕ) (xs : List α)
    (h : xs.length ≤ 2 ^ d) :
    (sortFuel le d xs).values = xs.mergeSort le := by
  induction d generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [sortFuel]
      | cons a xs => cases xs with
        | nil => simp [sortFuel]
        | cons b xs => simp only [List.length_cons, pow_zero] at h; omega
  | succ d ih =>
      match xs with
      | [] => simp [sortFuel]
      | [a] => simp [sortFuel]
      | a :: b :: xs =>
          have hl : ((a :: b :: xs).take (((a :: b :: xs).length + 1) / 2)).length ≤ 2 ^ d := by
            simp only [List.length_take, List.length_cons, pow_succ] at *; omega
          have hr : ((a :: b :: xs).drop (((a :: b :: xs).length + 1) / 2)).length ≤ 2 ^ d := by
            simp only [List.length_drop, List.length_cons, pow_succ] at *; omega
          simp only [sortFuel, merge_values, split_left, split_right, ih _ hl, ih _ hr]
          simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq]

/-- Comparison budget for the actual execution tree, valid even with insufficient fuel. -/
theorem sortFuel_comparisons_le (le : α → α → Bool) (d : ℕ) (xs : List α) :
    (sortFuel le d xs).comparisons ≤ d * xs.length := by
  induction d generalizing xs with
  | zero => simp [sortFuel]
  | succ d ih =>
      match xs with
      | [] => simp [sortFuel]
      | [a] => simp [sortFuel]
      | a :: b :: xs =>
          let k := ((a :: b :: xs).length + 1) / 2
          let l := (a :: b :: xs).take k
          let r := (a :: b :: xs).drop k
          have hl := ih l
          have hr := ih r
          have hm := merge_comparisons_le le (sortFuel le d l).values (sortFuel le d r).values
          simp only [sortFuel_length] at hm
          have hlen : l.length + r.length = (a :: b :: xs).length := by simp [l, r]; omega
          simp only [sortFuel, split_left, split_right]
          change (sortFuel le d l).comparisons + (sortFuel le d r).comparisons +
            (merge le (sortFuel le d l).values (sortFuel le d r).values).comparisons ≤ _
          nlinarith

/-- The work done at each level is linear in the number of elements. -/
theorem sortFuel_operations_le (le : α → α → Bool) (d : ℕ) (xs : List α)
    (hne : xs ≠ []) :
    (sortFuel le d xs).operations ≤ (16 * d + 2) * xs.length := by
  induction d generalizing xs with
  | zero => cases xs <;> simp_all [sortFuel]
  | succ d ih =>
      match xs with
      | [] => contradiction
      | [a] => simp [sortFuel]
      | a :: b :: xs =>
          let input := a :: b :: xs
          let k := (input.length + 1) / 2
          let l := input.take k
          let r := input.drop k
          have hlen : l.length + r.length = input.length := by simp [l, r]; omega
          have hk : k ≤ input.length := by simp [k, input]; omega
          have hlpos : 0 < l.length := by simp [l, k, input]
          have hrpos : 0 < r.length := by simp [r, k, input]; omega
          have hl := ih l (by simpa only [List.length_pos_iff] using hlpos)
          have hr := ih r (by simpa only [List.length_pos_iff] using hrpos)
          have hm := merge_operations_le le (sortFuel le d l).values (sortFuel le d r).values
          simp only [sortFuel_length] at hm
          have hs := split_operations_le k input
          have hin : 2 ≤ input.length := by simp [input]
          simp only [sortFuel, split_left, split_right]
          change (sortFuel le d l).operations + (sortFuel le d r).operations +
            (merge le (sortFuel le d l).values (sortFuel le d r).values).operations +
            (split k input).operations + input.length + 7 ≤ _
          nlinarith

/-- Public sorting program, with sufficient budget computed from input length.
The final charge includes the length pass and logarithm computation. -/
def sort (le : α → α → Bool) (xs : List α) : CountedList α :=
  let size := xs.length
  let depth := Nat.log2 size + 1
  let r := sortFuel le depth xs
  ⟨r.values, r.comparisons, r.operations + size + 3 * depth + 2⟩

@[simp] theorem sort_values (le : α → α → Bool) (xs : List α) :
    (sort le xs).values = xs.mergeSort le := by
  apply sortFuel_values
  by_cases hz : xs.length = 0
  · simp [hz]
  · exact Nat.le_of_lt ((Nat.log2_lt hz).mp (Nat.lt_succ_self _))

@[simp] theorem sort_length (le : α → α → Bool) (xs : List α) :
    (sort le xs).values.length = xs.length := by simp

theorem sort_perm (le : α → α → Bool) (xs : List α) :
    (sort le xs).values.Perm xs := by simpa using List.mergeSort_perm xs le

theorem sort_comparisons_le (le : α → α → Bool) (xs : List α) :
    (sort le xs).comparisons ≤ xs.length * (Nat.log2 xs.length + 1) := by
  simpa only [sort, Nat.mul_comm] using sortFuel_comparisons_le le (Nat.log2 xs.length + 1) xs

theorem sort_operations_le (le : α → α → Bool) (xs : List α) (hne : xs ≠ []) :
    (sort le xs).operations ≤ 24 * xs.length * (Nat.log2 xs.length + 1) := by
  have h := sortFuel_operations_le le (Nat.log2 xs.length + 1) xs hne
  have hn : 0 < xs.length := List.length_pos_iff.mpr hne
  simp only [sort]
  nlinarith

/-- Sort original indices, retaining item identities even when costs coincide. -/
def sortIndices {m : ℕ} (cost : Fin m → ℚ) : CountedList (Fin m) :=
  sort (fun a b => decide (cost a ≤ cost b)) (List.finRange m)

@[simp] theorem sortIndices_length {m : ℕ} (cost : Fin m → ℚ) :
    (sortIndices cost).values.length = m := by simp [sortIndices]

theorem sortIndices_perm {m : ℕ} (cost : Fin m → ℚ) :
    (sortIndices cost).values.Perm (List.finRange m) := sort_perm _ _

theorem sortIndices_sorted {m : ℕ} (cost : Fin m → ℚ) :
    (sortIndices cost).values.Pairwise (fun a b => cost a ≤ cost b) := by
  simp only [sortIndices, sort_values]
  have h := List.sorted_mergeSort
    (le := fun a b : Fin m => decide (cost a ≤ cost b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
    (List.finRange m)
  simpa only [decide_eq_true_eq] using h

/-- Stored index and value arrays, together with a complete-cover certificate.
Proof fields are erased. The computational fields are built only once. -/
structure CountedRow (m : ℕ) where
  indices : Array (Fin m)
  values : Array ℚ
  descending : Array ℚ
  comparisons : ℕ
  operations : ℕ
  indices_size : indices.size = m
  indices_perm : indices.toList.Perm (List.finRange m)

/-- Enumerate once, sort once, and materialize index and cost arrays once.
The extra linear charge covers enumeration, mapping, reversal, and all three array builds. -/
def countedSortRow {m : ℕ} (cost : Fin m → ℚ) : CountedRow m :=
  let r := sortIndices cost
  let rowValues := r.values.map cost
  ⟨r.values.toArray, rowValues.toArray, rowValues.reverse.toArray, r.comparisons,
    r.operations + 12 * m + 6, by simp [r], by simpa [r] using sortIndices_perm cost⟩

namespace CountedRow

/-- A permutation whose forward map is a constant-time read of the stored array.
The inverse is an index search and is not used by pointer lifting. -/
def order {m : ℕ} (row : CountedRow m) : Equiv.Perm (Fin m) where
  toFun r := row.indices[r.val]'(by rw [row.indices_size]; exact r.isLt)
  invFun a := ⟨row.indices.toList.idxOf a, by
    have h := List.idxOf_lt_length_iff.mpr (row.indices_perm.mem_iff.mpr (List.mem_finRange a))
    simpa only [Array.length_toList, row.indices_size] using h⟩
  left_inv r := by
    apply Fin.ext
    change row.indices.toList.idxOf (row.indices[r.val]'(_)) = r.val
    rw [← Array.getElem_toList]
    exact List.idxOf_getElem (row.indices_perm.nodup_iff.mpr (List.nodup_finRange m)) _ _
  right_inv a := by
    change row.indices[row.indices.toList.idxOf a]'(_) = a
    rw [← Array.getElem_toList]
    exact List.getElem_idxOf _

@[simp] theorem order_apply {m : ℕ} (row : CountedRow m) (r : Fin m) :
    row.order r = row.indices[r.val]'(by rw [row.indices_size]; exact r.isLt) := rfl

end CountedRow

/-- The index permutation computed by the instrumented sorting program. -/
def sortOrder {m : ℕ} (cost : Fin m → ℚ) : Equiv.Perm (Fin m) :=
  (countedSortRow cost).order

@[simp] theorem sortOrder_apply {m : ℕ} (cost : Fin m → ℚ) (r : Fin m) :
    sortOrder cost r = (sortIndices cost).values[r.val]'(by rw [sortIndices_length]; exact r.isLt) := by
  simp [sortOrder, countedSortRow]

theorem monotone_sortOrder {m : ℕ} (cost : Fin m → ℚ) :
    Monotone (cost ∘ sortOrder cost) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b; exact le_rfl
  · have h := (List.pairwise_iff_getElem.mp (sortIndices_sorted cost)) a.val b.val
      (by rw [sortIndices_length]; exact a.isLt)
      (by rw [sortIndices_length]; exact b.isLt) hlt
    simpa only [Function.comp_apply, sortOrder_apply] using h

/-- The stored ascending values agree with the established tuple-sort semantics,
without imposing distinct costs or a tie-breaking hypothesis. -/
theorem sortOrder_cost_eq_tuple {m : ℕ} (cost : Fin m → ℚ) :
    cost ∘ sortOrder cost = cost ∘ Tuple.sort cost :=
  Tuple.unique_monotone (monotone_sortOrder cost) (Tuple.monotone_sort cost)

@[simp] theorem countedSortRow_size {m : ℕ} (cost : Fin m → ℚ) :
    (countedSortRow cost).values.size = m := by simp [countedSortRow]

theorem countedSortRow_get {m : ℕ} (cost : Fin m → ℚ) (r : Fin m) :
    (countedSortRow cost).values[r.val]'(by rw [countedSortRow_size]; exact r.isLt) =
      cost (Tuple.sort cost r) := by
  have h := congrFun (sortOrder_cost_eq_tuple cost) r
  simpa [countedSortRow] using h

theorem countedSortRow_index_get {m : ℕ} (cost : Fin m → ℚ) (r : Fin m) :
    (countedSortRow cost).indices[r.val]'(by
      rw [(countedSortRow cost).indices_size]; exact r.isLt) = sortOrder cost r := rfl

theorem countedSortRow_comparisons_le {m : ℕ} (cost : Fin m → ℚ) :
    (countedSortRow cost).comparisons ≤ m * (Nat.log2 m + 1) := by
  simpa only [countedSortRow, sortIndices, List.length_finRange] using
    sort_comparisons_le (fun a b : Fin m => decide (cost a ≤ cost b)) (List.finRange m)

/-- Explicit `O(m log(m+1))` arithmetic-operation bound for a nonempty row. -/
theorem countedSortRow_operations_le {m : ℕ} (hm : 0 < m) (cost : Fin m → ℚ) :
    (countedSortRow cost).operations ≤ 44 * m * (Nat.log2 m + 1) := by
  have h := sort_operations_le (fun a b : Fin m => decide (cost a ≤ cost b))
    (List.finRange m) (by simpa only [← List.length_pos_iff, List.length_finRange] using hm)
  simp only [List.length_finRange] at h
  simp only [countedSortRow, sortIndices]
  nlinarith

/-- All rows are materialized in a vector; later access does not rerun sorting. -/
def countedSortRows {n m : ℕ} (cost : Fin n → Fin m → ℚ) : Vector (CountedRow m) n :=
  Vector.ofFn (fun i => countedSortRow (cost i))

@[simp] theorem countedSortRows_get {n m : ℕ} (cost : Fin n → Fin m → ℚ) (i : Fin n) :
    (countedSortRows cost)[i] = countedSortRow (cost i) := by simp [countedSortRows]

/-- Sum the work actually recorded by the cached row computations, and charge
both outer-vector construction and index-vector projection. -/
def rowsOperations {n m : ℕ} (rows : Vector (CountedRow m) n) : ℕ :=
  (∑ i : Fin n, rows[i].operations) + 6 * n

/-- Explicit `O(n*m*log(m+1))` row-preprocessing bound, including outer storage. -/
theorem countedSortRows_operations_le {n m : ℕ} (hm : 0 < m)
    (cost : Fin n → Fin m → ℚ) :
    rowsOperations (countedSortRows cost) ≤ 50 * n * m * (Nat.log2 m + 1) := by
  have h : (∑ i : Fin n, (countedSortRows cost)[i].operations) ≤
      n * (44 * m * (Nat.log2 m + 1)) := by
    calc
      _ ≤ ∑ _i : Fin n, 44 * m * (Nat.log2 m + 1) := Finset.sum_le_sum (fun i _ => by
        simpa [countedSortRows] using countedSortRow_operations_le hm (cost i))
      _ = _ := by simp
  simp only [rowsOperations]
  have hm' : 1 ≤ m * (Nat.log2 m + 1) := by nlinarith
  have hn := Nat.mul_le_mul_left n hm'
  nlinarith


namespace CountedRow

/-- Wrap the stored index array without traversing or copying it. -/
def indexVector {m : ℕ} (row : CountedRow m) : Vector (Fin m) m :=
  ⟨row.indices, row.indices_size⟩

@[simp] theorem indexVector_get {m : ℕ} (row : CountedRow m) (r : Fin m) :
    row.indexVector[r] = row.order r := rfl

theorem indexVector_injective {m : ℕ} (row : CountedRow m) :
    Function.Injective (fun r : Fin m => row.indexVector[r]) := by
  simpa only [indexVector_get] using row.order.injective

end CountedRow

/-- The direct pointer-lifting input; each inner vector reuses its sorted array. -/
def indexRows {n m : ℕ} (rows : Vector (CountedRow m) n) : Vector (Vector (Fin m) m) n :=
  rows.map CountedRow.indexVector

@[simp] theorem indexRows_get {n m : ℕ} (rows : Vector (CountedRow m) n)
    (i : Fin n) (r : Fin m) : (indexRows rows)[i][r] = rows[i].order r := by
  simp [indexRows, CountedRow.indexVector]

theorem indexRows_injective {n m : ℕ} (rows : Vector (CountedRow m) n) (i : Fin n) :
    Function.Injective (fun r : Fin m => (indexRows rows)[i][r]) := by
  simpa only [indexRows_get] using rows[i].order.injective

theorem countedSortRows_monotone {n m : ℕ} (cost : Fin n → Fin m → ℚ) (i : Fin n) :
    Monotone (fun r : Fin m => cost i ((indexRows (countedSortRows cost))[i][r])) := by
  simpa [indexRows, countedSortRows, sortOrder, CountedRow.indexVector] using monotone_sortOrder (cost i)

@[simp] theorem countedSortRow_descending_size {m : ℕ} (cost : Fin m → ℚ) :
    (countedSortRow cost).descending.size = m := by simp [countedSortRow]

/-- The descending cache is built by one counted reversal of the ascending row. -/
theorem countedSortRow_descending_get {m : ℕ} (cost : Fin m → ℚ) (r : Fin m) :
    (countedSortRow cost).descending[r.val]'(by
      rw [countedSortRow_descending_size]; exact r.isLt) = cost (Tuple.sort cost r.rev) := by
  have h := countedSortRow_get cost r.rev
  simpa [countedSortRow, List.getElem_reverse, Fin.rev, Nat.sub_sub, Nat.add_comm] using h


/-- The split meter counts precisely three charged operations for each cell
traversed and one terminal operation. -/
theorem split_operations_eq (k : ℕ) (xs : List α) :
    (split k xs).operations = 3 * min k xs.length + 1 := by
  induction k generalizing xs with
  | zero => simp [split]
  | succ k ih =>
      cases xs with
      | nil => simp [split]
      | cons a xs => simp [split, ih]; omega

/-- Each evaluated comparison takes one nonterminal merge branch with charge
five; the terminal branch has charge one. -/
theorem merge_operations_eq (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).operations = 5 * (merge le xs ys).comparisons + 1 := by
  induction xs, ys using merge.induct le with
  | case1 ys => simp [merge]
  | case2 a xs => simp [merge]
  | case3 a xs b ys h ih => simp only [merge, if_pos h]; omega
  | case4 a xs b ys h ih => simp only [merge, if_neg h]; omega

/-- The customary `n*m*log m` form holds from `m = 2` onward, as required for
an asymptotic bound; the previous theorem also covers singleton rows. -/
theorem countedSortRows_operations_log_bound {n m : ℕ} (hm : 2 ≤ m)
    (cost : Fin n → Fin m → ℚ) :
    rowsOperations (countedSortRows cost) ≤ 100 * n * m * Nat.log2 m := by
  have h := countedSortRows_operations_le (by omega : 0 < m) cost
  have hl : 1 ≤ Nat.log2 m := (Nat.le_log2 (by omega)).mpr (by simpa using hm)
  have hmul := Nat.mul_le_mul_left (50 * n * m) hl
  nlinarith

/-- Total preprocessing remains defined, including empty input rows. -/
theorem countedSortRow_operations_le_all {m : ℕ} (cost : Fin m → ℚ) :
    (countedSortRow cost).operations ≤ 44 * (m + 1) * (Nat.log2 m + 1) := by
  cases m with
  | zero => simp [countedSortRow, sortIndices, sort, sortFuel]
  | succ m =>
      have h := countedSortRow_operations_le (by omega : 0 < m + 1) cost
      nlinarith

end ExactHillShares.MergeSorting
