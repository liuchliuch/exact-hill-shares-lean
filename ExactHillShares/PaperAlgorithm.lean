import ExactHillShares.BinaryOutput
import ExactHillShares.Runtime
import ExactHillShares.PointerLiftSorting
import ExactHillShares.SortedRowProperties

/-!
# The paper-style executable original-item pipeline

The input is exact rational array data. The singleton branch never evaluates a
cost entry. Otherwise the counted merge sort is bound once; both prefix sums
and moving-pointer lifting reuse its stored rows. Recursive rank owners are
materialized once before the pointer pass.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- Project the already stored decreasing rows. Only the outer vector is built;
its inner arrays are shared with the sorting cache and the pointer lift. -/
def paperDescendingRows {n m : ℕ} (cached : Vector (MergeSorting.CountedRow m) n) :
    Vector (Array ℚ) n := cached.map (fun row => row.descending)

@[simp] theorem paperDescendingRows_get {n m : ℕ}
    (cached : Vector (MergeSorting.CountedRow m) n) (i : Fin n) :
    (paperDescendingRows cached)[i] = cached[i].descending := by
  simp [paperDescendingRows]

@[simp] theorem paperDescendingRows_size {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (i : Fin n) :
    (paperDescendingRows (MergeSorting.countedSortRows cost))[i].size = m := by
  simp [paperDescendingRows, MergeSorting.countedSortRows]

/-- The actual array lookup agrees with the established decreasing-row
semantics, including its zero tail. No sorting premise is assumed. -/
theorem paperDescendingRows_rowAt {n m : ℕ} (cost : Fin n → Fin m → ℚ) :
    (fun i r => rowAt (paperDescendingRows (MergeSorting.countedSortRows cost))[i] r) =
      originalRows cost := by
  funext i r
  by_cases hr : r < m
  · have hsize : r < (paperDescendingRows (MergeSorting.countedSortRows cost))[i].size := by
      simpa [paperDescendingRows, MergeSorting.countedSortRows] using hr
    rw [rowAt_of_lt _ r hsize]
    simpa [paperDescendingRows, MergeSorting.countedSortRows, originalRows, hr, rationalDescendingCost, rationalSortedCost] using
      MergeSorting.countedSortRow_descending_get (cost i) ⟨r, hr⟩
  · rw [rowAt_of_size_le _ r (by simpa [paperDescendingRows, MergeSorting.countedSortRows] using Nat.le_of_not_gt hr)]
    simp [originalRows, hr]

/-- Convert an ordered Safe certificate to the genuine supremum-defined share.
The formula is used only via the proved exact Hill-formula identity. -/
theorem safe_originalRows_hill {n m : ℕ} (hn : 2 ≤ n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j)
    (hnorm : ∀ i, ∑ j, cost i j = 1) (out : Allocation n)
    (hs : Safe (originalRows cost) Finset.univ 0 m out) :
    ∀ i, (charge (originalRows cost) 0 m out i : ℝ) ≤
      hill n (originalRows cost i 0 : ℝ) := by
  intro i
  have hnorm' : mass (originalRows cost i) 0 m = 1 :=
    (originalRows_mass cost i).trans (hnorm i)
  have hpos : (0 : ℚ) < mass (originalRows cost i) 0 m := by rw [hnorm']; norm_num
  have hp := head_pos (originalRows cost i) 0 m (originalRows_antitone cost hc i) hpos
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    simp [hm0] at hnorm'
  have hpT := head_le_mass (originalRows cost i) 0 m (originalRows_nonneg cost hc i) hm
  have hp1 : (originalRows cost i 0 : ℝ) ≤ 1 := by
    rw [hnorm'] at hpT
    exact_mod_cast hpT
  have hb := hs.2 i (Finset.mem_univ i)
  have hbR : (charge (originalRows cost) 0 m out i : ℝ) ≤
      (bound n (mass (originalRows cost i) 0 m) (originalRows cost i 0) : ℝ) := by
    exact_mod_cast (show charge (originalRows cost) 0 m out i ≤
      bound n (mass (originalRows cost i) 0 m) (originalRows cost i 0) by simpa using hb)
  rw [cast_bound hn (ne_of_gt hpos), hnorm'] at hbR
  norm_num only [Rat.cast_one] at hbR
  rw [← hill_eq_numericalBound hn (by exact_mod_cast hp) hp1] at hbR
  exact hbR

/-- One stored original-item owner vector, paired with its structural charge. -/
structure PaperLiftResult (n m : ℕ) where
  output : Vector (Fin n) m
  operations : ℕ

/-- Materialize every implicit recursive rank owner once, then execute the
moving-pointer pass against the already sorted original-index arrays. -/
def paperLiftCounted {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ)
    (cached : Vector (MergeSorting.CountedRow m) n)
    (hcached : cached = MergeSorting.countedSortRows cost) (out : Allocation n) :
    PaperLiftResult n m :=
  let ranks := Vector.ofFn (rankOwners hn out : Fin m → Fin n)
  let lifted := PointerLift.executeCachedSorted cost cached hcached (fun r => PointerLift.read ranks r.rev)
  ⟨PointerLift.sortedAllocation lifted,
    materializationOps n m + PointerLift.afterSortingOperations lifted⟩

/-- The complete cached pointer pass cannot increase any agent's decreasing
rank charge. Rank-owner validity is proved by the ordered algorithm. -/
theorem paperLiftCounted_safe {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ)
    (cached : Vector (MergeSorting.CountedRow m) n)
    (hcached : cached = MergeSorting.countedSortRows cost) (out : Allocation n)
    (hv : Valid Finset.univ 0 m out) (i : Fin n) :
    (∑ j, if PointerLift.read (paperLiftCounted hn cost cached hcached out).output j = i
      then cost i j else 0) ≤ charge (originalRows cost) 0 m out i := by
  have hl := PointerLift.lemma3_1_cached cost cached hcached (rankOwners hn out) i
  rw [rankOwners_charge hn cost out hv i] at hl
  have heq : (fun r : Fin m => PointerLift.read (Vector.ofFn
      (rankOwners hn out : Fin m → Fin n)) r.rev) = (fun r => rankOwners hn out r.rev) := by
    funext r
    exact PointerLift.read_ofFn _ _
  unfold paperLiftCounted
  dsimp only
  rw [heq]
  exact hl

/-- An instrumented analysis result. Counter evaluation is not part of the
output-only program whose arithmetic work is modeled. -/
structure PaperResult (n m : ℕ) where
  output : Option (Vector (Fin n) m)
  operations : ℕ

/-- Instrumented analysis of the original-item pipeline. This helper evaluates
structural counters and is not itself claimed to execute within their value.
The public output-only program below never evaluates this record. -/
def allocatePaperCounted {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ) :
    PaperResult n m :=
  if h : m ≤ n then ⟨some (Vector.ofFn (singletonAllocation h)), 3 * m + 2⟩
  else
    let cached := MergeSorting.countedSortRows cost
    let rows := paperDescendingRows cached
    let ranked := allocateBinaryRowsCounted rows m
    let preliminary := MergeSorting.rowsOperations cached + 3 * n + 4 + ranked.operations
    match ranked.output with
    | none => ⟨none, preliminary⟩
    | some out =>
      let lifted := paperLiftCounted hn cost cached rfl out
      ⟨some lifted.output, preliminary + lifted.operations⟩

/-- Actual rank materialization and pointer output, without evaluating an
analysis counter or an operation-record projection. -/
def paperLift {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ)
    (cached : Vector (MergeSorting.CountedRow m) n)
    (hcached : cached = MergeSorting.countedSortRows cost) (out : Allocation n) :
    Vector (Fin n) m :=
  let ranks := Vector.ofFn (rankOwners hn out : Fin m → Fin n)
  PointerLift.sortedAllocation
    (PointerLift.executeCachedSorted cost cached hcached (fun r => PointerLift.read ranks r.rev))

theorem paperLift_eq_counted {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ)
    (cached : Vector (MergeSorting.CountedRow m) n)
    (hcached : cached = MergeSorting.countedSortRows cost) (out : Allocation n) :
    paperLift hn cost cached hcached out =
      (paperLiftCounted hn cost cached hcached out).output := rfl

/-- The actual output-only original-item program. The singleton branch comes
before every cost read. Otherwise the merge-sort cache is bound once and reused
for prefix construction/binary recursion and pointer lifting. This definition
never calls a terminal-work counter or the instrumented analysis program. -/
def allocatePaper {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ) :
    Option (Vector (Fin n) m) :=
  if h : m ≤ n then some (Vector.ofFn (singletonAllocation h))
  else
    let cached := MergeSorting.countedSortRows cost
    let rows := paperDescendingRows cached
    (allocateBinaryRowsOnly rows m).map (paperLift hn cost cached rfl)

/-- Output equivalence is proved rather than relying on a compiler to remove
strictly evaluated work counters from the public algorithm. -/
theorem allocatePaper_eq_counted {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ) :
    allocatePaper hn cost = (allocatePaperCounted hn cost).output := by
  unfold allocatePaper allocatePaperCounted
  split_ifs with hmn
  · rfl
  · dsimp only
    rw [allocateBinaryRowsOnly_eq]
    unfold allocateBinaryRows
    cases (allocateBinaryRowsCounted (paperDescendingRows (MergeSorting.countedSortRows cost)) m).output
    · rfl
    · exact congrArg some (paperLift_eq_counted hn cost _ rfl _)

/-- Structural arithmetic cost assigned to the uninstrumented `allocatePaper`.
Computing this analysis value can itself do additional work; evaluating it is
not part of the public output-only allocation algorithm. -/
def allocatePaperOps {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ) : ℕ :=
  (allocatePaperCounted hn cost).operations

@[simp] theorem vectorCosts_paperDescendingRows {n m : ℕ} (cost : Fin n → Fin m → ℚ) :
    vectorCosts (paperDescendingRows (MergeSorting.countedSortRows cost)) =
      originalRows cost := by
  exact paperDescendingRows_rowAt cost

/-- The nontrivial pipeline always returns an allocation, with the original
row's exact rational formula bound. No run-success or sorting premise occurs. -/
theorem allocatePaper_nontrivial_correct {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j) (hmn : ¬ m ≤ n) :
    ∃ out, allocatePaper hn cost = some out ∧ ∀ i,
      (∑ j, if PointerLift.read out j = i then cost i j else 0) ≤
        bound n (∑ j, cost i j) (originalRows cost i 0) := by
  obtain ⟨ranked, hranked, hs⟩ := allocateBinaryRows_correct
    (paperDescendingRows (MergeSorting.countedSortRows cost)) m hn
    (fun i => by simpa [Vector.get] using paperDescendingRows_size cost i)
    (by simpa only [vectorCosts_paperDescendingRows] using originalRows_nonneg cost hc)
    (by simpa only [vectorCosts_paperDescendingRows] using originalRows_antitone cost hc)
  rw [vectorCosts_paperDescendingRows] at hs
  refine ⟨(paperLiftCounted hn cost _ rfl ranked).output, ?_, fun i => ?_⟩
  · unfold allocateBinaryRows at hranked
    rw [allocatePaper_eq_counted]
    simp only [allocatePaperCounted, dif_neg hmn, hranked]
  · have hl := paperLiftCounted_safe hn cost _ rfl ranked hs.1 i
    have hb := hs.2 i (Finset.mem_univ i)
    rw [Finset.card_univ, Fintype.card_fin, originalRows_mass] at hb
    exact hl.trans hb

/-- End-to-end genuine Hill guarantee for the executed original-item program.
Sorting, binary-search crossing, successful recursion, terminal feasibility and
pointer matching are all established by the implementation's own theorems. -/
theorem allocatePaper_hill_correct {n m : ℕ} (hn : 2 ≤ n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j)
    (hnorm : ∀ i, ∑ j, cost i j = 1) :
    ∃ out, allocatePaper (by omega) cost = some out ∧ ∀ i,
      load (fun j => (cost i j : ℝ)) (PointerLift.read out) i ≤
        hill n (originalRows cost i 0 : ℝ) := by
  by_cases hmn : m ≤ n
  · refine ⟨Vector.ofFn (singletonAllocation hmn), ?_, ?_⟩
    · simp [allocatePaper, allocatePaperCounted, hmn]
    · have heq : PointerLift.read (Vector.ofFn (singletonAllocation hmn)) =
          singletonAllocation hmn := by funext j; exact PointerLift.read_ofFn _ _
      rw [heq]
      exact singletonAllocation_hill_safe hmn (by omega)
        (fun i j => (cost i j : ℝ)) (fun i => (originalRows cost i 0 : ℝ))
        (originalRows_isNormalizedExact cost hc hnorm)
  · obtain ⟨ranked, hranked, hs⟩ := allocateBinaryRows_correct
      (paperDescendingRows (MergeSorting.countedSortRows cost)) m (by omega)
      (fun i => by simpa [Vector.get] using paperDescendingRows_size cost i)
      (by simpa only [vectorCosts_paperDescendingRows] using originalRows_nonneg cost hc)
      (by simpa only [vectorCosts_paperDescendingRows] using originalRows_antitone cost hc)
    rw [vectorCosts_paperDescendingRows] at hs
    refine ⟨(paperLiftCounted (by omega) cost _ rfl ranked).output, ?_, fun i => ?_⟩
    · unfold allocateBinaryRows at hranked
      rw [allocatePaper_eq_counted]
      simp only [allocatePaperCounted, dif_neg hmn, hranked]
    · have hl := paperLiftCounted_safe (by omega) cost _ rfl ranked hs.1 i
      have hlR : load (fun j => (cost i j : ℝ))
          (PointerLift.read (paperLiftCounted (by omega) cost _ rfl ranked).output) i ≤
            (charge (originalRows cost) 0 m ranked i : ℝ) := by
        simpa only [load, Rat.cast_sum, apply_ite, Rat.cast_zero] using
          (Rat.cast_le (K := ℝ)).mpr hl
      exact hlR.trans (safe_originalRows_hill hn cost hc hnorm ranked hs i)

/-- Public formulation against the specified exact maximum of each original
normalized row. The target `hill` is the supremum-defined share itself. -/
theorem allocatePaper_hill_safe {n m : ℕ} (hn : 2 ≤ n)
    (cost : Fin n → Fin m → ℚ) (α : Fin n → ℝ)
    (hv : ∀ i, IsNormalizedExact (fun j => (cost i j : ℝ)) (α i)) :
    ∃ out, allocatePaper (by omega) cost = some out ∧ ∀ i,
      load (fun j => (cost i j : ℝ)) (PointerLift.read out) i ≤ hill n (α i) := by
  have hc : ∀ i j, 0 ≤ cost i j := by
    intro i j
    have hh := ((hv i).1 j).1
    change (0 : ℝ) ≤ (cost i j : ℝ) at hh
    exact_mod_cast hh
  have hnorm : ∀ i, ∑ j, cost i j = 1 := by
    intro i
    have hh := (hv i).2.1
    change (∑ j, (cost i j : ℝ)) = 1 at hh
    exact_mod_cast hh
  have hs := originalRows_isNormalizedExact cost hc hnorm
  have hmax (i : Fin n) : (originalRows cost i 0 : ℝ) = α i := by
    obtain ⟨j, hj⟩ := (hs i).2.2
    obtain ⟨k, hk⟩ := (hv i).2.2
    exact le_antisymm (by rw [← hj]; exact ((hv i).1 j).2)
      (by rw [← hk]; exact ((hs i).1 k).2)
  obtain ⟨out, hout, houtbound⟩ := allocatePaper_hill_correct hn cost hc hnorm
  exact ⟨out, hout, fun i => by simpa [hmax i] using houtbound i⟩

end ExactHillShares.Algorithm
