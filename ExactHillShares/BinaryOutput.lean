import ExactHillShares.BinaryRecursion
import ExactHillShares.PrefixCacheOutput
import ExactHillShares.BinaryCrossingOutput

/-!
# Output-only execution, separate from cost analysis

The actual allocator in this module never evaluates the operation-analysis
functions. In particular, the concrete terminal runs once and `terminalOps`
is absent from the executable path. Every stage has an output-only version,
proved equal to the analyzed specification, so this separation does not depend
on compiler optimization or laziness. The arithmetic bounds in BinaryRecursion
are structural charges for this program; computing those analysis functions is
not claimed to have the same complexity as executing the allocator.
-/
namespace ExactHillShares.Algorithm

/-- Linear maximum selection with no execution counters. -/
def bestBoundaryOnly {α : Type*} : List (α × ℕ) → Option (α × ℕ)
  | [] => none
  | a :: as =>
    match bestBoundaryOnly as with
    | none => some a
    | some b => some (if a.2 ≤ b.2 then b else a)

theorem bestBoundaryOnly_eq {α : Type*} (as : List (α × ℕ)) :
    bestBoundaryOnly as = (bestBoundary as).value := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [bestBoundaryOnly, ih, bestBoundary]
    cases (bestBoundary as).value <;> rfl

/-- One row's executable boundary, with cached total and fixed-size exact Hill
formula. No operation/query annotation is evaluated. -/
def cachedRowBoundaryOnly (rows caches : Array (Array ℚ)) (q l k : ℕ)
    (i : Fin rows.size) : ℕ :=
  let table := cacheRow caches i.val
  let total := cachedMass table l k
  let budget := bound q total (matrixCosts rows i l)
  binarySafePrefixOnly table l k budget

theorem cachedRowBoundaryOnly_eq (rows caches : Array (Array ℚ)) (q l k : ℕ)
    (i : Fin rows.size) :
    cachedRowBoundaryOnly rows caches q l k i = (cachedRowBoundary rows caches q l k i).boundary := by
  exact binarySafePrefixOnly_eq _ _ _ _

/-- Materialize each boundary once, then linearly choose a maximum. This map
stores only agent identifiers and natural boundaries, never counters. -/
def cachedKnifeOnly (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) : Option (Fin rows.size × ℕ) :=
  let q := active.agents.length
  let values := active.agents.map (fun i => (i, cachedRowBoundaryOnly rows caches q l k i))
  bestBoundaryOnly values

theorem cachedKnifeOnly_eq (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) :
    cachedKnifeOnly rows caches active l k = cachedKnife rows caches active l k := by
  simp only [cachedKnifeOnly, bestBoundaryOnly_eq, cachedRowBoundaryOnly_eq,
    cachedKnife, cachedKnifeCounted, batchBest, computeBoundaryBatch_values]

/-- Output-only binary recursion. The two-agent branch evaluates `terminal`,
with no call to its cost-analysis function and no counter record construction. -/
def runCachedBinaryOnly (rows caches : Array (Array ℚ)) :
    ℕ → ActiveRows rows.size → ℕ → ℕ → Option (Allocation rows.size)
  | 0, _, _, k => if k = 0 then some (fun _ => none) else none
  | fuel + 1, active, l, k =>
    let A := active.finset
    let q := A.card
    if k = 0 then some (fun _ => none)
    else if hA : A.Nonempty then
      if q = 1 then some (whole (A.min' hA) l k)
      else match cachedEarly rows caches A l k with
        | some a => some (whole a l k)
        | none => if q = 2 then terminal (matrixCosts rows) A l k
          else match cachedKnifeOnly rows caches active l k with
            | none => none
            | some (a, s) =>
              (runCachedBinaryOnly rows caches fuel (active.erase a) (l + s) (k - s)).map
                (splice a l s)
    else none

/-- Branch-for-branch correspondence to the already verified cost model. -/
theorem runCachedBinaryOnly_eq (rows caches : Array (Array ℚ))
    (fuel : ℕ) (active : ActiveRows rows.size) (l k : ℕ) :
    runCachedBinaryOnly rows caches fuel active l k =
      (runCachedBinary rows caches fuel active l k).output := by
  induction fuel generalizing active l k with
  | zero => rfl
  | succ fuel ih =>
    simp only [runCachedBinaryOnly, runCachedBinary, cachedEarlyCounted,
      cachedKnifeOnly_eq, cachedKnife]
    split_ifs <;> try rfl
    all_goals split <;> try rfl
    all_goals split <;> try rfl
    all_goals simp_all [ih]

/-- Build the prefix tables once using an output-only builder, then allocate. -/
def allocateBinaryArrayOnly (rows : Array (Array ℚ)) (m : ℕ) : Option (Allocation rows.size) :=
  let caches := prefixRowsOnly rows
  runCachedBinaryOnly rows caches rows.size (ActiveRows.all rows.size) 0 m

theorem allocateBinaryArrayOnly_eq (rows : Array (Array ℚ)) (m : ℕ) :
    allocateBinaryArrayOnly rows m = (allocateBinaryArray rows m).output := by
  simp only [allocateBinaryArrayOnly, prefixRowsOnly_eq, runCachedBinaryOnly_eq,
    allocateBinaryArray, prefixRows]

/-- The output-only Vector API used by the actual original-item allocator. -/
def allocateBinaryRowsOnly {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) : Option (Allocation n) :=
  rows.size_toArray ▸ allocateBinaryArrayOnly rows.toArray m

theorem allocateBinaryRowsOnly_eq {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) :
    allocateBinaryRowsOnly rows m = allocateBinaryRows rows m := by
  cases rows with
  | mk data hs =>
    cases hs
    exact allocateBinaryArrayOnly_eq data m

/-- Full correctness of the actual output-only executable. Cost analysis is
not run in order to return this allocation. -/
theorem allocateBinaryRowsOnly_correct {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ)
    (hn : 0 < n) (hrect : ∀ i, (rows.get i).size = m)
    (hc : ∀ i j, 0 ≤ vectorCosts rows i j) (ha : ∀ i, Antitone (vectorCosts rows i)) :
    ∃ out, allocateBinaryRowsOnly rows m = some out ∧
      Safe (vectorCosts rows) Finset.univ 0 m out := by
  rw [allocateBinaryRowsOnly_eq]
  exact allocateBinaryRows_correct rows m hn hrect hc ha

end ExactHillShares.Algorithm
