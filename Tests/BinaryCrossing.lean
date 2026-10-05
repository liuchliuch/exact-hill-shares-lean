import ExactHillShares.BinaryRecursion

namespace ExactHillShares.Algorithm.BinaryTests

-- Compiled execution assertions test opaque rational operations without adding
-- native-decision axioms to any correctness theorem.
#eval show IO Unit from do
  let cache := prefixCache #[3, 2, 0, 2]
  -- Equality is safe, including a plateau of zero-cost entries.
  unless (binarySafePrefix cache 0 4 5).boundary == 3 do
    throw (IO.userError "strict crossing lost an equality plateau")
  -- A zero threshold still skips all initial zero entries.
  unless (binarySafePrefix (prefixCache #[0, 0, 2, 1]) 0 4 0).boundary == 2 do
    throw (IO.userError "zero budget failed to include initial zero costs")
  -- Exact total and empty inputs exercise the full-safe branch.
  unless (binarySafePrefix cache 0 4 7).boundary == 4 do
    throw (IO.userError "exact total did not include the entire row")
  unless (binarySafePrefix (prefixCache #[]) 0 0 0).boundary == 0 do
    throw (IO.userError "empty row returned a nonzero boundary")
  -- A proper suffix query and a relative strict crossing.
  unless cachedSuffix cache 4 1 == 4 do
    throw (IO.userError "incorrect cached suffix sum")
  unless (binarySafePrefix cache 1 3 2).boundary == 2 do
    throw (IO.userError "incorrect relative suffix crossing")
  -- The actual program computes the fuel and charges its construction.
  unless binaryFuel 1024 == (11, 42) do
    throw (IO.userError "incorrect logarithmic fuel or construction charge")
  unless prefixRowsWork #[#[3, 2, 0, 2], #[1, 1, 1, 1]] == 38 do
    throw (IO.userError "incorrect integrated prefix preprocessing charge")
  -- Every boundary is stored once before maximum selection.
  let chosen := batchBest (fun i : ℕ => binarySafePrefix cache 0 4 (i : ℚ)) [2, 5, 4]
  unless chosen.1.value == some (5, 3) do
    throw (IO.userError "stored-score maximum chose the wrong boundary")

/-- Three sorted normalized rows exercise the actual cached moving knife. -/
def equalFourRows : Array (Array ℚ) :=
  #[#[(1/4 : ℚ), 1/4, 1/4, 1/4],
    #[(1/4 : ℚ), 1/4, 1/4, 1/4],
    #[(1/4 : ℚ), 1/4, 1/4, 1/4]]

#eval show IO Unit from do
  let tables := prefixRows equalFourRows
  let active := ActiveRows.all equalFourRows.size
  let earlyResult := cachedEarlyCounted equalFourRows tables active.finset 0 4
  unless earlyResult.1 == none do
    throw (IO.userError "equal positive rows incorrectly took an early branch")
  let knifeResult := cachedKnifeCounted equalFourRows tables active 0 4
  unless knifeResult.1.value.map (fun p => (p.1.val, p.2)) == some (2, 2) do
    throw (IO.userError "materialized binary knife chose the wrong safe boundary")
  unless knifeResult.1.operations ≤ 100 * 3 * (Nat.log2 (4 + 1) + 1) do
    throw (IO.userError "binary knife exceeded its proved logarithmic bound")
  unless knifeResult.2 ≤ 3 * (Nat.log2 (4 + 1) + 3) do
    throw (IO.userError "binary knife exceeded its logarithmic query bound")
  let remaining := active.erase ⟨2, by decide⟩
  unless remaining.agents.map Fin.val == [0, 1] do
    throw (IO.userError "active-list erase changed another agent")

-- A zero row and a single-positive row are guarded before any binary search.
#eval show IO Unit from do
  let rows : Array (Array ℚ) := #[#[0, 0, 0], #[1, 0, 0], #[1/2, 1/4, 1/4]]
  let tables := prefixRows rows
  let active := ActiveRows.all rows.size
  unless (cachedEarly rows tables active.finset 0 3).map Fin.val == some 0 do
    throw (IO.userError "zero-total guard failed")
  unless (cachedEarly rows tables (active.erase ⟨0, by decide⟩).finset 0 3).map Fin.val == some 1 do
    throw (IO.userError "single-positive guard failed")

/-- The full concrete recursion performs a binary knife step and then invokes
its proved two-agent terminal exactly once. -/
def equalFourVector : Vector (Array ℚ) 3 :=
  #v[#[(1/4 : ℚ), 1/4, 1/4, 1/4],
    #[(1/4 : ℚ), 1/4, 1/4, 1/4],
    #[(1/4 : ℚ), 1/4, 1/4, 1/4]]

def owners {n : ℕ} (result : BinaryRunResult n) (limit : ℕ) :
    Option (List (Option ℕ)) :=
  result.output.map fun allocation => (List.range limit).map fun j =>
    (allocation j).map Fin.val

#eval show IO Unit from do
  let result := allocateBinaryRowsCounted equalFourVector 4
  unless owners result 6 == some [some 2, some 2, some 1, some 0, none, none] do
    throw (IO.userError "full binary recursion returned incorrect owners or escaped its range")
  unless result.terminalCalls == 1 do
    throw (IO.userError "full binary recursion did not invoke exactly one concrete terminal")
  unless result.operations ≤
      1000 * 3^2 * (Nat.log2 (4 + 1) + 1) + 3000 * (4 + 1)^3 + 4 * 3 * (4 + 1) do
    throw (IO.userError "full binary recursion exceeded its proved operation bound")
  unless result.queries == 17 do
    throw (IO.userError "full binary recursion lost its branch-following range-query charge")

-- All early exits use the same counted executable as the nontrivial branch.
#eval show IO Unit from do
  let zeroRows : Vector (Array ℚ) 3 := #v[#[0, 0], #[0, 0], #[0, 0]]
  let zeroResult := allocateBinaryRowsCounted zeroRows 2
  unless owners zeroResult 3 == some [some 0, some 0, none] do
    throw (IO.userError "zero-total recursion produced an incorrect whole assignment")
  unless zeroResult.terminalCalls == 0 do
    throw (IO.userError "zero-total recursion unnecessarily invoked the terminal")
  let emptyRows : Vector (Array ℚ) 2 := #v[#[], #[]]
  let emptyResult := allocateBinaryRowsCounted emptyRows 0
  unless owners emptyResult 2 == some [none, none] do
    throw (IO.userError "empty-item recursion produced an owner")
  unless emptyResult.queries == 0 && emptyResult.terminalCalls == 0 do
    throw (IO.userError "empty-item recursion performed unnecessary search")
  let oneRow : Vector (Array ℚ) 1 := #v[#[3, 2, 1]]
  let oneResult := allocateBinaryRowsCounted oneRow 3
  unless owners oneResult 4 == some [some 0, some 0, some 0, none] do
    throw (IO.userError "single-agent recursion produced an incorrect whole assignment")
  unless oneResult.queries == 0 && oneResult.terminalCalls == 0 do
    throw (IO.userError "single-agent recursion performed unnecessary search")

example : PrefixRowsValid equalFourRows (prefixRows equalFourRows) :=
  prefixRows_valid equalFourRows

#print axioms cachedMass_prefixCache_eq_mass
#print axioms cachedKnife_spec
#print axioms cachedLevelOps_le
#print axioms allocateBinaryRows_correct
#print axioms allocateBinaryRowsOps_bound

end ExactHillShares.Algorithm.BinaryTests
