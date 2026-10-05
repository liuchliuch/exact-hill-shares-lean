import ExactHillShares.BinaryOutput

namespace ExactHillShares.Algorithm.OutputTests

def finiteOwners {n : ℕ} (allocation : Option (Allocation n)) (m : ℕ) :
    Option (List (Option ℕ)) :=
  allocation.map fun out => (List.range m).map fun j => (out j).map Fin.val

-- Exercise the real output-only binary recursion, including multiple levels.
#eval show IO Unit from do
  let rows : Vector (Array ℚ) 4 :=
    Vector.ofFn fun _ => Array.replicate 9 (1 / 9 : ℚ)
  let actual := allocateBinaryRowsOnly rows 9
  let analyzed := allocateBinaryRows rows 9
  unless finiteOwners actual 11 == finiteOwners analyzed 11 do
    throw (IO.userError "output-only and analyzed recursion differ")
  unless finiteOwners actual 11 ==
      some [some 3, some 3, some 3, some 2, some 2, some 1, some 1, some 0, some 0, none, none] do
    throw (IO.userError "output-only multilevel allocation is incorrect")

-- Full-safe, empty, and single-agent paths do not invoke cost-analysis code.
#eval show IO Unit from do
  let zeroRows : Vector (Array ℚ) 3 := #v[#[0,0], #[0,0], #[0,0]]
  unless finiteOwners (allocateBinaryRowsOnly zeroRows 2) 3 == some [some 0, some 0, none] do
    throw (IO.userError "output-only zero-total branch failed")
  let emptyRows : Vector (Array ℚ) 2 := #v[#[], #[]]
  unless finiteOwners (allocateBinaryRowsOnly emptyRows 0) 2 == some [none, none] do
    throw (IO.userError "output-only empty branch failed")
  let oneRow : Vector (Array ℚ) 1 := #v[#[3,2,1]]
  unless finiteOwners (allocateBinaryRowsOnly oneRow 3) 4 == some [some 0, some 0, some 0, none] do
    throw (IO.userError "output-only single-agent branch failed")

#print axioms allocateBinaryRowsOnly_eq
#print axioms allocateBinaryRowsOnly_correct

end ExactHillShares.Algorithm.OutputTests
