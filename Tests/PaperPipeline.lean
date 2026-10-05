import ExactHillShares.PaperRuntime

namespace ExactHillShares.Algorithm.PaperTests
open scoped BigOperators

/-- Validate the actual emitted original owners, every rational load, and both
full-operation estimates. No assumed successful result or expected matching is
substituted for execution. -/
def checkRun {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ) : IO Unit := do
  let analysis := allocatePaperCounted hn cost
  let actual := allocatePaper hn cost
  unless actual == analysis.output do
    throw (IO.userError "output-only pipeline disagrees with its structural analysis")
  let operations := analysis.operations
  match actual with
  | none => throw (IO.userError "paper pipeline unexpectedly returned none")
  | some owner =>
    for i in List.finRange n do
      let total := (List.finRange m).foldl (fun acc j => acc + cost i j) 0
      let maximum := (List.finRange m).foldl (fun acc j => max acc (cost i j)) 0
      let charge := (List.finRange m).foldl
        (fun acc j => acc + if PointerLift.read owner j = i then cost i j else 0) 0
      unless charge ≤ bound n total maximum do
        throw (IO.userError s!"unsafe original-item load for agent {i.val}")
    unless operations ≤ 6000 * (m + 1)^3 do
      throw (IO.userError "paper cubic operation estimate failed")
    unless operations ≤ 120 * n * m * (Nat.log2 (m + 1) + 1) +
        1000 * n^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 do
      throw (IO.userError "paper source-shaped operation estimate failed")

def equalFive : Fin 3 → Fin 5 → ℚ := fun _ _ => 1 / 5

def permutedSeven (i : Fin 3) (j : Fin 7) : ℚ :=
  if i = 0 then ![3/10, 2/10, 1/10, 1/10, 1/10, 1/10, 1/10] j
  else if i = 1 then ![1/10, 3/10, 1/10, 1/10, 2/10, 1/10, 1/10] j
  else ![0, 1/4, 0, 1/4, 1/4, 0, 1/4] j

def twoPermuted (i : Fin 2) (j : Fin 3) : ℚ :=
  if i = 0 then ![(1/2 : ℚ), 1/3, 1/6] j else ![(1/6 : ℚ), 1/2, 1/3] j

#eval show IO Unit from do
  checkRun (by decide : 0 < 3) equalFive
  checkRun (by decide : 0 < 3) permutedSeven
  checkRun (by decide : 0 < 2) twoPermuted
  checkRun (by decide : 0 < 4) (fun (_ : Fin 4) (_ : Fin 9) => (1/9 : ℚ))
  checkRun (by decide : 0 < 1) (fun (_ : Fin 1) (_ : Fin 4) => (1/4 : ℚ))
  checkRun (by decide : 0 < 3) (fun (_ : Fin 3) (_ : Fin 7) => (0 : ℚ))
  checkRun (by decide : 0 < 3) (fun (_ : Fin 3) (j : Fin 0) => Fin.elim0 j)

/- Large agent count, equality boundary and empty input do not evaluate any
cost cell. A panic is deliberately placed behind each unused row function. -/
#eval show IO Unit from do
  let many := allocatePaper (by decide : 0 < 10000)
    (fun (_ : Fin 10000) (_ : Fin 2) => panic! "singleton branch read a cost")
  unless many.map (fun a => a.toArray.map Fin.val) == some #[0, 1] do
    throw (IO.userError "incorrect singleton preprocessing")
  unless allocatePaperOps (by decide : 0 < 10000)
      (fun (_ : Fin 10000) (_ : Fin 2) => panic! "singleton counter read a cost") == 8 do
    throw (IO.userError "singleton preprocessing depends on agent count")
  let equal := allocatePaper (by decide : 0 < 4)
    (fun (_ : Fin 4) (_ : Fin 4) => panic! "equality singleton branch read a cost")
  unless equal.map (fun a => a.toArray.map Fin.val) == some #[0, 1, 2, 3] do
    throw (IO.userError "n=m did not select singleton preprocessing")
  let empty := allocatePaper (by decide : 0 < 2)
    (fun (_ : Fin 2) (j : Fin 0) => Fin.elim0 j)
  unless empty.map (fun a => a.toArray.map Fin.val) == some #[] do
    throw (IO.userError "empty original-item output is incorrect")
  unless allocatePaperOps (by decide : 0 < 2)
      (fun (_ : Fin 2) (j : Fin 0) => Fin.elim0 j) == 2 do
    throw (IO.userError "empty branch is not constant-work")

/- Exercise actual cached binary queries and exactly one concrete terminal. -/
#eval show IO Unit from do
  let sorted := MergeSorting.countedSortRows
    (fun (_ : Fin 4) (_ : Fin 9) => (1/9 : ℚ))
  let result := allocateBinaryRowsCounted (paperDescendingRows sorted) 9
  unless result.queries > 0 do
    throw (IO.userError "nontrivial run never performed binary queries")
  unless result.terminalCalls == 1 do
    throw (IO.userError "nontrivial chain must invoke the terminal exactly once")
  let zero := allocateBinaryRowsCounted
    (paperDescendingRows (MergeSorting.countedSortRows
      (fun (_ : Fin 3) (_ : Fin 7) => (0 : ℚ)))) 7
  unless zero.queries == 3 && zero.terminalCalls == 0 do
    throw (IO.userError "zero-total early branch did work beyond its three cached guard queries")

#eval (allocatePaper (by decide : 0 < 3) equalFive).map (fun v => v.toArray.map Fin.val)
#eval allocatePaperOps (by decide : 0 < 3) equalFive
#eval (allocatePaper (by decide : 0 < 3) permutedSeven).map (fun v => v.toArray.map Fin.val)
#eval allocatePaperOps (by decide : 0 < 3) permutedSeven

example : ∃ out, allocatePaper (by decide : 0 < 3) equalFive = some out ∧
    (∀ i, load (fun j => (equalFive i j : ℝ)) (PointerLift.read out) i ≤ hill 3 (1/5 : ℝ)) ∧
    allocatePaperOps (by decide : 0 < 3) equalFive ≤ 6000 * (5 + 1)^3 := by
  apply allocatePaper_hill_and_cubic (by decide) equalFive (fun _ => (1/5 : ℝ))
  intro i
  norm_num [IsNormalizedExact, equalFive]

#print axioms allocatePaper_eq_counted
#print axioms allocatePaper_hill_safe
#print axioms allocatePaperOps_source_bound
#print axioms allocatePaperOps_bound
#print axioms allocatePaperOps_cubic
#print axioms allocatePaper_hill_and_runtime
#print axioms allocatePaper_hill_and_cubic

end ExactHillShares.Algorithm.PaperTests
