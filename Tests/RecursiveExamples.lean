import ExactHillShares.Terminal
import ExactHillShares.Runtime

open ExactHillShares.Algorithm

/-- Inspect the actual rational program's owners, using n as an out-of-range
sentinel if a malformed result ever leaves an item unassigned. -/
def owners {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ) : Option (List ℕ) :=
  (runWith terminal c n Finset.univ 0 m).map fun out =>
    (List.range m).map fun j => ((out j).map Fin.val).getD n

def row (xs : List ℚ) : ℕ → ℚ := fun j => xs[j]?.getD 0

-- Empty input, zero rows, and the single-positive early terminal.
#eval owners (n := 3) (fun _ => row []) 0
#eval owners (n := 3) (fun _ => row [0, 0, 0]) 3
#eval owners (n := 3) (fun _ => row [1, 0, 0]) 3

-- Large-maximum singleton shortcut: the literal DP width can be zero at 1/2.
#eval owners (n := 2) (fun _ => row [1/2, 1/4, 1/4]) 3

-- Low-maximum two-direction trimmed DP.
#eval owners (n := 2) (fun _ => row [1/5, 1/5, 1/5, 1/5, 1/5]) 5

-- Three-to-two recursion with heterogeneous rows.
#eval owners (n := 3) (fun i =>
  if i = 0 then row [1/4, 1/4, 1/8, 1/8, 1/8, 1/8]
  else if i = 1 then row [1/3, 1/6, 1/6, 1/6, 1/12, 1/12]
  else row [1/6, 1/6, 1/6, 1/6, 1/6, 1/6]) 6

-- Several moving-knife eliminations before the terminal call.
#eval owners (n := 5) (fun _ => row [1/10, 1/10, 1/10, 1/10, 1/10,
  1/10, 1/10, 1/10, 1/10, 1/10]) 10
