import ExactHillShares.OrderedAlgorithm

open ExactHillShares ExactHillShares.Algorithm

namespace OrderedRegression

def halfQuarterQuarter : Fin 3 → ℕ → ℚ := fun _ r =>
  if r = 0 then 1 / 2 else if r = 1 ∨ r = 2 then 1 / 4 else 0

def runSummary {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ) : Option (List (Option ℕ)) :=
  (allocateOrdered c m).map (fun out => (List.range m).map (fun r => (out r).map Fin.val))

-- Literal paper Algorithm 2 would reach zero trimming width in this case.
-- The corrected full recursion reaches the singleton shortcut and succeeds.
#eval runSummary halfQuarterQuarter 3

def zeroRows : Fin 3 → ℕ → ℚ := fun _ _ => 0
#eval runSummary zeroRows 4

def singlePositive : Fin 4 → ℕ → ℚ := fun _ r => if r = 0 then 1 else 0
#eval runSummary singlePositive 5

def equalSix : Fin 2 → ℕ → ℚ := fun _ r => if r < 6 then 1 / 6 else 0
#eval runSummary equalSix 6

def endpointThird : Fin 2 → ℕ → ℚ := fun _ r => if r < 3 then 1 / 3 else 0
#eval runSummary endpointThird 3

#eval runSummary zeroRows 0

end OrderedRegression
