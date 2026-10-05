import ExactHillShares.PrefixCache

/-!
# Output-only finite prefix preprocessing

These executable functions construct only arrays. They neither construct nor
evaluate analysis counters. The equality theorems identify their outputs with
the independently charged implementation, so its correctness and linear work
analysis apply without putting cost-model arithmetic in the production path.
-/
namespace ExactHillShares.Algorithm

/-- Append one prefix sum, with no execution-counter computation. -/
def buildPrefixLoopOnly (row : Array ℚ) : ℕ → Array ℚ
  | 0 => #[0]
  | k + 1 =>
    let prior := buildPrefixLoopOnly row k
    prior.push (rowAt prior k + rowAt row k)

def prefixCacheOnly (row : Array ℚ) : Array ℚ :=
  buildPrefixLoopOnly row row.size

@[simp] theorem buildPrefixLoopOnly_eq (row : Array ℚ) (k : ℕ) :
    buildPrefixLoopOnly row k = (buildPrefixLoop row k).1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [buildPrefixLoopOnly, buildPrefixLoop, ih]

@[simp] theorem prefixCacheOnly_eq (row : Array ℚ) :
    prefixCacheOnly row = prefixCache row := by
  exact buildPrefixLoopOnly_eq row row.size

/-- Actual outer-array construction, also free of analysis counters. -/
def buildPrefixRowsLoopOnly (rows : Array (Array ℚ)) : ℕ → Array (Array ℚ)
  | 0 => #[]
  | n + 1 =>
    let prior := buildPrefixRowsLoopOnly rows n
    let row := rows[n]?.getD #[]
    prior.push (prefixCacheOnly row)

def prefixRowsOnly (rows : Array (Array ℚ)) : Array (Array ℚ) :=
  buildPrefixRowsLoopOnly rows rows.size

@[simp] theorem buildPrefixRowsLoopOnly_eq (rows : Array (Array ℚ)) (n : ℕ) :
    buildPrefixRowsLoopOnly rows n = (buildPrefixRowsLoop rows n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [buildPrefixRowsLoopOnly, buildPrefixRowsLoop, ih,
      prefixCacheOnly_eq, prefixCache]

@[simp] theorem prefixRowsOnly_eq (rows : Array (Array ℚ)) :
    prefixRowsOnly rows = prefixRows rows := by
  exact buildPrefixRowsLoopOnly_eq rows rows.size

end ExactHillShares.Algorithm
