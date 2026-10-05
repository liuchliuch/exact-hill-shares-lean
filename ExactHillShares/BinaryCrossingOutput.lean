import ExactHillShares.BinaryCrossing

/-!
# Output-only binary crossing

This production path computes only fuel and the returned boundary. Queries and
operation counters occur solely in the separate charged implementation and the
equivalence theorems; no counter arithmetic runs when these functions are used.
-/
namespace ExactHillShares.Algorithm

/-- Actual divide-by-two fuel computation, retaining only the needed fuel. -/
def binaryFuelOnly (k : ℕ) : ℕ :=
  if h : 2 ≤ k then binaryFuelOnly (k / 2) + 1 else 1
termination_by k
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem binaryFuelOnly_eq (k : ℕ) : binaryFuelOnly k = (binaryFuel k).1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [binaryFuelOnly, binaryFuel]
    split_ifs with hk
    · simp only [ih (k / 2) (Nat.div_lt_self (by omega) (by omega))]
    · rfl

/-- The same midpoint decisions, without constructing result records/counters. -/
def binaryLoopOnly (safe : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := lo + (hi - lo) / 2
      if safe mid then binaryLoopOnly safe fuel mid hi
      else binaryLoopOnly safe fuel lo mid

@[simp] theorem binaryLoopOnly_eq (safe : ℕ → Bool) (fuel lo hi : ℕ) :
    binaryLoopOnly safe fuel lo hi = (binaryLoop safe fuel lo hi).boundary := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [binaryLoopOnly, binaryLoop]
    split_ifs <;> simp only [ih]

def binarySearchOnly (safe : ℕ → Bool) (k : ℕ) : ℕ :=
  binaryLoopOnly safe (binaryFuelOnly k) 0 k

@[simp] theorem binarySearchOnly_eq (safe : ℕ → Bool) (k : ℕ) :
    binarySearchOnly safe k = (binarySearch safe k).boundary := by
  simp only [binarySearchOnly, binaryLoopOnly_eq, binaryFuelOnly_eq, binarySearch]

def binaryPrefixOnly (cache : Array ℚ) (l k : ℕ) (B : ℚ) : ℕ :=
  binarySearchOnly (fun s => decide (cachedMass cache l s ≤ B)) k

@[simp] theorem binaryPrefixOnly_eq (cache : Array ℚ) (l k : ℕ) (B : ℚ) :
    binaryPrefixOnly cache l k B = (binaryPrefix cache l k B).boundary := by
  exact binarySearchOnly_eq _ k

/-- Production safe-prefix search: one full-range test followed, if necessary,
by the output-only midpoint recursion on the previously built prefix array. -/
def binarySafePrefixOnly (cache : Array ℚ) (l k : ℕ) (B : ℚ) : ℕ :=
  if cachedMass cache l k ≤ B then k else binaryPrefixOnly cache l k B

@[simp] theorem binarySafePrefixOnly_eq (cache : Array ℚ) (l k : ℕ) (B : ℚ) :
    binarySafePrefixOnly cache l k B = (binarySafePrefix cache l k B).boundary := by
  simp only [binarySafePrefixOnly, binarySafePrefix]
  split_ifs <;> simp only [binaryPrefixOnly_eq]

end ExactHillShares.Algorithm
