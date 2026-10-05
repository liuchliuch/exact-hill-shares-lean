import ExactHillShares.RecursiveAllocation
import ExactHillShares.PrefixCache
import Mathlib.Data.Nat.Log

/-!
# First strict prefix crossing by binary search

The search evaluates its predicate only at midpoint positions. It returns the
safe boundary and execution counters together. Rational range sums will be
supplied by a materialized prefix-sum array, rather than recomputed by a scan.
The counters are unit-cost arithmetic/control counts, not bit-complexity claims.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- Execution result, with the actual number of midpoint queries and a charge
for the recursive control path. `operations` includes a constant-time cached
rational sum comparison at each query. -/
structure BinaryResult where
  boundary : ℕ
  queries : ℕ
  operations : ℕ
  deriving Repr, DecidableEq

/-- Maintain a safe lower and unsafe upper endpoint. Equality of a rational
prefix sum with its budget must be encoded as `true` by the predicate. -/
def binaryLoop (safe : ℕ → Bool) : ℕ → ℕ → ℕ → BinaryResult
  | 0, lo, _ => ⟨lo, 0, 2⟩
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then ⟨lo, 0, 2⟩
    else
      let mid := lo + (hi - lo) / 2
      let result := if safe mid then binaryLoop safe fuel mid hi
                    else binaryLoop safe fuel lo mid
      ⟨result.boundary, result.queries + 1, result.operations + 16⟩

/-- This bound follows the executed branches, counting one query per midpoint.
The zero fuel case is never reached with nonadjacent endpoints in a valid run. -/
theorem binaryLoop_counts (safe : ℕ → Bool) (fuel lo hi : ℕ) :
    (binaryLoop safe fuel lo hi).queries ≤ fuel ∧
    (binaryLoop safe fuel lo hi).operations ≤ 16 * fuel + 2 := by
  induction fuel generalizing lo hi with
  | zero => simp [binaryLoop]
  | succ fuel ih =>
    simp only [binaryLoop]
    split_ifs with h hmid
    · simp
    · have hh := ih (lo + (hi - lo) / 2) hi
      simp only
      constructor <;> omega
    · have hh := ih lo (lo + (hi - lo) / 2)
      simp only
      constructor <;> omega

/-- A power-of-two width invariant proves that the actual returned endpoints
are adjacent. No oracle for the existence or location of a crossing is used. -/
theorem binaryLoop_spec (safe : ℕ → Bool) (fuel lo hi : ℕ)
    (hlt : lo < hi) (hwidth : hi - lo ≤ 2 ^ fuel)
    (hlo : safe lo = true) (hhi : safe hi = false) :
    lo ≤ (binaryLoop safe fuel lo hi).boundary ∧
    (binaryLoop safe fuel lo hi).boundary < hi ∧
    safe (binaryLoop safe fuel lo hi).boundary = true ∧
    safe ((binaryLoop safe fuel lo hi).boundary + 1) = false := by
  induction fuel generalizing lo hi with
  | zero =>
    have he : hi = lo + 1 := by norm_num at hwidth; omega
    simpa [binaryLoop, ← he, hlo] using And.intro hlt hhi
  | succ fuel ih =>
    by_cases hadj : hi ≤ lo + 1
    · have he : hi = lo + 1 := by omega
      simp [binaryLoop, hadj, hlo, ← he, hhi, hlt]
    · let mid := lo + (hi - lo) / 2
      have hmidlo : lo < mid := by dsimp [mid]; omega
      have hmidhi : mid < hi := by dsimp [mid]; omega
      have hw : hi - lo ≤ 2 * 2 ^ fuel := by simpa [pow_succ, Nat.mul_comm] using hwidth
      have hleft : mid - lo ≤ 2 ^ fuel := by dsimp [mid]; omega
      have hright : hi - mid ≤ 2 ^ fuel := by dsimp [mid]; omega
      cases hm : safe mid with
      | false =>
        have hh := ih lo mid hmidlo hleft hlo hm
        simpa only [binaryLoop, if_neg hadj, show lo + (hi - lo) / 2 = mid from rfl,
          hm, Bool.false_eq_true, ↓reduceIte] using
          (show lo ≤ (binaryLoop safe fuel lo mid).boundary ∧
            (binaryLoop safe fuel lo mid).boundary < hi ∧
            safe (binaryLoop safe fuel lo mid).boundary = true ∧
            safe ((binaryLoop safe fuel lo mid).boundary + 1) = false from
            ⟨hh.1, lt_trans hh.2.1 hmidhi, hh.2.2⟩)
      | true =>
        have hh := ih mid hi hmidhi hright hm hhi
        simpa only [binaryLoop, if_neg hadj, show lo + (hi - lo) / 2 = mid from rfl,
          hm, ↓reduceIte] using
          (show lo ≤ (binaryLoop safe fuel mid hi).boundary ∧
            (binaryLoop safe fuel mid hi).boundary < hi ∧
            safe (binaryLoop safe fuel mid hi).boundary = true ∧
            safe ((binaryLoop safe fuel mid hi).boundary + 1) = false from
            ⟨le_trans (le_of_lt hmidlo) hh.1, hh.2⟩)

/-- Fuel is computed by an actual counted divide-by-two loop. The primitive
logarithm is used only in the theorem, never as an uncharged executable oracle. -/
def binaryFuel (k : ℕ) : ℕ × ℕ :=
  if h : 2 ≤ k then
    let rest := binaryFuel (k / 2)
    (rest.1 + 1, rest.2 + 4)
  else (1, 2)
termination_by k
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem binaryFuel_correct (k : ℕ) :
    (binaryFuel k).1 = Nat.log2 k + 1 ∧ (binaryFuel k).2 = 4 * Nat.log2 k + 2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [binaryFuel]
    split_ifs with hk
    · have hh := ih (k / 2) (Nat.div_lt_self (by omega) (by omega))
      rw [Nat.log2, if_pos hk]
      dsimp only
      constructor <;> omega
    · rw [Nat.log2, if_neg hk]
      simp

@[simp] theorem binaryFuel_value (k : ℕ) : (binaryFuel k).1 = Nat.log2 k + 1 :=
  (binaryFuel_correct k).1

@[simp] theorem binaryFuel_work (k : ℕ) : (binaryFuel k).2 = 4 * Nat.log2 k + 2 :=
  (binaryFuel_correct k).2

/-- Starting with width `k`, `log2 k + 1` is enough to halve to adjacency.
The output counter includes the actual computation of this fuel. -/
def binarySearch (safe : ℕ → Bool) (k : ℕ) : BinaryResult :=
  let fuel := binaryFuel k
  let result := binaryLoop safe fuel.1 0 k
  ⟨result.boundary, result.queries, result.operations + fuel.2 + 2⟩

theorem binarySearch_spec (safe : ℕ → Bool) (k : ℕ)
    (hzero : safe 0 = true) (hend : safe k = false) :
    (binarySearch safe k).boundary < k ∧
    safe (binarySearch safe k).boundary = true ∧
    safe ((binarySearch safe k).boundary + 1) = false := by
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    rw [he, hzero] at hend
    cases hend
  simpa only [binarySearch, binaryFuel_value] using (binaryLoop_spec safe (Nat.log2 k + 1) 0 k hk
    (by simpa using Nat.le_of_lt (Nat.lt_log2_self (n := k))) hzero hend).2

theorem binarySearch_counts (safe : ℕ → Bool) (k : ℕ) :
    (binarySearch safe k).queries ≤ Nat.log2 k + 1 ∧
    (binarySearch safe k).operations ≤ 20 * (Nat.log2 k + 1) + 4 := by
  have hh := binaryLoop_counts safe (Nat.log2 k + 1) 0 k
  simp only [binarySearch, binaryFuel_value, binaryFuel_work]
  constructor <;> omega

/-- Strictly crossing prefixes are unique for a nonnegative cost row. This
connects the binary implementation to the previous verified linear scan. -/
theorem safePrefix_unique (c : ℕ → ℚ) (l k : ℕ) (B : ℚ)
    (hc : ∀ j, 0 ≤ c j) (hB : 0 ≤ B) (hcross : B < mass c l k)
    {r : ℕ} (_hr : r < k) (hsafe : mass c l r ≤ B)
    (hnext : B < mass c l (r + 1)) : r = safePrefix c l k B := by
  have hscan := safePrefix_spec c l k B hB
  have hscanlt := safePrefix_lt c l k B hB hcross
  apply le_antisymm
  · by_contra h
    have hle : safePrefix c l k B + 1 ≤ r := by omega
    have hh := mass_mono c l hc hle
    have hh' := hscan.2 hscanlt
    linarith
  · by_contra h
    have hle : r + 1 ≤ safePrefix c l k B := by omega
    have hh := mass_mono c l hc hle
    linarith

/-- Search only a previously built table. No summation or cache construction
occurs during a midpoint query. -/
def binaryPrefix (cache : Array ℚ) (l k : ℕ) (B : ℚ) : BinaryResult :=
  binarySearch (fun s => decide (cachedMass cache l s ≤ B)) k

/-- An exact nonnegative budget below the full cost establishes both initial
endpoint invariants, and the binary result is the first strict crossing. -/
theorem binaryPrefix_spec (row : Array ℚ) (l k : ℕ) (B : ℚ)
    (hk : l + k ≤ row.size) (hB : 0 ≤ B)
    (hcross : B < mass (rowAt row) l k) :
    (binaryPrefix (prefixCache row) l k B).boundary < k ∧
    mass (rowAt row) l (binaryPrefix (prefixCache row) l k B).boundary ≤ B ∧
    B < mass (rowAt row) l ((binaryPrefix (prefixCache row) l k B).boundary + 1) := by
  have hz : decide (cachedMass (prefixCache row) l 0 ≤ B) = true := by simp [hB]
  have he : decide (cachedMass (prefixCache row) l k ≤ B) = false := by
    rw [cachedMass_prefixCache_eq_mass row l k hk]
    exact decide_eq_false (not_le.mpr hcross)
  have hs := binarySearch_spec (fun s => decide (cachedMass (prefixCache row) l s ≤ B))
    k hz he
  change (binaryPrefix (prefixCache row) l k B).boundary < k ∧ _ at hs
  refine ⟨hs.1, ?_, ?_⟩
  · have hh := of_decide_eq_true hs.2.1
    change cachedMass (prefixCache row) l (binaryPrefix (prefixCache row) l k B).boundary ≤ B at hh
    rwa [cachedMass_prefixCache_eq_mass row l _ (by omega)] at hh
  · have hh := of_decide_eq_false hs.2.2
    change ¬ cachedMass (prefixCache row) l ((binaryPrefix (prefixCache row) l k B).boundary + 1) ≤ B at hh
    rw [cachedMass_prefixCache_eq_mass row l _ (by omega)] at hh
    exact lt_of_not_ge hh

/-- With nonnegative entries, every preceding prefix is safe and every larger
prefix is unsafe, including equal-cost plateaus. -/
theorem binaryPrefix_first_strict (row : Array ℚ) (l k : ℕ) (B : ℚ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i])
    (hk : l + k ≤ row.size) (hB : 0 ≤ B)
    (hcross : B < mass (rowAt row) l k) :
    (∀ j, j ≤ (binaryPrefix (prefixCache row) l k B).boundary →
      mass (rowAt row) l j ≤ B) ∧
    (∀ j, (binaryPrefix (prefixCache row) l k B).boundary < j →
      B < mass (rowAt row) l j) := by
  have hs := binaryPrefix_spec row l k B hk hB hcross
  have hm := mass_mono (rowAt row) l (rowAt_nonneg row hn)
  exact ⟨fun j hj => (hm hj).trans hs.2.1,
    fun j hj => hs.2.2.trans_le (hm (by omega))⟩

theorem binaryPrefix_eq_safePrefix (row : Array ℚ) (l k : ℕ) (B : ℚ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i])
    (hk : l + k ≤ row.size) (hB : 0 ≤ B)
    (hcross : B < mass (rowAt row) l k) :
    (binaryPrefix (prefixCache row) l k B).boundary = safePrefix (rowAt row) l k B := by
  have hs := binaryPrefix_spec row l k B hk hB hcross
  exact safePrefix_unique _ _ _ _ (rowAt_nonneg row hn) hB hcross hs.1 hs.2.1 hs.2.2

/-- A total search also handles a budget that pays for the whole range. The
full-range test is a single cached query, evaluated once. -/
def binarySafePrefix (cache : Array ℚ) (l k : ℕ) (B : ℚ) : BinaryResult :=
  if cachedMass cache l k ≤ B then ⟨k, 1, 6⟩
  else
    let result := binaryPrefix cache l k B
    ⟨result.boundary, result.queries + 1, result.operations + 6⟩

theorem safePrefix_of_mass_le (c : ℕ → ℚ) (l k : ℕ) (B : ℚ)
    (hc : ∀ j, 0 ≤ c j) (hB : 0 ≤ B) (hfull : mass c l k ≤ B) :
    safePrefix c l k B = k := by
  have hle := safePrefix_le c l k B
  have hs := safePrefix_spec c l k B hB
  by_contra hne
  have hlt : safePrefix c l k B < k := by omega
  have hh := (hs.2 hlt).trans_le ((mass_mono c l hc) (show safePrefix c l k B + 1 ≤ k by omega))
  exact (not_lt_of_ge hfull) hh

/-- The binary executable exactly replaces the linear primitive throughout its
valid input domain. Cache correctness and monotonicity are proved from the input. -/
theorem binarySafePrefix_eq_safePrefix (row : Array ℚ) (l k : ℕ) (B : ℚ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i])
    (hk : l + k ≤ row.size) (hB : 0 ≤ B) :
    (binarySafePrefix (prefixCache row) l k B).boundary = safePrefix (rowAt row) l k B := by
  unfold binarySafePrefix
  rw [cachedMass_prefixCache_eq_mass row l k hk]
  split_ifs with hfull
  · exact (safePrefix_of_mass_le _ _ _ _ (rowAt_nonneg row hn) hB hfull).symm
  · exact binaryPrefix_eq_safePrefix row l k B hn hk hB (lt_of_not_ge hfull)

/-- One full-range query plus at most log2(k)+1 midpoint queries; rational
arithmetic and array accesses are charged by the same executed recursion. -/
theorem binarySafePrefix_counts (cache : Array ℚ) (l k : ℕ) (B : ℚ) :
    (binarySafePrefix cache l k B).queries ≤ Nat.log2 k + 2 ∧
    (binarySafePrefix cache l k B).operations ≤ 20 * (Nat.log2 k + 1) + 10 := by
  unfold binarySafePrefix
  split_ifs with hfull
  · simp
  · have hh := binarySearch_counts (fun s => decide (cachedMass cache l s ≤ B)) k
    change (binaryPrefix cache l k B).queries ≤ _ ∧
      (binaryPrefix cache l k B).operations ≤ _ at hh
    constructor <;> dsimp only <;> omega

/-- Uniform item-count logarithmic bound for every residual interval. -/
theorem binarySafePrefix_counts_uniform (cache : Array ℚ) (l k m : ℕ) (B : ℚ)
    (hk : k ≤ m) :
    (binarySafePrefix cache l k B).queries ≤ Nat.log2 (m + 1) + 2 ∧
    (binarySafePrefix cache l k B).operations ≤ 30 * (Nat.log2 (m + 1) + 1) := by
  have hs := binarySafePrefix_counts cache l k B
  have hlog : Nat.log2 k ≤ Nat.log2 (m + 1) := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  constructor <;> omega

/-- The actual exact Hill threshold establishes the binary endpoints on every
nontrivial q≥3 recursive row. Thus callers need no crossing oracle. -/
theorem binaryPrefix_exact_bound (row : Array ℚ) (l k q : ℕ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i])
    (ha : Antitone (rowAt row)) (hk : l + k ≤ row.size) (hq : 3 ≤ q)
    (hT : mass (rowAt row) l k ≠ 0)
    (hpT : rowAt row l ≠ mass (rowAt row) l k) :
    let B := bound q (cachedMass (prefixCache row) l k) (rowAt row l)
    (binaryPrefix (prefixCache row) l k B).boundary < k ∧
    mass (rowAt row) l (binaryPrefix (prefixCache row) l k B).boundary ≤ B ∧
    B < mass (rowAt row) l ((binaryPrefix (prefixCache row) l k B).boundary + 1) := by
  dsimp only
  rw [cachedMass_prefixCache_eq_mass row l k hk]
  exact binaryPrefix_spec row l k _ hk
    (bound_nonneg _ l k q (by omega) (rowAt_nonneg row hn) ha)
    (bound_lt_mass _ l k q hq (rowAt_nonneg row hn) ha hT hpT)

end ExactHillShares.Algorithm
