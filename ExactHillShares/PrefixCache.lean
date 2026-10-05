import ExactHillShares.Algorithm

/-!
# Materialized rational prefix sums

The builder appends one prefix value at each recursive step. It never tabulates
interval sums. Array indexing, rational arithmetic, and amortized array push are
unit operations in the arithmetic/RAM cost model used below.
-/
namespace ExactHillShares.Algorithm

/-- An actual array lookup, with zero outside the finite input. -/
def rowAt (row : Array ℚ) (i : ℕ) : ℚ := row[i]?.getD 0

@[simp] theorem rowAt_of_lt (row : Array ℚ) (i : ℕ) (h : i < row.size) :
    rowAt row i = row[i] := by
  simp [rowAt, Array.getElem?_eq_getElem h]

@[simp] theorem rowAt_of_size_le (row : Array ℚ) (i : ℕ) (h : row.size ≤ i) :
    rowAt row i = 0 := by
  simp [rowAt, Array.getElem?_eq_none h]

/-- The data and its work counter are produced by the same loop. Each step
charges two reads, one addition, and one amortized push. The initial zero costs
one operation. -/
def buildPrefixLoop (row : Array ℚ) : ℕ → Array ℚ × ℕ
  | 0 => (#[0], 1)
  | k + 1 =>
    let prior := buildPrefixLoop row k
    (prior.1.push (rowAt prior.1 k + rowAt row k), prior.2 + 4)

/-- Prefix table including its initial zero; exactly `row.size + 1` entries. -/
def prefixCache (row : Array ℚ) : Array ℚ := (buildPrefixLoop row row.size).1

/-- The actual builder's charged arithmetic/RAM work. -/
def prefixCacheWork (row : Array ℚ) : ℕ := (buildPrefixLoop row row.size).2

@[simp] theorem buildPrefixLoop_size (row : Array ℚ) (k : ℕ) :
    (buildPrefixLoop row k).1.size = k + 1 := by
  induction k with
  | zero => simp [buildPrefixLoop]
  | succ k ih => simp [buildPrefixLoop, ih]

@[simp] theorem buildPrefixLoop_work (row : Array ℚ) (k : ℕ) :
    (buildPrefixLoop row k).2 = 4 * k + 1 := by
  induction k with
  | zero => simp [buildPrefixLoop]
  | succ k ih => simp [buildPrefixLoop, ih]; omega

@[simp] theorem prefixCache_size (row : Array ℚ) :
    (prefixCache row).size = row.size + 1 := by
  simp [prefixCache]

@[simp] theorem prefixCacheWork_eq (row : Array ℚ) :
    prefixCacheWork row = 4 * row.size + 1 := by
  simp [prefixCacheWork]

private theorem rowAt_push (row : Array ℚ) (x : ℚ) (i : ℕ) :
    rowAt (row.push x) i = if i = row.size then x else rowAt row i := by
  simp only [rowAt, Array.getElem?_push]
  split <;> simp_all

/-- Every populated prefix cell is its exact rational prefix sum. -/
theorem buildPrefixLoop_correct (row : Array ℚ) (k i : ℕ) (hi : i ≤ k) :
    rowAt (buildPrefixLoop row k).1 i = mass (rowAt row) 0 i := by
  induction k generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    simp [buildPrefixLoop, rowAt]
  | succ k ih =>
    simp only [buildPrefixLoop, rowAt_push, buildPrefixLoop_size]
    by_cases hik : i = k + 1
    · subst i
      rw [if_pos rfl, ih k (by omega)]
      rw [show k + 1 = k + 1 by rfl, mass_append]
      simp [mass_succ, add_comm]
    · rw [if_neg hik]
      exact ih i (by omega)

/-- Querying a prefix table performs exactly two array reads and one subtraction. -/
def cachedMass (cache : Array ℚ) (l k : ℕ) : ℚ :=
  rowAt cache (l + k) - rowAt cache l

@[simp] theorem cachedMass_zero (cache : Array ℚ) (l : ℕ) :
    cachedMass cache l 0 = 0 := by simp [cachedMass]

/-- The array query agrees with the recursive specification on every valid range. -/
theorem cachedMass_prefixCache_eq_mass (row : Array ℚ) (l k : ℕ)
    (h : l + k ≤ row.size) :
    cachedMass (prefixCache row) l k = mass (rowAt row) l k := by
  unfold cachedMass prefixCache
  rw [buildPrefixLoop_correct row row.size (l + k) h,
    buildPrefixLoop_correct row row.size l (by omega), mass_append]
  simp

@[simp] theorem cachedMass_prefixCache_total (row : Array ℚ) :
    cachedMass (prefixCache row) 0 row.size = mass (rowAt row) 0 row.size :=
  cachedMass_prefixCache_eq_mass row 0 row.size (by omega)

theorem rowAt_nonneg (row : Array ℚ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i]) :
    ∀ i, 0 ≤ rowAt row i := by
  intro i
  by_cases hi : i < row.size
  · simpa only [rowAt_of_lt row i hi] using hn i hi
  · simp [rowAt_of_size_le row i (by omega)]

/-- Monotonicity is asserted precisely within the materialized table's domain. -/
theorem cachedMass_prefixCache_mono (row : Array ℚ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i])
    (l s k : ℕ) (hsk : s ≤ k) (hk : l + k ≤ row.size) :
    cachedMass (prefixCache row) l s ≤ cachedMass (prefixCache row) l k := by
  rw [cachedMass_prefixCache_eq_mass row l s (by omega),
    cachedMass_prefixCache_eq_mass row l k hk]
  exact mass_mono (rowAt row) l (rowAt_nonneg row hn) hsk

/-- A suffix uses the same table and the same constant-time range query. -/
def cachedSuffix (cache : Array ℚ) (m l : ℕ) : ℚ :=
  cachedMass cache l (m - l)

theorem cachedSuffix_eq_mass (row : Array ℚ) (l : ℕ) (hl : l ≤ row.size) :
    cachedSuffix (prefixCache row) row.size l = mass (rowAt row) l (row.size - l) := by
  exact cachedMass_prefixCache_eq_mass row l (row.size - l) (by omega)

theorem prefixCacheWork_le (row : Array ℚ) :
    prefixCacheWork row ≤ 4 * (row.size + 1) := by
  rw [prefixCacheWork_eq]
  omega

@[simp] theorem prefixCache_initial (row : Array ℚ) :
    rowAt (prefixCache row) 0 = 0 := by
  simpa [prefixCache] using buildPrefixLoop_correct row row.size 0 (by omega)

theorem cachedMass_append (cache : Array ℚ) (l s k : ℕ) :
    cachedMass cache l (s + k) =
      cachedMass cache l s + cachedMass cache (l + s) k := by
  simp only [cachedMass, Nat.add_assoc]
  ring

theorem cachedMass_prefixCache_nonneg (row : Array ℚ)
    (hn : ∀ i, (h : i < row.size) → 0 ≤ row[i]) (l k : ℕ)
    (hk : l + k ≤ row.size) : 0 ≤ cachedMass (prefixCache row) l k := by
  rw [cachedMass_prefixCache_eq_mass row l k hk]
  exact mass_nonneg (rowAt row) l k (rowAt_nonneg row hn)

/-- Outer preprocessing also builds its actual array incrementally. Its two
additional operations per row are the input-row lookup and output-row push. -/
def buildPrefixRowsLoop (rows : Array (Array ℚ)) : ℕ → Array (Array ℚ) × ℕ
  | 0 => (#[], 0)
  | n + 1 =>
    let prior := buildPrefixRowsLoop rows n
    let row := rows[n]?.getD #[]
    let built := buildPrefixLoop row row.size
    (prior.1.push built.1, prior.2 + built.2 + 2)

def prefixRows (rows : Array (Array ℚ)) : Array (Array ℚ) :=
  (buildPrefixRowsLoop rows rows.size).1

def prefixRowsWork (rows : Array (Array ℚ)) : ℕ :=
  (buildPrefixRowsLoop rows rows.size).2

@[simp] theorem buildPrefixRowsLoop_size (rows : Array (Array ℚ)) (n : ℕ) :
    (buildPrefixRowsLoop rows n).1.size = n := by
  induction n with
  | zero => simp [buildPrefixRowsLoop]
  | succ n ih => simp [buildPrefixRowsLoop, ih]

@[simp] theorem prefixRows_size (rows : Array (Array ℚ)) :
    (prefixRows rows).size = rows.size := by simp [prefixRows]

theorem buildPrefixRowsLoop_correct (rows : Array (Array ℚ)) (n i : ℕ)
    (hi : i < n) :
    (buildPrefixRowsLoop rows n).1[i]? =
      some (prefixCache (rows[i]?.getD #[])) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [buildPrefixRowsLoop, Array.getElem?_push, buildPrefixRowsLoop_size]
    by_cases hin : i = n
    · subst i
      simp [prefixCache]
    · rw [if_neg hin]
      exact ih i (by omega)

/-- Every outer-array cell contains the verified prefix table of that input row. -/
theorem prefixRows_correct (rows : Array (Array ℚ)) (i : ℕ)
    (hi : i < rows.size) :
    (prefixRows rows)[i]?.getD #[] = prefixCache rows[i] := by
  simp [prefixRows, buildPrefixRowsLoop_correct rows rows.size i hi,
    Array.getElem?_eq_getElem hi]

open scoped BigOperators

/-- Exact summed preprocessing charge, including the outer-array accesses. -/
theorem buildPrefixRowsLoop_work (rows : Array (Array ℚ)) (n : ℕ) :
    (buildPrefixRowsLoop rows n).2 =
      ∑ i ∈ Finset.range n, (4 * (rows[i]?.getD #[]).size + 3) := by
  induction n with
  | zero => simp [buildPrefixRowsLoop]
  | succ n ih =>
    simp only [buildPrefixRowsLoop, buildPrefixLoop_work, ih, Finset.sum_range_succ]
    omega

theorem prefixRowsWork_eq_sum (rows : Array (Array ℚ)) :
    prefixRowsWork rows =
      ∑ i ∈ Finset.range rows.size, (4 * (rows[i]?.getD #[]).size + 3) := by
  exact buildPrefixRowsLoop_work rows rows.size

/-- A rectangular `n` by `m` input has a linear charged construction cost. -/
theorem prefixRowsWork_rectangular (rows : Array (Array ℚ)) (m : ℕ)
    (hrect : ∀ i, (hi : i < rows.size) → rows[i].size = m) :
    prefixRowsWork rows = rows.size * (4 * m + 3) := by
  rw [prefixRowsWork_eq_sum]
  calc
    _ = ∑ _i ∈ Finset.range rows.size, (4 * m + 3) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp only [Array.getElem?_eq_getElem hi', Option.getD_some, hrect i hi']
    _ = _ := by simp

theorem prefixRowsWork_le (rows : Array (Array ℚ)) (m : ℕ)
    (hrect : ∀ i, (hi : i < rows.size) → rows[i].size = m) :
    prefixRowsWork rows ≤ 4 * rows.size * (m + 1) := by
  rw [prefixRowsWork_rectangular rows m hrect]
  nlinarith

/-- Two outer/inner array reads define the zero-extended matrix input. -/
def arrayCosts (rows : Array (Array ℚ)) (i j : ℕ) : ℚ :=
  rowAt (rows[i]?.getD #[]) j

/-- The multirow cache query reads its row once, then performs two scalar reads
and a subtraction. It does no summation or preprocessing. -/
def cachedRowMass (caches : Array (Array ℚ)) (i l k : ℕ) : ℚ :=
  cachedMass (caches[i]?.getD #[]) l k

theorem cachedRowMass_prefixRows_eq_mass (rows : Array (Array ℚ))
    (i l k : ℕ) (hi : i < rows.size) (hk : l + k ≤ rows[i].size) :
    cachedRowMass (prefixRows rows) i l k = mass (arrayCosts rows i) l k := by
  rw [cachedRowMass, prefixRows_correct rows i hi,
    cachedMass_prefixCache_eq_mass rows[i] l k hk]
  congr 1
  funext j
  simp [arrayCosts, Array.getElem?_eq_getElem hi]

/-- The paper's suffix sum S(r) is recovered by two reads from the prefix
representation. This equality justifies the representation change directly. -/
theorem cachedSuffix_eq_sum (row : Array ℚ) (r : ℕ) (hr : r ≤ row.size) :
    cachedSuffix (prefixCache row) row.size r =
      ∑ j ∈ Finset.range (row.size - r), rowAt row (r + j) := by
  rw [cachedSuffix_eq_mass row r hr, mass_eq_sum]

/-- On positive-width matrices the preprocessing is literally bounded by a
constant times n*m. Zero-width matrices instead use the n*(m+1) bound above. -/
theorem prefixRowsWork_linear_nm (rows : Array (Array ℚ)) (m : ℕ) (hm : 0 < m)
    (hrect : ∀ i, (hi : i < rows.size) → rows[i].size = m) :
    prefixRowsWork rows ≤ 7 * rows.size * m := by
  rw [prefixRowsWork_rectangular rows m hrect]
  have hh : rows.size ≤ rows.size * m := Nat.le_mul_of_pos_right _ hm
  nlinarith

end ExactHillShares.Algorithm
