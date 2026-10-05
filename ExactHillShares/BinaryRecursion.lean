import ExactHillShares.CachedBinaryAlgorithm
import ExactHillShares.Terminal

/-!
# Structural analysis of the cached binary recursion

The active agents are a duplicate-free list with a constant-cost finite-set
view. Prefix arrays are prepared once outside this recursion. Guards read
cached totals, each binary boundary is computed once and stored, and a linear
scan selects a maximum. This module defines the semantic output and structural
cost analysis together. Its cost-analysis functions are not part of the actual
allocator: evaluating a cost model can itself be more expensive than the program
it describes. BinaryOutput supplies the independent counter-free executable and
proves output equality. The terminal is the concrete proved divider/cheaper-bundle
chooser; its cost analysis is used only as an annotation here.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

structure BinaryRunResult (n : ℕ) where
  output : Option (Allocation n)
  operations : ℕ
  /-- Number of cached range-sum queries; the separately charged terminal
  performs its own linear/DP work rather than cached binary queries. -/
  queries : ℕ
  terminalCalls : ℕ

/-- Analysis model for the original recursive case structure. Its operation
field is a structural charge, not a bound on evaluating this analysis record.
Use `runCachedBinaryOnly` for execution without the cost-analysis overhead. -/
def runCachedBinary (rows caches : Array (Array ℚ)) :
    ℕ → ActiveRows rows.size → ℕ → ℕ → BinaryRunResult rows.size
  | 0, _, _, k => ⟨if k = 0 then some (fun _ => none) else none, 1, 0, 0⟩
  | fuel + 1, active, l, k =>
    let A := active.finset
    let q := A.card
    if k = 0 then ⟨some (fun _ => none), 1, 0, 0⟩
    else if hA : A.Nonempty then
      if q = 1 then ⟨some (whole (A.min' hA) l k), 5 + 4 * q, 0, 0⟩
      else
        let earlyResult := cachedEarlyCounted rows caches A l k
        let pre := 20 + 4 * q + earlyResult.2
        match earlyResult.1 with
        | some a => ⟨some (whole a l k), pre + 5, q, 0⟩
        | none => if q = 2 then
            ⟨terminal (matrixCosts rows) A l k,
              pre + terminalOps (matrixCosts rows) A l k, q, 1⟩
          else
            let knifeResult := cachedKnifeCounted rows caches active l k
            match knifeResult.1.value with
            | none => ⟨none, pre + knifeResult.1.operations, q + knifeResult.2, 0⟩
            | some (a, s) =>
              let tail := runCachedBinary rows caches fuel (active.erase a) (l + s) (k - s)
              ⟨tail.output.map (splice a l s), pre + knifeResult.1.operations + 5 + tail.operations,
                q + knifeResult.2 + tail.queries, tail.terminalCalls⟩
    else ⟨none, 5, 0, 0⟩

/-- Every concrete branch is safe. In particular, no terminal callback,
feasibility oracle, or binary-crossing assumption remains. -/
theorem runCachedBinary_correct (rows caches : Array (Array ℚ))
    (hv : PrefixRowsValid rows caches) (fuel : ℕ) (active : ActiveRows rows.size) (l k : ℕ)
    (hfuel : active.finset.card ≤ fuel) (hA : active.finset.Nonempty)
    (hn : ∀ i ∈ active.finset, ∀ j, 0 ≤ matrixCosts rows i j)
    (ha : ∀ i ∈ active.finset, Antitone (matrixCosts rows i))
    (hrange : ∀ i ∈ active.finset, l + k ≤ rows[i].size) :
    ∃ out, (runCachedBinary rows caches fuel active l k).output = some out ∧
      Safe (matrixCosts rows) active.finset l k out := by
  induction fuel generalizing active l k with
  | zero => have := Finset.card_pos.mpr hA; omega
  | succ fuel ih =>
    by_cases hk : k = 0
    · subst k
      exact ⟨_, by simp [runCachedBinary], empty_safe (matrixCosts rows) active.finset l⟩
    by_cases hq1 : active.finset.card = 1
    · exact ⟨_, by simp [runCachedBinary, hk, hA, hq1],
        one_safe (matrixCosts rows) active.finset l k hA hq1⟩
    have hq1' : active.agents.length ≠ 1 := hq1
    have heq := cachedEarly_eq rows caches hv active.finset l k hrange
    cases he : cachedEarly rows caches active.finset l k with
    | some a =>
      have he' : early (matrixCosts rows) active.finset l k = some a := by rw [← heq]; exact he
      exact ⟨_, by simp [runCachedBinary, cachedEarlyCounted, hk, hA, hq1, hq1', he],
        early_safe (matrixCosts rows) active.finset l k hn ha he'⟩
    | none =>
      have he' : early (matrixCosts rows) active.finset l k = none := by rw [← heq]; exact he
      obtain ⟨hT, hpT⟩ := early_none he'
      by_cases hq2 : active.finset.card = 2
      · obtain ⟨out, hout, hs⟩ := terminal_correct (matrixCosts rows) active.finset l k
          hq2 (by omega) hn ha hT hpT
        exact ⟨out, by simpa [runCachedBinary, cachedEarlyCounted, hk, hA, hq1, hq1', he, hq2] using hout, hs⟩
      have hq2' : active.agents.length ≠ 2 := hq2
      have hq3 : 3 ≤ active.finset.card := by have := Finset.card_pos.mpr hA; omega
      obtain ⟨a, s, hknife, hamem, hsk, hpref, htail⟩ :=
        cachedKnife_spec rows caches hv active l k hq3 hn ha hrange hT hpT
      have hcard := Finset.card_erase_add_one hamem
      have hA' : (active.erase a).finset.Nonempty := by
        rw [ActiveRows.erase_finset]
        exact Finset.card_pos.mp (by omega)
      have hrange' : ∀ i ∈ (active.erase a).finset,
          l + s + (k - s) ≤ rows[i].size := by
        intro i hi
        rw [ActiveRows.erase_finset] at hi
        have hh := hrange i (Finset.mem_of_mem_erase hi)
        omega
      obtain ⟨tail, hrun, hvalid, hsafe⟩ := ih (active.erase a) (l + s) (k - s)
        (by rw [ActiveRows.erase_finset]; omega) hA'
        (by simpa using fun i hi => hn i (Finset.mem_of_mem_erase hi))
        (by simpa using fun i hi => ha i (Finset.mem_of_mem_erase hi)) hrange'
      rw [ActiveRows.erase_finset] at hvalid hsafe
      refine ⟨splice a l s tail, ?_, splice_valid hamem (Nat.le_of_lt hsk) hvalid, ?_⟩
      · change (cachedKnifeCounted rows caches active l k).1.value = some (a,s) at hknife
        simp [runCachedBinary, cachedEarlyCounted, hk, hA, hq1, hq1', he, hq2, hq2', hknife, hrun]
      · intro i hi
        rw [charge_splice (matrixCosts rows) a i l s k (Nat.le_of_lt hsk) tail]
        by_cases hai : a = i
        · subst i
          rw [if_pos rfl, charge_erased (matrixCosts rows) hvalid, add_zero]
          exact hpref
        · have hi' : i ∈ active.finset.erase a := Finset.mem_erase.mpr ⟨Ne.symm hai, hi⟩
          rw [if_neg hai, zero_add]
          exact (hsafe i hi').trans (htail i hi')

/-- The program reaches at most one concrete terminal call, rather than
charging the cubic terminal bound at every level. -/
theorem runCachedBinary_terminalCalls_le (rows caches : Array (Array ℚ))
    (fuel : ℕ) (active : ActiveRows rows.size) (l k : ℕ) :
    (runCachedBinary rows caches fuel active l k).terminalCalls ≤ 1 := by
  induction fuel generalizing active l k with
  | zero => simp [runCachedBinary]
  | succ fuel ih =>
    simp only [runCachedBinary]
    split_ifs <;> try dsimp only
    all_goals try omega
    all_goals split <;> try dsimp only
    all_goals try omega
    all_goals split <;> try dsimp only
    all_goals try omega
    all_goals exact ih _ _ _

/-- The structural execution charge has one chain of logarithmic moving-knife
levels and at most one cubic terminal. This bounds the charged program, not the
work needed to evaluate its possibly more expensive analysis functions. -/
theorem runCachedBinary_operations_le (rows caches : Array (Array ℚ))
    (fuel : ℕ) (active : ActiveRows rows.size) (l k m : ℕ)
    (hf : active.finset.card ≤ fuel) (hk : k ≤ m)
    (hn : ∀ i ∈ active.finset, ∀ j, 0 ≤ matrixCosts rows i j)
    (ha : ∀ i ∈ active.finset, Antitone (matrixCosts rows i)) :
    (runCachedBinary rows caches fuel active l k).operations ≤
      500 * fuel^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 := by
  induction fuel generalizing active l k with
  | zero =>
    have hpos : 0 < (m + 1)^3 := pow_pos (by omega) _
    simp only [runCachedBinary]
    omega
  | succ fuel ih =>
    have hcubepos : 0 < (m + 1)^3 := pow_pos (by omega) _
    by_cases hk0 : k = 0
    · simp only [runCachedBinary, if_pos hk0]
      omega
    by_cases hA : active.finset.Nonempty
    · have hpos := Finset.card_pos.mpr hA
      have hlevel := cachedLevelOps_le rows caches active l k m hk hpos
      unfold cachedLevelOps at hlevel
      have hstep : 20 + 4 * active.finset.card + cachedEarlyOps active.finset +
          cachedKnifeOps rows caches active l k + 5 +
          500 * fuel^2 * (Nat.log2 (m + 1) + 1) ≤
          500 * (fuel + 1)^2 * (Nat.log2 (m + 1) + 1) := by
        have hm := Nat.mul_le_mul_right (Nat.log2 (m + 1) + 1) hf
        nlinarith
      simp only [runCachedBinary, if_neg hk0, dif_pos hA, cachedEarlyCounted]
      by_cases hq1 : active.finset.card = 1
      · rw [if_pos hq1]
        simp only
        nlinarith
      rw [if_neg hq1]
      cases he : cachedEarly rows caches active.finset l k with
      | some a =>
        simp only
        nlinarith
      | none =>
        simp only
        by_cases hq2 : active.finset.card = 2
        · rw [if_pos hq2]
          simp only
          have ht := terminalOps_cubic (matrixCosts rows) active.finset l k hq2 (by omega) hn ha
          have hm : k^3 ≤ (m + 1)^3 := Nat.pow_le_pow_left (by omega) 3
          nlinarith
        rw [if_neg hq2]
        cases hki : (cachedKnifeCounted rows caches active l k).1.value with
        | none =>
          simp only
          change 20 + 4 * active.finset.card + cachedEarlyOps active.finset +
            cachedKnifeOps rows caches active l k ≤ _
          nlinarith
        | some pair =>
          rcases pair with ⟨a, s⟩
          simp only
          have hmem := cachedKnife_some rows caches active l k a s hki
          have hcard := Finset.card_erase_add_one hmem
          have hrec := ih (active.erase a) (l + s) (k - s)
            (by rw [ActiveRows.erase_finset]; omega) (by omega)
            (by simpa using fun i hi => hn i (Finset.mem_of_mem_erase hi))
            (by simpa using fun i hi => ha i (Finset.mem_of_mem_erase hi))
          change 20 + 4 * active.finset.card + cachedEarlyOps active.finset +
            cachedKnifeOps rows caches active l k + 5 +
            (runCachedBinary rows caches fuel (active.erase a) (l + s) (k - s)).operations ≤ _
          omega
    · simp only [runCachedBinary, if_neg hk0, dif_neg hA]
      omega

/-- Analysis wrapper including prefix preprocessing and initial active-list
construction. The counter-free executable is `allocateBinaryArrayOnly`. -/
def allocateBinaryArray (rows : Array (Array ℚ)) (m : ℕ) : BinaryRunResult rows.size :=
  let prepared := buildPrefixRowsLoop rows rows.size
  let result := runCachedBinary rows prepared.1 rows.size (ActiveRows.all rows.size) 0 m
  ⟨result.output, prepared.2 + result.operations + 4 * rows.size + 4,
    result.queries, result.terminalCalls⟩

theorem allocateBinaryArray_correct (rows : Array (Array ℚ)) (m : ℕ)
    (hn : 0 < rows.size) (hrect : ∀ i : Fin rows.size, rows[i].size = m)
    (hc : ∀ i j, 0 ≤ matrixCosts rows i j) (ha : ∀ i, Antitone (matrixCosts rows i)) :
    ∃ out, (allocateBinaryArray rows m).output = some out ∧
      Safe (matrixCosts rows) Finset.univ 0 m out := by
  have hh := runCachedBinary_correct rows (prefixRows rows) (prefixRows_valid rows)
    rows.size (ActiveRows.all rows.size) 0 m
    (by simp) (by rw [ActiveRows.all_finset]; exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
    (by simpa using fun i (_hi : i ∈ (Finset.univ : Finset (Fin rows.size))) => hc i)
    (by simpa using fun i (_hi : i ∈ (Finset.univ : Finset (Fin rows.size))) => ha i)
    (by intro i hi; rw [hrect i]; omega)
  simpa only [allocateBinaryArray, prefixRows, ActiveRows.all_finset] using hh

/-- Original-indexed rows in an actual finite vector, for composition with
sorting and the original-item matching lift. -/
def vectorCosts {n : ℕ} (rows : Vector (Array ℚ) n) (i : Fin n) : ℕ → ℚ :=
  rowAt (rows.get i)

def allocateBinaryRowsCounted {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) :
    BinaryRunResult n :=
  rows.size_toArray ▸ allocateBinaryArray rows.toArray m

def allocateBinaryRows {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) :
    Option (Allocation n) := (allocateBinaryRowsCounted rows m).output

def allocateBinaryRowsOps {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) : ℕ :=
  (allocateBinaryRowsCounted rows m).operations

theorem allocateBinaryRows_correct {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ)
    (hn : 0 < n) (hrect : ∀ i, (rows.get i).size = m)
    (hc : ∀ i j, 0 ≤ vectorCosts rows i j) (ha : ∀ i, Antitone (vectorCosts rows i)) :
    ∃ out, allocateBinaryRows rows m = some out ∧
      Safe (vectorCosts rows) Finset.univ 0 m out := by
  cases rows with
  | mk data hs =>
    cases hs
    exact allocateBinaryArray_correct data m hn hrect hc ha

/-- Structural arithmetic charge including one linear prefix preprocessing and
initial active-list construction. Only data invariants occur in the hypotheses.
This is not a bound on evaluating the analysis record itself. -/
theorem allocateBinaryArray_operations_le (rows : Array (Array ℚ)) (m : ℕ)
    (hn : 0 < rows.size) (hrect : ∀ i : Fin rows.size, rows[i].size = m)
    (hc : ∀ i j, 0 ≤ matrixCosts rows i j) (ha : ∀ i, Antitone (matrixCosts rows i)) :
    (allocateBinaryArray rows m).operations ≤
      1000 * rows.size^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 +
        4 * rows.size * (m + 1) := by
  have hp := prefixRowsWork_le rows m (fun i hi => hrect ⟨i, hi⟩)
  have hr := runCachedBinary_operations_le rows (prefixRows rows) rows.size
    (ActiveRows.all rows.size) 0 m m (by simp) le_rfl
    (fun i hi => hc i) (fun i hi => ha i)
  have hsize : rows.size ≤ rows.size^2 := Nat.le_self_pow (by decide) rows.size
  have hlog : rows.size^2 ≤ rows.size^2 * (Nat.log2 (m + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change prefixRowsWork rows +
    (runCachedBinary rows (prefixRows rows) rows.size (ActiveRows.all rows.size) 0 m).operations +
      4 * rows.size + 4 ≤ _
  nlinarith

/-- Original-agent-indexed public runtime theorem for the counted Vector API. -/
theorem allocateBinaryRowsOps_bound {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ)
    (hn : 0 < n) (hrect : ∀ i, (rows.get i).size = m)
    (hc : ∀ i j, 0 ≤ vectorCosts rows i j) (ha : ∀ i, Antitone (vectorCosts rows i)) :
    allocateBinaryRowsOps rows m ≤
      1000 * n^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 + 4 * n * (m + 1) := by
  cases rows with
  | mk data hs =>
    cases hs
    exact allocateBinaryArray_operations_le data m hn hrect hc ha

/-- The full chain's cached-query count is quadratic in the number of active
agents and logarithmic in the number of items. No row assumptions are needed
for this execution-count bound. -/
theorem runCachedBinary_queries_le (rows caches : Array (Array ℚ))
    (fuel : ℕ) (active : ActiveRows rows.size) (l k m : ℕ)
    (hf : active.finset.card ≤ fuel) (hk : k ≤ m) :
    (runCachedBinary rows caches fuel active l k).queries ≤
      10 * fuel^2 * (Nat.log2 (m + 1) + 1) := by
  induction fuel generalizing active l k with
  | zero => simp [runCachedBinary]
  | succ fuel ih =>
    have hb := cachedKnifeQueries_le rows caches active l k m hk
    have hm := Nat.mul_le_mul_right (Nat.log2 (m + 1) + 1) hf
    have hstep : active.finset.card + (cachedKnifeCounted rows caches active l k).2 +
        10 * fuel^2 * (Nat.log2 (m + 1) + 1) ≤
        10 * (fuel + 1)^2 * (Nat.log2 (m + 1) + 1) := by nlinarith
    by_cases hk0 : k = 0
    · simp only [runCachedBinary, if_pos hk0]
      omega
    by_cases hA : active.finset.Nonempty
    · simp only [runCachedBinary, if_neg hk0, dif_pos hA, cachedEarlyCounted]
      by_cases hq1 : active.finset.card = 1
      · rw [if_pos hq1]
        simp only
        omega
      rw [if_neg hq1]
      cases he : cachedEarly rows caches active.finset l k with
      | some a => simp only; omega
      | none =>
        simp only
        by_cases hq2 : active.finset.card = 2
        · rw [if_pos hq2]
          simp only
          omega
        rw [if_neg hq2]
        cases hki : (cachedKnifeCounted rows caches active l k).1.value with
        | none => simp only; omega
        | some pair =>
          rcases pair with ⟨a,s⟩
          simp only
          have hmem := cachedKnife_some rows caches active l k a s hki
          have hcard := Finset.card_erase_add_one hmem
          have hrec := ih (active.erase a) (l+s) (k-s)
            (by rw [ActiveRows.erase_finset]; omega) (by omega)
          omega
    · simp only [runCachedBinary, if_neg hk0, dif_neg hA]
      omega

theorem allocateBinaryRows_queries_le {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) :
    (allocateBinaryRowsCounted rows m).queries ≤ 10 * n^2 * (Nat.log2 (m+1)+1) := by
  cases rows with
  | mk data hs =>
    cases hs
    exact runCachedBinary_queries_le data (prefixRows data) data.size
      (ActiveRows.all data.size) 0 m m (by simp) le_rfl

theorem allocateBinaryRows_terminalCalls_le {n : ℕ} (rows : Vector (Array ℚ) n) (m : ℕ) :
    (allocateBinaryRowsCounted rows m).terminalCalls ≤ 1 := by
  cases rows with
  | mk data hs =>
    cases hs
    exact runCachedBinary_terminalCalls_le data (prefixRows data) data.size
      (ActiveRows.all data.size) 0 m

end ExactHillShares.Algorithm
