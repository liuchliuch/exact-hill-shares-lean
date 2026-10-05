import ExactHillShares.BinaryCrossingBatch

/-!
# Cached guards and a materialized binary moving knife

Every residual total and midpoint sum is a difference of two cells of the
already built prefix array. The suffix sum S_i(r) is the same query ending at
m, so no suffix is rescanned. Cost entries are direct finite-array reads.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- An executable active list with its no-duplicates invariant. Its finite-set
view merely wraps the existing list, so no sorting or deduplication is hidden. -/
structure ActiveRows (n : ℕ) where
  agents : List (Fin n)
  nodup : agents.Nodup

namespace ActiveRows

def finset {n : ℕ} (active : ActiveRows n) : Finset (Fin n) :=
  ⟨active.agents, active.nodup⟩

@[simp] theorem mem_finset {n : ℕ} (active : ActiveRows n) (i : Fin n) :
    i ∈ active.finset ↔ i ∈ active.agents := by rfl

@[simp] theorem card_finset {n : ℕ} (active : ActiveRows n) :
    active.finset.card = active.agents.length := by rfl

def erase {n : ℕ} (active : ActiveRows n) (i : Fin n) : ActiveRows n :=
  ⟨active.agents.erase i, active.nodup.erase i⟩

@[simp] theorem erase_finset {n : ℕ} (active : ActiveRows n) (i : Fin n) :
    (active.erase i).finset = active.finset.erase i := by
  ext j
  simp only [mem_finset, erase, List.Nodup.mem_erase_iff active.nodup, Finset.mem_erase]

def all (n : ℕ) : ActiveRows n := ⟨List.finRange n, List.nodup_finRange n⟩

@[simp] theorem all_finset (n : ℕ) : (all n).finset = Finset.univ := by
  ext i
  simp [all, List.mem_finRange]

end ActiveRows

/-- The actual input matrix, read through its outer and inner arrays. -/
def matrixCosts (rows : Array (Array ℚ)) (i : Fin rows.size) : ℕ → ℚ :=
  rowAt rows[i]

/-- Stored outer-array row lookup, with an empty default outside its bounds. -/
def cacheRow (caches : Array (Array ℚ)) (i : ℕ) : Array ℚ :=
  caches[i]?.getD #[]

/-- Correctness of the already materialized tables, proved by preprocessing. -/
def PrefixRowsValid (rows caches : Array (Array ℚ)) : Prop :=
  ∀ i : Fin rows.size, cacheRow caches i.val = prefixCache rows[i]

theorem prefixRows_valid (rows : Array (Array ℚ)) :
    PrefixRowsValid rows (prefixRows rows) := by
  intro i
  exact prefixRows_correct rows i.val i.isLt

/-- A residual row total costs one outer lookup and two scalar lookups. -/
def cachedMatrixMass {n : ℕ} (caches : Array (Array ℚ)) (i : Fin n) (l k : ℕ) : ℚ :=
  cachedMass (cacheRow caches i.val) l k

theorem cachedMatrixMass_eq (rows caches : Array (Array ℚ))
    (hv : PrefixRowsValid rows caches) (i : Fin rows.size) (l k : ℕ)
    (hk : l + k ≤ rows[i].size) :
    cachedMatrixMass caches i l k = mass (matrixCosts rows i) l k := by
  rw [cachedMatrixMass, hv i, cachedMass_prefixCache_eq_mass rows[i] l k hk]
  rfl

/-- The full total is let-bound once per agent before both early tests. -/
def cachedEarlyCandidates (rows caches : Array (Array ℚ))
    (A : Finset (Fin rows.size)) (l k : ℕ) : Finset (Fin rows.size) :=
  A.filter fun i =>
    let total := cachedMatrixMass caches i l k
    total = 0 ∨ matrixCosts rows i l = total

def cachedEarly (rows caches : Array (Array ℚ))
    (A : Finset (Fin rows.size)) (l k : ℕ) : Option (Fin rows.size) :=
  let candidates := cachedEarlyCandidates rows caches A l k
  if h : candidates.Nonempty then some (candidates.min' h) else none

theorem cachedEarlyCandidates_eq (rows caches : Array (Array ℚ))
    (hv : PrefixRowsValid rows caches) (A : Finset (Fin rows.size)) (l k : ℕ)
    (hk : ∀ i ∈ A, l + k ≤ rows[i].size) :
    cachedEarlyCandidates rows caches A l k = earlyCandidates (matrixCosts rows) A l k := by
  ext i
  simp only [cachedEarlyCandidates, earlyCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨hi, by simpa only [cachedMatrixMass_eq rows caches hv i l k (hk i hi)] using h⟩
  · rintro ⟨hi, h⟩
    exact ⟨hi, by simpa only [cachedMatrixMass_eq rows caches hv i l k (hk i hi)] using h⟩

theorem cachedEarly_eq (rows caches : Array (Array ℚ))
    (hv : PrefixRowsValid rows caches) (A : Finset (Fin rows.size)) (l k : ℕ)
    (hk : ∀ i ∈ A, l + k ≤ rows[i].size) :
    cachedEarly rows caches A l k = early (matrixCosts rows) A l k := by
  simp only [cachedEarly, early, cachedEarlyCandidates_eq rows caches hv A l k hk]

/-- Conservative charged result of the actual cached early pass. The total is
computed once per row in the filter; a second linear pass chooses the least
qualifying identifier. The returned data and charge are available together. -/
def cachedEarlyCounted (rows caches : Array (Array ℚ))
    (A : Finset (Fin rows.size)) (l k : ℕ) : Option (Fin rows.size) × ℕ :=
  (cachedEarly rows caches A l k, 16 * A.card + 4)

/-- Fixed-size rational Hill-formula evaluation, cached total, and one binary
search. The returned boundary and search counter are evaluated together. The
charge includes 48 setup/formula operations; the binary component itself
charges its executable divide-by-two fuel computation. -/
def cachedRowBoundary (rows caches : Array (Array ℚ)) (q l k : ℕ)
    (i : Fin rows.size) : BinaryResult :=
  let table := cacheRow caches i.val
  let total := cachedMass table l k
  let budget := bound q total (matrixCosts rows i l)
  let result := binarySafePrefix table l k budget
  ⟨result.boundary, result.queries + 1,
    result.operations + 48⟩

theorem cachedRowBoundary_eq (rows caches : Array (Array ℚ))
    (hv : PrefixRowsValid rows caches) (q l k : ℕ) (hq : 1 ≤ q)
    (i : Fin rows.size) (hn : ∀ j, 0 ≤ matrixCosts rows i j)
    (ha : Antitone (matrixCosts rows i)) (hk : l + k ≤ rows[i].size) :
    (cachedRowBoundary rows caches q l k i).boundary =
      safePrefix (matrixCosts rows i) l k
        (bound q (mass (matrixCosts rows i) l k) (matrixCosts rows i l)) := by
  simp only [cachedRowBoundary, hv i,
    cachedMass_prefixCache_eq_mass rows[i] l k hk]
  exact binarySafePrefix_eq_safePrefix rows[i] l k _
    (fun j hj => by simpa only [matrixCosts, rowAt_of_lt rows[i] j hj] using hn j) hk
    (bound_nonneg (matrixCosts rows i) l k q hq hn ha)

theorem cachedRowBoundary_operations_le (rows caches : Array (Array ℚ))
    (q l k m : ℕ) (i : Fin rows.size) (hk : k ≤ m) :
    (cachedRowBoundary rows caches q l k i).operations ≤
      80 * (Nat.log2 (m + 1) + 1) := by
  have hs := (binarySafePrefix_counts_uniform (cacheRow caches i.val) l k m
    (bound q (cachedMass (cacheRow caches i.val) l k) (matrixCosts rows i l)) hk).2
  simp only [cachedRowBoundary]
  omega

/-- Charges the cached early filter, its linear tie-breaking pass, and setup.
All tests use already stored totals; this charge contains no item-count factor. -/
def cachedEarlyOps {n : ℕ} (A : Finset (Fin n)) : ℕ := 16 * A.card + 4

/-- Any active maximizer of the verified safe boundaries is a valid moving
knife choice. Tie-breaking is immaterial to the allocation guarantee. -/
theorem knife_safe_of_max {n : ℕ} (c : Fin n → ℕ → ℚ)
    (A : Finset (Fin n)) (l k : ℕ) (hA : 3 ≤ A.card)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i))
    (hT : ∀ i ∈ A, mass (c i) l k ≠ 0)
    (hpT : ∀ i ∈ A, c i l ≠ mass (c i) l k)
    (a : Fin n) (s : ℕ) (hamem : a ∈ A)
    (hs : s = safePrefix (c a) l k (bound A.card (mass (c a) l k) (c a l)))
    (hmax : ∀ i ∈ A,
      safePrefix (c i) l k (bound A.card (mass (c i) l k) (c i l)) ≤ s) :
    s < k ∧ mass (c a) l s ≤ bound A.card (mass (c a) l k) (c a l) ∧
      ∀ i ∈ A.erase a,
        bound (A.erase a).card (mass (c i) (l + s) (k - s)) (c i (l + s)) ≤
          bound A.card (mass (c i) l k) (c i l) := by
  let f := fun i => safePrefix (c i) l k (bound A.card (mass (c i) l k) (c i l))
  have hnon (i) (hi : i ∈ A) :=
    bound_nonneg (c i) l k A.card (by omega) (hn i hi) (ha i hi)
  have hlt (i) (hi : i ∈ A) :=
    bound_lt_mass (c i) l k A.card hA (hn i hi) (ha i hi) (hT i hi) (hpT i hi)
  have hsk : s < k := by
    rw [hs]
    exact safePrefix_lt (c a) l k _ (hnon a hamem) (hlt a hamem)
  refine ⟨hsk, ?_, ?_⟩
  · rw [hs]
    exact (safePrefix_spec (c a) l k _ (hnon a hamem)).1
  · intro i hi
    have hiA := Finset.mem_of_mem_erase hi
    have hfi : f i < k := safePrefix_lt (c i) l k _ (hnon i hiA) (hlt i hiA)
    have hc := (safePrefix_spec (c i) l k _ (hnon i hiA)).2 hfi
    change bound A.card (mass (c i) l k) (c i l) < mass (c i) l (f i + 1) at hc
    have hcross : bound A.card (mass (c i) l k) (c i l) < mass (c i) l (s + 1) :=
      hc.trans_le (mass_mono (c i) l (hn i hiA) (Nat.succ_le_succ (hmax i hiA)))
    have hcard := Finset.card_erase_add_one hamem
    have hh := bound_tail (c i) l k s (A.erase a).card (by omega)
      (hn i hiA) (ha i hiA) hsk (by simpa [hcard] using hcross)
    simpa [hcard] using hh

theorem cachedRowBoundary_queries_le (rows caches : Array (Array ℚ))
    (q l k m : ℕ) (i : Fin rows.size) (hk : k ≤ m) :
    (cachedRowBoundary rows caches q l k i).queries ≤ Nat.log2 (m + 1) + 3 := by
  have hs := (binarySafePrefix_counts_uniform (cacheRow caches i.val) l k m
    (bound q (cachedMass (cacheRow caches i.val) l k) (matrixCosts rows i l)) hk).1
  simp only [cachedRowBoundary]
  omega

/-- The executable knife materializes each active boundary exactly once, then
performs a linear maximum scan over those stored natural numbers. The active
list is traversed sequentially; neither cost access nor score access uses list
indexing. The 4q+4 charge includes active-list traversal and setup. -/
def cachedKnifeCounted (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) : BoundaryChoice (Fin rows.size) × ℕ :=
  let q := active.agents.length
  let result := batchBest (cachedRowBoundary rows caches q l k) active.agents
  (⟨result.1.value, result.1.operations + 4 * q + 4⟩, result.2)

def cachedKnife (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) : Option (Fin rows.size × ℕ) :=
  (cachedKnifeCounted rows caches active l k).1.value

def cachedKnifeOps (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) : ℕ :=
  (cachedKnifeCounted rows caches active l k).1.operations

/-- Same moving-knife contract as the linear semantic algorithm, with every
binary-search and tail-domination premise discharged from the finite input. -/
theorem cachedKnife_spec (rows caches : Array (Array ℚ))
    (hv : PrefixRowsValid rows caches) (active : ActiveRows rows.size) (l k : ℕ)
    (hA : 3 ≤ active.finset.card)
    (hn : ∀ i ∈ active.finset, ∀ j, 0 ≤ matrixCosts rows i j)
    (ha : ∀ i ∈ active.finset, Antitone (matrixCosts rows i))
    (hk : ∀ i ∈ active.finset, l + k ≤ rows[i].size)
    (hT : ∀ i ∈ active.finset, mass (matrixCosts rows i) l k ≠ 0)
    (hpT : ∀ i ∈ active.finset, matrixCosts rows i l ≠ mass (matrixCosts rows i) l k) :
    ∃ a s, cachedKnife rows caches active l k = some (a, s) ∧ a ∈ active.finset ∧ s < k ∧
      mass (matrixCosts rows a) l s ≤
        bound active.finset.card (mass (matrixCosts rows a) l k) (matrixCosts rows a l) ∧
      ∀ i ∈ active.finset.erase a,
        bound (active.finset.erase a).card (mass (matrixCosts rows i) (l + s) (k - s))
          (matrixCosts rows i (l + s)) ≤
          bound active.finset.card (mass (matrixCosts rows i) l k) (matrixCosts rows i l) := by
  let compute := cachedRowBoundary rows caches active.finset.card l k
  have hne : active.agents ≠ [] := by
    intro he
    have hh := active.card_finset
    rw [he] at hh
    simp only [List.length_nil] at hh
    omega
  obtain ⟨a, haList, hout, hmax⟩ := batchBest_spec compute active.agents hne
  have hamem : a ∈ active.finset := haList
  have heq (i : Fin rows.size) (hi : i ∈ active.finset) :
      (compute i).boundary = safePrefix (matrixCosts rows i) l k
        (bound active.finset.card (mass (matrixCosts rows i) l k) (matrixCosts rows i l)) :=
    cachedRowBoundary_eq rows caches hv active.finset.card l k (by omega) i
      (hn i hi) (ha i hi) (hk i hi)
  have hmax' : ∀ i ∈ active.finset,
      safePrefix (matrixCosts rows i) l k
        (bound active.finset.card (mass (matrixCosts rows i) l k) (matrixCosts rows i l)) ≤
          (compute a).boundary := by
    intro i hi
    rw [← heq i hi]
    exact hmax i hi
  have hs := knife_safe_of_max (matrixCosts rows) active.finset l k hA hn ha hT hpT
    a (compute a).boundary hamem (heq a hamem) hmax'
  exact ⟨a, (compute a).boundary, hout, hamem, hs⟩

/-- Every returned choice is active, independently of numerical assumptions. -/
theorem cachedKnife_some (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) (a : Fin rows.size) (s : ℕ)
    (h : cachedKnife rows caches active l k = some (a, s)) : a ∈ active.finset := by
  let compute := cachedRowBoundary rows caches active.agents.length l k
  have hs := bestBoundary_spec (computeBoundaryBatch compute active.agents).values
  change (bestBoundary (computeBoundaryBatch compute active.agents).values).value = some (a, s) at h
  rw [h] at hs
  rw [computeBoundaryBatch_values] at hs
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hs.1
  have hba : b = a := congrArg Prod.fst he
  simpa only [hba] using hb

/-- A branch-local O(q log(m+1)) arithmetic bound, including row formulas,
logarithm/fuel computation, eager storage, and linear maximum selection. -/
theorem cachedKnifeOps_le (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k m : ℕ) (hk : k ≤ m)
    (hA : 0 < active.finset.card) :
    cachedKnifeOps rows caches active l k ≤
      100 * active.finset.card * (Nat.log2 (m + 1) + 1) := by
  have hb := (batchBest_operations
    (cachedRowBoundary rows caches active.agents.length l k) active.agents
    (Nat.log2 (m + 1) + 3) (80 * (Nat.log2 (m + 1) + 1))
    (fun i _hi => cachedRowBoundary_queries_le rows caches active.agents.length l k m i hk)
    (fun i _hi => cachedRowBoundary_operations_le rows caches active.agents.length l k m i hk)).1
  simp only [ActiveRows.card_finset] at hA ⊢
  unfold cachedKnifeOps cachedKnifeCounted
  dsimp only
  nlinarith

/-- Total cached range-query count of the materialized boundary batch. -/
theorem cachedKnifeQueries_le (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k m : ℕ) (hk : k ≤ m) :
    (cachedKnifeCounted rows caches active l k).2 ≤
      active.finset.card * (Nat.log2 (m + 1) + 3) := by
  have hb := (batchBest_operations
    (cachedRowBoundary rows caches active.agents.length l k) active.agents
    (Nat.log2 (m + 1) + 3) (80 * (Nat.log2 (m + 1) + 1))
    (fun i _hi => cachedRowBoundary_queries_le rows caches active.agents.length l k m i hk)
    (fun i _hi => cachedRowBoundary_operations_le rows caches active.agents.length l k m i hk)).2
  exact hb

/-- All nonterminal guard, scan, erase and splice setup charges at one level. -/
def cachedLevelOps (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k : ℕ) : ℕ :=
  20 + 4 * active.finset.card + cachedEarlyOps active.finset +
    cachedKnifeOps rows caches active l k + 5

theorem cachedLevelOps_le (rows caches : Array (Array ℚ))
    (active : ActiveRows rows.size) (l k m : ℕ) (hk : k ≤ m)
    (hA : 0 < active.finset.card) :
    cachedLevelOps rows caches active l k ≤
      160 * active.finset.card * (Nat.log2 (m + 1) + 1) := by
  have hh := cachedKnifeOps_le rows caches active l k m hk hA
  unfold cachedLevelOps cachedEarlyOps
  nlinarith

end ExactHillShares.Algorithm
