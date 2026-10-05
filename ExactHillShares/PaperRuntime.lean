import ExactHillShares.PaperAlgorithm

/-!
# Complete paper-style arithmetic runtime

The charged model has unit-cost exact rational arithmetic, rational comparison,
floor, array lookup/update and amortized push, and bounded integer control.
It does not claim bit complexity or Lean VM running time. The charge is a
structural arithmetic cost model for the independently
defined output-only `allocatePaper`. The instrumented helper has a proved equal
output, but evaluating its analysis counters can cost additional work and is
not asserted to obey the modeled bound. The actual program never calls those
terminal/DP analysis-counter functions.
The detailed estimate retains the sorting, linear prefix preprocessing,
quadratic-in-agents binary search, terminal cubic DP and linear pointer terms.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- The materialized rank-to-original lift includes rank-closure traversal and
its O(nm) pointer pass. It uses the already computed merge-sort cache. -/
theorem paperLiftCounted_operations_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (cost : Fin n → Fin m → ℚ) (cached : Vector (MergeSorting.CountedRow m) n)
    (hcached : cached = MergeSorting.countedSortRows cost) (out : Allocation n) :
    (paperLiftCounted hn cost cached hcached out).operations ≤
      4 * (n + 1) * m + 34 * (n * m) := by
  unfold paperLiftCounted
  dsimp only
  exact Nat.add_le_add_left (PointerLift.lemma3_1_after_sorting _ hn hm) _

/-- Source-shaped, explicit end-to-end estimate before using n<m. Every term
models a concrete stage of the output-only implementation. -/
theorem allocatePaperOps_source_bound {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j) (hmn : ¬ m ≤ n) :
    allocatePaperOps hn cost ≤
      50 * n * m * (Nat.log2 m + 1) +
      1000 * n^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 +
      4 * n * (m + 1) + 4 * (n + 1) * m + 34 * (n * m) + 3 * n + 4 := by
  have hm : 0 < m := by omega
  have hsort := MergeSorting.countedSortRows_operations_le hm cost
  have hrun := allocateBinaryRowsOps_bound
    (paperDescendingRows (MergeSorting.countedSortRows cost)) m hn
    (fun i => by simpa [Vector.get] using paperDescendingRows_size cost i)
    (by simpa only [vectorCosts_paperDescendingRows] using originalRows_nonneg cost hc)
    (by simpa only [vectorCosts_paperDescendingRows] using originalRows_antitone cost hc)
  unfold allocatePaperOps allocatePaperCounted
  rw [dif_neg hmn]
  dsimp only
  cases hresult : (allocateBinaryRowsCounted
      (paperDescendingRows (MergeSorting.countedSortRows cost)) m).output with
  | none =>
    dsimp only
    unfold allocateBinaryRowsOps at hrun
    omega
  | some ranked =>
    dsimp only
    have hlift := paperLiftCounted_operations_le hn hm cost
      (MergeSorting.countedSortRows cost) rfl ranked
    unfold allocateBinaryRowsOps at hrun
    omega

/-- The displayed paper dependence O(nm log(m+1)+n² log(m+1)+m³), including
all preprocessing and output. The singleton branch also satisfies this bound. -/
theorem allocatePaperOps_bound {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j) :
    allocatePaperOps hn cost ≤
      120 * n * m * (Nat.log2 (m + 1) + 1) +
      1000 * n^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 := by
  by_cases hmn : m ≤ n
  · have heq : allocatePaperOps hn cost = 3 * m + 2 := by
      simp [allocatePaperOps, allocatePaperCounted, hmn]
    rw [heq]
    have hh : m + 1 ≤ (m + 1)^3 := Nat.le_self_pow (by decide) _
    omega
  · have h := allocatePaperOps_source_bound hn cost hc hmn
    have hm : 0 < m := by omega
    have hlog : Nat.log2 m ≤ Nat.log2 (m + 1) := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right (by omega)
    have hs := Nat.mul_le_mul_left (50 * n * m) (Nat.add_le_add_right hlog 1)
    have hn' : n ≤ n * m := Nat.le_mul_of_pos_right _ hm
    have hm' : m ≤ n * m := Nat.le_mul_of_pos_left _ hn
    have hnm : 1 ≤ n * m := Nat.mul_pos hn hm
    have hg : n * m ≤ n * m * (Nat.log2 (m + 1) + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith

/-- Singleton preprocessing before any row read yields the item-count-only
cubic bound even if arbitrarily many agents are supplied. -/
theorem allocatePaperOps_cubic {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j) :
    allocatePaperOps hn cost ≤ 6000 * (m + 1)^3 := by
  by_cases hmn : m ≤ n
  · have heq : allocatePaperOps hn cost = 3 * m + 2 := by
      simp [allocatePaperOps, allocatePaperCounted, hmn]
    rw [heq]
    have hh : m + 1 ≤ (m + 1)^3 := Nat.le_self_pow (by decide) _
    omega
  · have hb := allocatePaperOps_bound hn cost hc
    have hnle : n ≤ m + 1 := by omega
    have hmle : m ≤ m + 1 := by omega
    have hl : Nat.log2 (m + 1) + 1 ≤ 2 * (m + 1) := by
      have hh := Nat.log2_le_self (m + 1)
      omega
    have hnm := Nat.mul_le_mul hnle hmle
    have hn2 := Nat.pow_le_pow_left hnle 2
    have hs := Nat.mul_le_mul hnm hl
    have hr := Nat.mul_le_mul hn2 hl
    nlinarith

/-- Conventional m³ form for nonempty item sets. Empty input returns the empty
owner vector in constant work, as covered by `allocatePaperOps_cubic`. -/
theorem allocatePaperOps_cubic_nonempty {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j) :
    allocatePaperOps hn cost ≤ 48000 * m^3 := by
  have hb := allocatePaperOps_cubic hn cost hc
  have hh : m + 1 ≤ 2 * m := by omega
  have hp := Nat.pow_le_pow_left hh 3
  nlinarith

/-- Combined executable correctness and source-shaped arithmetic guarantee,
with no orderedness, crossing, sorting, success, or callback assumptions. -/
theorem allocatePaper_hill_and_runtime {n m : ℕ} (hn : 2 ≤ n)
    (cost : Fin n → Fin m → ℚ) (α : Fin n → ℝ)
    (hv : ∀ i, IsNormalizedExact (fun j => (cost i j : ℝ)) (α i)) :
    ∃ out, allocatePaper (by omega) cost = some out ∧
      (∀ i, load (fun j => (cost i j : ℝ)) (PointerLift.read out) i ≤ hill n (α i)) ∧
      allocatePaperOps (by omega) cost ≤
        120 * n * m * (Nat.log2 (m + 1) + 1) +
        1000 * n^2 * (Nat.log2 (m + 1) + 1) + 3000 * (m + 1)^3 := by
  have hc : ∀ i j, 0 ≤ cost i j := by
    intro i j
    have hh := ((hv i).1 j).1
    change (0 : ℝ) ≤ (cost i j : ℝ) at hh
    exact_mod_cast hh
  obtain ⟨out, hout, hsafe⟩ := allocatePaper_hill_safe hn cost α hv
  exact ⟨out, hout, hsafe, allocatePaperOps_bound (by omega) cost hc⟩

/-- End-to-end theorem in the item-only arithmetic form claimed after the
cost-independent n≥m preprocessing. -/
theorem allocatePaper_hill_and_cubic {n m : ℕ} (hn : 2 ≤ n)
    (cost : Fin n → Fin m → ℚ) (α : Fin n → ℝ)
    (hv : ∀ i, IsNormalizedExact (fun j => (cost i j : ℝ)) (α i)) :
    ∃ out, allocatePaper (by omega) cost = some out ∧
      (∀ i, load (fun j => (cost i j : ℝ)) (PointerLift.read out) i ≤ hill n (α i)) ∧
      allocatePaperOps (by omega) cost ≤ 6000 * (m + 1)^3 := by
  have hc : ∀ i j, 0 ≤ cost i j := by
    intro i j
    have hh := ((hv i).1 j).1
    change (0 : ℝ) ≤ (cost i j : ℝ) at hh
    exact_mod_cast hh
  obtain ⟨out, hout, hsafe⟩ := allocatePaper_hill_safe hn cost α hv
  exact ⟨out, hout, hsafe, allocatePaperOps_cubic (by omega) cost hc⟩

end ExactHillShares.Algorithm
